-- Prove2me | solution 1 for N25.level25_gamma0_index
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:58.091291+00:00
-- url     : https://prove2.me/submissions/0c71d181-87ee-446e-9980-9edb2a5a6421

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_primitive_rows
import Theorems.Thm_N25_level25_gammaH_rightRel
import Theorems.Thm_N25_level25_gamma0_row_normalization
import Theorems.Thm_N25_level25_gamma0_scaling_invariance
import Theorems.Thm_N25_level25_gamma0_finite_census
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

namespace N25

private theorem quotient_card_of_normal_form {G R : Type*} (s : Setoid G)
    (f : G → R) (hf : Function.Surjective f) (code : R → ℕ)
    (hcode : Function.Injective code) (normal : R → ℕ)
    (hattain : ∀ r, ∃ v, code v = normal r ∧ normal v = normal r)
    (hrel : ∀ a b, s a b ↔ normal (f a) = normal (f b)) :
    Nat.card (Quotient s) = Nat.card {r : R // code r = normal r} := by
  classical
  let nrm : R → R := fun r => (hattain r).choose
  have hncode (r : R) : code (nrm r) = normal r := (hattain r).choose_spec.1
  have hnnorm (r : R) : normal (nrm r) = normal r := (hattain r).choose_spec.2
  let fn : G → {r : R // code r = normal r} :=
    fun a => ⟨nrm (f a), (hncode (f a)).trans (hnnorm (f a)).symm⟩
  have hfn (a b : G) (h : s a b) : fn a = fn b := by
    apply Subtype.ext
    apply hcode
    change code (nrm (f a)) = code (nrm (f b))
    rw [hncode, hncode, (hrel a b).mp h]
  let qf : Quotient s → {r : R // code r = normal r} := Quotient.lift fn hfn
  apply Nat.card_congr
  apply Equiv.ofBijective qf
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y h
    apply Quotient.sound
    apply (hrel x y).mpr
    have hc := congrArg (fun v : {r : R // code r = normal r} => code v.val) h
    change code (nrm (f x)) = code (nrm (f y)) at hc
    simpa only [hncode] using hc
  · intro r
    obtain ⟨a, ha⟩ := hf r.val
    refine ⟨Quotient.mk s a, ?_⟩
    apply Subtype.ext
    apply hcode
    change code (nrm (f a)) = code r.val
    rw [hncode, ha, r.property]

/-- The full-unit residue-row quotient has thirty integral modular cosets. -/
theorem _root_.solution : (CongruenceSubgroup.Gamma0 25).index = 30 := by
  classical
  let R := ZMod 25 × ZMod 25
  let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
  let normal : R → R := fun r =>
    if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
  let code : R → ℕ := fun r => r.1.val + 25*r.2.val
  let row : SL(2, ℤ) → R := fun A => ((A 1 0 : ZMod 25), (A 1 1 : ZMod 25))
  have hp : ∀ A, primitive (row A) := level25_primitive_rows.1
  have hlift : ∀ r : R, primitive r → ∃ A, row A = r := level25_primitive_rows.2
  let PR := {r : R // primitive r}
  let f : SL(2, ℤ) → PR := fun A => ⟨row A, hp A⟩
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨A, hA⟩ := hlift r.val r.property
    exact ⟨A, Subtype.ext hA⟩
  have hcode : Function.Injective code := by
    intro r s h
    have hr1 := r.1.val_lt
    have hr2 := r.2.val_lt
    have hs1 := s.1.val_lt
    have hs2 := s.2.val_lt
    change r.1.val + 25*r.2.val = s.1.val + 25*s.2.val at h
    have hv : r.1.val = s.1.val ∧ r.2.val = s.2.val := by omega
    apply Prod.ext
    · apply Fin.ext
      change r.1.val = s.1.val
      exact hv.1
    · apply Fin.ext
      change r.2.val = s.2.val
      exact hv.2
  let Γ := CongruenceSubgroup.Gamma0 25
  let rel := QuotientGroup.rightRel Γ
  have hrowrel (A B : SL(2, ℤ)) : rel A B ↔
      ∃ u : (ZMod 25)ˣ, row B = ((u : ZMod 25)*(row A).1,(u : ZMod 25)*(row A).2) := by
    constructor
    · intro h
      have h' : QuotientGroup.rightRel (CohCarrier.GammaH 25 ⊤) A B := by
        rw [CohCarrier.GammaH_top]
        exact h
      obtain ⟨u, _, hc, hd⟩ := (level25_gammaH_rightRel ⊤ A B).mp h'
      exact ⟨u, Prod.ext hc hd⟩
    · rintro ⟨u, h⟩
      have h' : QuotientGroup.rightRel (CohCarrier.GammaH 25 ⊤) A B :=
        (level25_gammaH_rightRel ⊤ A B).mpr
          ⟨u, Subgroup.mem_top _, congrArg Prod.fst h, congrArg Prod.snd h⟩
      rw [CohCarrier.GammaH_top] at h'
      exact h'
  have hrel (A B : SL(2, ℤ)) : rel A B ↔ code (normal (row A)) = code (normal (row B)) := by
    constructor
    · intro h
      obtain ⟨u, hu⟩ := (hrowrel A B).mp h
      have hs : normal ((u : ZMod 25)*(row A).1,(u : ZMod 25)*(row A).2) = normal (row A) :=
        (level25_gamma0_scaling_invariance (row A) (hp A) u).1
      rw [hu, hs]
    · intro h
      have hn : normal (row A) = normal (row B) := hcode h
      obtain ⟨uA, huA⟩ := (level25_gamma0_row_normalization (row A) (hp A)).1
      obtain ⟨uB, huB⟩ := (level25_gamma0_row_normalization (row B) (hp B)).1
      apply (hrowrel A B).mpr
      refine ⟨uB⁻¹*uA, ?_⟩
      have hc := congrArg Prod.fst (huA.trans (hn.trans huB.symm))
      have hd := congrArg Prod.snd (huA.trans (hn.trans huB.symm))
      change (uA : ZMod 25)*(row A).1 = (uB : ZMod 25)*(row B).1 at hc
      change (uA : ZMod 25)*(row A).2 = (uB : ZMod 25)*(row B).2 at hd
      apply Prod.ext
      · change (row B).1 = ((uB⁻¹*uA : (ZMod 25)ˣ) : ZMod 25)*(row A).1
        calc
          _ = ((uB⁻¹ : (ZMod 25)ˣ) : ZMod 25)*((uB : ZMod 25)*(row B).1) := by simp
          _ = ((uB⁻¹ : (ZMod 25)ˣ) : ZMod 25)*((uA : ZMod 25)*(row A).1) := by rw [hc]
          _ = _ := by simp only [Units.val_mul]; ring
      · change (row B).2 = ((uB⁻¹*uA : (ZMod 25)ˣ) : ZMod 25)*(row A).2
        calc
          _ = ((uB⁻¹ : (ZMod 25)ˣ) : ZMod 25)*((uB : ZMod 25)*(row B).2) := by simp
          _ = ((uB⁻¹ : (ZMod 25)ˣ) : ZMod 25)*((uA : ZMod 25)*(row A).2) := by rw [hd]
          _ = _ := by simp only [Units.val_mul]; ring
  have hattain (r : PR) : ∃ v : PR,
      code v.val = code (normal r.val) ∧ code (normal v.val) = code (normal r.val) := by
    have hn := level25_gamma0_row_normalization r.val r.property
    refine ⟨⟨normal r.val, hn.2.1⟩, rfl, ?_⟩
    exact congrArg code hn.2.2
  have hcard : Nat.card (Quotient rel) = Nat.card {r : PR // code r.val = code (normal r.val)} :=
    quotient_card_of_normal_form rel f hf (fun r => code r.val)
      (fun a b h => Subtype.ext (hcode h)) (fun r => code (normal r.val)) hattain hrel
  let e : {r : PR // code r.val = code (normal r.val)} ≃
      {r : R // primitive r ∧ normal r = r} :=
    { toFun := fun r => ⟨r.val.val, r.val.property, (hcode r.property).symm⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩, congrArg code r.property.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card {r : R // primitive r ∧ normal r = r} = 30 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact level25_gamma0_finite_census.1
  calc
    Γ.index = Nat.card (SL(2, ℤ) ⧸ Γ) := rfl
    _ = Nat.card (Quotient rel) :=
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ).symm
    _ = Nat.card {r : PR // code r.val = code (normal r.val)} := hcard
    _ = Nat.card {r : R // primitive r ∧ normal r = r} := Nat.card_congr e
    _ = 30 := hc

end N25
