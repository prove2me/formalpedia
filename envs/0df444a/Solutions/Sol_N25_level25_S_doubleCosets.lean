-- Prove2me | solution 1 for N25.level25_S_doubleCosets
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:43.800204+00:00
-- url     : https://prove2.me/submissions/6c334047-ca9b-4099-9c52-d7f4861b99d2

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_primitive_rows
import Theorems.Thm_N25_level25_gammaH_rightRel
import Theorems.Thm_N25_level25_subgroup_membership
import Theorems.Thm_N25_level25_elliptic_orbit_normalization
import Theorems.Thm_N25_level25_row_census
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

private theorem doubleCoset_card_of_normal_form {G R : Type*} [Group G]
    (Γ K : Subgroup G) (f : G → R) (hf : Function.Surjective f)
    (code : R → ℕ) (hcode : Function.Injective code) (normal : R → ℕ)
    (hstable : ∀ a b, DoubleCoset.setoid (Γ : Set G) (K : Set G) a b →
      normal (f a) = normal (f b))
    (hconnect : ∀ a b, f a = f b → DoubleCoset.setoid (Γ : Set G) (K : Set G) a b)
    (hattain : ∀ a, ∃ b, DoubleCoset.setoid (Γ : Set G) (K : Set G) a b ∧
      code (f b) = normal (f a)) :
    Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) =
      Nat.card {r : R // code r = normal r} := by
  let s := DoubleCoset.setoid (Γ : Set G) (K : Set G)
  apply quotient_card_of_normal_form s f hf code hcode normal
  · intro r
    obtain ⟨a, rfl⟩ := hf r
    obtain ⟨b, hab, hb⟩ := hattain a
    exact ⟨f b, hb, (hstable a b hab).symm⟩
  · intro a b
    constructor
    · exact hstable a b
    · intro hab
      obtain ⟨a', haa', ha'⟩ := hattain a
      obtain ⟨b', hbb', hb'⟩ := hattain b
      have heq : f a' = f b' := hcode (ha'.trans (hab.trans hb'.symm))
      exact s.trans haa' (s.trans (hconnect a' b' heq) (s.symm hbb'))

private theorem doubleCoset_zpowers_invariant {G : Type*} [Group G]
    (Γ : Subgroup G) (g : G) (F : G → ℕ)
    (hleft : ∀ h ∈ Γ, ∀ a, F (h * a) = F a)
    (hright : ∀ a, F (a * g) = F a) :
    ∀ a b, DoubleCoset.setoid (Γ : Set G) (Subgroup.zpowers g : Set G) a b → F a = F b := by
  let K : Subgroup G :=
    { carrier := {b | ∀ a, F (a * b) = F a}
      one_mem' := by intro a; simp
      mul_mem' := by
        intro b c hb hc a
        rw [← mul_assoc, hc, hb]
      inv_mem' := by
        intro b hb a
        have h := hb (a * b⁻¹)
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm }
  have hg : g ∈ K := hright
  have hK : Subgroup.zpowers g ≤ K := Subgroup.zpowers_le.mpr hg
  intro a b hab
  obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.mp hab
  have hkp : ∀ a, F (a * k) = F a := hK hk
  rw [mul_assoc, hleft h hh, hkp]

/-- The elliptic involution has eighty double cosets at the prescribed level subgroup. -/
theorem _root_.solution :
    Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH 25 H25 : Set SL(2, ℤ))
      (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) = 80 := by
  classical
  let R := Fin 25 × Fin 25
  let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
  let scale : ℕ → R → R := fun h r =>
    (⟨h*r.1.val%25, Nat.mod_lt _ (by decide)⟩,
     ⟨h*r.2.val%25, Nat.mod_lt _ (by decide)⟩)
  let labels : Fin 4 → ℕ := ![1,7,18,24]
  let code : R → ℕ := fun r => r.1.val + 25*r.2.val
  let normcode : R → ℕ := fun r =>
    min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
  let S : R → R := fun r => (r.2, ⟨(25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
  let snorm : R → ℕ := fun r => min (normcode r) (normcode (S r))
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
    apply Prod.ext <;> apply Fin.ext
    all_goals
      have hr1 := r.1.isLt
      have hr2 := r.2.isLt
      have hs1 := s.1.isLt
      have hs2 := s.2.isLt
      change r.1.val + 25*r.2.val = s.1.val + 25*s.2.val at h
      omega
  have hmul (A B : SL(2, ℤ)) (i j : Fin 2) :
      ((A*B) i j : ZMod 25) = (A i 0 : ZMod 25)*(B 0 j : ZMod 25) +
        (A i 1 : ZMod 25)*(B 1 j : ZMod 25) := by
    change (((A : Matrix (Fin 2) (Fin 2) ℤ)*(B : Matrix (Fin 2) (Fin 2) ℤ)) i j : ZMod 25) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrowS (A : SL(2, ℤ)) : row (A*ModularGroup.S) = S (row A) := by
    apply Prod.ext
    · change ((A*ModularGroup.S) 1 0 : ZMod 25) = (A 1 1 : ZMod 25)
      rw [hmul]
      simp [ModularGroup.S]
    · change ((A*ModularGroup.S) 1 1 : ZMod 25) = -(A 1 0 : ZMod 25)
      rw [hmul]
      simp [ModularGroup.S]
  have hscale (i : Fin 4) (r : R) :
      (scale (labels i) r).1 = ((fun x y : ZMod 25 => x*y) ((labels i : ℕ) : ZMod 25) r.1) ∧
      (scale (labels i) r).2 = ((fun x y : ZMod 25 => x*y) ((labels i : ℕ) : ZMod 25) r.2) := by
    fin_cases i <;> constructor <;> apply Fin.ext <;> rfl
  have huclass (u : (ZMod 25)ˣ) (hu : u ∈ H25) :
      ∃ i : Fin 4, (u : ZMod 25) = ((labels i : ℕ) : ZMod 25) := by
    rcases (level25_subgroup_membership u).mp hu with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  have hulabel (i : Fin 4) : ∃ u : (ZMod 25)ˣ,
      u ∈ H25 ∧ (u : ZMod 25) = ((labels i : ℕ) : ZMod 25) := by
    have hc : ∀ i : Fin 4, Nat.Coprime (labels i) 25 := by decide +kernel
    refine ⟨ZMod.unitOfCoprime (labels i) (hc i), ?_, rfl⟩
    rw [level25_subgroup_membership]
    change ((labels i : ℕ) : ZMod 25) = 1 ∨ ((labels i : ℕ) : ZMod 25) = 7 ∨
      ((labels i : ℕ) : ZMod 25) = 18 ∨ ((labels i : ℕ) : ZMod 25) = 24
    fin_cases i <;> norm_num [labels]
  obtain ⟨hatt, _, hsc, hgen⟩ := level25_elliptic_orbit_normalization
  have hleft (h : SL(2, ℤ)) (hh : h ∈ CohCarrier.GammaH 25 H25) (A : SL(2, ℤ)) :
      snorm (row (h*A)) = snorm (row A) := by
    have hrel : QuotientGroup.rightRel (CohCarrier.GammaH 25 H25) A (h*A) := by
      rw [QuotientGroup.rightRel_apply]
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
    obtain ⟨u, hu, hc, hd⟩ := (level25_gammaH_rightRel H25 A (h*A)).mp hrel
    obtain ⟨i, hi⟩ := huclass u hu
    have hr : row (h*A) = scale (labels i) (row A) := by
      apply Prod.ext
      · change ((h*A) 1 0 : ZMod 25) = (scale (labels i) (row A)).1
        rw [(hscale i (row A)).1, hc, hi]
      · change ((h*A) 1 1 : ZMod 25) = (scale (labels i) (row A)).2
        rw [(hscale i (row A)).2, hd, hi]
    rw [hr]
    exact (hsc (row A) i).1
  have hright (A : SL(2, ℤ)) : snorm (row (A*ModularGroup.S)) = snorm (row A) := by
    rw [hrowS]
    exact (hgen (row A)).1
  let Γ := CohCarrier.GammaH 25 H25
  let K := Subgroup.zpowers ModularGroup.S
  let ds := DoubleCoset.setoid (Γ : Set SL(2, ℤ)) (K : Set SL(2, ℤ))
  have hstable : ∀ A B, ds A B → snorm (row A) = snorm (row B) :=
    doubleCoset_zpowers_invariant Γ ModularGroup.S (fun A => snorm (row A)) hleft hright
  have hrl (A B : SL(2, ℤ)) (h : QuotientGroup.rightRel Γ A B) : ds A B := by
    apply DoubleCoset.rel_iff.mpr
    refine ⟨B*A⁻¹, (QuotientGroup.rightRel_apply).mp h, 1, K.one_mem, ?_⟩
    simp
  have hconnect (A B : SL(2, ℤ)) (h : f A = f B) : ds A B := by
    apply hrl
    apply (level25_gammaH_rightRel H25 A B).mpr
    have hr : row A = row B := congrArg Subtype.val h
    refine ⟨1, H25.one_mem, ?_, ?_⟩
    · have hc := congrArg Prod.fst hr
      change (A 1 0 : ZMod 25) = (B 1 0 : ZMod 25) at hc
      simpa only [Units.val_one, one_mul] using hc.symm
    · have hd := congrArg Prod.snd hr
      change (A 1 1 : ZMod 25) = (B 1 1 : ZMod 25) at hd
      simpa only [Units.val_one, one_mul] using hd.symm
  have hattain (A : SL(2, ℤ)) : ∃ B, ds A B ∧ code (row B) = snorm (row A) := by
    obtain ⟨i, n, hn⟩ := hatt (row A) (hp A)
    let C : SL(2, ℤ) := if n.val = 0 then A else A*ModularGroup.S
    have hC : row C = if n.val=0 then row A else S (row A) := by
      by_cases h : n.val=0 <;> simp [C, h, hrowS]
    let v := scale (labels i) (row C)
    have hv : primitive v := ((hsc (row C) i).2.2).mpr (hp C)
    obtain ⟨B, hB⟩ := hlift v hv
    obtain ⟨u, hu, hval⟩ := hulabel i
    have hCB : QuotientGroup.rightRel Γ C B := by
      apply (level25_gammaH_rightRel H25 C B).mpr
      refine ⟨u, hu, ?_, ?_⟩
      · have hb := congrArg Prod.fst hB
        change (B 1 0 : ZMod 25) = (scale (labels i) (row C)).1 at hb
        rw [hb, (hscale i (row C)).1, hval]
      · have hb := congrArg Prod.snd hB
        change (B 1 1 : ZMod 25) = (scale (labels i) (row C)).2 at hb
        rw [hb, (hscale i (row C)).2, hval]
    have hAC : ds A C := by
      by_cases h : n.val=0
      · simpa only [C, if_pos h] using ds.refl A
      · apply DoubleCoset.rel_iff.mpr
        refine ⟨1, Γ.one_mem, ModularGroup.S, Subgroup.mem_zpowers _, ?_⟩
        simp [C, h]
    refine ⟨B, ds.trans hAC (hrl C B hCB), ?_⟩
    change code (row B) = snorm (row A)
    rw [hB]
    change code (scale (labels i) (row C)) = snorm (row A)
    rw [hC]
    exact hn
  have hcard : Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) (K : Set SL(2, ℤ))) =
      Nat.card {r : PR // code r.val = snorm r.val} :=
    doubleCoset_card_of_normal_form Γ K f hf (fun r => code r.val)
      (fun a b h => Subtype.ext (hcode h)) (fun r => snorm r.val) hstable hconnect hattain
  rw [hcard]
  let e : {r : PR // code r.val = snorm r.val} ≃
      {r : R // primitive r ∧ code r = snorm r} :=
    { toFun := fun r => ⟨r.val.val, r.val.property, r.property⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩, r.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcen : (((Finset.univ : Finset R).filter primitive).filter
      (fun r => code r = normcode r) |>.filter (fun r => code r ≤ normcode (S r))).card = 80 :=
    level25_row_census.2.2.2.2.1
  have heq : (Finset.univ : Finset R).filter (fun r => primitive r ∧ code r = snorm r) =
      (((Finset.univ : Finset R).filter primitive).filter
        (fun r => code r = normcode r)).filter (fun r => code r ≤ normcode (S r)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hnle : normcode r ≤ code r := le_trans (min_le_left _ _) (min_le_left _ _)
    dsimp only [snorm]
    omega
  rw [heq]
  exact hcen

end N25
