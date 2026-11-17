-- Prove2me | solution 1 for N25.level25_gamma0_ST_doubleCosets
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:55.623791+00:00
-- url     : https://prove2.me/submissions/bfe75b2d-8ace-4a00-9a09-33b7760767db

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_primitive_rows
import Theorems.Thm_N25_level25_gammaH_rightRel
import Theorems.Thm_N25_level25_gamma0_row_normalization
import Theorems.Thm_N25_level25_gamma0_scaling_invariance
import Theorems.Thm_N25_level25_gamma0_elliptic_normalization
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

/-- The elliptic order-three operator has ten double cosets at Gamma0(25). -/
theorem _root_.solution :
    Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma0 25 : Set SL(2, ℤ))
      (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) = 10 := by
  classical
  let R := ZMod 25 × ZMod 25
  let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
  let normal : R → R := fun r =>
    if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
  let code : R → ℕ := fun r => r.1.val + 25*r.2.val
  let ST : R → R := fun r => (r.2,r.2-r.1)
  let stnorm : R → ℕ := fun r => min (code (normal r)) (min (code (normal (ST r))) (code (normal (ST (ST r)))))
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
  have hmul (A B : SL(2, ℤ)) (i j : Fin 2) :
      ((A*B) i j : ZMod 25) = (A i 0 : ZMod 25)*(B 0 j : ZMod 25) +
        (A i 1 : ZMod 25)*(B 1 j : ZMod 25) := by
    change (((A : Matrix (Fin 2) (Fin 2) ℤ)*(B : Matrix (Fin 2) (Fin 2) ℤ)) i j : ZMod 25) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrowST (A : SL(2, ℤ)) : row (A*(ModularGroup.S * ModularGroup.T)) = ST (row A) := by
    apply Prod.ext
    · change ((A*(ModularGroup.S * ModularGroup.T)) 1 0 : ZMod 25) = (A 1 1 : ZMod 25)
      rw [hmul]
      simp only [hmul]
      simp [ModularGroup.S, ModularGroup.T]
      <;> ring
    · change ((A*(ModularGroup.S * ModularGroup.T)) 1 1 : ZMod 25) = (A 1 1 : ZMod 25) - (A 1 0 : ZMod 25)
      rw [hmul]
      simp only [hmul]
      simp [ModularGroup.S, ModularGroup.T]
      <;> ring
  obtain ⟨_, hatt, hgen⟩ := level25_gamma0_elliptic_normalization
  have hSTscale (u : (ZMod 25)ˣ) (r : R) :
      ST ((u : ZMod 25)*r.1,(u : ZMod 25)*r.2) =
        ((u : ZMod 25)*(ST r).1,(u : ZMod 25)*(ST r).2) := by
    apply Prod.ext
    · rfl
    · dsimp only [ST]
      ring
  have hleft (h : SL(2, ℤ)) (hh : h ∈ Γ) (A : SL(2, ℤ)) :
      stnorm (row (h*A)) = stnorm (row A) := by
    have hrel : rel A (h*A) := by
      rw [QuotientGroup.rightRel_apply]
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
    obtain ⟨u, hu⟩ := (hrowrel A (h*A)).mp hrel
    have hn : normal ((u : ZMod 25)*(row A).1,(u : ZMod 25)*(row A).2) = normal (row A) :=
      (level25_gamma0_scaling_invariance (row A) (hp A) u).1
    have hpST := (hgen (row A) (hp A)).2.2.2
    have hpSTST := (hgen (ST (row A)) hpST).2.2.2
    have hnST : normal ((u : ZMod 25)*(ST (row A)).1,(u : ZMod 25)*(ST (row A)).2) = normal (ST (row A)) :=
      (level25_gamma0_scaling_invariance (ST (row A)) hpST u).1
    have hnSTST : normal ((u : ZMod 25)*(ST (ST (row A))).1,(u : ZMod 25)*(ST (ST (row A))).2) = normal (ST (ST (row A))) :=
      (level25_gamma0_scaling_invariance (ST (ST (row A))) hpSTST u).1
    rw [hu]
    dsimp only [stnorm]
    rw [hn]
    simp_rw [hSTscale]
    rw [hnST, hnSTST]
  have hright (A : SL(2, ℤ)) : stnorm (row (A*(ModularGroup.S * ModularGroup.T))) = stnorm (row A) := by
    rw [hrowST]
    exact (hgen (row A) (hp A)).2.1
  let K := Subgroup.zpowers (ModularGroup.S * ModularGroup.T)
  let ds := DoubleCoset.setoid (Γ : Set SL(2, ℤ)) (K : Set SL(2, ℤ))
  have hstable : ∀ A B, ds A B → stnorm (row A) = stnorm (row B) :=
    doubleCoset_zpowers_invariant Γ (ModularGroup.S * ModularGroup.T) (fun A => stnorm (row A)) hleft hright
  have hrl (A B : SL(2, ℤ)) (h : rel A B) : ds A B := by
    apply DoubleCoset.rel_iff.mpr
    refine ⟨B*A⁻¹, (QuotientGroup.rightRel_apply).mp h, 1, K.one_mem, ?_⟩
    simp
  have hconnect (A B : SL(2, ℤ)) (h : f A = f B) : ds A B := by
    apply hrl
    apply (hrowrel A B).mpr
    refine ⟨1, ?_⟩
    simpa only [Units.val_one, one_mul] using (congrArg Subtype.val h).symm
  have hattainStrong (A : SL(2, ℤ)) : ∃ B, ds A B ∧
      code (row B) = stnorm (row A) ∧ normal (row B) = row B := by
    obtain ⟨n, hn⟩ := hatt (row A) (hp A)
    let C : SL(2, ℤ) := if n.val=0 then A else if n.val=1 then A*(ModularGroup.S * ModularGroup.T) else (A*(ModularGroup.S * ModularGroup.T))*(ModularGroup.S * ModularGroup.T)
    have hC : row C = if n.val=0 then row A else if n.val=1 then ST (row A) else ST (ST (row A)) := by
      by_cases h : n.val=0
      · simp [C, h]
      · by_cases h1 : n.val=1 <;> simp [C, h, h1, hrowST]
    have hnC := level25_gamma0_row_normalization (row C) (hp C)
    obtain ⟨B, hB⟩ := hlift (normal (row C)) hnC.2.1
    obtain ⟨u, hu⟩ := hnC.1
    have hCB : rel C B := (hrowrel C B).mpr ⟨u, hB.trans hu.symm⟩
    have hAC : ds A C := by
      by_cases h : n.val=0
      · simpa only [C, if_pos h] using ds.refl A
      · by_cases h1 : n.val=1
        · apply DoubleCoset.rel_iff.mpr
          refine ⟨1, Γ.one_mem, ModularGroup.S * ModularGroup.T, Subgroup.mem_zpowers _, ?_⟩
          simp [C, h, h1]
        · apply DoubleCoset.rel_iff.mpr
          refine ⟨1, Γ.one_mem, (ModularGroup.S * ModularGroup.T)*(ModularGroup.S * ModularGroup.T),
            K.mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _), ?_⟩
          simp [C, h, h1, mul_assoc]
    refine ⟨B, ds.trans hAC (hrl C B hCB), ?_, ?_⟩
    · rw [hB, hC]
      exact hn
    · rw [hB]
      exact hnC.2.2
  have hattain (A : SL(2, ℤ)) : ∃ B, ds A B ∧ code (row B) = stnorm (row A) := by
    obtain ⟨B, hAB, hcodeB, _⟩ := hattainStrong A
    exact ⟨B, hAB, hcodeB⟩
  have hfixed (r : R) (hr : primitive r) (hc : code r = stnorm r) : normal r = r := by
    obtain ⟨A, hA⟩ := hlift r hr
    obtain ⟨B, _, hB, hnB⟩ := hattainStrong A
    have heq : row B = r := hcode (hB.trans ((congrArg stnorm hA).trans hc.symm))
    simpa only [heq] using hnB
  have hcard : Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) (K : Set SL(2, ℤ))) =
      Nat.card {r : PR // code r.val = stnorm r.val} :=
    doubleCoset_card_of_normal_form Γ K f hf (fun r => code r.val)
      (fun a b h => Subtype.ext (hcode h)) (fun r => stnorm r.val) hstable hconnect hattain
  rw [hcard]
  let e : {r : PR // code r.val = stnorm r.val} ≃
      {r : R // primitive r ∧ code r = stnorm r} :=
    { toFun := fun r => ⟨r.val.val, r.val.property, r.property⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩, r.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcen : (((Finset.univ : Finset R).filter (fun r => primitive r ∧ normal r = r)).filter
      (fun r => code r ≤ code (normal (ST r)) ∧ code r ≤ code (normal (ST (ST r))))).card = 10 :=
    level25_gamma0_finite_census.2.2.1
  have heq : (Finset.univ : Finset R).filter (fun r => primitive r ∧ code r = stnorm r) =
      (((Finset.univ : Finset R).filter (fun r => primitive r ∧ normal r = r)).filter
        (fun r => code r ≤ code (normal (ST r)) ∧ code r ≤ code (normal (ST (ST r))))) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hr, hc⟩
      have hn := hfixed r hr hc
      refine ⟨⟨hr, hn⟩, ?_⟩
      have hm : code r = min (code r) (min (code (normal (ST r))) (code (normal (ST (ST r))))) := by
        simpa only [stnorm, hn] using hc
      omega
    · rintro ⟨⟨hr, hn⟩, hc⟩
      refine ⟨hr, ?_⟩
      dsimp only [stnorm]
      rw [hn]
      omega
  rw [heq]
  exact hcen

end N25
