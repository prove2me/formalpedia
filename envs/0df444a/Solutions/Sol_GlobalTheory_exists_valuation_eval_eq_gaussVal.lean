-- Prove2me | solution 1 for GlobalTheory.exists_valuation_eval_eq_gaussVal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:12:13.881643+00:00
-- url     : https://prove2.me/submissions/ff72198c-e510-4fcb-9f7a-3ca1c1d2cd4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

open IsLocalRing

private def liftCoeff {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O) (a : K) : O :=
  if ha : v a ≤ 1 then Classical.choose (hO.exists_of_le_one ha) else 0

private theorem liftCoeff_map {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O)
    {a : K} (ha : v a ≤ 1) : algebraMap O K (liftCoeff v hO a) = a := by
  simp only [liftCoeff, ha, ↓reduceDIte]
  exact Classical.choose_spec (hO.exists_of_le_one ha)

private theorem liftCoeff_zero {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O) :
    liftCoeff v hO 0 = 0 := by
  apply hO.hom_inj
  rw [liftCoeff_map v hO (by simp), map_zero]

private def liftPoly {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O)
    (f : MvPolynomial σ K) : MvPolynomial σ O :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange (liftCoeff v hO) (liftCoeff_zero v hO) (AddMonoidAlgebra.coeff f))

private theorem liftPoly_coeff {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O)
    (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (liftPoly v hO f) = liftCoeff v hO (coeff m f) := by
  unfold liftPoly
  change (AddMonoidAlgebra.coeff
      (AddMonoidAlgebra.ofCoeff
        (Finsupp.mapRange (liftCoeff v hO) (liftCoeff_zero v hO) (AddMonoidAlgebra.coeff f)))) m =
    liftCoeff v hO (coeff m f)
  rw [AddMonoidAlgebra.coeff_ofCoeff]
  exact Finsupp.mapRange_apply (hf := liftCoeff_zero v hO)

private theorem liftPoly_map {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O)
    {f : MvPolynomial σ K} (hf : gaussVal v f ≤ 1) :
    map (algebraMap O K) (liftPoly v hO f) = f := by
  ext m
  rw [coeff_map, liftPoly_coeff]
  exact liftCoeff_map v hO ((le_gaussVal v f m).trans hf)

private theorem exists_eval_ne_zero {k : Type*} [Field k] [Infinite k]
    {p : MvPolynomial σ k} (hp : p ≠ 0) : ∃ x : σ → k, eval x p ≠ 0 := by
  by_contra hnone
  push Not at hnone
  exact hp (MvPolynomial.funext fun x => by simp [hnone x])

private theorem exists_eval_both_ne_zero {k : Type*} [Field k] [Infinite k]
    {p q : MvPolynomial σ k} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ x : σ → k, eval x p ≠ 0 ∧ eval x q ≠ 0 := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  obtain ⟨x, hx⟩ := exists_eval_ne_zero hpq
  exact ⟨x, fun h => hx (by simp [h]), fun h => hx (by simp [h])⟩

private theorem mk_liftCoeff {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) {a : K} (ha : v a = 1) :
    algebraMap O (ResidueField O) (liftCoeff v hO a) ≠ 0 := by
  intro h
  have hmem : liftCoeff v hO a ∈ maximalIdeal O := Ideal.Quotient.eq_zero_iff_mem.mp h
  have hnU : ¬ IsUnit (liftCoeff v hO a) := (mem_maximalIdeal _).mp hmem
  have hU : IsUnit (liftCoeff v hO a) := by
    rw [hO.isUnit_iff_valuation_eq_one, liftCoeff_map v hO ha.le, ha]
  exact hnU hU

private theorem residue_of_gaussVal_eq_one {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) {f : MvPolynomial σ K} (hf : gaussVal v f = 1) :
    map (algebraMap O (ResidueField O)) (liftPoly v hO f) ≠ 0 := by
  have hfne : f ≠ 0 := by
    intro h
    have : gaussVal v f = 0 := by
      subst h
      simpa [gaussVal_C (σ := σ)] using gaussVal_C (σ := σ) v (0 : K)
    exact zero_ne_one (this.symm.trans hf)
  obtain ⟨m, -, hmeq⟩ :=
    exists_mem_support_coeffSup_eq (N := v) (c := (AddMonoidAlgebra.coeff f)) (by
      intro h0
      exact hfne (by
        rw [← AddMonoidAlgebra.ofCoeff_coeff f, h0]
        rfl))
  have hv1 : v (coeff m f) = 1 := by
    change v ((AddMonoidAlgebra.coeff f) m) = 1
    have : coeffSup v (AddMonoidAlgebra.coeff f) = gaussVal v f := rfl
    exact hmeq.symm.trans (this.trans hf)
  intro h0
  have : coeff m (map (algebraMap O (ResidueField O)) (liftPoly v hO f)) = 0 := by
    rw [h0]; simp
  rw [coeff_map, liftPoly_coeff] at this
  exact mk_liftCoeff v hO hv1 this

private theorem eval_algebraMap {O : Type*} [CommRing O] [Algebra O K] (x : σ → O)
    (p : MvPolynomial σ O) :
    eval (fun i => algebraMap O K (x i)) (map (algebraMap O K) p) =
      algebraMap O K (eval x p) := by
  rw [eval_map]
  exact (eval₂_comp (algebraMap O K) x p).symm

private theorem eval_residue {O : Type*} [CommRing O] [IsLocalRing O] (x : σ → O)
    (p : MvPolynomial σ O) :
    eval (fun i => algebraMap O (ResidueField O) (x i))
        (map (algebraMap O (ResidueField O)) p) =
      algebraMap O (ResidueField O) (eval x p) := by
  rw [eval_map]
  exact (eval₂_comp (algebraMap O (ResidueField O)) x p).symm

private theorem v_eval_eq_one_of_residue {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) {x : σ → O} {p : MvPolynomial σ O}
    (h : algebraMap O (ResidueField O) (eval x p) ≠ 0) :
    v (algebraMap O K (eval x p)) = 1 := by
  have hU : IsUnit (eval x p) := by
    have : eval x p ∉ maximalIdeal O := mt Ideal.Quotient.eq_zero_iff_mem.mpr h
    simpa [mem_maximalIdeal, mem_nonunits_iff] using this
  exact hO.one_of_isUnit hU

private theorem lift_residue_point {O : Type*} [CommRing O] [IsLocalRing O]
    (y : σ → ResidueField O) : ∃ x : σ → O,
    (fun i => algebraMap O (ResidueField O) (x i)) = y := by
  refine ⟨fun i => Classical.choose (Ideal.Quotient.mk_surjective (y i)), ?_⟩
  funext i
  exact Classical.choose_spec (Ideal.Quotient.mk_surjective (y i))

theorem solution {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) [Infinite (IsLocalRing.ResidueField O)] (f d : MvPolynomial σ K)
    (hd : gaussVal v d = 1) :
    ∃ x : σ → K, (∀ i, v (x i) ≤ 1) ∧ v (eval x d) = 1 ∧ v (eval x f) = gaussVal v f := by
  have hpt (p : MvPolynomial σ K) (hp : gaussVal v p = 1) :
      ∃ x : σ → K, (∀ i, v (x i) ≤ 1) ∧ v (eval x d) = 1 ∧ v (eval x p) = 1 := by
    let dO := liftPoly v hO d
    let pO := liftPoly v hO p
    let dR := map (algebraMap O (ResidueField O)) dO
    let pR := map (algebraMap O (ResidueField O)) pO
    have hdR : dR ≠ 0 := residue_of_gaussVal_eq_one v hO hd
    have hpR : pR ≠ 0 := residue_of_gaussVal_eq_one v hO hp
    obtain ⟨y, hyd, hyp⟩ := exists_eval_both_ne_zero hdR hpR
    obtain ⟨xO, hxO⟩ := lift_residue_point (O := O) y
    let x : σ → K := fun i => algebraMap O K (xO i)
    have hx : ∀ i, v (x i) ≤ 1 := fun i => hO.map_le_one (xO i)
    have hdmap : map (algebraMap O K) dO = d := liftPoly_map v hO hd.le
    have hpmap : map (algebraMap O K) pO = p := liftPoly_map v hO hp.le
    have hvd : v (eval x d) = 1 := by
      have : eval x d = algebraMap O K (eval xO dO) := by
        rw [← hdmap, eval_algebraMap]
      rw [this]
      refine v_eval_eq_one_of_residue v hO ?_
      rw [← eval_residue, hxO]
      exact hyd
    have hvp : v (eval x p) = 1 := by
      have : eval x p = algebraMap O K (eval xO pO) := by
        rw [← hpmap, eval_algebraMap]
      rw [this]
      refine v_eval_eq_one_of_residue v hO ?_
      rw [← eval_residue, hxO]
      exact hyp
    exact ⟨x, hx, hvd, hvp⟩
  by_cases hf0 : gaussVal v f = 0
  · have f0 : f = 0 :=
      (gaussVal_eq_zero_iff_of_supp v (valuation_supp_eq_bot (K := K) v)).mp hf0
    obtain ⟨x, hx, hxd, _⟩ := hpt (C 1) (by simp [gaussVal_C (σ := σ)])
    refine ⟨x, hx, hxd, ?_⟩
    rw [f0]
    simp [map_zero]
  · have hfne : f ≠ 0 := by
      intro h
      apply hf0
      subst h
      simpa [gaussVal_C (σ := σ)] using gaussVal_C (σ := σ) v (0 : K)
    obtain ⟨m, -, hmeq⟩ :=
      exists_mem_support_coeffSup_eq (N := v) (c := (AddMonoidAlgebra.coeff f)) (by
        intro h0
        exact hfne (by
        rw [← AddMonoidAlgebra.ofCoeff_coeff f, h0]
        rfl))
    have hvγ : v (coeff m f) = gaussVal v f := by
      change v ((AddMonoidAlgebra.coeff f) m) = gaussVal v f
      have : coeffSup v (AddMonoidAlgebra.coeff f) = gaussVal v f := rfl
      exact hmeq.symm.trans this
    have hc0 : coeff m f ≠ 0 := by
      intro h
      apply hf0
      simpa [h, map_zero] using hvγ.symm
    set γ := gaussVal v f
    set c := coeff m f
    set p : MvPolynomial σ K := C c⁻¹ * f
    have hp : gaussVal v p = 1 := by
      have : gaussVal v p = v c⁻¹ * γ := by
        change gaussVal v (C c⁻¹ * f) = _
        rw [map_mul, gaussVal_C (σ := σ)]
      rw [this, Valuation.map_inv, hvγ]
      exact inv_mul_cancel₀ hf0
    obtain ⟨x, hx, hxd, hxp⟩ := hpt p hp
    refine ⟨x, hx, hxd, ?_⟩
    have heval : eval x p = c⁻¹ * eval x f := by
      simp [p, eval_mul, eval_C]
    have : v (c⁻¹ * eval x f) = 1 := by rwa [← heval]
    have : v c⁻¹ * v (eval x f) = 1 := by rwa [map_mul] at this
    have hinv : γ⁻¹ * v (eval x f) = 1 := by
      rwa [Valuation.map_inv, hvγ] at this
    have := congrArg (fun t => γ * t) hinv
    rw [← mul_assoc, mul_inv_cancel₀ hf0, one_mul, mul_one] at this
    exact this
