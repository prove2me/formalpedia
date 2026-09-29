-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6b8d97da-2f17-5061-8899-5c179091e9cb

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex.ModularCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ModularPolynomialData jqModC map_jqModC primCosetReps cosetConj qTwist qTwist_coeff cosetSubst coeffMap coeffMap_coeff"
namespace CosetDescentAux
p2m_open "ModularCurve"

variable {R S : Type*} [CommRing R] [CommRing S]

def conjR (u : Rˣ) (J : LaurentSeries R) (t : ℕ × ℕ × ℕ) : LaurentSeries R :=
  if h : t.1 = 0 then 0 else
    haveI : NeZero (t.1 * t.1) := ⟨Nat.mul_ne_zero h h⟩
    qExpand R (t.1 * t.1) (qTwist (u ^ (t.1 * t.2.1)) J)

theorem conjR_eq_cosetConj {K : Type*} [Field K] (ζ : Kˣ) (J : LaurentSeries K) (t : ℕ × ℕ × ℕ) :
    conjR ζ J t = cosetConj ζ J t := by
  unfold conjR cosetConj
  by_cases h : t.1 = 0
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    rfl

def phiAt (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ)) (R : Type*) [CommRing R] :
    Polynomial (LaurentSeries R) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries R)) (qExpand R N (jqModC R)))

theorem coeffMap_qExpand (f : R →+* S) (M : ℕ) [NeZero M] (x : LaurentSeries R) :
    coeffMap f (qExpand R M x) = qExpand S M (coeffMap f x) := by
  ext k
  by_cases hk : (M : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd M _ hk, qExpand_coeff_of_not_dvd M _ hk, map_zero]

theorem coeffMap_qTwist (f : R →+* S) (u : Rˣ) (x : LaurentSeries R) :
    coeffMap f (qTwist u x) = qTwist (Units.map (f : R →* S) u) (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul]
  congr 1
  rw [← map_zpow, Units.coe_map, MonoidHom.coe_coe]

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S := by
  show (jqModC R).map f = jqModC S
  exact map_jqModC f

theorem coeffMap_conjR (f : R →+* S) (u : Rˣ) (J : LaurentSeries R) (t : ℕ × ℕ × ℕ) :
    coeffMap f (conjR u J t) = conjR (Units.map (f : R →* S) u) (coeffMap f J) t := by
  unfold conjR
  by_cases h : t.1 = 0
  · rw [dif_pos h, dif_pos h, map_zero]
  · rw [dif_neg h, dif_neg h, coeffMap_qExpand, coeffMap_qTwist, map_pow]

theorem phiAt_map (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ)) (f : R →+* S) :
    (phiAt N Φ R).map (coeffMap f) = phiAt N Φ S := by
  unfold phiAt
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, coeffMap_qExpand, coeffMap_jqModC]

theorem coeffMap_eval_conjR (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ)) (f : R →+* S) (u : Rˣ)
    (t : ℕ × ℕ × ℕ) :
    coeffMap f ((phiAt N Φ R).eval (conjR u (jqModC R) t))
      = (phiAt N Φ S).eval (conjR (Units.map (f : R →* S) u) (jqModC S) t) := by
  rw [← Polynomial.coe_evalRingHom, ← phiAt_map N Φ f, ← coeffMap_jqModC f, ← coeffMap_conjR]
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_map, ← Polynomial.coe_eval₂RingHom]
  exact Polynomial.hom_eval₂ _ _ _ _ |>.trans (by simp)

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

end ModularCurve.CosetDescentAux

open ModularCurve.CosetDescentAux in
theorem solution
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (hC : ∃ ζ : ℂˣ, IsPrimitiveRoot ζ N ∧ ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ))
        (ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC ℂ) t))
    (K : Type*) [Field K] (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) :
    ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (ModularCurve.qExpand K N (ModularCurve.jqModC K)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC K) t) := by
  classical
  obtain ⟨ζC, hζCu, hrootC⟩ := hC
  have hζC : IsPrimitiveRoot (ζC : ℂ) N := IsPrimitiveRoot.coe_units_iff.mpr hζCu
  intro t ht
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

  set R : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {(ζC : ℂ)} with hR
  have hzmem : (ζC : ℂ) ∈ R := Algebra.self_mem_adjoin_singleton ℤ (ζC : ℂ)
  set z : R := ⟨(ζC : ℂ), hzmem⟩ with hz
  have hzpow : z ^ N = 1 := by
    apply Subtype.ext
    show ((ζC : ℂ)) ^ N = 1
    exact hζC.pow_eq_one
  have hzmul : z * z ^ (N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hN, hzpow]
  set u : Rˣ := Units.mkOfMulEqOne z (z ^ (N - 1)) hzmul with hu

  let ι : R →+* ℂ := (R.val : R →ₐ[ℤ] ℂ).toRingHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hιu : Units.map (ι : R →* ℂ) u = ζC := by
    ext
    rfl
  have hR0 : (phiAt N data.Φ R).eval (conjR u (jqModC R) t) = 0 := by
    apply coeffMap_injective hι
    rw [map_zero, coeffMap_eval_conjR, hιu, conjR_eq_cosetConj]
    exact hrootC t ht

  have hint : IsIntegral ℤ (ζC : ℂ) := hζC.isIntegral hN
  have hmin : minpoly ℤ (ζC : ℂ) = Polynomial.cyclotomic N ℤ :=
    (Polynomial.cyclotomic_eq_minpoly hζC hN).symm
  have hζroot : Polynomial.eval₂ (Int.castRingHom K) (ζ : K) (minpoly ℤ (ζC : ℂ)) = 0 := by
    rw [hmin, ← Polynomial.eval_map, Polynomial.map_cyclotomic_int]
    exact (IsPrimitiveRoot.coe_units_iff.mpr hζ).isRoot_cyclotomic hN
  let e : AdjoinRoot (minpoly ℤ (ζC : ℂ)) ≃ₐ[ℤ] R := minpoly.equivAdjoin hint
  let φ : R →+* K := (AdjoinRoot.lift (Int.castRingHom K) (ζ : K) hζroot).comp e.symm.toAlgHom.toRingHom
  have heroot : e (AdjoinRoot.root _) = z := by
    show minpoly.equivAdjoin hint (AdjoinRoot.root _) = z
    first
    | exact minpoly.equivAdjoin_apply_root hint
    | (rw [minpoly.equivAdjoin, AlgEquiv.ofBijective_apply]; exact AdjoinRoot.liftHom_root (R := ℤ))
    | simp [minpoly.equivAdjoin, hz]
  have hφz : φ z = (ζ : K) := by
    show AdjoinRoot.lift (Int.castRingHom K) (ζ : K) hζroot (e.symm z) = ζ
    rw [← heroot, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_root]
  have hφu : Units.map (φ : R →* K) u = ζ := by
    ext
    exact hφz

  have := congrArg (coeffMap φ) hR0
  rw [coeffMap_eval_conjR, hφu, conjR_eq_cosetConj, map_zero] at this
  exact this

end

end S_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex (solution)
