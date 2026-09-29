-- Prove2me | solution 1 for NumberField.exists_isNonarchimedean_absoluteValue_extends
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/eebc4138-c2b4-5a28-ae45-ccaa2d2d81e1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isNonarchimedean_absoluteValue_extends

set_option Elab.async false
set_option autoImplicit false

open NumberField IsDedekindDomain

attribute [local instance] Valued.toNontriviallyNormedField

namespace UnitsSol

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]

theorem isUltrametricDist_adicCompletion (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) :
    IsUltrametricDist (v.adicCompletion ↥L) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one (fun n => ?_)
  rw [show ((n : ℕ) : v.adicCompletion ↥L) = FinitePlace.embedding v ((n : ℕ) : ↥L) from
      (map_natCast (FinitePlace.embedding v) n).symm]
  rw [show ((n : ℕ) : ↥L) = algebraMap (𝓞 ↥L) ↥L ((n : ℕ) : 𝓞 ↥L) from
      (map_natCast (algebraMap (𝓞 ↥L) ↥L) n).symm]
  exact FinitePlace.norm_le_one (K := ↥L) v ((n : ℕ) : 𝓞 ↥L)

end UnitsSol

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : NumberField.FinitePlace ↥L) :
    ∃ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ ∧
      ∀ a : ↥L, μ (a : AlgebraicClosure ℚ) = ν a := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L), FinitePlace.mk v = ν :=
    ⟨ν.maximalIdeal, FinitePlace.mk_maximalIdeal ν⟩
  haveI hUltra : IsUltrametricDist (v.adicCompletion ↥L) :=
    UnitsSol.isUltrametricDist_adicCompletion L v
  letI : Algebra ↥L (AlgebraicClosure (v.adicCompletion ↥L)) :=
    ((algebraMap (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L))).comp (FinitePlace.embedding v)).toAlgebra
  haveI halg : Algebra.IsAlgebraic ↥L (AlgebraicClosure ℚ) := by
    haveI h0 : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) ↥L
  haveI hnz1 : Module.IsTorsionFree ↥L (AlgebraicClosure ℚ) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (algebraMap ↥L (AlgebraicClosure ℚ)).injective
  haveI hnz2 : Module.IsTorsionFree ↥L (AlgebraicClosure (v.adicCompletion ↥L)) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (algebraMap ↥L (AlgebraicClosure (v.adicCompletion ↥L))).injective
  letI φ : AlgebraicClosure ℚ →ₐ[↥L] AlgebraicClosure (v.adicCompletion ↥L) := IsAlgClosed.lift
  refine ⟨{ toFun := fun x => spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ x)
            map_mul' := ?_
            nonneg' := ?_
            eq_zero' := ?_
            add_le' := ?_ }, ?_, ?_⟩
  · intro x y
    show spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ (x * y))
        = spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ x)
          * spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ y)
    rw [map_mul φ, map_mul]
  · intro x
    exact apply_nonneg _ _
  · intro x
    show spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ x) = 0 ↔ x = 0
    constructor
    · intro h
      by_contra hx
      have hφx : φ x ≠ 0 := fun h0 =>
        hx ((map_eq_zero_iff φ.toRingHom φ.toRingHom.injective).mp h0)
      have hlt := spectralNorm_zero_lt hφx
        (Algebra.IsAlgebraic.isAlgebraic (R := v.adicCompletion ↥L) (φ x))
      rw [spectralMulAlgNorm_def] at h
      linarith
    · intro h
      rw [h, map_zero φ, map_zero]
  · intro x y
    show spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ (x + y))
        ≤ spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ x)
          + spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ y)
    rw [map_add φ]
    exact map_add_le_add _ _ _
  · intro x y
    show spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ (x + y))
        ≤ max (spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ x))
            (spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ y))
    rw [map_add φ]
    simpa only [spectralMulAlgNorm_def] using
      (isNonarchimedean_spectralNorm (K := v.adicCompletion ↥L) (L := AlgebraicClosure (v.adicCompletion ↥L))) (φ x) (φ y)
  · intro a
    show spectralMulAlgNorm (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (φ (a : AlgebraicClosure ℚ)) = ν a
    have hφa : φ ((a : AlgebraicClosure ℚ)) = algebraMap ↥L (AlgebraicClosure (v.adicCompletion ↥L)) a := φ.commutes a
    have halgM : algebraMap ↥L (AlgebraicClosure (v.adicCompletion ↥L)) a
        = algebraMap (v.adicCompletion ↥L) (AlgebraicClosure (v.adicCompletion ↥L)) (FinitePlace.embedding v a) := rfl
    rw [hφa, halgM, spectralMulAlgNorm_def, spectralNorm_extends, ← hv, FinitePlace.mk_apply]

#print axioms solution

end S_NumberField_exists_isNonarchimedean_absoluteValue_extends
end P2MW
export P2MW.S_NumberField_exists_isNonarchimedean_absoluteValue_extends (solution)
