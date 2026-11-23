-- Prove2me | solution 1 for GlobalTheory.ideal_eq_bot_of_flat_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:00.268858+00:00
-- url     : https://prove2.me/submissions/afd984c5-0700-49b9-9448-529a1f67acb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution (T : Type*) {R : Type*} [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra T R] [IsLocalHom (algebraMap T R)] {J : Ideal R} (hJ : J ≠ ⊤)
    [Module.Flat T (R ⧸ J)] : J = ⊥ := by
  by_contra hJ0
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ0 hϖ
  have h1 : algebraMap T R π ∈ Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq ▸ map_nonunit _ _ hπ.not_isUnit
  have h2 : algebraMap T R (π ^ n) ∈ J := by
    rw [hn, map_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow h1 n
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R ⧸ J)
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hπ.ne_zero))
  have h3 : (1 : R ⧸ J) = 0 := hreg (by
    change π ^ n • (1 : R ⧸ J) = π ^ n • 0
    rw [smul_zero, ← Algebra.algebraMap_eq_smul_one, IsScalarTower.algebraMap_apply T R (R ⧸ J)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2)
  exact hJ ((Ideal.eq_top_iff_one J).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h3))
end GlobalTheory
