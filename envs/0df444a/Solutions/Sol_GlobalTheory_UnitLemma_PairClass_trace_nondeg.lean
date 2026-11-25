-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PairClass.trace_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:42.5188+00:00
-- url     : https://prove2.me/submissions/e8856bc3-9a3a-4aab-9ef3-77af46049469

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_aeval_eq_of_separable
import Theorems.Thm_GlobalTheory_UnitLemma_PairClass_aeval_mulLeft_apply
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_exists_annihilator_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isNilpotent_of_trace_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass
namespace GlobalTheory.UnitLemma.PairClass
theorem _root_.solution (F A : Type) [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (x : A)
    (hx : ∀ y, Algebra.trace F A (x * y) = 0) : x = 0 := by
  classical
  let b := Module.finBasis F A
  have hM : IsNilpotent (Algebra.leftMulMatrix b x) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ', hx]
  obtain ⟨k, hk⟩ := hM
  have hxk : x ^ k = 0 := by
    rw [← map_pow] at hk
    exact Algebra.leftMulMatrix_injective b (by rw [hk, map_zero])
  obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable a hs x
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (LinearMap.mulLeft F a) hs _ dvd_rfl
  have h1 : (LinearMap.mulLeft F a).charpoly ∣ q ^ (k + 1) :=
    he _ (by rw [aeval_mulLeft_apply, map_pow, pow_succ, hxk, zero_mul, zero_mul])
  obtain ⟨r, hr⟩ := (Squarefree.dvd_pow_iff_dvd hs.squarefree (Nat.succ_ne_zero k)).1 h1
  have h3 : aeval (LinearMap.mulLeft F a) q = 0 := by
    rw [hr, map_mul, LinearMap.aeval_self_charpoly, zero_mul]
  have h4 := LinearMap.congr_fun h3 1
  rwa [aeval_mulLeft_apply, mul_one] at h4
end GlobalTheory.UnitLemma.PairClass
