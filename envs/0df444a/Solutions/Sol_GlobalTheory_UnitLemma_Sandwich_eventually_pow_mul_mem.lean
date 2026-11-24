-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Sandwich.eventually_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:29.815071+00:00
-- url     : https://prove2.me/submissions/3c6cd61a-4d65-4f13-924e-47abc15fcebb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_exists_dvd_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Sandwich
namespace GlobalTheory.UnitLemma.Sandwich
theorem _root_.solution {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) (S : Submodule O A)
    (x : A) (d : O) (hd : d ≠ 0) (hx : d • x ∈ S) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → algebraMap O A a ^ n * x ∈ S := by
  obtain ⟨k, c, hc⟩ := exists_dvd_pow a ha d hd
  refine ⟨k, fun n hn => ?_⟩
  have e : algebraMap O A a ^ n * x = (a ^ (n - k) * c) • (d • x) := by
    rw [smul_smul, Algebra.smul_def, ← map_pow]
    congr 2
    rw [mul_assoc, mul_comm c d, ← hc, ← pow_add, Nat.sub_add_cancel hn]
  rw [e]
  exact S.smul_mem _ hx
end GlobalTheory.UnitLemma.Sandwich
