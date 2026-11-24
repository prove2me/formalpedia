-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Sandwich.sub_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:16.969101+00:00
-- url     : https://prove2.me/submissions/00ed4f0b-e2b3-43c1-94bd-a714a4dc7d5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_eventually_pow_mul_mem
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_exists_smul_isIntegral

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
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Sandwich
theorem _root_.solution (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O) (L : Submodule K.O B.A) (hL : L.FG) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  classical
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ x : B.A, ∃ k : ℕ, ∀ n, k ≤ n →
      algebraMap K.O B.A a ^ n * x ∈ Subalgebra.toSubmodule (integralClosure K.O B.A) := by
    intro x
    obtain ⟨d, hd, hi⟩ := exists_smul_isIntegral B x
    exact eventually_pow_mul_mem a ha _ x d hd hi
  choose k hk using hk
  refine ⟨s.sup k, fun n hn y hy => ?_⟩
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hk x n ((Finset.le_sup hx).trans hn)
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz => rw [mul_add]; exact hx.add hz
  | smul r x _ hx => rw [mul_smul_comm, Algebra.smul_def]; exact isIntegral_algebraMap.mul hx
end GlobalTheory.UnitLemma.Sandwich
