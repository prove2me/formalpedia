-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Sandwich.integral_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:11.323969+00:00
-- url     : https://prove2.me/submissions/e9497833-aaac-44c3-9e3e-8349cb710f27

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
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_exists_smul_mem
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_traceForm_nondegenerate
import Theorems.Thm_GlobalTheory_DiscConductor_isIntegral_trace_of_isIntegral


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
theorem _root_.solution (hP : B.P.Separable) (a : K.O) (ha : a ∈ IsLocalRing.maximalIdeal K.O)
    (L : Submodule K.O B.A) (hL : Submodule.span K.E (L : Set B.A) = ⊤) :
    ∃ m : ℕ, ∀ n, m ≤ n → ∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L := by
  classical
  have hnd := traceForm_nondegenerate B hP
  let b0 := Module.finBasis K.E B.A
  choose d hd0 hdi using fun i => exists_smul_isIntegral B (b0 i)
  have hu : ∀ i, IsUnit (algebraMap K.O K.E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral K.O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let bd := (Algebra.traceForm K.E B.A).dualBasis hnd b
  choose c hc0 hc using fun i => exists_smul_mem B L hL (bd i)
  choose k hk using fun i => eventually_pow_mul_mem a ha L (bd i) (c i) (hc0 i) (hc i)
  refine ⟨Finset.univ.sup k, fun n hn y hy => ?_⟩
  have hrep := bd.sum_repr y
  have hint : ∀ i, ∃ o : K.O, algebraMap K.O K.E o = bd.repr y i := by
    intro i
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A _ (hy.mul (hb i)))
  choose o ho using hint
  rw [← hrep, Finset.mul_sum]
  refine L.sum_mem fun i _ => ?_
  rw [← ho i, algebraMap_smul, mul_smul_comm]
  exact L.smul_mem _ (hk i n ((Finset.le_sup (Finset.mem_univ i)).trans hn))
end GlobalTheory.UnitLemma.Sandwich
