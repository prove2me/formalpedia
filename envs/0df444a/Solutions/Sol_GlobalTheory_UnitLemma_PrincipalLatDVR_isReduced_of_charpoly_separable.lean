-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLatDVR.isReduced_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:46.119209+00:00
-- url     : https://prove2.me/submissions/8efa3602-bce0-4aae-ae9b-4cec7606e9b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Theorems.Thm_GlobalTheory_CharpolyDvd_charpoly_dvd_pow_finrank
import Theorems.Thm_GlobalTheory_UnitLemma_exists_aeval_eq_of_charpoly_separable
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLatDVR
namespace GlobalTheory.UnitLemma.PrincipalLatDVR
theorem _root_.solution {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨f, rfl⟩ := exists_aeval_eq_of_charpoly_separable g hP a
  obtain ⟨m, hm⟩ := ha
  have hf : aeval (LinearMap.mulLeft E g) (f ^ m) = 0 := by
    have h2 : aeval g (f ^ m) = 0 := by rw [map_pow, hm]
    have := aeval_algHom_apply (Algebra.lmul E A) g (f ^ m)
    rw [h2, map_zero] at this
    exact this
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  rw [← pow_mul] at h1
  obtain ⟨q, hq⟩ := hP.squarefree.isRadical _ _ h1
  have hc : aeval g (LinearMap.mulLeft E g).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g)
    have h' : Algebra.lmul E A (aeval g (LinearMap.mulLeft E g).charpoly) = 0 := by
      rw [← aeval_algHom_apply]; exact h
    simpa using congrArg (fun F : Module.End E A => F 1) h'
  rw [hq, map_mul, hc, zero_mul]
end GlobalTheory.UnitLemma.PrincipalLatDVR
