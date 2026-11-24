-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HypSplit.det_ne_zero_of_hypJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:12.391662+00:00
-- url     : https://prove2.me/submissions/b06fb1ef-82c9-4be2-ad64-431d4fd65fce

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hLin_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.HypSplit.hLin_apply

set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HypSplit
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}
namespace GlobalTheory.CompanionTheory.SW.HypSplit
theorem _root_.solution {M₁ : ℕ} (A : Matrix (Fin M₁) (Fin M₁) E) (h : (hypJ A).det ≠ 0) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply h
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Fin.cons 0 (Fin.cons 0 v), ?_, ?_⟩
  · intro h1
    apply hv
    funext i
    simpa using congrFun h1 i.succ.succ
  · funext a
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · have := congrFun hAv a
      simpa [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ] using this
end GlobalTheory.CompanionTheory.SW.HypSplit
