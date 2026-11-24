-- Prove2me | solution 1 for GlobalTheory.HeckeLat.summable_exp_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:35:07.483594+00:00
-- url     : https://prove2.me/submissions/08713eaa-a471-49da-a217-0b1143a1dc8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
import Theorems.Thm_GlobalTheory_HeckeLat_embHom_injective
import Theorems.Thm_GlobalTheory_HeckeLat_summable_exp_neg_mul_norm_sq
import Theorems.Thm_GlobalTheory_HeckeLat_discrete_embLat
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckeLat
theorem _root_.solution {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun α : 𝓞 K => Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2) := by
  haveI := discrete_embLat hφ
  have hs : Summable fun x : embLat φ ↦ Real.exp (-ε * ‖(x : I → ℂ)‖ ^ 2) :=
    summable_exp_neg_mul_norm_sq (embLat φ) hε
  have hmem : ∀ α : 𝓞 K, embHom φ α ∈ embLat φ := fun α => LinearMap.mem_range_self _ α
  let j : 𝓞 K → embLat φ := fun α => ⟨embHom φ α, hmem α⟩
  have hj : Function.Injective j := fun a b h => embHom_injective hφ (congrArg Subtype.val h)
  have h2 := hs.comp_injective hj
  refine h2.congr fun α => ?_
  simp only [Function.comp_apply, j]
  rfl
end GlobalTheory.HeckeLat
