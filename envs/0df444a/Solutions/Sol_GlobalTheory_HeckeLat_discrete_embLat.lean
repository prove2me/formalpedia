-- Prove2me | solution 1 for GlobalTheory.HeckeLat.discrete_embLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:51.406129+00:00
-- url     : https://prove2.me/submissions/e97d2703-fbee-4cf8-8f3a-6c860b30f8cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
import Theorems.Thm_GlobalTheory_HeckeLat_one_le_norm_emb
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
theorem _root_.solution {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : DiscreteTopology (embLat φ) := by
  refine DiscreteTopology.of_forall_le_dist one_pos fun x y hxy => ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  rw [Subtype.dist_eq, dist_eq_norm]
  have hsub : (x : I → ℂ) - y = GlobalTheory.HeckeTheta.emb φ ((a - b : 𝓞 K) : K) := by
    rw [← ha, ← hb]
    funext i
    simp [embHom, GlobalTheory.HeckeTheta.emb]
  rw [hsub]
  apply one_le_norm_emb hφ
  rw [← hsub, sub_ne_zero]
  exact fun h => hxy (Subtype.ext h)
end GlobalTheory.HeckeLat
