-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.suppSplit_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:33:58.543866+00:00
-- url     : https://prove2.me/submissions/bf37b040-8e5a-4f18-9164-452ce9bf7504

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_splitPl_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_support_iff
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ} (N : ℕ)
    (h : Matrix (Fin n) (Fin n) (RA F E)) : SuppSplit c N h ↔ SupportedAtSplit N h := by
  rw [SuppSplit, support_iff (fun v => SplitPl c v ∧ (N : 𝓞 F) ∉ v.asIdeal), SupportedAtSplit]
  simp only [splitPl_iff c h2 hc]
end GlobalTheory.UnRep.Compare
