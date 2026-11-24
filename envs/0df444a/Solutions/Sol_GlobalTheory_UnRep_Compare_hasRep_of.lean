-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.hasRep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:43:38.680488+00:00
-- url     : https://prove2.me/submissions/925c5673-2132-4c84-99a7-c83df6fad563

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_suppSplit_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_congAtA_of_congOneAt
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnE_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnit_of_isUnA
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnit_of_isUnE
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
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) {N : ℕ} (hN : N ≠ 0)
    (H : HasSplitRepresentatives c G (L : Set (Fin n → E)) N N) : HasRep c G L N := by
  intro g hg
  obtain ⟨γ, h, k, hγ, ⟨hh, hs⟩, ⟨hk, hst, hcong⟩, e⟩ := H g.1 hg
  rw [← isUnE_iff] at hγ
  obtain ⟨γ, rfl⟩ := isUnit_of_isUnE c hG hγ
  obtain ⟨h, rfl⟩ := isUnit_of_isUnA c hG hh
  obtain ⟨k, rfl⟩ := isUnit_of_isUnA c hG hk
  refine ⟨γ, h, k, hγ, hh, hk, e, (suppSplit_iff c h2 hc N _).2 hs, ?_, fun z hz => ?_⟩
  · have := congAtA_of_congOneAt L hN hN one_ne_zero k.1 (fun z hz => by
      rw [one_smul, ← SetLike.mem_coe, ← hst]; exact ⟨z, hz, rfl⟩) hcong (t := 1) (j := 1) (by simp)
    simpa only [one_smul] using this
  · rw [← SetLike.mem_coe, ← hst] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
end GlobalTheory.UnRep.Compare
