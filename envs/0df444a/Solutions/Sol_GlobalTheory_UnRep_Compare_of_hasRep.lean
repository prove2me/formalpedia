-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.of_hasRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:43:39.532887+00:00
-- url     : https://prove2.me/submissions/48f5c3eb-f456-4616-85a8-3b613a952479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_suppSplit_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnE_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnit_of_isUnA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ)
    (H : HasRep c G L (N * D)) : HasSplitRepresentatives c G (L : Set (Fin n → E)) N D := by
  intro g hg
  obtain ⟨g, rfl⟩ := isUnit_of_isUnA c hG hg
  obtain ⟨γ, h, k, hγ, hh, hk, e, hs, hcong, hinv⟩ := H g hg
  obtain ⟨T, hT, hT'⟩ := (suppSplit_iff c h2 hc _ _).1 hs
  refine ⟨γ.1, h.1, k.1, (isUnE_iff c G _).1 hγ, ⟨hh, T, fun v hv => ⟨(hT v hv).1, fun h => (hT v hv).2 ?_⟩, hT'⟩,
    ⟨hk, ?_, fun v _ z hz => ?_⟩, e⟩
  · rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ h
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, e⟩ := hcong z hz
      rw [sub_eq_iff_eq_add.1 e]
      exact add_mem (nsmul_mem hw _) hz
    · intro z hz
      exact ⟨_, hinv z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  · obtain ⟨w, hw, e⟩ := hcong z hz
    refine ⟨N • w, nsmul_mem hw _, fun i => ?_⟩
    rw [smul_smul, mul_comm D, ← e]
    rfl
end GlobalTheory.UnRep.Compare
