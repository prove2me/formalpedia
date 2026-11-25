-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.splitExampleFrame_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:39.367933+00:00
-- url     : https://prove2.me/submissions/02e99e56-a36d-4d1d-8c7e-63423806f40a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_lead_last
import Theorems.Thm_GlobalTheory_HL_Model_lead_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    (toyG L hE ϖ hϖ m).G = algebraMap F E ((ϖ : F) ^ 6) := by
  have hcj : ∀ a : F, L.cj (algebraMap F E a) = algebraMap F E a := fun a => L.cj.commutes a
  have hZ : (toyG L hE ϖ hϖ m).Zh = !![-(algebraMap F E ϖ) ^ 2, 0; 0, -1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Frames.Zh, Frames.h, toyG, hf_extZ, hermitian_form_six_apply]
  simp only [Frames.G, Frames.D, hZ, lead_last]
  rw [show ((Fin.last 1).castSucc : Fin (1 + 1 + 1)) = ⟨1, by omega⟩ from rfl, lead_one]
  simp [toyG, Matrix.det_fin_two_of, hcj]
  ring
end GlobalTheory.HL.Inhab
