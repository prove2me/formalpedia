-- Prove2me | solution 1 for GlobalTheory.HL.MoveSame.exists_coef_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:14.996163+00:00
-- url     : https://prove2.me/submissions/863bf551-6eff-4e32-988d-0baa18650b1c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevels
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_StdLat_exists_coef
import Theorems.Thm_GlobalTheory_HL_TermBasic_map_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveSame
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveSame
theorem _root_.solution {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {n : S.GLV} (hn : n ∈ S.Nof g)
    {J : ℕ} {y : S.V} (hy : y ∈ S.spanTo g J) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), ¬ (i : ℕ) < J → c i = 0) ∧ y = ∑ i, c i • n (g i) := by
  obtain ⟨c, hc, e⟩ := StdLat.exists_coef g _ (TermBasic.map_mem hg ((S.Nof g).inv_mem hn) J hy)
  refine ⟨c, hc, ?_⟩
  have e2 : n (n⁻¹ y) = y := n.apply_symm_apply y
  rw [← e2, e]
  simp only [map_sum, map_smul]
end GlobalTheory.HL.MoveSame
