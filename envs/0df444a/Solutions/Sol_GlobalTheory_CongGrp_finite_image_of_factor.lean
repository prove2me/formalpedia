-- Prove2me | solution 1 for GlobalTheory.CongGrp.finite_image_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:28:55.466883+00:00
-- url     : https://prove2.me/submissions/a693b2f6-09af-4ad1-ae16-4e8f0a0f5299

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.CongGrp
namespace GlobalTheory.CongGrp
theorem _root_.solution {α β γ : Type} (S : Set α) (f : α → β) (g : α → γ) [Finite β]
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y → g x = g y) : (g '' S).Finite := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, _⟩
  · simp
  haveI : Nonempty α := ⟨x0⟩
  refine (Set.finite_range fun t => g (Function.invFunOn f S t)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨f x, ?_⟩
  have hex : ∃ a ∈ S, f a = f x := ⟨x, hx, rfl⟩
  exact h _ (Function.invFunOn_mem hex) _ hx (Function.invFunOn_eq hex)
end GlobalTheory.CongGrp
