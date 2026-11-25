-- Prove2me | solution 1 for GlobalTheory.T.card_hermitianLattices_glued_along_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:49.091858+00:00
-- url     : https://prove2.me/submissions/acb0706c-feda-41f6-a647-40fd7074aa68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLineStatement
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_GlobalTheory_Mass_LineGlue_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (T : 𝓞 K), T ≠ 0 → Module.finrank K (perp h U) = 1 → IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ ((Ideal.absNorm (Ideal.span {T}) * discN (hRes h U) A : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.Mass.LineGlue.main | exact GlobalTheory.Mass.LineGlue.main | (intros; apply GlobalTheory.Mass.LineGlue.main <;> assumption)
end _root_.GlobalTheory.T
