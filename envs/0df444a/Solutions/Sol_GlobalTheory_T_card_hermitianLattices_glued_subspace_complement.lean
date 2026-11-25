-- Prove2me | solution 1 for GlobalTheory.T.card_hermitianLattices_glued_subspace_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:02.611327+00:00
-- url     : https://prove2.me/submissions/21048311-3f3d-437a-bd38-95071daa87c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedSubspaceComplement
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedSubspaceComplementStatement
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_GlobalTheory_Mass_Glue_main


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
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (e e' : ℕ), IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → (∃ t : Finset ↥U, t.card ≤ e ∧ dual (hRes h U) A = A ⊔ Submodule.span (𝓞 K) (t : Set _)) → (∃ t : Finset ↥(perp h U), t.card ≤ e' ∧ dual (hRes h (perp h U)) B = B ⊔ Submodule.span (𝓞 K) (t : Set _)) → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ (((discN (hRes h U) A * discN (hRes h (perp h U)) B) ^ (e + e') : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.Mass.Glue.main | exact GlobalTheory.Mass.Glue.main | (intros; apply GlobalTheory.Mass.Glue.main <;> assumption)
end _root_.GlobalTheory.T
