-- Prove2me | solution 1 for GlobalTheory.T.witt_extension_totally_definite_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:29:52.986634+00:00
-- url     : https://prove2.me/submissions/7a649118-d633-4630-8be8-f3783dc20e1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Theorems.Thm_GlobalTheory_Mass_Witt_witt_definite


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
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  first | exact @GlobalTheory.Mass.Witt.witt_definite | exact GlobalTheory.Mass.Witt.witt_definite | (intros; apply GlobalTheory.Mass.Witt.witt_definite <;> assumption)
end _root_.GlobalTheory.T
