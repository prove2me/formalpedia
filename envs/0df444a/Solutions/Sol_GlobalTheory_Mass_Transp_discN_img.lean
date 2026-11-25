-- Prove2me | solution 1 for GlobalTheory.Mass.Transp.discN_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:42.192642+00:00
-- url     : https://prove2.me/submissions/9566ff74-0da5-429a-915f-c8615853b2a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
import Theorems.Thm_GlobalTheory_Mass_Transp_dual_img

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Transp
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace GlobalTheory.Mass.Transp
theorem _root_.solution (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule R V) :
    discN h' (img e L) = discN h L := by
  unfold discN idxN
  rw [dual_img e he]
  have h1 : ∀ M : Submodule R V, (img e M).toAddSubgroup
      = M.toAddSubgroup.map (e.toAddEquiv : V →+ V') := by
    intro M; ext y; simp [img]
  rw [h1, h1]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ e.injective
end GlobalTheory.Mass.Transp
