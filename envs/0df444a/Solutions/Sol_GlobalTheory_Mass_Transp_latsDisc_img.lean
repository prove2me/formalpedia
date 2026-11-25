-- Prove2me | solution 1 for GlobalTheory.Mass.Transp.latsDisc_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:10:02.060798+00:00
-- url     : https://prove2.me/submissions/b862eda2-532e-4bb9-9c2e-75dc558b1dac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
import Theorems.Thm_GlobalTheory_Mass_Transp_discN_img
import Theorems.Thm_GlobalTheory_Mass_Transp_intLat_img

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
theorem _root_.solution (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (n : ℕ)
    (L : Submodule R V) (hL : L ∈ latsDisc (R := R) h n) : img e L ∈ latsDisc (R := R) h' n :=
  ⟨intLat_img e he L hL.1, (discN_img e he L).trans hL.2⟩
end GlobalTheory.Mass.Transp
