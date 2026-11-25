-- Prove2me | solution 1 for GlobalTheory.Mass.Transp.img_img_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:51.325797+00:00
-- url     : https://prove2.me/submissions/0397727c-61a0-4363-bcb1-76d8c95e50a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
import Theorems.Thm_GlobalTheory_Mass_Transp_mem_img

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
open NumberField Matrix
open scoped ENNReal Classical
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
omit [StarRing K]
namespace GlobalTheory.Mass.Transp
namespace _root_.GlobalTheory.Mass.Transp
theorem _root_.solution (e : V ≃ₗ[K] V') (L : Submodule R V') :
    _root_.GlobalTheory.Mass.Transp.img e (_root_.GlobalTheory.Mass.Transp.img e.symm L) = L := by
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.mem_img]
end _root_.GlobalTheory.Mass.Transp
end GlobalTheory.Mass.Transp
