-- Prove2me | solution 1 for GlobalTheory.DegCnt.Glue.finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:00:19.888092+00:00
-- url     : https://prove2.me/submissions/fd82309e-defd-4f70-b596-52872e058c96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Glue
open TensorProduct
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]
namespace GlobalTheory.DegCnt.Glue
theorem _root_.solution {D : Submodule (𝓞 K) V} {W : Submodule K V} (h : D ≤ rs (𝓞 K) W) :
    Module.finrank (𝓞 K) D ≤ Module.finrank K W := by
  let f : D →ₗ[𝓞 K] W := { toFun := fun d => ⟨d, h d.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b e => Subtype.ext (congrArg (fun z : W => (z : V)) e)
  have h1 := LinearMap.rank_le_of_injective f hf
  rw [← IsLocalization.rank_eq (N := W) K (nonZeroDivisors (𝓞 K)) le_rfl] at h1
  exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K W)
end GlobalTheory.DegCnt.Glue
