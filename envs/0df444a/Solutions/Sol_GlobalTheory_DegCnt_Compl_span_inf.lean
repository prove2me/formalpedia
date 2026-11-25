-- Prove2me | solution 1 for GlobalTheory.DegCnt.Compl.span_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:27:15.113265+00:00
-- url     : https://prove2.me/submissions/be605d7e-3263-4504-85bd-4c01390f978a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IdxSupRight
import Theorems.Thm_GlobalTheory_DegCnt_Compl_exists_mult

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Compl
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.Compl
theorem _root_.solution {M : Submodule (𝓞 K) V} {T : Submodule K V} (hT : T ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ rs (𝓞 K) T : Submodule (𝓞 K) V) : Set V) = T := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => hx.2
  · intro v hv
    obtain ⟨c, hc, h⟩ := exists_mult (hT hv)
    rw [← Submodule.smul_mem_iff _ hc]
    exact Submodule.subset_span ⟨h, T.smul_mem c hv⟩
end GlobalTheory.DegCnt.Compl
