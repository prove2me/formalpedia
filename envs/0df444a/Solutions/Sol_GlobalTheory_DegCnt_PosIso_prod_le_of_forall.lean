-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.prod_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:31:30.887799+00:00
-- url     : https://prove2.me/submissions/8727b1a5-835c-4aa0-b4c5-980c89ef3526

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution {ι : Type} [Fintype ι] (A : ι → Submodule (𝓞 K) K) (J : Submodule (𝓞 K) K)
    (h : ∀ f : ι → K, (∀ i, f i ∈ A i) → ∏ i, f i ∈ J) : ∏ i, A i ≤ J := by
  have : ∏ i, A i = ∏ i, Submodule.span (𝓞 K) (A i : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (Set.mem_fintype_prod _ _).1 hy
  exact h f hf
end GlobalTheory.DegCnt.PosIso
