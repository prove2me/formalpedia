-- Prove2me | solution 1 for GlobalTheory.UnipStab.symm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:34.588793+00:00
-- url     : https://prove2.me/submissions/65cb1872-7551-4a96-a94e-a3c39389c037

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnipStab
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
variable {F}
namespace GlobalTheory.UnipStab
theorem _root_.solution [FiniteDimensional K V] (s : V ≃ₗ[K] V) (S : Submodule K V)
    (h : ∀ x ∈ S, s x ∈ S) {x : V} (hx : x ∈ S) : s.symm x ∈ S := by
  have h1 : S.map (s : V →ₗ[K] V) = S := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    · exact LinearEquiv.finrank_map_eq s S
  rw [← h1] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy
end GlobalTheory.UnipStab
