-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.smul_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:39.724958+00:00
-- url     : https://prove2.me/submissions/88f07a03-d519-46f9-a9eb-7165aac7a0cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_smul_mem_of_pairing
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
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
variable {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : 𝓞 K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      (γ : K) * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {y ξ : V} (hy : ∀ u ∈ N.F'.X, H.B y u = 0) (hξ : ξ ∈ N.F.Xa N.j) (h : y - ξ ∈ Λ) : γ • y ∈ Λ := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hΛ.1.2, mem_dual_iff] at hx
    exact hx.2
  have h1 := smul_mem_of_pairing N Λ hΛ γ hγ hξ fun u hu hu' => by
    have := neg_mem (hint _ h u hu)
    simpa [hy u hu'] using this
  have h2 : γ • ξ ∈ Λ := by rw [← algebraMap_smul K γ ξ]; exact h1
  simpa [smul_sub] using add_mem (Λ.smul_mem γ h) h2
end GlobalTheory.DegCnt.PosIso
