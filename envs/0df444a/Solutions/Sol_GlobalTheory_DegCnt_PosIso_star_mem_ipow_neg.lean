-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.star_mem_ipow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:51:41.974249+00:00
-- url     : https://prove2.me/submissions/3d04884c-cc9a-4225-ab2d-dde222edd5ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_star_mem_one
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_star_mem_ipow_nat
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
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ ipow 𝔡 (-(n : ℤ)), star x ∈ ipow 𝔡 (-(n : ℤ)) := by
  have hne : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (n : ℤ)) ≠ 0 := zpow_ne_zero _ (by simpa using h)
  have key : ∀ x : K, x ∈ ipow 𝔡 (-(n : ℤ)) ↔ ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x
    unfold ipow
    rw [zpow_neg, FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne]
    simp only [FractionalIdeal.mem_coe, ← FractionalIdeal.coe_one (S := (𝓞 K)⁰)]
  intro x hx
  rw [key] at hx ⊢
  intro y hy
  have := star_mem_one (hx _ (star_mem_ipow_nat 𝔡 h hs n y hy))
  simpa using this
end GlobalTheory.DegCnt.PosIso
