-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.star_mem_ipow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:14.730272+00:00
-- url     : https://prove2.me/submissions/5ec8151b-6279-4d1f-9bb3-f675d692efd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_ipow_add
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_ipow_zero
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_ipow_mul
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_mem_ipow_of
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_star_mem_one
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (n : ℤ) : ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
  have hm : ∀ m n : ℤ, (∀ x ∈ ipow 𝔡 m, star x ∈ ipow 𝔡 m) → (∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n) →
      ∀ x ∈ ipow 𝔡 (m + n), star x ∈ ipow 𝔡 (m + n) := by
    intro m n hm hn x hx
    rw [ipow_add h] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']; exact ipow_mul h (hm a ha) (hn b hb)
    · rw [star_add]; exact add_mem ha hb
  have h0 : ∀ x ∈ ipow 𝔡 0, star x ∈ ipow 𝔡 0 := by
    rw [ipow_zero]; exact fun x => star_mem_one
  have h1 : ∀ x ∈ ipow 𝔡 1, star x ∈ ipow 𝔡 1 := by
    intro x hx
    rw [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact hs y hy
  have h2 : ∀ x ∈ ipow 𝔡 (-1), star x ∈ ipow 𝔡 (-1) := by
    intro x hx
    refine mem_ipow_of h (m := 1) fun y hy => ?_
    have := h0 _ (by simpa using ipow_mul h (h1 y hy) hx)
    simpa [star_mul'] using this
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact hm _ _ ih h1
  | pred i ih => rw [sub_eq_add_neg]; exact hm _ _ ih h2
end GlobalTheory.DegCnt.PosJ
