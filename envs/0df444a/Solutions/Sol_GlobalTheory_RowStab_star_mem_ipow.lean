-- Prove2me | solution 1 for GlobalTheory.RowStab.star_mem_ipow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:57.084597+00:00
-- url     : https://prove2.me/submissions/b501fb03-b165-4133-b49e-04f996a86d6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Theorems.Thm_GlobalTheory_RowStab_star_pow_mem
import Theorems.Thm_GlobalTheory_RowStab_star_mem_one
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors
open GlobalTheory GlobalTheory.RowStab
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.RowStab
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥)
    (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ) {x : K} (hx : x ∈ ipow 𝔡 n) :
    star x ∈ ipow 𝔡 n := by
  have hA : ∀ k : ℕ, ∀ x : K, x ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ k) →
      star x ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ k) := by
    intro k x hx
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal] at *
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', e⟩ := star_pow_mem h𝔡s k y hy
    exact ⟨y', hy', e⟩
  unfold ipow at *
  rw [FractionalIdeal.mem_coe] at *
  rcases n with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast] at *
    exact hA k x hx
  · have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ^ (k + 1) ≠ 0 := by
      apply pow_ne_zero; simpa using h𝔡
    rw [zpow_negSucc, FractionalIdeal.mem_inv_iff h0] at *
    intro y hy
    have := star_mem_one (hx (star y) (hA _ y hy))
    simpa [star_mul', mul_comm] using this
end GlobalTheory.RowStab
