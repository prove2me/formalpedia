-- Prove2me | solution 1 for GlobalTheory.DegCnt.Absorb.star_mem_ipow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:44.538046+00:00
-- url     : https://prove2.me/submissions/ff64a9d7-a3da-4644-8803-062d444da327

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_nat
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_iff
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_coe_sig
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_star_mem_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K]
namespace GlobalTheory.DegCnt.Absorb
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ) :
    ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
  have hm : 𝔡.map (sig K : 𝓞 K →+* 𝓞 K) ≤ 𝔡 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, e⟩ := hs x hx
    have : y = sig K x := by ext; rw [e, coe_sig]
    rw [Ideal.mem_comap]
    exact this ▸ hy
  have hn : ∀ n : ℕ, ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
    intro n x hx
    obtain ⟨d, hd, rfl⟩ := (mem_ipow_nat 𝔡 n x).1 hx
    refine (mem_ipow_nat 𝔡 n _).2 ⟨sig K d, ?_, rfl⟩
    have := Ideal.mem_map_of_mem (sig K : 𝓞 K →+* 𝓞 K) hd
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hm n this
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact hn m
  · intro x hx
    rw [mem_ipow_iff h, neg_neg] at hx ⊢
    intro u hu
    have := star_mem_one (hx _ (hn m u hu))
    rwa [star_mul', star_star] at this
end GlobalTheory.DegCnt.Absorb
