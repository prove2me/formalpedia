-- Prove2me | solution 1 for GlobalTheory.DegCnt.NormOneCount.exists_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:10.892376+00:00
-- url     : https://prove2.me/submissions/fa3fb917-813a-4489-a987-8abbe0aec8e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
import Theorems.Thm_GlobalTheory_DegCnt_NormOneCount_isIntegral_of_mul_mem
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
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NormOneCount
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.DegCnt.NormOneCount
theorem _root_.solution [StarRing K] (hK : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    {𝔞 𝔞' : Ideal (𝓞 K)} (h : 𝔞' ≠ ⊥) {c d : K} (hc : c * star c = 1) (hd : d * star d = 1)
    (h1 : ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) (h2 : ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) :
    ∃ ζ : Units.torsion K, c = algebraMap (𝓞 K) K ((ζ : (𝓞 K)ˣ) : 𝓞 K) * d := by
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hd0 : d ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have i1 : IsIntegral ℤ (c / d) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h2, show c / d * t * d = t * c by field_simp, h1]; exact ht
  have i2 : IsIntegral ℤ (d / c) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h1, show d / c * t * c = t * d by field_simp, h2]; exact ht
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c / d := ⟨⟨c / d, i1⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = d / c := ⟨⟨d / c, i2⟩, rfl⟩
  have hm : a * b = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_one, ha, hb]
    field_simp
  have hn : ∀ (φ : K →+* ℂ) (e : K), e * star e = 1 → ‖φ e‖ = 1 := fun φ e he => by
    have h3 := congrArg (fun z => ‖φ z‖) he
    simp only [map_mul, hK, map_one, norm_mul, norm_one, RCLike.norm_conj] at h3
    nlinarith [norm_nonneg (φ e)]
  refine ⟨⟨Units.mkOfMulEqOne _ _ hm, (Units.mem_torsion K).2 fun w => ?_⟩, ?_⟩
  · show w (algebraMap (𝓞 K) K a) = 1
    rw [ha, ← InfinitePlace.norm_embedding_eq, map_div₀, norm_div, hn _ c hc, hn _ d hd, div_one]
  · show c = algebraMap (𝓞 K) K a * d
    rw [ha]
    field_simp
end GlobalTheory.DegCnt.NormOneCount
