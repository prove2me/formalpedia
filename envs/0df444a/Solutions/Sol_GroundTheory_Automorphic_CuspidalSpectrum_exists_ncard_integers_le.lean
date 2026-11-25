-- Prove2me | solution 1 for GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:51.922111+00:00
-- url     : https://prove2.me/submissions/01db6512-d791-49d1-8020-c771c1fa7c5b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
import Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_abs_repr_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Set
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.CuspidalSpectrum
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Automorphic.CuspidalSpectrum
theorem _root_.solution :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      {z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.Finite ∧
      (({z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.ncard : ℝ) ≤
        C * (1 + T) ^ Module.finrank ℚ K) := by
  classical
  obtain ⟨C₀, hC₀, hrepr⟩ := exists_abs_repr_le K
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  have hd : Fintype.card ι = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  refine ⟨(3 + 2 * C₀) ^ Module.finrank ℚ K, by positivity, fun T hT => ?_⟩
  set N : ℕ := ⌈C₀ * T⌉₊
  set box : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N
  set c : 𝓞 K → ι → ℤ := fun z i => (RingOfIntegers.basis K).repr z i
  have hmaps : ∀ z ∈ {z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}, c z ∈ (box : Set (ι → ℤ)) := by
    intro z hz
    have hnorm : ‖mixedEmbedding K (z : K)‖ ≤ T := by
      rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
      refine Finset.sup'_le _ _ fun w _ => ?_
      rw [mixedEmbedding.normAtPlace_apply]
      exact hz w
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    have h1 := (hrepr z i).trans (mul_le_mul_of_nonneg_left hnorm hC₀)
    have h2 : C₀ * T ≤ N := Nat.le_ceil _
    have h3 : |(c z i : ℝ)| ≤ N := h1.trans h2
    rw [abs_le] at h3
    rw [Finset.mem_Icc]
    constructor <;> [exact_mod_cast (by linarith [h3.1] : (-(N : ℝ)) ≤ c z i);
      exact_mod_cast h3.2]
  have hinj : InjOn c {z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T} := by
    intro z _ z' _ h
    refine (RingOfIntegers.basis K).repr.injective (Finsupp.ext fun i => ?_)
    exact congrFun h i
  have hfin : (box : Set (ι → ℤ)).Finite := Finset.finite_toSet _
  refine ⟨hfin.of_injOn hmaps hinj, ?_⟩
  have hcard := Set.ncard_le_ncard_of_injOn c hmaps hinj hfin
  rw [Set.ncard_coe_finset, Fintype.card_piFinset] at hcard
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ] at hcard
  have hN : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [hN, hd] at hcard
  have hNle : (2 * N + 1 : ℝ) ≤ (3 + 2 * C₀) * (1 + T) := by
    have : (N : ℝ) ≤ C₀ * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    nlinarith
  calc (({z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.ncard : ℕ) : ℝ)
      ≤ ((2 * N + 1) ^ Module.finrank ℚ K : ℕ) := by exact_mod_cast hcard
    _ = (2 * N + 1 : ℝ) ^ Module.finrank ℚ K := by push_cast; ring
    _ ≤ ((3 + 2 * C₀) * (1 + T)) ^ Module.finrank ℚ K := by gcongr
    _ = (3 + 2 * C₀) ^ Module.finrank ℚ K * (1 + T) ^ Module.finrank ℚ K := mul_pow _ _ _
end GroundTheory.Automorphic.CuspidalSpectrum
