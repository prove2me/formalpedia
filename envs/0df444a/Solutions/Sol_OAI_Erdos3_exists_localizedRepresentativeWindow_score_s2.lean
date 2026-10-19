-- Prove2me | solution 1 for OAI.Erdos3.exists_localizedRepresentativeWindow_score_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:44.493288+00:00
-- url     : https://prove2.me/submissions/b216f144-c9b5-4e5f-9b7e-4098b4c55bb9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

theorem residue_fraction_mem_unit_interval {N : ℕ} [NeZero N] (x : ZMod N) :
    0 ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact ⟨by positivity, (div_le_one hN).mpr (by exact_mod_cast x.val_lt.le)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem interiorIntervalCutoff_one (eta : ℝ≥0) (heta : 0 < eta) {x : ℝ}
    (hx : 2 * (eta : ℝ) ≤ x ∧ x ≤ 1 - 2 * eta) : interiorIntervalCutoff eta x = 1 := by
  apply linearCutoff_eq_one _ _ heta
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem interiorIntervalCutoff_cyclic_loss {N : ℕ} [NeZero N]
    (eta : ℝ≥0) (heta : 0 < eta) :
    (𝔼 x : ZMod N, |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)|) ≤
      12 * (eta : ℝ) + 3 / N := by
  let E := cyclicWrapExceptional (0 : ZMod N) (2 * eta)
  have hcap (x : ZMod N) : |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)| ≤ 1 := by
    have h := interiorIntervalCutoff_range eta ((x.val : ℝ) / N)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hgood (x : ZMod N) (hx : x ∉ E) :
      |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)| ≤ 0 := by
    obtain ⟨h0, h1, _⟩ := outside_cyclicWrapExceptional (0 : ZMod N) x hx
    rw [interiorIntervalCutoff_one eta heta ⟨h0.le, h1.le⟩]
    norm_num
  have h := expect_abs_le_of_exceptional_set E _ (by norm_num : (0 : ℝ) ≤ 0) hcap hgood
  simp only [zero_add, one_mul, ZMod.card] at h
  apply h.trans
  calc
    _ ≤ 6 * (2 * (eta : ℝ)) + 3 / N :=
      cyclicWrapExceptional_density_le (0 : ZMod N) (show 0 ≤ 2 * (eta : ℝ) by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CyclicInteriorScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem bounded_cutoff_score_lower {X : Type*} [Fintype X]
    (f b : X → ℝ) {M epsilon sigma : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hb : (𝔼 x, |1 - b x|) ≤ epsilon)
    (hscore : sigma ≤ 𝔼 x, f x) :
    sigma - M * epsilon ≤ 𝔼 x, f x * b x := by
  have hloss : (𝔼 x, f x * (1 - b x)) ≤ M * epsilon := by
    calc
      _ ≤ 𝔼 x, M * |1 - b x| := by
        apply Finset.expect_le_expect
        intro x _
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _))
      _ = M * (𝔼 x, |1 - b x|) := (Finset.mul_expect ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hb hM
  have he : (𝔼 x, f x) = (𝔼 x, f x * b x) + (𝔼 x, f x * (1 - b x)) := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro x _
    ring
  linarith

theorem interiorIntervalCutoff_score {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (eta : ℝ≥0) (heta : 0 < eta) (hwidth : (eta : ℝ) ≤ sigma / (100 * M))
    (hN : 1 / (N : ℝ) ≤ sigma / (100 * M)) :
    3 * sigma / 4 ≤ 𝔼 x, f x * interiorIntervalCutoff eta ((x.val : ℝ) / N) := by
  have h := bounded_cutoff_score_lower f
    (fun x => interiorIntervalCutoff eta ((x.val : ℝ) / N)) hM.le hf
    (interiorIntervalCutoff_cyclic_loss eta heta) hscore
  have he : M * (sigma / (100 * M)) = sigma / 100 := by field_simp [hM.ne']
  have hw := mul_le_mul_of_nonneg_left hwidth hM.le
  have hrec := mul_le_mul_of_nonneg_left hN hM.le
  have hthree : (3 : ℝ) / N = 3 * (1 / N) := by ring
  rw [he] at hw hrec
  rw [hthree] at h
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositivePartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_weighted_partition_score {Ω ι : Type*} [Fintype Ω] [Fintype ι] [Nonempty ι]
    (a : Ω → ℝ) (w : ι → Ω → ℝ) (hsum : ∀ x, ∑ i, w i x = 1)
    {S : ℝ} (hS : S ≤ 𝔼 x, a x) :
    ∃ i, S / Fintype.card ι ≤ 𝔼 x, a x * w i x := by
  have htotal : (∑ i, 𝔼 x, a x * w i x) = 𝔼 x, a x := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.mul_sum, hsum, mul_one]
  have hmean : (𝔼 i, 𝔼 x, a x * w i x) = (𝔼 x, a x) / Fintype.card ι := by
    rw [Fintype.expect_eq_sum_div_card, htotal]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (show S / Fintype.card ι ≤ 𝔼 i, 𝔼 x, a x * w i x from
      hmean.symm ▸ div_le_div_of_nonneg_right hS (Nat.cast_nonneg _))
  exact ⟨i, hi⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem representativeWindowCount_pos : 0 < representativeWindowCount := by
  unfold representativeWindowCount intervalSiteCount
  omega

theorem exists_localizedRepresentativeWindow_score_s2_oai {N : ℕ} [NeZero N]
    (f : ZMod N → ℝ) {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (eta : ℝ≥0) (heta : 0 < eta) (hwidth : (eta : ℝ) ≤ sigma / (100 * M))
    (hN : 1 / (N : ℝ) ≤ sigma / (100 * M)) :
    ∃ i : Fin representativeWindowCount, 3 * sigma / (4 * representativeWindowCount) ≤
      𝔼 x, f x * (localizedRepresentativeWindow eta heta i).value ((x.val : ℝ) / N) := by
  let : Nonempty (Fin representativeWindowCount) := ⟨⟨0, representativeWindowCount_pos⟩⟩
  have hs := interiorIntervalCutoff_score f hM hsigma hf hscore eta heta hwidth hN
  have hsum (x : ZMod N) : (∑ i : Fin representativeWindowCount,
      intervalSiteWeight 1 (1 / 16) i ((x.val : ℝ) / N)) = 1 :=
    intervalSiteWeight_sum (by norm_num) (by norm_num) _
      (by rw [abs_of_nonneg (residue_fraction_mem_unit_interval x).1]
          exact (residue_fraction_mem_unit_interval x).2)
  obtain ⟨i, hi⟩ := exists_weighted_partition_score (ι := Fin representativeWindowCount)
    (fun x : ZMod N => f x * interiorIntervalCutoff eta ((x.val : ℝ) / N))
    (fun i x => intervalSiteWeight 1 (1 / 16) i ((x.val : ℝ) / N)) hsum hs
  refine ⟨i, ?_⟩
  simpa only [Fintype.card_fin, div_div, mul_assoc, localizedRepresentativeWindow] using hi

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_localizedRepresentativeWindow_score_s2_oai := @OAI.Erdos3.exists_localizedRepresentativeWindow_score_s2_oai
