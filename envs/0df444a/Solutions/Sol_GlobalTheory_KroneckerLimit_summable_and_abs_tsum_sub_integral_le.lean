-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.summable_and_abs_tsum_sub_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:17.368333+00:00
-- url     : https://prove2.me/submissions/cb8a69d9-c847-4deb-be27-01bc238a9b3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Theorems.Thm_GlobalTheory_KroneckerLimit_abs_sum_range_sub_integral_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology MeasureTheory Set
open scoped Real
namespace GlobalTheory.KroneckerLimit
private theorem le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici {f : ℝ → ℝ} (hm : MonotoneOn f (Iic 0))
    (ha : AntitoneOn f (Ici 0)) (t : ℝ) : f t ≤ f 0 := by
  rcases le_total t 0 with h | h
  · exact hm (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h
  · exact ha (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
end GlobalTheory.KroneckerLimit
end

set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (hi : Integrable f) (a : ℝ) :
    Summable (fun n : ℤ => f (a + n)) ∧ |∑' n : ℤ, f (a + n) - ∫ t, f t| ≤ f 0 := by
  have htop : ∀ t, f t ≤ f 0 := fun t => le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici hm ha t
  have hfin : ∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), f (a - N + i) ≤ (∫ t, f t) + f 0 ∧
      ∫ t in (a - N)..(a + N), f t ≤ ∑ i ∈ Finset.range (2 * N), f (a - N + i) + f 0 := by
    intro N
    have h := abs_le.1 (abs_sum_range_sub_integral_le h0 hc hm ha (a - N) (2 * N))
    have he : a - N + ((2 * N : ℕ) : ℝ) = a + N := by push_cast; ring
    rw [he] at h
    have hle : ∫ t in (a - N)..(a + N), f t ≤ ∫ t, f t := by
      rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => h0 t)
    obtain ⟨hl1, hl2⟩ := h
    constructor <;> linarith
  have himg : ∀ N : ℕ, ∑ n ∈ (Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N), f (a + n) =
      ∑ i ∈ Finset.range (2 * N), f (a - N + i) := by
    intro N
    rw [Finset.sum_image (by intro i _ j _ h; simpa using h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    push_cast
    ring
  have hset : ∀ s : Finset ℤ, ∃ N : ℕ,
      s ⊆ (Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N) := by
    intro s
    obtain ⟨S, hS⟩ : ∃ S : ℕ, S = ∑ m ∈ s, m.natAbs := ⟨_, rfl⟩
    refine ⟨S + 1, fun n hn => ?_⟩
    have hle : n.natAbs ≤ S := hS ▸
      Finset.single_le_sum (f := fun m : ℤ => m.natAbs) (fun _ _ => Nat.zero_le _) hn
    rw [Finset.mem_image]
    refine ⟨(n + ((S + 1 : ℕ) : ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  have hbound : ∀ s : Finset ℤ, ∑ n ∈ s, f (a + n) ≤ (∫ t, f t) + f 0 := by
    intro s
    obtain ⟨N, hN⟩ := hset s
    have := Finset.sum_le_sum_of_subset_of_nonneg hN (fun n _ _ => h0 (a + n))
    rw [himg N] at this
    linarith [(hfin N).1]
  have hsum : Summable (fun n : ℤ => f (a + n)) := summable_of_sum_le (fun n => h0 _) hbound
  refine ⟨hsum, abs_le.2 ⟨?_, ?_⟩⟩
  · have hbot : Tendsto (fun N : ℕ => a - (N : ℝ)) atTop atBot :=
      tendsto_atBot.2 fun b => eventually_atTop.2 ⟨⌈a - b⌉₊, fun N hN => by
        have h1 := Nat.le_ceil (a - b)
        have h2 : ((⌈a - b⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
        linarith⟩
    have htop' : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop :=
      tendsto_atTop.2 fun b => eventually_atTop.2 ⟨⌈b - a⌉₊, fun N hN => by
        have h1 := Nat.le_ceil (b - a)
        have h2 : ((⌈b - a⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
        linarith⟩
    have hlim := intervalIntegral_tendsto_integral hi hbot htop'
    have : ∫ t, f t ≤ ∑' n : ℤ, f (a + n) + f 0 := le_of_tendsto' hlim fun N => by
      show ∫ t in (a - N)..(a + N), f t ≤ _
      have h1 := (hfin N).2
      have h2 := hsum.sum_le_tsum ((Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N))
        (fun n _ => h0 _)
      rw [himg N] at h2
      linarith
    linarith
  · have := Real.tsum_le_of_sum_le (fun n => h0 _) hbound
    linarith
end GlobalTheory.KroneckerLimit
