-- Prove2me | solution 1 for IterOmega_IterStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:36:52.930239+00:00
-- url     : https://prove2.me/submissions/91ad5a53-a6fb-474d-836d-d69c18db0baf

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
import Theorems.Thm_epsilon_ConcatFin
import Theorems.Thm_subset_IterStar_IterFin
import Theorems.Thm_IterStar_seg_exists
import Theorems.Thm_P2M_Stream__extract_extract2__d35761143a43
import Theorems.Thm_segment_idem
import Theorems.Thm_segment_lower_bound
import Theorems.Thm_segment_range_val
import Theorems.Thm_segment_upper_bound
import Theorems.Thm_segment_zero


set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (List A)} :
    (L∗)^ω = L^ω := by
  ext as ; constructor
  · rintro ⟨φ, h_mono, h_init, h_rest⟩
    have h_rest' := fun m ↦ IterStar_seg_exists <| h_rest m
    choose sz ψ h_monoOn h_beg h_end h_seg using h_rest'
    have h_sz : ∀ n, sz n > 0 := by
      intro n ; by_contra ; have h_contra : sz n = 0 := by omega
      specialize h_beg n ; specialize h_end n
      simp [h_contra, length_extract] at h_end
      have := h_mono (show n < n + 1 by omega) ; omega
    let ξ n := ∑ i ∈ range n, sz i
    have h_init' : ξ 0 = 0 := by simp [ξ]
    have h_mono' : StrictMono ξ := by
      apply strictMono_nat_of_lt_succ ; intro n
      simp [ξ, Finset.sum_range_succ] ; exact h_sz n
    use (fun k ↦ φ (Segment ξ k) + ψ (Segment ξ k) (k - ξ (Segment ξ k)))
    simp [segment_zero h_mono' h_init', h_beg, h_init]
    suffices h : ∀ k,
        φ (Segment ξ k) + ψ (Segment ξ k) (k - ξ (Segment ξ k)) <
        φ (Segment ξ (k + 1)) + ψ (Segment ξ (k + 1)) (k + 1 - ξ (Segment ξ (k + 1))) ∧
        as.extract (φ (Segment ξ k) + ψ (Segment ξ k) (k - ξ (Segment ξ k)))
          (φ (Segment ξ (k + 1)) + ψ (Segment ξ (k + 1)) (k + 1 - ξ (Segment ξ (k + 1)))) ∈ L by
      constructor
      · apply strictMono_nat_of_lt_succ ; intro k ; exact (h k).1
      · intro k ; exact (h k).2
    intro k
    have := segment_lower_bound h_mono' h_init' k
    have := segment_upper_bound h_mono' h_init' k
    have h0 : ξ (Segment ξ k + 1) = ξ (Segment ξ k) + sz (Segment ξ k) := by simp [ξ, Finset.sum_range_succ]
    specialize h_seg (Segment ξ k) (k - ξ (Segment ξ k)) (by omega)
    specialize h_end (Segment ξ k)
    simp [length_extract] at h_end
    have h1 : ψ (Segment ξ k) (k - ξ (Segment ξ k) + 1) ≤ φ (Segment ξ k + 1) - φ (Segment ξ k) := by
      have := StrictMonoOn.monotoneOn (h_monoOn (Segment ξ k))
        (show k - ξ (Segment ξ k) + 1 < sz (Segment ξ k) + 1 by omega)
        (show sz (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (by omega) ; omega
    simp [extract_extract2' h1] at h_seg
    rcases (show k + 1 < ξ (Segment ξ k + 1) ∨ k + 1 = ξ (Segment ξ k + 1) by omega) with h_k | h_k
    · have h2 := segment_range_val h_mono' (show ξ (Segment ξ k) ≤ k + 1 by omega) (h_k)
      have h3 := h_monoOn (Segment ξ k)
        (show k - ξ (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (show k - ξ (Segment ξ k) + 1 < sz (Segment ξ k) + 1 by omega)
        (show k - ξ (Segment ξ k) < k - ξ (Segment ξ k) + 1 by omega)
      simp [h2, h3, h_seg, (show k + 1 - ξ (Segment ξ k) = k - ξ (Segment ξ k) + 1 by omega)]
    · have := h_mono (show Segment ξ k < Segment ξ k + 1 by omega)
      simp [h_k, h0, h_end, (show k - ξ (Segment ξ k) + 1 = k + 1 - ξ (Segment ξ k) by omega),
        (show φ (Segment ξ k) + (φ (Segment ξ k + 1) - φ (Segment ξ k)) = φ (Segment ξ k + 1) by omega)] at h_seg
      simp [h_k, segment_idem h_mono', h_beg, h_seg]
      have h3 := h_monoOn (Segment ξ k)
        (show k - ξ (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (show sz (Segment ξ k) < sz (Segment ξ k) + 1 by omega)
        (show k - ξ (Segment ξ k) < sz (Segment ξ k) by omega)
      omega
  · rintro ⟨φ, h_mono, h_init, h_rest⟩
    use φ ; simp [h_mono, h_init] ; intro n
    apply subset_IterStar_IterFin L 1
    change _ ∈ IterFin L 1
    simp [IterFin, epsilon_ConcatFin]
    exact h_rest n
