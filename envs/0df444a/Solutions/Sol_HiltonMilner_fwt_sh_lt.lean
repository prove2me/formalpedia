-- Prove2me | solution 1 for HiltonMilner.fwt_sh_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:11:07.630192+00:00
-- url     : https://prove2.me/submissions/c29a3dff-bf50-4c78-8ba1-eb1fa5815ebf

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Theorems.Thm_HiltonMilner_wt_shift_lt

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z : ℕ} (hyz : y < z) {𝒜 : Finset (Finset ℕ)} (hne : sh y z 𝒜 ≠ 𝒜) :
    fwt (sh y z 𝒜) < fwt 𝒜 := by
  classical
  set c := UV.compress ({y} : Finset ℕ) {z}
  have hdef : sh y z 𝒜 = {a ∈ 𝒜 | c a ∈ 𝒜} ∪ {a ∈ 𝒜.image c | a ∉ 𝒜} := rfl
  have himg : {a ∈ 𝒜.image c | a ∉ 𝒜} = {a ∈ 𝒜 | c a ∉ 𝒜}.image c := by
    rw [filter_image]
  have hmove : ({a ∈ 𝒜 | c a ∉ 𝒜} : Finset _).Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    apply hne
    rw [hdef, himg, hem, image_empty, union_empty, filter_true_of_mem]
    intro a ha
    by_contra hca
    have : a ∈ ({a ∈ 𝒜 | c a ∉ 𝒜} : Finset _) := mem_filter.2 ⟨ha, hca⟩
    rw [hem] at this; simp at this
  unfold fwt
  rw [hdef, sum_union UV.compress_disjoint, himg, sum_image UV.compress_injOn]
  conv_rhs => rw [← filter_union_filter_not_eq (fun a => c a ∈ 𝒜) 𝒜,
    sum_union (disjoint_filter_filter_not _ _ _)]
  refine Nat.add_lt_add_left (sum_lt_sum_of_nonempty hmove fun a ha => ?_) _
  rw [mem_filter] at ha
  have hca : c a ≠ a := fun e => ha.2 (by rw [e]; exact ha.1)
  simp only [c, compress_eq] at hca ⊢
  unfold shiftSet at hca ⊢
  split_ifs at hca ⊢ with h
  · exact wt_shift_lt hyz h.1 h.2
  · exact absurd rfl hca
end HiltonMilner
