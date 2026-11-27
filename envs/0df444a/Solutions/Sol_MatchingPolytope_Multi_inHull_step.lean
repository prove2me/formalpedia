-- Prove2me | solution 1 for MatchingPolytope.Multi.inHull_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:45.255074+00:00
-- url     : https://prove2.me/submissions/19d274d7-94e2-482d-bb61-84eab3e2b885

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_inHull_of_reducible
public import Theorems.Thm_MatchingPolytope_Multi_exists_reducible_along
public import Theorems.Thm_MatchingPolytope_Multi_exists_ker_of_card_lt
public import Theorems.Thm_MatchingPolytope_Multi_exists_pm_small
public import Theorems.Thm_MatchingPolytope_Multi_three_le_card_gcut
public import Theorems.Thm_MatchingPolytope_Multi_InHull_convex
public import Theorems.Thm_MatchingPolytope_Multi_InHull_of_mem
public import Theorems.Thm_MatchingPolytope_Multi_InHull_push
public import Theorems.Thm_MatchingPolytope_Multi_chi_mem_poly
public import Theorems.Thm_MatchingPolytope_Multi_gcut_self
public import Theorems.Thm_MatchingPolytope_Multi_inside_self
public import Theorems.Thm_MatchingPolytope_Multi_sum_degree


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [Fintype E]
    (IH : ∀ (ends' : E → Sym2 V) (W' : Finset V) (F' : Finset E),
      W'.card + F'.card < W.card + F.card → Valid ends' W' F' →
        ∀ x ∈ Poly ends' W' F', InHull (IsPM ends' W' F') x)
    (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    InHull (IsPM ends W F) x := by
  classical
  by_cases hred : Reducible ends W F x
  · exact inHull_of_reducible IH hV hx hred
  by_cases hk : ∃ d, Ker ends W F d ∧ d ≠ 0
  · obtain ⟨d, hd, hd0⟩ := hk
    have hd' : Ker ends W F (-d) :=
      ⟨fun e he => by simp [hd.1 e he], fun v hv => by simp [hd.2 v hv]⟩
    obtain ⟨t1, ht1, hm1, hr1⟩ := exists_reducible_along hV hx hred hd hd0
    obtain ⟨t2, ht2, hm2, hr2⟩ := exists_reducible_along hV hx hred hd' (neg_ne_zero.2 hd0)
    have h1 := inHull_of_reducible IH hV hm1 hr1
    have h2 := inHull_of_reducible IH hV hm2 hr2
    have hconv := h1.convex h2 (a := t2 / (t1 + t2)) (b := t1 / (t1 + t2)) (by positivity)
      (by positivity) (by field_simp; ring)
    convert hconv using 1
    funext e
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    field_simp
    ring
  push Not at hk
  have hFW : F.card ≤ W.card := by
    by_contra h
    obtain ⟨d, hd, hd0⟩ := exists_ker_of_card_lt (ends := ends) (lt_of_not_ge h)
    exact hd0 (hk d hd)
  by_cases hW4 : W.card ≤ 4
  · obtain ⟨M, hM⟩ := exists_pm_small hV hx hW4
    have hchi := chi_mem_poly hV hM
    have hker : Ker ends W F (chi M - x) := by
      refine ⟨fun e he => by simp [hchi.1 e he, hx.1 e he], fun v hv => ?_⟩
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, hchi.2.2.1 v hv, hx.2.2.1 v hv, sub_self]
    have := hk _ hker
    rw [sub_eq_zero] at this
    rw [← this]
    exact InHull.of_mem hM
  · exfalso
    have hdeg := sum_degree (β := ℕ) hV subset_rfl W (fun _ => 1)
    rw [gcut_self hV subset_rfl, inside_self hV subset_rfl] at hdeg
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_empty, zero_add] at hdeg
    have h3 : ∑ v ∈ W, 3 ≤ ∑ v ∈ W, (gcut ends F {v}).card :=
      Finset.sum_le_sum fun v hv => three_le_card_gcut hV hx hred (by omega) hv
    simp only [Finset.sum_const, smul_eq_mul] at h3
    omega
end MatchingPolytope.Multi
