-- Prove2me | solution 1 for MatchingPolytope.Multi.card_gcut_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:02.515232+00:00
-- url     : https://prove2.me/submissions/e9ef5d0c-7af4-4efc-852a-5b3b2b0270a7

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_sum_degree

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {M : Finset E} (hM : IsPM ends W F M) {S : Finset V}
    (hS : S ⊆ W) (hodd : Odd S.card) : Odd (gcut ends M S).card := by
  have h := sum_degree (β := ℕ) hV hM.1 S (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [Finset.sum_congr rfl (fun v hv => hM.2 v (hS hv))] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h] at hodd
  rcases Nat.even_or_odd (gcut ends M S).card with he | ho
  · exfalso
    rw [Nat.odd_iff] at hodd
    obtain ⟨k, hk⟩ := he
    omega
  · exact ho
end MatchingPolytope.Multi
