-- Prove2me | solution 1 for MatchingPolytope.Multi.exists_reducible_along
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:12.403517+00:00
-- url     : https://prove2.me/submissions/dc88ba80-f340-43be-9f80-40e9a87c0c17

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_exists_pos_add_mem
public import Theorems.Thm_MatchingPolytope_Multi_exists_neg_of_ker
public import Theorems.Thm_MatchingPolytope_Multi_isClosed_poly


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq V] (hV : Valid ends W F) {x d : E → ℝ}
    (hx : x ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F x) (hd : Ker ends W F d) (hd0 : d ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ x + t • d ∈ Poly ends W F ∧ Reducible ends W F (x + t • d) := by
  obtain ⟨e₀, he₀⟩ := exists_neg_of_ker hV hd hd0
  set T : Set ℝ := {t | 0 ≤ t ∧ x + t • d ∈ Poly ends W F} with hT
  have hbdd : BddAbove T := by
    refine ⟨x e₀ / -d e₀, fun t ht => ?_⟩
    have h := ht.2.2.1 e₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hcl : IsClosed T := by
    have : T = Set.Ici 0 ∩ (fun t : ℝ => x + t • d) ⁻¹' Poly ends W F := rfl
    rw [this]
    exact isClosed_Ici.inter ((isClosed_poly ends W F).preimage (by fun_prop))
  have hne : T.Nonempty := ⟨0, le_rfl, by simpa using hx⟩
  have hmem := hcl.csSup_mem hne hbdd
  obtain ⟨ε, hε, hεmem⟩ := exists_pos_add_mem hV hx hirr hd
  have hpos : 0 < sSup T := lt_of_lt_of_le hε (le_csSup hbdd ⟨hε.le, hεmem⟩)
  refine ⟨sSup T, hpos, hmem.2, ?_⟩
  by_contra hred
  obtain ⟨ε', hε', hmem'⟩ := exists_pos_add_mem hV hmem.2 hred hd
  have : sSup T + ε' ∈ T := by
    refine ⟨by linarith, ?_⟩
    have heq : x + (sSup T + ε') • d = x + sSup T • d + ε' • d := by
      rw [add_smul, add_assoc]
    rw [heq]; exact hmem'
  have := le_csSup hbdd this
  linarith
end MatchingPolytope.Multi
