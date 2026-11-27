-- Prove2me | solution 1 for MatchingPolytope.Multi.exists_ker_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:47.927013+00:00
-- url     : https://prove2.me/submissions/b3a0101d-2cc6-44f0-96e4-3ff0bcba87ff

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [Finite E] (hlt : W.card < F.card) :
    ∃ d, Ker ends W F d ∧ d ≠ 0 := by
  classical
  have := Fintype.ofFinite E
  let L : (E → ℝ) →ₗ[ℝ] (W → ℝ) × ((univ \ F : Finset E) → ℝ) :=
    (LinearMap.pi fun v : W => ∑ e ∈ gcut ends F {(v : V)}, LinearMap.proj e).prod
      (LinearMap.pi fun e : (univ \ F : Finset E) => LinearMap.proj (e : E))
  have hrank : Module.finrank ℝ ((W → ℝ) × ((univ \ F : Finset E) → ℝ)) <
      Module.finrank ℝ (E → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have := Finset.card_le_univ F
    omega
  obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt hrank
    (f := L))
  rw [LinearMap.mem_ker] at hd
  refine ⟨d, ⟨fun e he => ?_, fun v hv => ?_⟩, hd0⟩
  · have := congrArg (fun p => p.2 ⟨e, by simp [he]⟩) hd
    simpa [L] using this
  · have := congrArg (fun p => p.1 ⟨v, hv⟩) hd
    simpa [L] using this
end MatchingPolytope.Multi
