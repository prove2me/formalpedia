-- Prove2me | solution 1 for HyperCheeger.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:33.125409+00:00
-- url     : https://prove2.me/submissions/96fe2537-da7f-4d96-aec6-94ba7911c994

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance
import Theorems.Thm_HyperCheeger_eq_1

section
set_option autoImplicit false

namespace HyperCheeger.Dev.Eq2

/-- With at least two vertices there is a proper nonempty subset. -/
lemma index_nonempty {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) :
    Nonempty {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ} := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  refine ⟨⟨{a}, Finset.singleton_nonempty a, fun h => hab ?_⟩⟩
  have hb : b ∈ ({a} : Finset V) := h ▸ Finset.mem_univ b
  exact (Finset.mem_singleton.mp hb).symm

end HyperCheeger.Dev.Eq2

namespace HyperCheeger
open HyperCheeger.Dev.Eq2 in
theorem chk_eq_2 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) (H : Hypergraph V) :
    H.conductance ≤ H.diffusionConductance ∧
      H.diffusionConductance ≤ (H.rank : ℝ) / 2 * H.conductance := by
  have := index_nonempty hV
  unfold Hypergraph.conductance Hypergraph.diffusionConductance
  constructor
  · exact ciInf_mono (Set.finite_range _).bddBelow
      fun S => (HyperCheeger.eq_1 H S.1 S.2.1 S.2.2).1
  · obtain ⟨S, hS⟩ := exists_eq_ciInf_of_finite
      (f := fun S : {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ} => H.conductanceSet S)
    rw [← hS]
    exact (ciInf_le (Set.finite_range _).bddBelow S).trans
      (HyperCheeger.eq_1 H S.1 S.2.1 S.2.2).2

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_eq_2 := @HyperCheeger.chk_eq_2
