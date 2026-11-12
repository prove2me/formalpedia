-- Prove2me | solution 1 for HyperCheeger.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:30.674941+00:00
-- url     : https://prove2.me/submissions/c71b76a2-a153-4cda-9951-61bdac9a72a6

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance

section
set_option autoImplicit false

namespace HyperCheeger.Dev.Eq1

open HyperCheeger HyperCheeger.Hypergraph

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma degree_nonneg (H : Hypergraph V) (u : V) : 0 ≤ H.degree u :=
  Finset.sum_nonneg fun e he => H.w_nonneg e (Finset.mem_filter.mp he).1

lemma vol_nonneg (H : Hypergraph V) (S : Finset V) : 0 ≤ H.vol S :=
  Finset.sum_nonneg fun u _ => degree_nonneg H u

/-- The elementary inequality behind eq. (1): for naturals `p, q ≥ 1` with `p + q ≤ r`,
`1 ≤ pq/(p+q-1) ≤ r/2`. -/
lemma key (p q r : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : p + q ≤ r) :
    1 ≤ (p : ℝ) * q / ((p : ℝ) + q - 1) ∧ (p : ℝ) * q / ((p : ℝ) + q - 1) ≤ (r : ℝ) / 2 := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr' : (p : ℝ) + q ≤ r := by exact_mod_cast hr
  have hd : (0 : ℝ) < p + q - 1 := by linarith
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 2)]; nlinarith

lemma edge_bounds (H : Hypergraph V) (S : Finset V) (e : Finset V) (he : e ∈ H.boundary S) :
    H.w e ≤ H.w e / ((e.card : ℝ) - 1) * ((e ∩ S).card : ℝ) * ((e ∩ Sᶜ).card : ℝ) ∧
    H.w e / ((e.card : ℝ) - 1) * ((e ∩ S).card : ℝ) * ((e ∩ Sᶜ).card : ℝ) ≤
      (H.rank : ℝ) / 2 * H.w e := by
  obtain ⟨heE, hS, hSc⟩ := Finset.mem_filter.mp he
  have hw := H.w_nonneg e heE
  have hcard : (e ∩ S).card + (e ∩ Sᶜ).card = e.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext x; by_cases hx : x ∈ S <;> simp [hx]
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right disjoint_compl_right)
  have hrank : e.card ≤ H.rank := Finset.le_sup (f := Finset.card) heE
  obtain ⟨h1, h2⟩ := key (e ∩ S).card (e ∩ Sᶜ).card H.rank (Finset.card_pos.mpr hS)
    (Finset.card_pos.mpr hSc) (hcard ▸ hrank)
  have hc : (e.card : ℝ) = ((e ∩ S).card : ℝ) + ((e ∩ Sᶜ).card : ℝ) := by
    exact_mod_cast hcard.symm
  have eq : H.w e / ((e.card : ℝ) - 1) * ((e ∩ S).card : ℝ) * ((e ∩ Sᶜ).card : ℝ) =
      H.w e * (((e ∩ S).card : ℝ) * ((e ∩ Sᶜ).card : ℝ) /
        (((e ∩ S).card : ℝ) + ((e ∩ Sᶜ).card : ℝ) - 1)) := by
    rw [hc]; ring
  rw [eq]
  constructor
  · nlinarith
  · nlinarith

end HyperCheeger.Dev.Eq1

namespace HyperCheeger
open HyperCheeger.Dev.Eq1 in
theorem chk_eq_1 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) (S : Finset V)
    (hS : S.Nonempty) (hS' : S ≠ Finset.univ) :
    H.conductanceSet S ≤ H.diffusionConductanceSet S ∧
      H.diffusionConductanceSet S ≤ (H.rank : ℝ) / 2 * H.conductanceSet S := by
  have hm : 0 ≤ min (H.vol S) (H.vol Sᶜ) := le_min (vol_nonneg H S) (vol_nonneg H Sᶜ)
  unfold Hypergraph.conductanceSet Hypergraph.diffusionConductanceSet
  constructor
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun e he => (edge_bounds H S e he).1) hm
  · rw [← mul_div_assoc, Finset.mul_sum]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun e he => (edge_bounds H S e he).2) hm

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_eq_1 := @HyperCheeger.chk_eq_1
