-- Prove2me | solution 1 for HDXHitting.vertex_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:52.442894+00:00
-- url     : https://prove2.me/submissions/902bfbca-1bef-49e1-9a2e-4600e4d56e2f

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkDist

section
set_option autoImplicit false
namespace HDXHitting.Dev.VD
open HDXHitting

theorem prod_split {V : Type*} [DecidableEq V] (f : V → ℝ) (v : V) (ε : ℝ) (σ : Finset V) :
    ∏ w ∈ σ, f w = ∏ w ∈ σ, Function.update f v (f v - ε) w +
      (if v ∈ σ then ε * ∏ w ∈ σ.erase v, Function.update f v (f v - ε) w else 0) := by
  have hE : ∏ w ∈ σ.erase v, Function.update f v (f v - ε) w = ∏ w ∈ σ.erase v, f w := by
    apply Finset.prod_congr rfl
    intro w hw
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  by_cases h : v ∈ σ
  · rw [if_pos h, ← Finset.mul_prod_erase σ f h,
      ← Finset.mul_prod_erase σ (Function.update f v (f v - ε)) h, hE]
    simp only [Function.update_self]
    ring
  · rw [if_neg h, add_zero]
    apply Finset.prod_congr rfl
    intro w hw
    rw [Function.update_of_ne (fun e => h (by rw [← e]; exact hw))]

theorem link_hit {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (v : V) (g : V → ℝ) :
    hit (linkDist p {v}) g =
      (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ * ∏ w ∈ σ.erase v, g w) /
        ∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => {v} ⊆ σ'), p σ' := by
  unfold hit linkDist
  rw [Finset.sum_div]
  have h1 : ∀ σ : Finset V, (if Disjoint ({v} : Finset V) σ then
        p ({v} ∪ σ) / ∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => {v} ⊆ σ'), p σ' else 0) *
        ∏ w ∈ σ, g w =
      if v ∉ σ then (p (insert v σ) * ∏ w ∈ (insert v σ).erase v, g w) /
        ∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => {v} ⊆ σ'), p σ' else 0 := by
    intro σ
    by_cases h : v ∈ σ
    · simp [h]
    · simp [h, Finset.erase_eq_of_notMem h, Finset.disjoint_singleton_left,
        div_mul_eq_mul_div, Finset.singleton_union]
  simp_rw [h1]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun σ => σ.erase v) (fun σ => insert v σ)
  · intro σ hσ; simp at hσ ⊢
  · intro σ hσ; simp at hσ ⊢
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact Finset.insert_erase hσ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact Finset.erase_insert hσ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [Finset.insert_erase hσ]

end HDXHitting.Dev.VD
namespace HDXHitting
open HDXHitting.Dev.VD in
theorem chk_vertex_decomposition {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (v : V) (hv : 0 < vertexMeasure d p v)
    (f : V → ℝ) (ε : ℝ) :
    hit p f = hit p (Function.update f v (f v - ε)) +
      (d : ℝ) * ε * vertexMeasure d p v * hit (linkDist p {v}) (Function.update f v (f v - ε)) := by
  have hd : (d : ℝ) ≠ 0 := by
    intro h
    unfold vertexMeasure at hv
    rw [h] at hv
    simp at hv
  have hP : (∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => {v} ⊆ σ'), p σ') =
      (d : ℝ) * vertexMeasure d p v := by
    unfold vertexMeasure
    field_simp
    simp [Finset.singleton_subset_iff]
  have hP0 : (∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => {v} ⊆ σ'), p σ') ≠ 0 := by
    rw [hP]; exact (mul_pos (by positivity) hv).ne'
  rw [link_hit, hP]
  rw [hP] at hP0
  have e1 : (d : ℝ) * ε * vertexMeasure d p v *
      ((∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ),
          p σ * ∏ w ∈ σ.erase v, Function.update f v (f v - ε) w) / (↑d * vertexMeasure d p v)) =
      ε * ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ),
          p σ * ∏ w ∈ σ.erase v, Function.update f v (f v - ε) w := by
    field_simp
  rw [e1]
  unfold hit
  have : ∀ σ : Finset V, p σ * ∏ w ∈ σ, f w = p σ * ∏ w ∈ σ, Function.update f v (f v - ε) w +
      ε * (if v ∈ σ then p σ * ∏ w ∈ σ.erase v, Function.update f v (f v - ε) w else 0) := by
    intro σ
    rw [prod_split f v ε σ]
    split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_vertex_decomposition := @HDXHitting.chk_vertex_decomposition
