-- Prove2me | solution 1 for HDXHitting.partite_vertex_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:52.833706+00:00
-- url     : https://prove2.me/submissions/0d69132b-c7a4-4edd-a8df-4ce8f14f9bef

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkDist
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly
import Theorems.Thm_HDXHitting_vertex_decomposition

section
set_option autoImplicit false
namespace HDXHitting.Dev.PVD
open HDXHitting

theorem link_update {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (v : V)
    (f : V → ℝ) (a : ℝ) :
    hit (linkDist p {v}) (Function.update f v a) = hit (linkDist p {v}) f := by
  unfold hit
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : v ∈ σ
  · have : ¬ Disjoint ({v} : Finset V) σ := by
      rw [Finset.disjoint_singleton_left]; exact not_not.mpr h
    unfold linkDist
    rw [if_neg this]
    simp
  · congr 1
    apply Finset.prod_congr rfl
    intro w hw
    rw [Function.update_of_ne (fun e => h (by rw [← e]; exact hw))]

theorem d_ne {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ) (v : V)
    (hv : 0 < vertexMeasure d p v) : (d : ℝ) ≠ 0 := by
  intro h
  unfold vertexMeasure at hv
  rw [h] at hv
  simp at hv

end HDXHitting.Dev.PVD
namespace HDXHitting
open HDXHitting.Dev.PVD in
theorem chk_partite_vertex_decomposition {V ι : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq ι] (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι)
    (S : Finset ι) (lam : ℝ) (v : V) (hv : 0 < vertexMeasure d p v) (f : V → ℝ) (h : ℝ)
    (hh : h = (d : ℝ) * vertexMeasure d p v * f v) :
    hit p f = hit p (Function.update f v 0) + h * hit (linkDist p {v}) f ∧
      colourMean p c (Function.update f v 0) = colourMean p c f - h • Pi.single (c v) 1 ∧
      (0 ≤ f v →
        hit p (Function.update f v 0) ≤ cPoly S lam (colourMean p c (Function.update f v 0)) →
        hit (linkDist p {v}) f ≤ cPoly (S.erase (c v)) lam (colourMean (linkDist p {v}) c f) →
        hit p f ≤ cPoly S lam (colourMean p c f - h • Pi.single (c v) 1) +
          h * cPoly (S.erase (c v)) lam (colourMean (linkDist p {v}) c f)) := by
  have hd := d_ne d p v hv
  have h1 : hit p f = hit p (Function.update f v 0) + h * hit (linkDist p {v}) f := by
    have := HDXHitting.vertex_decomposition d p hp v hv f (f v)
    rw [sub_self, link_update] at this
    rw [hh]
    rw [this]
    ring
  have h2 : colourMean p c (Function.update f v 0) = colourMean p c f - h • Pi.single (c v) 1 := by
    funext i
    have hP : (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ) =
        (d : ℝ) * vertexMeasure d p v := by
      unfold vertexMeasure
      field_simp
    unfold colourMean
    have e : ∀ w : V, (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => w ∈ σ), p σ) *
        Function.update f v 0 w =
        (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => w ∈ σ), p σ) * f w -
        (if w = v then (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ) * f v
          else 0) := by
      intro w
      by_cases hw : w = v
      · subst hw; simp
      · simp [hw, Function.update_of_ne hw]
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, Finset.mem_filter, Finset.mem_univ,
      true_and, smul_eq_mul]
    rw [hP, hh]
    by_cases hc : c v = i
    · simp [hc]
    · simp [hc, Ne.symm hc]
  refine ⟨h1, h2, ?_⟩
  intro hfv hA hB
  have hnn : 0 ≤ h := by
    rw [hh]
    have : 0 ≤ vertexMeasure d p v := hv.le
    positivity
  rw [h1, ← h2]
  gcongr
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_partite_vertex_decomposition := @HDXHitting.chk_partite_vertex_decomposition
