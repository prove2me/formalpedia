-- Prove2me | solution 1 for HyperCheeger.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:07:05.466748+00:00
-- url     : https://prove2.me/submissions/2ae9207c-6ce5-4bab-ad00-83c6ac9b2162

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_conductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Theorems.Thm_HyperCheeger_eq_7

section
set_option autoImplicit false

namespace HyperCheeger.Dev.SweepAux

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable section

/-- The weight of the edges leaving `S`. -/
def cut (a : V → V → ℝ) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, a u v

/-- The volume of `S`. -/
def vol (a : V → V → ℝ) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v, a u v

/-- The `0/1` indicator of `S`. -/
def ind (S : Finset V) (u : V) : ℝ := if u ∈ S then 1 else 0

/-- `D(f) = ∑_u d(u) f(u)`. -/
def dsum (a : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ u, (∑ v, a u v) * f u

/-- `X(f) = ½ ∑_{u,v} a(u,v) |f u − f v|`. -/
def xsum (a : V → V → ℝ) (f : V → ℝ) : ℝ := (1 / 2 : ℝ) * ∑ u, ∑ v, a u v * |f u - f v|

lemma vol_eq (a : V → V → ℝ) (S : Finset V) :
    ∑ u, (∑ v, a u v) * ind S u = vol a S := by
  unfold vol ind
  simp [mul_ite, Finset.sum_ite_mem]

lemma cut_eq_one (a : V → V → ℝ) (S : Finset V) :
    ∑ u, ∑ v, a u v * (ind S u * (1 - ind S v)) = cut a S := by
  unfold cut
  have h : ∀ u, ∑ v, a u v * (ind S u * (1 - ind S v)) =
      if u ∈ S then ∑ v ∈ Sᶜ, a u v else 0 := by
    intro u
    by_cases hu : u ∈ S
    · rw [if_pos hu, ← Fintype.sum_ite_mem Sᶜ]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      by_cases hv : v ∈ S <;> simp [ind, hu, hv]
    · simp [ind, hu]
  rw [Finset.sum_congr rfl (fun u _ => h u), Fintype.sum_ite_mem]

lemma cut_eq_two (a : V → V → ℝ) (hsymm : ∀ u v, a u v = a v u) (S : Finset V) :
    ∑ u, ∑ v, a u v * (ind S u * (1 - ind S v) + ind S v * (1 - ind S u)) = 2 * cut a S := by
  have h2 : ∑ u, ∑ v, a u v * (ind S v * (1 - ind S u)) = cut a S := by
    rw [Finset.sum_comm, ← cut_eq_one a S]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [hsymm]
  simp only [mul_add, Finset.sum_add_distrib, cut_eq_one, h2]
  ring

omit [Fintype V] in
/-- Pointwise splitting of `|f u - f v|` along the bottom level `m` of `f`. -/
lemma decomp_abs (f f' : V → ℝ) (S : Finset V) (m : ℝ) (hf : ∀ u, 0 ≤ f u) (hm0 : 0 < m)
    (hm : ∀ u, 0 < f u → m ≤ f u) (hS : ∀ u, u ∈ S ↔ 0 < f u)
    (hf' : ∀ u, f' u = max (f u - m) 0) (u v : V) :
    |f u - f v| = |f' u - f' v| +
      m * (ind S u * (1 - ind S v) + ind S v * (1 - ind S u)) := by
  have key : ∀ w, (w ∈ S ∧ f' w = f w - m ∧ m ≤ f w) ∨ (w ∉ S ∧ f w = 0 ∧ f' w = 0) := by
    intro w
    by_cases h : 0 < f w
    · exact Or.inl ⟨(hS w).2 h, by rw [hf']; exact max_eq_left (sub_nonneg.2 (hm w h)), hm w h⟩
    · have h0 : f w = 0 := le_antisymm (not_lt.1 h) (hf w)
      refine Or.inr ⟨fun hw => h ((hS w).1 hw), h0, ?_⟩
      rw [hf', h0]; exact max_eq_right (by linarith)
  rcases key u with ⟨hu, hu1, hu2⟩ | ⟨hu, hu1, hu2⟩ <;>
  rcases key v with ⟨hv, hv1, hv2⟩ | ⟨hv, hv1, hv2⟩ <;>
  simp only [ind, hu, hv, if_true, if_false, hu1, hu2, hv1, hv2]
  · rw [show f u - m - (f v - m) = f u - f v by ring]; ring
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
  · simp

lemma dsum_decomp (a : V → V → ℝ) (f f' : V → ℝ) (S : Finset V) (m : ℝ) (hf : ∀ u, 0 ≤ f u)
    (hm0 : 0 < m) (hm : ∀ u, 0 < f u → m ≤ f u) (hS : ∀ u, u ∈ S ↔ 0 < f u)
    (hf' : ∀ u, f' u = max (f u - m) 0) :
    dsum a f = dsum a f' + m * vol a S := by
  rw [← vol_eq, dsum, dsum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hpt : f u = f' u + m * ind S u := by
    by_cases h : 0 < f u
    · rw [hf', max_eq_left (sub_nonneg.2 (hm u h)), ind, if_pos ((hS u).2 h)]; ring
    · have h0 : f u = 0 := le_antisymm (not_lt.1 h) (hf u)
      rw [hf', ind, if_neg (fun hu => h ((hS u).1 hu)), h0, max_eq_right (by linarith)]; ring
  linear_combination (∑ v, a u v) * hpt

lemma xsum_decomp (a : V → V → ℝ) (hsymm : ∀ u v, a u v = a v u) (f f' : V → ℝ) (S : Finset V)
    (m : ℝ) (hf : ∀ u, 0 ≤ f u)
    (hm0 : 0 < m) (hm : ∀ u, 0 < f u → m ≤ f u) (hS : ∀ u, u ∈ S ↔ 0 < f u)
    (hf' : ∀ u, f' u = max (f u - m) 0) :
    xsum a f = xsum a f' + m * cut a S := by
  have h : ∑ u, ∑ v, a u v * |f u - f v| = ∑ u, ∑ v, (a u v * |f' u - f' v| +
      m * (a u v * (ind S u * (1 - ind S v) + ind S v * (1 - ind S u)))) := by
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    linear_combination a u v * decomp_abs f f' S m hf hm0 hm hS hf' u v
  rw [xsum, xsum, h]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [cut_eq_two a hsymm S]
  ring

/-- The discrete co-area inequality, by induction on the size of the support: if every
positive level set `{c ≤ f}` beats ratio `φ`, then `φ D(f) < X(f)` unless `f = 0`. -/
lemma key (a : V → V → ℝ) (hsymm : ∀ u v, a u v = a v u) (φ : ℝ) (n : ℕ) :
    ∀ f : V → ℝ, (∀ u, 0 ≤ f u) →
      (univ.filter (fun u => 0 < f u)).card ≤ n →
      (∀ c : ℝ, 0 < c → (univ.filter (fun u => c ≤ f u)).Nonempty →
        φ * vol a (univ.filter (fun u => c ≤ f u)) < cut a (univ.filter (fun u => c ≤ f u))) →
      φ * dsum a f < xsum a f ∨ ∀ u, f u = 0 := by
  induction n with
  | zero =>
    intro f hf hcard _
    right; intro u
    have hE : univ.filter (fun u => 0 < f u) = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    have hu : ¬ 0 < f u := by
      intro h
      have hmem : u ∈ univ.filter (fun u => 0 < f u) := by simp [h]
      rw [hE] at hmem
      simp at hmem
    exact le_antisymm (not_lt.1 hu) (hf u)
  | succ n ih =>
    intro f hf hcard hcut
    by_cases h0 : ∀ u, f u = 0
    · exact Or.inr h0
    left
    push Not at h0
    obtain ⟨u0, hu0⟩ := h0
    have hpos0 : 0 < f u0 := lt_of_le_of_ne (hf u0) (Ne.symm hu0)
    obtain ⟨S, hSdef⟩ : ∃ S : Finset V, S = univ.filter (fun u => 0 < f u) := ⟨_, rfl⟩
    have hS : ∀ u, u ∈ S ↔ 0 < f u := by intro u; simp [hSdef]
    have hSne : S.Nonempty := ⟨u0, (hS u0).2 hpos0⟩
    obtain ⟨w, hwS, hwmin⟩ := S.exists_min_image f hSne
    have hwpos : 0 < f w := (hS w).1 hwS
    have hm : ∀ u, 0 < f u → f w ≤ f u := fun u hu => hwmin u ((hS u).2 hu)
    obtain ⟨f', hf'⟩ : ∃ f' : V → ℝ, ∀ u, f' u = max (f u - f w) 0 := ⟨_, fun _ => rfl⟩
    have hf'nn : ∀ u, 0 ≤ f' u := fun u => by rw [hf']; exact le_max_right _ _
    have hsub : univ.filter (fun u => 0 < f' u) ⊂ S := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨w, hwS, ?_⟩
        simp [hf']
      · intro u hu
        rw [hS]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf'] at hu
        rcases lt_max_iff.1 hu with h | h
        · linarith
        · exact absurd h (lt_irrefl 0)
    have hcard' : (univ.filter (fun u => 0 < f' u)).card ≤ n := by
      have h1 := Finset.card_lt_card hsub
      rw [hSdef] at h1
      omega
    have hlev : ∀ c : ℝ, 0 < c →
        univ.filter (fun u => c ≤ f' u) = univ.filter (fun u => c + f w ≤ f u) := by
      intro c hc; ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf', le_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h; left; linarith
    have hcut' : ∀ c : ℝ, 0 < c → (univ.filter (fun u => c ≤ f' u)).Nonempty →
        φ * vol a (univ.filter (fun u => c ≤ f' u)) < cut a (univ.filter (fun u => c ≤ f' u)) := by
      intro c hc hne
      rw [hlev c hc] at hne ⊢
      exact hcut (c + f w) (by linarith) hne
    have hSlev : univ.filter (fun u => f w ≤ f u) = S := by
      ext u
      rw [hS]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; linarith
      · exact hm u
    have hcutS : φ * vol a S < cut a S := by
      have h1 := hcut (f w) hwpos (hSlev ▸ hSne)
      rwa [hSlev] at h1
    have hrec : φ * dsum a f' ≤ xsum a f' := by
      rcases ih f' hf'nn hcard' hcut' with h | h
      · exact h.le
      · have h1 : dsum a f' = 0 := by simp [dsum, h]
        have h2 : xsum a f' = 0 := by simp [xsum, h]
        rw [h1, h2]; simp
    rw [dsum_decomp a f f' S (f w) hf hwpos hm hS hf',
      xsum_decomp a hsymm f f' S (f w) hf hwpos hm hS hf']
    have h3 := mul_lt_mul_of_pos_left hcutS hwpos
    nlinarith

lemma sqrt_div_mul (P D : ℝ) (hP : 0 ≤ P) (hD : 0 < D) :
    Real.sqrt (2 * ((1 / 2 : ℝ) * P) / D) * D = Real.sqrt (P * D) := by
  have h : P * D = 2 * ((1 / 2 : ℝ) * P) / D * D ^ 2 := by
    rw [div_mul_eq_mul_div, eq_div_iff hD.ne']; ring
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hD.le]

omit [DecidableEq V] in
/-- Cauchy–Schwarz over ordered pairs. -/
lemma cs (a : V → V → ℝ) (ha : ∀ u v, 0 ≤ a u v) (g : V → ℝ) :
    (∑ u, ∑ v, a u v * |g u ^ 2 - g v ^ 2|) ^ 2 ≤
      (∑ u, ∑ v, a u v * (g u - g v) ^ 2) * ∑ u, ∑ v, a u v * (g u + g v) ^ 2 := by
  simp only [← Fintype.sum_prod_type']
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => ?_) (fun p _ => ?_)
    (fun p _ => ?_)
  · exact mul_nonneg (ha _ _) (sq_nonneg _)
  · exact mul_nonneg (ha _ _) (sq_nonneg _)
  · rw [mul_pow, sq_abs]
    apply le_of_eq
    ring

omit [DecidableEq V] in
lemma sum_plus_le (a : V → V → ℝ) (ha : ∀ u v, 0 ≤ a u v) (hsymm : ∀ u v, a u v = a v u)
    (g : V → ℝ) :
    ∑ u, ∑ v, a u v * (g u + g v) ^ 2 ≤ 4 * ∑ u, (∑ v, a u v) * g u ^ 2 := by
  have h0 : ∑ u, ∑ v, a u v * g u ^ 2 = ∑ u, (∑ v, a u v) * g u ^ 2 := by
    simp [Finset.sum_mul]
  have h1 : ∑ u, ∑ v, a u v * g v ^ 2 = ∑ u, (∑ v, a u v) * g u ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [hsymm]
  calc ∑ u, ∑ v, a u v * (g u + g v) ^ 2
      ≤ ∑ u, ∑ v, (2 * (a u v * g u ^ 2) + 2 * (a u v * g v ^ 2)) := by
        refine Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => ?_))
        nlinarith [mul_nonneg (ha u v) (sq_nonneg (g u - g v))]
    _ = 4 * ∑ u, (∑ v, a u v) * g u ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1]
        ring

end

end HyperCheeger.Dev.SweepAux

namespace HyperCheeger.Dev

open HyperCheeger.Dev.SweepAux in
/-- The sweep (level-set) lemma behind the upper Cheeger bound: for a nonnegative `g` on the
vertices of a graph with symmetric nonnegative pair weights `a`, some level set `S` of `g`
inside the support of `g` has `cut(S) ≤ √(2 Q(g) / D(g)) · vol(S)`, where
`Q(g) = ½ ∑_{u,v} a(u,v) (g u − g v)²` and `D(g) = ∑_u d(u) g(u)²`, `d(u) = ∑_v a(u,v)`. -/
theorem sweep {V : Type} [Fintype V] [DecidableEq V] (a : V → V → ℝ)
    (ha : ∀ u v, 0 ≤ a u v) (hsymm : ∀ u v, a u v = a v u)
    (g : V → ℝ) (hg : ∀ u, 0 ≤ g u)
    (hD : 0 < ∑ u, (∑ v, a u v) * g u ^ 2) :
    ∃ S : Finset V, S.Nonempty ∧ (∀ u ∈ S, 0 < g u) ∧
      (∑ u ∈ S, ∑ v ∈ Sᶜ, a u v) ≤
        Real.sqrt (2 * ((1 / 2 : ℝ) * ∑ u, ∑ v, a u v * (g u - g v) ^ 2) /
            ∑ u, (∑ v, a u v) * g u ^ 2) *
          ∑ u ∈ S, ∑ v, a u v := by
  by_contra hcon
  push Not at hcon
  have hk := key a hsymm (Real.sqrt (2 * ((1 / 2 : ℝ) * ∑ u, ∑ v, a u v * (g u - g v) ^ 2) /
            ∑ u, (∑ v, a u v) * g u ^ 2)) (Fintype.card V) (fun u => g u ^ 2)
    (fun u => sq_nonneg _) (Finset.card_le_univ _) (by
      intro c hc hne
      refine hcon _ hne (fun u hu => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine lt_of_le_of_ne (hg u) (fun h => ?_)
      rw [← h] at hu
      linarith [show (0 : ℝ) ^ 2 = 0 by norm_num])
  rcases hk with hk | hk
  · -- Cauchy–Schwarz bound contradicts the strict co-area inequality
    simp only [dsum, xsum] at hk
    have hPnn : 0 ≤ ∑ u, ∑ v, a u v * (g u - g v) ^ 2 :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (ha u v) (sq_nonneg _)
    have hYnn : 0 ≤ ∑ u, ∑ v, a u v * |g u ^ 2 - g v ^ 2| :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (ha u v) (abs_nonneg _)
    have hcs := cs a ha g
    have hE := sum_plus_le a ha hsymm g
    have hsq := sqrt_div_mul _ _ hPnn hD
    rw [hsq] at hk
    have hle : (1 / 2 : ℝ) * ∑ u, ∑ v, a u v * |g u ^ 2 - g v ^ 2| ≤
        Real.sqrt ((∑ u, ∑ v, a u v * (g u - g v) ^ 2) * ∑ u, (∑ v, a u v) * g u ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [mul_le_mul_of_nonneg_left hE hPnn]
    linarith
  · have : ∑ u, (∑ v, a u v) * g u ^ 2 = 0 := by simp [hk]
    linarith

end HyperCheeger.Dev
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

namespace HyperCheeger.Dev.Thm31

open HyperCheeger HyperCheeger.Hypergraph

variable {V : Type} [Fintype V] [DecidableEq V]

theorem degree_nonneg (G : Hypergraph V) (u : V) : 0 ≤ G.degree u := by
  unfold Hypergraph.degree
  exact Finset.sum_nonneg fun e he => G.w_nonneg e (Finset.mem_filter.mp he).1

theorem vol_nonneg (G : Hypergraph V) (S : Finset V) : 0 ≤ G.vol S :=
  Finset.sum_nonneg fun u _ => degree_nonneg G u

/-- For a 2-graph the adjacency entry is the weight of the edge `{u,v}`, written as a sum. -/
theorem adj_two (G : Hypergraph V) (hG : G.IsTwoGraph) (u v : V) :
    G.adj u v = ∑ e ∈ G.edges, if (u ≠ v ∧ u ∈ e ∧ v ∈ e) then G.w e else 0 := by
  unfold Hypergraph.adj
  rw [Matrix.of_apply]
  by_cases huv : u = v
  · simp [huv]
  · rw [if_neg huv, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    have hc : ((e.card : ℝ) - 1) = 1 := by rw [hG e he]; norm_num
    rw [hc, div_one]
    have : ({u, v} : Finset V) ⊆ e ↔ (u ≠ v ∧ u ∈ e ∧ v ∈ e) := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      tauto
    simp only [this]

theorem adj_nonneg (G : Hypergraph V) (hG : G.IsTwoGraph) (u v : V) : 0 ≤ G.adj u v := by
  rw [adj_two G hG]
  refine Finset.sum_nonneg fun e he => ?_
  split_ifs
  · exact G.w_nonneg e he
  · exact le_rfl

theorem adj_symm (G : Hypergraph V) (u v : V) : G.adj u v = G.adj v u := by
  unfold Hypergraph.adj
  simp only [Matrix.of_apply]
  by_cases huv : u = v
  · subst huv; rfl
  · rw [if_neg huv, if_neg (Ne.symm huv), Finset.pair_comm]

theorem sum_adj (G : Hypergraph V) (hG : G.IsTwoGraph) (u : V) :
    ∑ v, G.adj u v = G.degree u := by
  simp_rw [adj_two G hG]
  rw [Finset.sum_comm]
  unfold Hypergraph.degree
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  by_cases hu : u ∈ e
  · rw [if_pos hu, ← Finset.sum_filter]
    have hf : (Finset.univ.filter fun v => u ≠ v ∧ u ∈ e ∧ v ∈ e) = e.erase u := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [hf, Finset.sum_const, Finset.card_erase_of_mem hu, hG e he]
    simp
  · rw [if_neg hu]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg]
    tauto

/-- The boundary weight of `S` is the cut `∑_{u ∈ S} ∑_{v ∉ S} a u v`. -/
theorem boundary_eq_cut (G : Hypergraph V) (hG : G.IsTwoGraph) (S : Finset V) :
    ∑ e ∈ G.boundary S, G.w e = ∑ u ∈ S, ∑ v ∈ Sᶜ, G.adj u v := by
  simp_rw [adj_two G hG]
  have h1 : ∀ u ∈ S, ∀ v ∈ Sᶜ, ∀ e ∈ G.edges,
      (if (u ≠ v ∧ u ∈ e ∧ v ∈ e) then G.w e else 0) =
        G.w e * ((if u ∈ e then (1 : ℝ) else 0) * (if v ∈ e then (1 : ℝ) else 0)) := by
    intro u hu v hv e _
    have huv : u ≠ v := by
      rintro rfl
      exact (Finset.mem_compl.mp hv) hu
    by_cases hue : u ∈ e <;> by_cases hve : v ∈ e <;> simp [hue, hve, huv]
  rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv =>
    Finset.sum_congr rfl (h1 u hu v hv)]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  unfold Hypergraph.boundary
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [show (∑ x ∈ S, ∑ y ∈ Sᶜ, G.w e * ((if x ∈ e then (1:ℝ) else 0) * if y ∈ e then 1 else 0)) =
      G.w e * ((∑ x ∈ S, if x ∈ e then (1:ℝ) else 0) * ∑ y ∈ Sᶜ, if y ∈ e then (1:ℝ) else 0) by
    rw [Finset.sum_mul_sum, Finset.mul_sum]; simp_rw [Finset.mul_sum]]
  rw [Finset.sum_boole, Finset.sum_boole]
  rw [Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm S,
    Finset.inter_comm Sᶜ]
  have hsum : (e ∩ S).card + (e ∩ Sᶜ).card = 2 := by
    rw [← hG e he, ← Finset.card_union_of_disjoint]
    · rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    · exact Finset.disjoint_left.mpr fun x hx hx' =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hx').2) (Finset.mem_inter.mp hx).2
  simp only [← Finset.card_pos]
  set p := (e ∩ S).card
  set q := (e ∩ Sᶜ).card
  have hq : q = 2 - p := by omega
  have hp : p ≤ 2 := by omega
  interval_cases p <;> simp [hq]


theorem quad_deg (G : Hypergraph V) (x : V → ℝ) :
    x ⬝ᵥ (G.degMat *ᵥ x) = ∑ u, G.degree u * x u ^ 2 := by
  unfold Hypergraph.degMat
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun u _ => by ring

theorem quad_lap (G : Hypergraph V) (hG : G.IsTwoGraph) (x : V → ℝ) :
    x ⬝ᵥ (G.lap *ᵥ x) = 1 / 2 * ∑ u, ∑ v, G.adj u v * (x u - x v) ^ 2 := by
  have e1 : ∑ u, ∑ v, G.adj u v * (x u - x v) ^ 2 =
      ∑ u, ∑ v, G.adj u v * x u ^ 2 + ∑ u, ∑ v, G.adj u v * x v ^ 2 -
        2 * ∑ u, ∑ v, G.adj u v * x u * x v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e2 : ∑ u, ∑ v, G.adj u v * x u ^ 2 = ∑ u, G.degree u * x u ^ 2 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul, sum_adj G hG]
  have e3 : ∑ u, ∑ v, G.adj u v * x v ^ 2 = ∑ u, G.degree u * x u ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← sum_adj G hG v, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [adj_symm]
  have e4 : x ⬝ᵥ (G.adj *ᵥ x) = ∑ u, ∑ v, G.adj u v * x u * x v := by
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e5 : x ⬝ᵥ (G.degMat *ᵥ x) = ∑ u, G.degree u * x u ^ 2 := quad_deg G x
  unfold Hypergraph.lap
  rw [Matrix.sub_mulVec, dotProduct_sub, e4, e5, e1, e2, e3]
  ring

/-- The cut computation for a two-valued vector. -/
theorem two_valued (G : Hypergraph V) (S : Finset V) (p q : ℝ) :
    ∑ u, ∑ v, G.adj u v * ((if u ∈ S then p else q) - (if v ∈ S then p else q)) ^ 2 =
      2 * (p - q) ^ 2 * ∑ u ∈ S, ∑ v ∈ Sᶜ, G.adj u v := by
  have hS : ∀ u ∈ S, ∑ v, G.adj u v * ((if u ∈ S then p else q) - (if v ∈ S then p else q)) ^ 2
      = (p - q) ^ 2 * ∑ v ∈ Sᶜ, G.adj u v := by
    intro u hu
    rw [← Finset.sum_add_sum_compl S, Finset.mul_sum]
    rw [Finset.sum_eq_zero (fun v hv => by simp [hu, hv]), zero_add]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.mem_compl] at hv
    simp only [hu, hv, if_true, if_false]
    ring
  have hSc : ∀ u ∈ Sᶜ, ∑ v, G.adj u v * ((if u ∈ S then p else q) - (if v ∈ S then p else q)) ^ 2
      = (p - q) ^ 2 * ∑ v ∈ S, G.adj v u := by
    intro u hu
    rw [Finset.mem_compl] at hu
    rw [← Finset.sum_add_sum_compl S, Finset.mul_sum]
    rw [Finset.sum_eq_zero (s := Sᶜ) (fun v hv => by
      rw [Finset.mem_compl] at hv; simp [hu, hv]), add_zero]
    refine Finset.sum_congr rfl fun v hv => ?_
    simp only [hu, hv, if_true, if_false]
    rw [adj_symm]
    ring
  rw [← Finset.sum_add_sum_compl S, Finset.sum_congr rfl hS, Finset.sum_congr rfl hSc,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm (s := Sᶜ)]
  ring

/-- A weighted median. -/
theorem median (d y : V → ℝ) (hd : ∀ u, 0 ≤ d u) [Nonempty V] :
    ∃ c : ℝ, ∑ u ∈ Finset.univ.filter (fun u => y u < c), d u ≤ (∑ u, d u) / 2 ∧
      ∑ u ∈ Finset.univ.filter (fun u => c < y u), d u ≤ (∑ u, d u) / 2 := by
  have hW : 0 ≤ ∑ u, d u := Finset.sum_nonneg fun u _ => hd u
  set T := Finset.univ.filter
    (fun v => (∑ u, d u) / 2 ≤ ∑ u ∈ Finset.univ.filter (fun u => y u ≤ y v), d u) with hTdef
  have hT : T.Nonempty := by
    obtain ⟨vm, -, hvm⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
    refine ⟨vm, ?_⟩
    rw [hTdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.filter_true_of_mem fun u _ => hvm u (Finset.mem_univ u)]
    linarith
  obtain ⟨v0, hv0T, hmin⟩ := Finset.exists_min_image T y hT
  refine ⟨y v0, ?_, ?_⟩
  · by_cases hne : (Finset.univ.filter (fun u => y u < y v0)).Nonempty
    · obtain ⟨v1, hv1, hmax⟩ := Finset.exists_max_image _ y hne
      have hv1' : y v1 < y v0 := (Finset.mem_filter.mp hv1).2
      have heq : Finset.univ.filter (fun u => y u < y v0) =
          Finset.univ.filter (fun u => y u ≤ y v1) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact hmax u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · intro h
          linarith
      have hv1T : v1 ∉ T := fun h => by linarith [hmin v1 h]
      rw [hTdef, Finset.mem_filter] at hv1T
      rw [heq]
      simp only [Finset.mem_univ, true_and, not_le] at hv1T
      exact hv1T.le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      linarith
  · have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => y u ≤ y v0) d
    simp only [not_le] at h1
    have h2 := (Finset.mem_filter.mp hv0T).2
    linarith

theorem Q_nonneg (G : Hypergraph V) (hG : G.IsTwoGraph) (x : V → ℝ) :
    0 ≤ 1 / 2 * ∑ u, ∑ v, G.adj u v * (x u - x v) ^ 2 :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
    mul_nonneg (adj_nonneg G hG u v) (sq_nonneg _))

theorem D_nonneg (G : Hypergraph V) (x : V → ℝ) : 0 ≤ ∑ u, G.degree u * x u ^ 2 :=
  Finset.sum_nonneg fun u _ => mul_nonneg (degree_nonneg G u) (sq_nonneg _)

theorem conductanceSet_nonneg (G : Hypergraph V) (S : Finset V) : 0 ≤ G.conductanceSet S := by
  unfold Hypergraph.conductanceSet
  refine div_nonneg (Finset.sum_nonneg fun e he => G.w_nonneg e (Finset.mem_filter.mp he).1) ?_
  exact le_min (vol_nonneg G S) (vol_nonneg G Sᶜ)

theorem conductance_le (G : Hypergraph V) {S : Finset V} (h1 : S.Nonempty)
    (h2 : S ≠ Finset.univ) {r : ℝ} (h : G.conductanceSet S ≤ r) : G.conductance ≤ r :=
  (ciInf_le (Set.finite_range _).bddBelow (⟨S, h1, h2⟩ :
    {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ})).trans h


/-- A zero-degree vertex forces `ν₂ ≤ 0`. -/
theorem nu2_nonpos (hV : 2 ≤ Fintype.card V) (G : Hypergraph V) (u : V)
    (hu : G.degree u = 0) : G.nu2 ≤ 0 := by
  have hlb := (HyperCheeger.eq_7 hV G).2.2.2
  set y : V → ℝ := fun v => if v = u then 1 else 0 with hy
  have hy0 : y ≠ 0 := fun h => by
    have := congrFun h u
    simp [hy] at this
  have hyd : y ⬝ᵥ G.degree = 0 := by
    simp [dotProduct, hy, hu]
  have hD : y ⬝ᵥ (G.degMat *ᵥ y) = 0 := by
    rw [quad_deg]
    simp [hy, hu]
  exact hlb ⟨y, hy0, hyd, by rw [hD, div_zero]⟩

theorem lower_set (hV : 2 ≤ Fintype.card V) (G : Hypergraph V) (hG : G.IsTwoGraph)
    (S : Finset V) (hS1 : S.Nonempty) (hS2 : S ≠ Finset.univ) :
    G.nu2 / 2 ≤ G.conductanceSet S := by
  by_cases hz : ∃ u, G.degree u = 0
  · obtain ⟨u, hu⟩ := hz
    have := nu2_nonpos hV G u hu
    have := conductanceSet_nonneg G S
    linarith
  push Not at hz
  have hpos : ∀ u, 0 < G.degree u := fun u => (degree_nonneg G u).lt_of_ne (hz u).symm
  have hSc : Sᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
    exact hS2
  set A := G.vol S with hA
  set B := G.vol Sᶜ with hB
  have hApos : 0 < A := Finset.sum_pos (fun u _ => hpos u) hS1
  have hBpos : 0 < B := Finset.sum_pos (fun u _ => hpos u) hSc
  set c := ∑ u ∈ S, ∑ v ∈ Sᶜ, G.adj u v with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => adj_nonneg G hG u v
  set y : V → ℝ := fun u => if u ∈ S then B else -A with hy
  have hy0 : y ≠ 0 := fun h => by
    obtain ⟨u, hu⟩ := hS1
    have := congrFun h u
    simp only [hy, hu, if_true, Pi.zero_apply] at this
    linarith
  have hyd : y ⬝ᵥ G.degree = 0 := by
    simp only [dotProduct]
    rw [← Finset.sum_add_sum_compl S]
    have h1 : ∑ u ∈ S, y u * G.degree u = B * A := by
      rw [hA, Hypergraph.vol, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u hu => by simp [hy, hu]
    have h2 : ∑ u ∈ Sᶜ, y u * G.degree u = -(A * B) := by
      rw [hB, Hypergraph.vol, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_compl] at hu
      simp [hy, hu]
    rw [h1, h2]
    ring
  have hQ : y ⬝ᵥ (G.lap *ᵥ y) = (A + B) ^ 2 * c := by
    rw [quad_lap G hG, hy, two_valued]
    ring
  have hDy : y ⬝ᵥ (G.degMat *ᵥ y) = A * B ^ 2 + B * A ^ 2 := by
    rw [quad_deg, ← Finset.sum_add_sum_compl S]
    have h1 : ∑ u ∈ S, G.degree u * y u ^ 2 = A * B ^ 2 := by
      rw [hA, Hypergraph.vol, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u hu => by simp [hy, hu]
    have h2 : ∑ u ∈ Sᶜ, G.degree u * y u ^ 2 = B * A ^ 2 := by
      rw [hB, Hypergraph.vol, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_compl] at hu
      simp [hy, hu]
    rw [h1, h2]
  have hle : G.nu2 ≤ (A + B) ^ 2 * c / (A * B ^ 2 + B * A ^ 2) :=
    (HyperCheeger.eq_7 hV G).2.2.2 ⟨y, hy0, hyd, by rw [hQ, hDy]⟩
  have hcs : G.conductanceSet S = c / min A B := by
    unfold Hypergraph.conductanceSet
    rw [boundary_eq_cut G hG]
  rw [hcs]
  have hmin : 0 < min A B := lt_min hApos hBpos
  have key : (A + B) ^ 2 * c / (A * B ^ 2 + B * A ^ 2) ≤ 2 * c / min A B := by
    rw [div_le_div_iff₀ (by positivity) hmin]
    rcases le_total A B with hAB | hAB
    · rw [min_eq_left hAB]
      have := mul_nonneg (mul_nonneg (mul_nonneg hc0 hApos.le) (add_pos hApos hBpos).le)
        (sub_nonneg.mpr hAB)
      nlinarith [this]
    · rw [min_eq_right hAB]
      have := mul_nonneg (mul_nonneg (mul_nonneg hc0 hBpos.le) (add_pos hApos hBpos).le)
        (sub_nonneg.mpr hAB)
      nlinarith [this]
  have : 2 * c / min A B = 2 * (c / min A B) := by ring
  linarith


/-- The final sweep step: a nonnegative test vector with small support and small Rayleigh
quotient yields a set of small conductance. -/
theorem upper_from_g (G : Hypergraph V) (hG : G.IsTwoGraph) (hpos : ∀ u, 0 < G.degree u)
    (ν : ℝ) (g : V → ℝ) (hg : ∀ u, 0 ≤ g u) (hD : 0 < ∑ u, G.degree u * g u ^ 2)
    (hQ : 1 / 2 * ∑ u, ∑ v, G.adj u v * (g u - g v) ^ 2 ≤ ν * ∑ u, G.degree u * g u ^ 2)
    (P : Finset V) (hP : ∀ u, 0 < g u → u ∈ P)
    (hPvol : ∑ u ∈ P, G.degree u ≤ (∑ u, G.degree u) / 2) :
    ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧ G.conductanceSet S ≤ Real.sqrt (2 * ν) := by
  have hD' : 0 < ∑ u, (∑ v, G.adj u v) * g u ^ 2 := by simp_rw [sum_adj G hG]; exact hD
  obtain ⟨S, hSne, hSpos, hcut⟩ := HyperCheeger.Dev.sweep (fun u v => G.adj u v)
    (adj_nonneg G hG) (adj_symm G) g hg hD'
  simp only [sum_adj G hG] at hcut
  set Q := 1 / 2 * ∑ u, ∑ v, G.adj u v * (g u - g v) ^ 2
  set D := ∑ u, G.degree u * g u ^ 2
  set W := ∑ u, G.degree u
  have hsq : Real.sqrt (2 * Q / D) ≤ Real.sqrt (2 * ν) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hD]
    linarith
  have hvS : 0 < ∑ u ∈ S, G.degree u := Finset.sum_pos (fun u _ => hpos u) hSne
  have hSP : ∑ u ∈ S, G.degree u ≤ ∑ u ∈ P, G.degree u :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => hP u (hSpos u hu))
      (fun u _ _ => (hpos u).le)
  have hcompl : ∑ u ∈ S, G.degree u + ∑ u ∈ Sᶜ, G.degree u = W := Finset.sum_add_sum_compl S _
  have hSne' : S ≠ Finset.univ := by
    rintro rfl
    have : ∑ u ∈ (Finset.univ : Finset V), G.degree u = W := rfl
    linarith
  refine ⟨S, hSne, hSne', ?_⟩
  have hmin : min (G.vol S) (G.vol Sᶜ) = ∑ u ∈ S, G.degree u := by
    unfold Hypergraph.vol
    apply min_eq_left
    linarith
  unfold Hypergraph.conductanceSet
  rw [boundary_eq_cut G hG, hmin, div_le_iff₀ hvS]
  calc _ ≤ Real.sqrt (2 * Q / D) * ∑ u ∈ S, G.degree u := hcut
    _ ≤ _ := mul_le_mul_of_nonneg_right hsq hvS.le

theorem upper_pos (hV : 2 ≤ Fintype.card V) (G : Hypergraph V) (hG : G.IsTwoGraph)
    (hpos : ∀ u, 0 < G.degree u) :
    ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
      G.conductanceSet S ≤ Real.sqrt (2 * G.nu2) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨y, hy0, hyd, hnu⟩ := (HyperCheeger.eq_7 hV G).2.2.1
  rw [quad_lap G hG, quad_deg] at hnu
  set ν := G.nu2
  set Qy := 1 / 2 * ∑ u, ∑ v, G.adj u v * (y u - y v) ^ 2 with hQy
  set Dy := ∑ u, G.degree u * y u ^ 2 with hDy
  have hDypos : 0 < Dy := by
    obtain ⟨u, hu⟩ := Function.ne_iff.mp hy0
    refine Finset.sum_pos' (fun v _ => mul_nonneg (hpos v).le (sq_nonneg _))
      ⟨u, Finset.mem_univ _, mul_pos (hpos u) (by
        have : y u ≠ 0 := by simpa using hu
        positivity)⟩
  have hν : 0 ≤ ν := by rw [hnu]; exact div_nonneg (Q_nonneg G hG y) hDypos.le
  have hQyeq : Qy = ν * Dy := by rw [hnu]; field_simp
  have hdy : ∑ u, G.degree u * y u = 0 := by
    rw [← hyd, dotProduct]
    exact Finset.sum_congr rfl fun u _ => mul_comm _ _
  obtain ⟨c, hlt, hgt⟩ := median G.degree y (degree_nonneg G)
  set zp : V → ℝ := fun u => max (y u - c) 0 with hzp
  set zm : V → ℝ := fun u => max (c - y u) 0 with hzm
  have hpt1 : ∀ u v, (zp u - zp v) ^ 2 + (zm u - zm v) ^ 2 ≤ (y u - y v) ^ 2 := by
    intro u v
    simp only [hzp, hzm]
    rcases le_total (y u) c with h1 | h1 <;> rcases le_total (y v) c with h2 | h2
    · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
        max_eq_left (by linarith)]
      nlinarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
        max_eq_right (by linarith)]
      nlinarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
        max_eq_left (by linarith)]
      nlinarith
    · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
        max_eq_right (by linarith)]
      nlinarith
  have hpt2 : ∀ u, zp u ^ 2 + zm u ^ 2 = (y u - c) ^ 2 := by
    intro u
    simp only [hzp, hzm]
    rcases le_total (y u) c with h1 | h1
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  set Qp := 1 / 2 * ∑ u, ∑ v, G.adj u v * (zp u - zp v) ^ 2
  set Qm := 1 / 2 * ∑ u, ∑ v, G.adj u v * (zm u - zm v) ^ 2
  set Dp := ∑ u, G.degree u * zp u ^ 2
  set Dm := ∑ u, G.degree u * zm u ^ 2
  have hQsplit : Qp + Qm ≤ Qy := by
    have : ∑ u, ∑ v, G.adj u v * (zp u - zp v) ^ 2 + ∑ u, ∑ v, G.adj u v * (zm u - zm v) ^ 2
        ≤ ∑ u, ∑ v, G.adj u v * (y u - y v) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun u _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hpt1 u v) (adj_nonneg G hG u v)
    simp only [Qp, Qm, hQy]
    linarith
  have hDsplit : Dp + Dm = ∑ u, G.degree u * (y u - c) ^ 2 := by
    simp only [Dp, Dm]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [← mul_add, hpt2]
  have hDz : Dy ≤ ∑ u, G.degree u * (y u - c) ^ 2 := by
    have : ∑ u, G.degree u * (y u - c) ^ 2 =
        Dy - 2 * c * ∑ u, G.degree u * y u + c ^ 2 * ∑ u, G.degree u := by
      rw [hDy, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [this, hdy]
    have : 0 ≤ ∑ u, G.degree u := Finset.sum_nonneg fun u _ => (hpos u).le
    nlinarith [sq_nonneg c]
  have hmain : Qp + Qm ≤ ν * (Dp + Dm) := by
    rw [hDsplit]
    nlinarith [mul_le_mul_of_nonneg_left hDz hν]
  have hQp0 : 0 ≤ Qp := Q_nonneg G hG zp
  have hQm0 : 0 ≤ Qm := Q_nonneg G hG zm
  have hDp0 : 0 ≤ Dp := D_nonneg G zp
  have hDm0 : 0 ≤ Dm := D_nonneg G zm
  have hDpm : 0 < Dp + Dm := by linarith
  by_cases h1 : 0 < Dp ∧ Qp ≤ ν * Dp
  · refine upper_from_g G hG hpos ν zp (fun u => le_max_right _ _) h1.1 h1.2
      (Finset.univ.filter fun u => c < y u) (fun u hu => ?_) hgt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hzp, lt_max_iff, lt_irrefl, or_false] at hu
    linarith
  · have h2 : 0 < Dm ∧ Qm ≤ ν * Dm := by
      rw [not_and_or, not_lt, not_le] at h1
      rcases h1 with h1 | h1
      · have hDp : Dp = 0 := le_antisymm h1 hDp0
        refine ⟨by linarith, ?_⟩
        rw [hDp] at hmain
        nlinarith
      · have hQm : Qm < ν * Dm := by nlinarith
        refine ⟨?_, hQm.le⟩
        by_contra hDm
        push Not at hDm
        have : ν * Dm ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hν hDm
        linarith
    refine upper_from_g G hG hpos ν zm (fun u => le_max_right _ _) h2.1 h2.2
      (Finset.univ.filter fun u => y u < c) (fun u hu => ?_) hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hzm, lt_max_iff, lt_irrefl, or_false] at hu
    linarith

end HyperCheeger.Dev.Thm31

namespace HyperCheeger

open HyperCheeger.Dev.Thm31 in
theorem chk_theorem_3_1 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (G : Hypergraph V) (hG : G.IsTwoGraph) (hconn : G.IsConnected) :
    G.nu2 / 2 ≤ G.conductance ∧ G.conductance ≤ Real.sqrt (2 * G.nu2) := by
  obtain ⟨u0, v0, huv⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card V by omega)
  have hsingle : ∀ u : V, ({u} : Finset V) ≠ Finset.univ := by
    intro u h
    have h1 : Fintype.card V ≤ 1 := by
      rw [← Finset.card_univ, ← h, Finset.card_singleton]
    omega
  constructor
  · have : Nonempty {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ} :=
      ⟨⟨{u0}, Finset.singleton_nonempty _, hsingle u0⟩⟩
    exact le_ciInf fun S => lower_set hV G hG S.1 S.2.1 S.2.2
  · by_cases hz : ∃ u, G.degree u = 0
    · obtain ⟨u, hu⟩ := hz
      refine conductance_le G (Finset.singleton_nonempty u) (hsingle u) ?_
      have hv : G.vol {u} = 0 := by simp [Hypergraph.vol, hu]
      have hm : min (G.vol {u}) (G.vol {u}ᶜ) = 0 := by
        rw [hv]; exact min_eq_left (vol_nonneg G _)
      unfold Hypergraph.conductanceSet
      rw [hm, div_zero]
      exact Real.sqrt_nonneg _
    · push Not at hz
      have hpos : ∀ u, 0 < G.degree u := fun u => (degree_nonneg G u).lt_of_ne (hz u).symm
      obtain ⟨S, h1, h2, h3⟩ := upper_pos hV G hG hpos
      exact conductance_le G h1 h2 h3


end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_theorem_3_1 := @HyperCheeger.chk_theorem_3_1
