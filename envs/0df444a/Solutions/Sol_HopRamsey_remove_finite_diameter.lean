-- Prove2me | solution 1 for HopRamsey.remove_finite_diameter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:36:19.636807+00:00
-- url     : https://prove2.me/submissions/d5d4c2df-e85a-4a82-8e51-921fe222e426

import Mathlib
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_IsStochRamseyEmbedding
import Definitions.Def_HopRamsey_augmentComplete
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_truncGeom
import Definitions.Def_HopRamsey_truncateLabels

open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

variable {V : Type}

lemma walkWeight_append (G : WGraph V) {u v w : V} (p : G.graph.Walk u v) (q : G.graph.Walk v w) :
    G.walkWeight (p.append q) = G.walkWeight p + G.walkWeight q := by
  simp [WGraph.walkWeight, SimpleGraph.Walk.edges_append, List.map_append, List.sum_append]

lemma walkWeight_reverse (G : WGraph V) {u v : V} (p : G.graph.Walk u v) :
    G.walkWeight p.reverse = G.walkWeight p := by
  simp [WGraph.walkWeight, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]

lemma hopDist_mono (G : WGraph V) {a b : ℕ} (hab : a ≤ b) (u v : V) :
    hopDist G b u v ≤ hopDist G a u v := by
  unfold hopDist
  refine le_iInf fun p => le_iInf fun hp => ?_
  exact iInf_le_of_le p (iInf_le_of_le (le_trans hp hab) le_rfl)

lemma hopDist_le_walk (G : WGraph V) {a : ℕ} {u v : V} (p : G.graph.Walk u v) (hp : p.length ≤ a) :
    hopDist G a u v ≤ G.walkWeight p :=
  iInf_le_of_le p (iInf_le_of_le hp le_rfl)

lemma hopDist_self (G : WGraph V) (a : ℕ) (u : V) : hopDist G a u u = 0 := by
  refine le_antisymm ?_ (by positivity)
  calc hopDist G a u u ≤ G.walkWeight (SimpleGraph.Walk.nil : G.graph.Walk u u) :=
        hopDist_le_walk G _ (by simp)
    _ = 0 := by simp [WGraph.walkWeight]

lemma hopDist_symm (G : WGraph V) (a : ℕ) (u v : V) : hopDist G a u v = hopDist G a v u := by
  have key : ∀ x y : V, hopDist G a y x ≤ hopDist G a x y := by
    intro x y
    unfold hopDist
    refine le_iInf fun p => le_iInf fun hp => ?_
    refine iInf_le_of_le p.reverse (iInf_le_of_le (by simpa using hp) ?_)
    rw [walkWeight_reverse]
  exact le_antisymm (key v u) (key u v)

lemma hopDist_triangle (G : WGraph V) (a b : ℕ) (u v w : V) :
    hopDist G (a + b) u w ≤ hopDist G a u v + hopDist G b v w := by
  unfold hopDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun p => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hp => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun q => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hq => ?_
  refine iInf_le_of_le (p.append q) (iInf_le_of_le ?_ ?_)
  · simp [SimpleGraph.Walk.length_append]; omega
  · rw [walkWeight_append]

/-- With all edge weights at least `m`, distinct vertices are at hop-distance at least `m`. -/
lemma hopDist_ge_of_ne (G : WGraph V) {m : ℝ} (hm : ∀ e ∈ G.graph.edgeSet, m ≤ G.w e) (a : ℕ)
    {u v : V} (huv : u ≠ v) : ENNReal.ofReal m ≤ hopDist G a u v := by
  unfold hopDist
  refine le_iInf fun p => le_iInf fun _ => ?_
  cases p with
  | nil => exact absurd rfl huv
  | cons hadj q =>
    simp only [WGraph.walkWeight, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
    exact le_trans (ENNReal.ofReal_le_ofReal (hm _ hadj)) le_self_add

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

/-- Expectation of a `[0,∞]`-valued function under a PMF. -/
noncomputable def ex {α : Type*} (p : PMF α) (F : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * F a

lemma ex_bind {α β : Type*} (p : PMF α) (f : α → PMF β) (F : β → ℝ≥0∞) :
    ex (p.bind f) F = ex p (fun a => ex (f a) F) := by
  unfold ex
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

lemma ex_pure {α : Type*} (a : α) (F : α → ℝ≥0∞) : ex (PMF.pure a) F = F a := by
  unfold ex
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

lemma ex_map {α β : Type*} (p : PMF α) (g : α → β) (F : β → ℝ≥0∞) :
    ex (p.map g) F = ex p (fun a => F (g a)) := by
  rw [← PMF.bind_pure_comp, ex_bind]
  simp [ex_pure]

lemma ex_mono {α : Type*} (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a ∈ p.support, F a ≤ G a) :
    ex p F ≤ ex p G := by
  unfold ex
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) _
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

lemma ex_le_of_le {α : Type*} (p : PMF α) {F : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a ∈ p.support, F a ≤ c) :
    ex p F ≤ c := by
  calc ex p F ≤ ex p (fun _ => c) := ex_mono p h
    _ = c := by unfold ex; rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma ex_const {α : Type*} (p : PMF α) (c : ℝ≥0∞) : ex p (fun _ => c) = c := by
  unfold ex; rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma ex_add {α : Type*} (p : PMF α) (F G : α → ℝ≥0∞) :
    ex p (fun a => F a + G a) = ex p F + ex p G := by
  unfold ex; simp_rw [mul_add]; exact ENNReal.tsum_add

lemma ex_mul_const {α : Type*} (p : PMF α) (F : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ex p (fun a => F a * c) = ex p F * c := by
  unfold ex; simp_rw [← mul_assoc]; exact ENNReal.tsum_mul_right

lemma ex_const_mul {α : Type*} (p : PMF α) (F : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ex p (fun a => c * F a) = c * ex p F := by
  unfold ex; simp_rw [mul_left_comm _ c]; exact ENNReal.tsum_mul_left

lemma toOuterMeasure_eq_ex {α : Type*} (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    p.toOuterMeasure s = ex p (fun a => if a ∈ s then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  unfold ex
  congr 1; ext a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

/-- Weight of the geometric law, real form. -/
noncomputable def gw (p : ℝ) (r : ℕ) : ℝ := (1 - p) ^ r * p

lemma truncGeom_support {p : ℝ} {k : ℕ} (hk : 0 < k) (hp : 0 < p) :
    ∀ r ∈ (truncGeom p k).support, r < k := by
  intro r hr
  unfold truncGeom at hr
  rw [dif_pos ⟨hk, hp⟩] at hr
  rw [PMF.support_map] at hr
  obtain ⟨R, -, rfl⟩ := hr
  exact R.isLt

lemma sum_gw (p : ℝ) (m : ℕ) : ∑ r ∈ Finset.range m, gw p r = 1 - (1 - p) ^ m := by
  unfold gw
  rw [← Finset.sum_mul]
  rcases eq_or_ne p 0 with h0 | h0
  · subst h0; simp
  have := geom_sum_mul (1 - p) m
  have h' : (1 - p) - 1 = -p := by ring
  rw [h'] at this
  linear_combination -this

lemma gw_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : ℕ) : 0 ≤ gw p r :=
  mul_nonneg (pow_nonneg (by linarith) _) hp0

/-- The expectation under the truncated geometric law. -/
lemma ex_truncGeom {p : ℝ} {k : ℕ} (hk : 0 < k) (hp0 : 0 < p) (hp1 : p ≤ 1) (F : ℕ → ℝ≥0∞) :
    ex (truncGeom p k) F =
      (∑ r ∈ Finset.range k, ENNReal.ofReal (gw p r) * F r) / ENNReal.ofReal (1 - (1 - p) ^ k) := by
  unfold truncGeom
  rw [dif_pos ⟨hk, hp0⟩, ex_map]
  unfold ex
  simp only [PMF.normalize_apply]
  rw [tsum_fintype]
  have hZ : (∑' R : Fin k, truncGeomWeight p k R) = ENNReal.ofReal (1 - (1 - p) ^ k) := by
    rw [tsum_fintype]
    unfold truncGeomWeight
    rw [Fin.sum_univ_eq_sum_range (fun r => ENNReal.ofReal ((1 - p) ^ r * p)) k]
    rw [← sum_gw p k, ENNReal.ofReal_sum_of_nonneg (fun R _ => gw_nonneg hp0.le hp1 R)]
    rfl
  rw [hZ, div_eq_mul_inv, Finset.sum_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun r => ENNReal.ofReal (gw p r) * F r * (ENNReal.ofReal (1 - (1 - p) ^ k))⁻¹) k]
  refine Finset.sum_congr rfl fun R _ => ?_
  unfold truncGeomWeight gw
  ring

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

variable {V : Type}

lemma aug_w_of_edge (G : WGraph V) {ω : ℝ} (hω : 0 < ω) {e : Sym2 V} (he : e ∈ G.graph.edgeSet) :
    (augmentComplete G ω hω).w e = G.w e := by
  classical
  unfold augmentComplete; simp only; rw [if_pos he]

lemma aug_w_of_not_edge (G : WGraph V) {ω : ℝ} (hω : 0 < ω) {e : Sym2 V}
    (he : e ∉ G.graph.edgeSet) : (augmentComplete G ω hω).w e = ω := by
  classical
  unfold augmentComplete; simp only; rw [if_neg he]

/-- Distances can only decrease in the augmented graph. -/
lemma hopDist_aug_le (G : WGraph V) {ω : ℝ} (hω : 0 < ω) (a : ℕ) (u v : V) :
    hopDist (augmentComplete G ω hω) a u v ≤ hopDist G a u v := by
  unfold hopDist
  refine le_iInf fun p => le_iInf fun hp => ?_
  have hle : G.graph ≤ (augmentComplete G ω hω).graph := by
    unfold augmentComplete; exact le_top
  refine iInf_le_of_le (p.mapLe hle) (iInf_le_of_le (by rwa [SimpleGraph.Walk.length_mapLe]) ?_)
  unfold WGraph.walkWeight
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  apply le_of_eq
  congr 1
  apply List.map_congr_left
  intro e he
  rw [aug_w_of_edge G hω (p.edges_subset_edgeSet he)]

/-- Below `ω`, augmented distances are realised by walks of `G`. -/
lemma hopDist_le_aug (G : WGraph V) {ω : ℝ} (hω : 0 < ω) (a : ℕ) (u v : V)
    (hlt : hopDist (augmentComplete G ω hω) a u v < ENNReal.ofReal ω) :
    hopDist G a u v ≤ hopDist (augmentComplete G ω hω) a u v := by
  set G' := augmentComplete G ω hω
  refine le_of_forall_gt fun c hc => ?_
  have hm : hopDist G' a u v < min c (ENNReal.ofReal ω) := lt_min hc hlt
  unfold hopDist at hm
  rw [iInf_lt_iff] at hm
  obtain ⟨p, hp⟩ := hm
  rw [iInf_lt_iff] at hp
  obtain ⟨hpl, hpw⟩ := hp
  have hall : ∀ e ∈ p.edges, e ∈ G.graph.edgeSet := by
    intro e he
    by_contra hne
    have h1 : ENNReal.ofReal (G'.w e) ≤ G'.walkWeight p := by
      unfold WGraph.walkWeight
      exact List.le_sum_of_mem (List.mem_map_of_mem he)
    rw [aug_w_of_not_edge G hω hne] at h1
    exact absurd (lt_of_le_of_lt h1 (lt_of_lt_of_le hpw (min_le_right _ _))) (lt_irrefl _)
  set q := p.transfer G.graph hall
  have hq : G.walkWeight q = G'.walkWeight p := by
    unfold WGraph.walkWeight
    rw [SimpleGraph.Walk.edges_transfer]
    congr 1
    apply List.map_congr_left
    intro e he
    rw [aug_w_of_edge G hω (hall e he)]
  calc hopDist G a u v ≤ G.walkWeight q :=
        hopDist_le_walk G q (by rw [SimpleGraph.Walk.length_transfer]; exact hpl)
    _ = G'.walkWeight p := hq
    _ < c := lt_of_lt_of_le hpw (min_le_left _ _)

lemma le_maxFiniteHopDist [Fintype V] (G : WGraph V) (a : ℕ) {u v : V}
    (hfin : hopDist G a u v ≠ ⊤) : hopDist G a u v ≤ maxFiniteHopDist G a := by
  unfold maxFiniteHopDist
  refine le_trans ?_ (Finset.le_sup (f := fun u => (Finset.univ : Finset V).sup fun v =>
    if hopDist G a u v < ⊤ then hopDist G a u v else 0) (Finset.mem_univ u))
  refine le_trans ?_ (Finset.le_sup (f := fun v =>
    if hopDist G a u v < ⊤ then hopDist G a u v else 0) (Finset.mem_univ v))
  simp [lt_top_iff_ne_top.mpr hfin]

theorem remove_finite_diameter' [Fintype V] [DecidableEq V] (G : WGraph V) (h η : ℕ)
    (ρ ε α ω : ℝ) (hρ : 1 ≤ ρ) (hω : 0 < ω)
    (hωΦ : ENNReal.ofReal (2 * ρ) * maxFiniteHopDist G h ≤ ENNReal.ofReal ω)
    (D' : PMF (HST V × Finset V)) (hleaves : ∀ x ∈ D'.support, x.1.leaves = Set.univ)
    (hD' : IsStochRamseyEmbedding (augmentComplete G ω hω) h D' η ρ ε α) :
    (∀ x ∈ (D'.map fun x => (truncateLabels x.1 (ENNReal.ofReal (ω / 2)), x.2)).support,
        x.1.leaves = Set.univ) ∧
      IsStochRamseyEmbedding G h (D'.map fun x => (truncateLabels x.1 (ENNReal.ofReal (ω / 2)), x.2))
        η ρ ε α := by
  set G' := augmentComplete G ω hω
  set θ := ENNReal.ofReal (ω / 2)
  obtain ⟨hHop, hDist, hExc, hExp⟩ := hD'
  have hθω : θ < ENNReal.ofReal ω := by
    rw [ENNReal.ofReal_lt_ofReal_iff hω]; linarith
  -- saved pairs at finite distance are never truncated
  have keep : ∀ x ∈ D'.support, ∀ u ∈ x.2, ∀ v : V, hopDist G h u v ≠ ⊤ → x.1.ρ v u ≤ θ := by
    intro x hx u hu v hfin
    have h1 := hDist x hx u hu v
    have h2 := hopDist_aug_le G hω h u v
    have h3 := le_maxFiniteHopDist G h hfin
    calc x.1.ρ v u ≤ ENNReal.ofReal ρ * hopDist G' h u v := h1
      _ ≤ ENNReal.ofReal ρ * maxFiniteHopDist G h := mul_le_mul_right (h2.trans h3) _
      _ ≤ θ := by
          have e : ENNReal.ofReal (2 * ρ) = 2 * ENNReal.ofReal ρ := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          have e2 : ENNReal.ofReal ω = 2 * θ := by
            simp only [θ]; rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
            ring_nf
          rw [e, e2, mul_assoc] at hωΦ
          exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hωΦ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [PMF.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hleaves y hy
  · intro x hx u v
    rw [PMF.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [truncateLabels]
    split_ifs with hθ
    · exact le_top
    · push Not at hθ
      have h1 := hHop y hy u v
      have hlt : hopDist G' (η * h) u v < ENNReal.ofReal ω := lt_of_le_of_lt (h1.trans hθ) hθω
      exact le_trans (hopDist_le_aug G hω _ u v hlt) h1
  · intro x hx u hu v
    rw [PMF.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [truncateLabels] at hu ⊢
    by_cases hfin : hopDist G h u v = ⊤
    · rw [hfin, ENNReal.mul_top (by simp; linarith)]; exact le_top
    · have hk := keep y hy u hu v hfin
      rw [if_neg (not_lt.mpr hk)]
      exact le_trans (hDist y hy u hu v) (mul_le_mul_right (hopDist_aug_le G hω h u v) _)
  · intro v
    rw [PMF.toOuterMeasure_map_apply]
    exact hExc v
  · intro u v
    have e : (∑' x, (D'.map fun x => (truncateLabels x.1 θ, x.2)) x *
        (if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0)) =
        ∑' y, D' y * (if u ∈ y.2 ∧ v ∈ y.2 then (truncateLabels y.1 θ).ρ u v else 0) := by
      have := ex_map D' (fun x => (truncateLabels x.1 θ, x.2))
        (fun x => if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0)
      unfold ex at this; exact this
    rw [e]
    by_cases hfin : hopDist G h u v = ⊤
    · by_cases hα : 0 < α
      · rw [hfin, ENNReal.mul_top (by simpa using hα)]; exact le_top
      · have h0 : ENNReal.ofReal α = 0 := ENNReal.ofReal_eq_zero.mpr (not_lt.mp hα)
        have hz := hExp u v
        rw [h0, zero_mul, nonpos_iff_eq_zero, ENNReal.tsum_eq_zero] at hz
        rw [h0, zero_mul, nonpos_iff_eq_zero, ENNReal.tsum_eq_zero]
        intro y
        have hy := hz y
        by_cases hy0 : D' y = 0
        · simp [hy0]
        · rw [mul_eq_zero] at hy
          rcases hy with hy | hy
          · exact absurd hy hy0
          · simp only [truncateLabels]
            split_ifs at hy ⊢ with h1 h2
            · rw [hy] at h2; exact absurd h2 (not_lt.mpr bot_le)
            · simp [hy]
            · simp
    · refine le_trans (le_of_eq ?_) (le_trans (hExp u v)
        (mul_le_mul_right (hopDist_aug_le G hω h u v) _))
      congr 1; ext y
      by_cases hy : y ∈ D'.support
      · split_ifs with huv
        · simp only [truncateLabels]
          have hk := keep y hy u huv.1 v hfin
          rw [y.1.symm v u] at hk
          rw [if_neg (not_lt.mpr hk)]
        · rfl
      · rw [PMF.mem_support_iff, not_not] at hy; simp [hy]

end HopRamsey.FZ


open scoped ENNReal
open ARTreeCover HopRamsey

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (h η : ℕ)
    (ρ ε α ω : ℝ) (hρ : 1 ≤ ρ) (hω : 0 < ω)
    (hωΦ : ENNReal.ofReal (2 * ρ) * maxFiniteHopDist G h ≤ ENNReal.ofReal ω)
    (D' : PMF (HST V × Finset V)) (hleaves : ∀ x ∈ D'.support, x.1.leaves = Set.univ)
    (hD' : IsStochRamseyEmbedding (augmentComplete G ω hω) h D' η ρ ε α) :
    (∀ x ∈ (D'.map fun x => (truncateLabels x.1 (ENNReal.ofReal (ω / 2)), x.2)).support,
        x.1.leaves = Set.univ) ∧
      IsStochRamseyEmbedding G h (D'.map fun x => (truncateLabels x.1 (ENNReal.ofReal (ω / 2)), x.2))
        η ρ ε α := by
  exact HopRamsey.FZ.remove_finite_diameter' G h η ρ ε α ω hρ hω hωΦ D' hleaves hD'
