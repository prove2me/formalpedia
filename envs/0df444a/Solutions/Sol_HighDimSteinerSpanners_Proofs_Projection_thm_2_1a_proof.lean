-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Projection.thm_2_1a_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:07.149724+00:00
-- url     : https://prove2.me/submissions/e4191762-5814-4acf-b869-7510ae43a1ab

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Projection
private lemma weightedWalk_nonnegative {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ)
  (hweight : ∀ e ∈ H.edgeSet, 0 ≤ w e) : ∀ {u v : V} (q_w : H.Walk u v), 0 ≤ walkWeight w q_w := by
  intro u v q_w
  induction q_w with
  | nil => exact le_rfl
  | @cons u b v hadj q' ih =>
    exact add_nonneg (hweight s(u, b) (H.mem_edgeSet.mpr hadj)) ih
private lemma weightedWalk_append {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ {u v z :
    V} (q₁ : H.Walk u v) (q₂ : H.Walk v z),
    walkWeight w (q₁.append q₂) = walkWeight w q₁ + walkWeight w q₂ := by
  intro u v z q₁ q₂
  induction q₁ with
  | nil =>
    rw [SimpleGraph.Walk.nil_append]
    simp [walkWeight]
  | @cons u b v _ q' ih =>
    rw [SimpleGraph.Walk.cons_append]
    simp only [walkWeight, ih, add_assoc]
private lemma weightedWalk_reverse {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ {u v : V}
    (q_w : H.Walk u v),
    walkWeight w q_w.reverse = walkWeight w q_w := by
  have hww_append := @weightedWalk_append _ H w
  intro u v q_w
  induction q_w with
  | nil =>
    rw [SimpleGraph.Walk.reverse_nil]
  | @cons u b v _ q' ih =>
    rw [SimpleGraph.Walk.reverse_cons, hww_append, ih]
    simp only [walkWeight, add_zero]
    rw [@Sym2.eq_swap _ b u, add_comm]
private lemma weightedGraphDist_self {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ u : V,
    graphDist H w u u = 0 := by
  intro u
  apply nonpos_iff_eq_zero.mp
  calc
    graphDist H w u u ≤ ENNReal.ofReal (walkWeight w SimpleGraph.Walk.nil) :=
      iInf_le _ SimpleGraph.Walk.nil
    _ = 0 := by simp [walkWeight]
private lemma weightedGraphDist_symm {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ u v :
    V, graphDist H w u v = graphDist H w v u := by
  have hww_reverse := @weightedWalk_reverse _ H w
  have hle : ∀ u v : V, graphDist H w u v ≤ graphDist H w v u := by
    intro u v
    unfold graphDist
    refine le_iInf (fun q_w => ?_)
    calc
      (⨅ p_w : H.Walk u v, ENNReal.ofReal (walkWeight w p_w))
        ≤ ENNReal.ofReal (walkWeight w q_w.reverse) := iInf_le _ q_w.reverse
      _ = ENNReal.ofReal (walkWeight w q_w) := by rw [hww_reverse]
  exact fun u v => le_antisymm (hle u v) (hle v u)
private lemma weightedGraphDist_adj_le {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) : ∀ {u v
    : V}, H.Adj u v →
    graphDist H w u v ≤ ENNReal.ofReal (w s(u, v)) := by
  intro u v hadj
  calc
    graphDist H w u v ≤ ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj .nil)) :=
      iInf_le _ (SimpleGraph.Walk.cons hadj .nil)
    _ = ENNReal.ofReal (w s(u, v)) := by simp [walkWeight]
private lemma weightedGraphDist_triangle {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ)
  (hweight : ∀ e ∈ H.edgeSet, 0 ≤ w e) : ∀ u v z : V,
    graphDist H w u z ≤ graphDist H w u v + graphDist H w v z := by
  have hww_nonneg := @weightedWalk_nonnegative _ H w hweight
  have hww_append := @weightedWalk_append _ H w
  intro u v z
  unfold graphDist
  rw [ENNReal.iInf_add]
  refine le_iInf (fun q₁ => ?_)
  rw [ENNReal.add_iInf]
  refine le_iInf (fun q₂ => ?_)
  rw [← ENNReal.ofReal_add (hww_nonneg q₁) (hww_nonneg q₂), ← hww_append]
  exact iInf_le _ (q₁.append q₂)
private lemma finiteMetricGap (P : Type) [MetricSpace P] [Finite P] (s : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : P, dist a b < s + ε → dist a b ≤ s := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let BadPairs : Finset (P × P) := Finset.univ.filter (fun ab : P × P => s < dist ab.1 ab.2)
  let ε : ℝ :=
    if hne : BadPairs.Nonempty then
      (BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s)) / 2
    else 1
  have hε_pos : 0 < ε := by
    dsimp only [ε]
    split_ifs with hne
    · have hinf_pos : 0 < BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s) := by
        rw [Finset.lt_inf'_iff]
        intro ab hab
        have hlt : s < dist ab.1 ab.2 := (Finset.mem_filter.mp hab).2
        linarith
      linarith
    · norm_num
  let B : ℝ := s + ε
  have h_gap : ∀ a b : P, dist a b < B → dist a b ≤ s := by
    intro a b hlt
    by_contra hnot
    have hgt : s < dist a b := not_le.mp hnot
    have hmem : (a, b) ∈ BadPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
    have hne : BadPairs.Nonempty := ⟨(a, b), hmem⟩
    have hε_eq : ε = (BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s)) / 2 := dif_pos hne
    have hinf_le : BadPairs.inf' hne (fun ab => dist ab.1 ab.2 - s) ≤ dist a b - s :=
      Finset.inf'_le _ hmem
    dsimp [B] at hlt
    linarith
  exact ⟨ε, hε_pos, h_gap⟩
end HighDimSteinerSpanners.Proofs.Projection
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Projection
namespace HighDimSteinerSpanners.Proofs.Projection
theorem _root_.solution :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C r : ℝ), 1 ≤ C → 0 < r →
        ∀ (S : Type) [Fintype S]
          (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ),
          IsGeneralNonMetricSteinerSpanner C H w →
          ∃ G_hat : SimpleGraph P,
            Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
            (∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r) ∧
            (∀ x y : P, 0 < dist x y → dist x y ≤ r →
              ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r) := by
  classical
  intro P _ _ hP_card C r hC hr S _ H w hSpan
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨ε, hε_pos, h_gap⟩ := finiteMetricGap P (C * r)
  let B : ℝ := C * r + ε
  have hCr_pos : 0 < C * r := mul_pos (by linarith) hr
  have hB_pos : 0 < B := by dsimp [B]; linarith
  have h_transfer : ∀ a b : P,
      graphDist H w (.inl a) (.inl b) < ENNReal.ofReal B → dist a b ≤ C * r := by
    intro a b hlt
    have hof : ENNReal.ofReal (dist a b) < ENNReal.ofReal B :=
      lt_of_le_of_lt (hSpan.noncontracting a b) hlt
    exact h_gap a b ((ENNReal.ofReal_lt_ofReal_iff hB_pos).mp hof)
  have hww_nonneg := @weightedWalk_nonnegative _ H w hSpan.weight_nonneg
  have hgd_self := weightedGraphDist_self H w
  have hgd_symm := weightedGraphDist_symm H w
  have hgd_adj_le := @weightedGraphDist_adj_le _ H w
  have hgd_triangle := weightedGraphDist_triangle H w hSpan.weight_nonneg
  have hπ_ex : ∀ u : P ⊕ S, ∃ z ∈ (Finset.univ : Finset P),
      ∀ z' ∈ (Finset.univ : Finset P),
        graphDist H w u (.inl z) ≤ graphDist H w u (.inl z') :=
    fun u => Finset.exists_min_image Finset.univ (fun z => graphDist H w u (.inl z))
      Finset.univ_nonempty
  let π : P ⊕ S → P := fun u => Classical.choose (hπ_ex u)
  have hπ_min : ∀ (u : P ⊕ S) (z : P),
      graphDist H w u (.inl (π u)) ≤ graphDist H w u (.inl z) :=
    fun u z => (Classical.choose_spec (hπ_ex u)).2 z (Finset.mem_univ z)
  have hπ_inl : ∀ x : P, π (.inl x) = x := by
    intro x
    by_contra hne
    have hd_pos : 0 < dist x (π (.inl x)) := dist_pos.mpr (Ne.symm hne)
    have hgd_pos : 0 < graphDist H w (.inl x) (.inl (π (.inl x))) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd_pos) (hSpan.noncontracting x (π (.inl x)))
    have hgd_zero : graphDist H w (.inl x) (.inl (π (.inl x))) ≤ 0 := by
      calc
        graphDist H w (.inl x) (.inl (π (.inl x)))
          ≤ graphDist H w (.inl x) (.inl x) := hπ_min (.inl x) x
        _ = 0 := hgd_self (.inl x)
    exact (not_lt_of_ge hgd_zero) hgd_pos
  let G_hat : SimpleGraph P :=
    { Adj := fun a b => a ≠ b ∧ dist a b ≤ C * r ∧
        ∃ u v : P ⊕ S, H.Adj u v ∧ s(π u, π v) = s(a, b)
      symm := ⟨by
        intro a b ⟨hab, hd, u, v, huv, hs⟩
        refine ⟨hab.symm, ?_, u, v, huv, ?_⟩
        · rwa [dist_comm]
        · rw [hs, Sym2.eq_swap]⟩
      loopless := ⟨fun a h => h.1 rfl⟩ }
  have hG_edge : ∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r :=
    fun _ _ h => ⟨dist_pos.mpr h.1, h.2.1⟩
  have hG_card : Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet := by
    have hex : ∀ e' : G_hat.edgeSet, ∃ e : H.edgeSet, Sym2.map π e.1 = e'.1 := by
      rintro ⟨s', hs'⟩
      revert hs'
      refine Sym2.ind (fun a b hs' => ?_) s'
      rw [SimpleGraph.mem_edgeSet] at hs'
      obtain ⟨_, _, u, v, huv, hs⟩ := hs'
      refine ⟨⟨s(u, v), H.mem_edgeSet.mpr huv⟩, ?_⟩
      simpa only [Sym2.map_mk] using hs
    let f : G_hat.edgeSet → H.edgeSet := fun e' => Classical.choose (hex e')
    have hf_spec : ∀ e' : G_hat.edgeSet, Sym2.map π (f e').1 = e'.1 :=
      fun e' => Classical.choose_spec (hex e')
    have hf_inj : Function.Injective f := by
      intro e₁ e₂ heq
      apply Subtype.ext
      rw [← hf_spec e₁, ← hf_spec e₂, heq]
    exact Nat.card_le_card_of_injective f hf_inj
  have hG_path : ∀ x y : P, 0 < dist x y → dist x y ≤ r →
      ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r := by
    intro x y _ hxy_le
    have hC_dist_lt : C * dist x y < B := by
      have h1 : C * dist x y ≤ C * r := mul_le_mul_of_nonneg_left hxy_le (by linarith)
      dsimp [B]; linarith
    have hgd_xy_lt : graphDist H w (.inl x) (.inl y) < ENNReal.ofReal B :=
      lt_of_le_of_lt (hSpan.stretch x y) ((ENNReal.ofReal_lt_ofReal_iff hB_pos).mpr hC_dist_lt)
    obtain ⟨q_H, hq_H⟩ : ∃ q_H : H.Walk (.inl x) (.inl y),
        ENNReal.ofReal (walkWeight w q_H) < ENNReal.ofReal B := by
      unfold graphDist at hgd_xy_lt
      exact iInf_lt_iff.mp hgd_xy_lt
    have h_ball : ∀ (u : P ⊕ S) (q_rem : H.Walk u (.inl y)),
        graphDist H w (.inl x) u + ENNReal.ofReal (walkWeight w q_rem) < ENNReal.ofReal B →
        dist x (π u) ≤ C * r := by
      intro u q_rem hbud
      apply h_transfer x (π u)
      have h1 : graphDist H w u (.inl (π u)) ≤ ENNReal.ofReal (walkWeight w q_rem) :=
        le_trans (hπ_min u y) (iInf_le _ q_rem)
      calc
        graphDist H w (.inl x) (.inl (π u))
          ≤ graphDist H w (.inl x) u + graphDist H w u (.inl (π u)) :=
            hgd_triangle (.inl x) u (.inl (π u))
        _ ≤ graphDist H w (.inl x) u + ENNReal.ofReal (walkWeight w q_rem) :=
            add_le_add le_rfl h1
        _ < ENNReal.ofReal B := hbud
    have h_ind : ∀ (u v₀ : P ⊕ S) (q₂ : H.Walk u v₀),
        v₀ = .inl y →
        graphDist H w (.inl x) u + ENNReal.ofReal (walkWeight w q₂) < ENNReal.ofReal B →
        ∃ q₀ : G_hat.Walk (π u) y,
          ∀ z ∈ q₀.support, dist x z ≤ C * r := by
      intro u v₀ q₂
      induction q₂ with
      | @nil u =>
        intro hv₀ hbud
        subst hv₀
        have hu_ball : dist x (π (.inl y)) ≤ C * r := h_ball (.inl y) .nil hbud
        rw [hπ_inl y] at hu_ball ⊢
        refine ⟨SimpleGraph.Walk.nil, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        rwa [hz]
      | @cons u v v₀ hadj q₂' ih =>
        intro hv₀ hbud
        subst hv₀
        have hu_ball : dist x (π u) ≤ C * r := h_ball u (.cons hadj q₂') hbud
        have hw_nn : 0 ≤ w s(u, v) := hSpan.weight_nonneg s(u, v) (H.mem_edgeSet.mpr hadj)
        have hsplit : ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj q₂')) =
            ENNReal.ofReal (w s(u, v)) + ENNReal.ofReal (walkWeight w q₂') := by
          simp only [walkWeight]
          exact ENNReal.ofReal_add hw_nn (hww_nonneg q₂')
        have hbud_v :
            graphDist H w (.inl x) v + ENNReal.ofReal (walkWeight w q₂') < ENNReal.ofReal B := by
          have hstep : graphDist H w (.inl x) v ≤
              graphDist H w (.inl x) u + ENNReal.ofReal (w s(u, v)) :=
            le_trans (hgd_triangle (.inl x) u v) (add_le_add le_rfl (hgd_adj_le hadj))
          calc
            graphDist H w (.inl x) v + ENNReal.ofReal (walkWeight w q₂')
              ≤ (graphDist H w (.inl x) u + ENNReal.ofReal (w s(u, v))) +
                  ENNReal.ofReal (walkWeight w q₂') :=
                add_le_add hstep le_rfl
            _ = graphDist H w (.inl x) u +
                  ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj q₂')) := by
                rw [hsplit, add_assoc]
            _ < ENNReal.ofReal B := hbud
        obtain ⟨q_tail, hq_tail⟩ := ih rfl hbud_v
        by_cases heq : π u = π v
        · rw [heq]
          exact ⟨q_tail, hq_tail⟩
        · have h_adj_hat : G_hat.Adj (π u) (π v) := by
            refine ⟨heq, ?_, u, v, hadj, rfl⟩
            apply h_transfer (π u) (π v)
            have h_left : graphDist H w (.inl (π u)) u ≤ graphDist H w (.inl x) u := by
              rw [hgd_symm (.inl (π u)) u, hgd_symm (.inl x) u]
              exact hπ_min u x
            have h_mid : graphDist H w u v ≤ ENNReal.ofReal (w s(u, v)) := hgd_adj_le hadj
            have h_right : graphDist H w v (.inl (π v)) ≤ ENNReal.ofReal (walkWeight w q₂') :=
              le_trans (hπ_min v y) (iInf_le _ q₂')
            calc
              graphDist H w (.inl (π u)) (.inl (π v))
                ≤ graphDist H w (.inl (π u)) u + graphDist H w u (.inl (π v)) :=
                  hgd_triangle (.inl (π u)) u (.inl (π v))
              _ ≤ graphDist H w (.inl (π u)) u +
                    (graphDist H w u v + graphDist H w v (.inl (π v))) :=
                  add_le_add le_rfl (hgd_triangle u v (.inl (π v)))
              _ ≤ graphDist H w (.inl x) u +
                    (ENNReal.ofReal (w s(u, v)) + ENNReal.ofReal (walkWeight w q₂')) :=
                  add_le_add h_left (add_le_add h_mid h_right)
              _ = graphDist H w (.inl x) u +
                    ENNReal.ofReal (walkWeight w (SimpleGraph.Walk.cons hadj q₂')) := by
                  rw [hsplit]
              _ < ENNReal.ofReal B := hbud
          refine ⟨SimpleGraph.Walk.cons h_adj_hat q_tail, ?_⟩
          intro z hz
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz_tail
          · exact hu_ball
          · exact hq_tail z hz_tail
    have hbud_init :
        graphDist H w (.inl x) (.inl x) + ENNReal.ofReal (walkWeight w q_H) < ENNReal.ofReal B := by
      rwa [hgd_self (.inl x), zero_add]
    have h_proj := h_ind (.inl x) (.inl y) q_H rfl hbud_init
    rw [hπ_inl x] at h_proj
    obtain ⟨q₀, hq₀⟩ := h_proj
    refine ⟨q₀.bypass, q₀.bypass_isPath, ?_⟩
    intro z hz
    exact hq₀ z (q₀.support_bypass_subset_support hz)
  exact ⟨G_hat, hG_card, hG_edge, hG_path⟩
end HighDimSteinerSpanners.Proofs.Projection
