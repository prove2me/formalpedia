-- Prove2me | solution 1 for LeightonRao.ShortPaths.corollary_20
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:58:49.467108+00:00
-- url     : https://prove2.me/submissions/eee41c45-cef0-4df5-9513-56a33a1665bd

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting



namespace LeightonRao.ShortPaths

variable {V : Type} [Fintype V] [DecidableEq V]

section Grow
variable (N : Network V) (ℓ : V → V → ℝ) (D : V → ENNReal) (R : Finset V) (σ : ℝ)

def l19cut (B : Finset V) : ℝ := ∑ u ∈ B, ∑ v ∈ R \ B, N.C u v

noncomputable def l19W (R : Finset V) : ℝ := (1/2) * ∑ u ∈ R, ∑ v ∈ R, N.C u v * ℓ u v

noncomputable def l19k (B : Finset V) (r : ℝ) (u v : V) : ℝ :=
  if u ∈ B ∧ v ∈ B then ℓ u v else if u ∈ B then r - (D u).toReal
  else if v ∈ B then r - (D v).toReal else 0

noncomputable def l19vol (B : Finset V) (r : ℝ) : ℝ :=
  σ + (1/2) * ∑ u ∈ R, ∑ v ∈ R, N.C u v * l19k ℓ D B r u v

noncomputable def l19ball (a : ℝ) : Finset V := R.filter (fun v => D v < ENNReal.ofReal a)

end Grow

lemma l19_sum_ind (R B : Finset V) (hB : B ⊆ R) (f : V → V → ℝ) :
    ∑ u ∈ R, ∑ v ∈ R, (if u ∈ B ∧ v ∉ B then f u v else 0) = ∑ u ∈ B, ∑ v ∈ R \ B, f u v := by
  have h : ∀ u ∈ R, ∑ v ∈ R, (if u ∈ B ∧ v ∉ B then f u v else 0) =
      if u ∈ B then ∑ v ∈ R \ B, f u v else 0 := by
    intro u _
    by_cases hu : u ∈ B
    · simp only [hu, true_and, if_true]
      rw [← Finset.sum_filter, Finset.sdiff_eq_filter]
    · simp [hu]
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 hB]

lemma l19_sum_ind2 (R B : Finset V) (f : V → V → ℝ) :
    ∑ u ∈ R, ∑ v ∈ R, (if u ∉ B ∧ v ∉ B then f u v else 0) =
      ∑ u ∈ R \ B, ∑ v ∈ R \ B, f u v := by
  have h : ∀ u ∈ R, ∑ v ∈ R, (if u ∉ B ∧ v ∉ B then f u v else 0) =
      if u ∉ B then ∑ v ∈ R \ B, f u v else 0 := by
    intro u _
    by_cases hu : u ∈ B
    · simp [hu]
    · simp only [hu, not_false_eq_true, true_and, if_true]
      rw [← Finset.sum_filter, Finset.sdiff_eq_filter]
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter, ← Finset.sdiff_eq_filter]

lemma l19_cut_symm (N : Network V) (R B : Finset V) :
    ∑ v ∈ B, ∑ u ∈ R \ B, N.C u v = l19cut N R B := by
  unfold l19cut
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => N.C_symm u v

lemma l19_vol_lin (N : Network V) (ℓ : V → V → ℝ) (D : V → ENNReal) (R : Finset V) (σ : ℝ)
    (B : Finset V) (hB : B ⊆ R) (a a' : ℝ) :
    l19vol N ℓ D R σ B a = l19vol N ℓ D R σ B a' + l19cut N R B * (a - a') := by
  have hp : ∀ u v, N.C u v * l19k ℓ D B a u v = N.C u v * l19k ℓ D B a' u v +
      ((if u ∈ B ∧ v ∉ B then N.C u v * (a - a') else 0) +
       (if v ∈ B ∧ u ∉ B then N.C u v * (a - a') else 0)) := by
    intro u v
    unfold l19k
    by_cases hu : u ∈ B <;> by_cases hv : v ∈ B <;> simp [hu, hv] <;> ring
  unfold l19vol
  simp_rw [hp, Finset.sum_add_distrib]
  rw [l19_sum_ind R B hB, Finset.sum_comm (f := fun u v => if v ∈ B ∧ u ∉ B then _ else _)]
  rw [l19_sum_ind R B hB (fun v u => N.C u v * (a - a'))]
  have h1 : ∑ u ∈ B, ∑ v ∈ R \ B, N.C u v * (a - a') = l19cut N R B * (a - a') := by
    unfold l19cut; rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]
  have h2 : ∑ v ∈ B, ∑ u ∈ R \ B, N.C u v * (a - a') = l19cut N R B * (a - a') := by
    rw [← l19_cut_symm N R B, Finset.sum_mul]; simp_rw [Finset.sum_mul]
  rw [h1, h2]; ring

lemma l19_vol_ge (N : Network V) (ℓ : V → V → ℝ) (hℓ : ∀ u v, 0 ≤ ℓ u v) (D : V → ENNReal)
    (R : Finset V) (σ : ℝ) (B : Finset V) (r : ℝ) (hr : ∀ u ∈ B, (D u).toReal ≤ r) :
    σ ≤ l19vol N ℓ D R σ B r := by
  unfold l19vol
  have : 0 ≤ ∑ u ∈ R, ∑ v ∈ R, N.C u v * l19k ℓ D B r u v := by
    apply Finset.sum_nonneg; intro u _; apply Finset.sum_nonneg; intro v _
    apply mul_nonneg (N.C_nonneg _ _)
    unfold l19k
    split_ifs with h1 h2 h3
    · exact hℓ _ _
    · linarith [hr u h2]
    · linarith [hr v h3]
    · exact le_rfl
  linarith

lemma l19_vol_jump (N : Network V) (ℓ : V → V → ℝ) (hℓ : ∀ u v, 0 ≤ ℓ u v) (D : V → ENNReal)
    (R : Finset V) (σ : ℝ) (B B' : Finset V) (r : ℝ) (hBB : B ⊆ B')
    (hnew : ∀ u ∈ B', u ∉ B → (D u).toReal = r)
    (htri : ∀ u ∈ B, ∀ v ∈ B', v ∉ B → 0 < N.C u v → r - (D u).toReal ≤ ℓ u v)
    (htri' : ∀ u ∈ B, ∀ v ∈ B', v ∉ B → 0 < N.C v u → r - (D u).toReal ≤ ℓ v u) :
    l19vol N ℓ D R σ B r ≤ l19vol N ℓ D R σ B' r := by
  unfold l19vol
  have : ∑ u ∈ R, ∑ v ∈ R, N.C u v * l19k ℓ D B r u v ≤
      ∑ u ∈ R, ∑ v ∈ R, N.C u v * l19k ℓ D B' r u v := by
    apply Finset.sum_le_sum; intro u _; apply Finset.sum_le_sum; intro v _
    rcases (N.C_nonneg u v).lt_or_eq with hC | hC
    · apply mul_le_mul_of_nonneg_left _ hC.le
      have hC' : 0 < N.C v u := by rw [N.C_symm]; exact hC
      unfold l19k
      by_cases hu : u ∈ B <;> by_cases hv : v ∈ B
      · simp [hu, hv, hBB hu, hBB hv]
      · by_cases hv' : v ∈ B'
        · simp [hu, hv, hBB hu, hv']; linarith [htri u hu v hv' hv hC]
        · simp [hu, hv, hBB hu, hv']
      · by_cases hu' : u ∈ B'
        · simp [hu, hv, hBB hv, hu']; linarith [htri' v hv u hu' hu hC]
        · simp [hu, hv, hBB hv, hu']
      · by_cases hu' : u ∈ B' <;> by_cases hv' : v ∈ B'
        · simp [hu, hv, hu', hv']; exact hℓ _ _
        · simp [hu, hv, hu', hv', hnew u hu' hu]
        · simp [hu, hv, hu', hv', hnew v hv' hv]
        · simp [hu, hv, hu', hv']
    · rw [← hC]; simp
  linarith

lemma l19_vol_le (N : Network V) (ℓ : V → V → ℝ) (hℓ : ∀ u v, 0 ≤ ℓ u v) (D : V → ENNReal)
    (R : Finset V) (σ : ℝ) (B : Finset V) (hB : B ⊆ R) (a : ℝ)
    (hr : ∀ u ∈ B, (D u).toReal ≤ a)
    (htri : ∀ u ∈ B, ∀ v ∈ R, v ∉ B → 0 < N.C u v → a - (D u).toReal ≤ ℓ u v)
    (htri' : ∀ u ∈ B, ∀ v ∈ R, v ∉ B → 0 < N.C v u → a - (D u).toReal ≤ ℓ v u) :
    l19vol N ℓ D R σ B a ≤ σ + l19W N ℓ R - l19W N ℓ (R \ B) := by
  have hp : ∀ u ∈ R, ∀ v ∈ R, N.C u v * l19k ℓ D B a u v +
      (if u ∉ B ∧ v ∉ B then N.C u v * ℓ u v else 0) ≤ N.C u v * ℓ u v := by
    intro u hu v hv
    rcases (N.C_nonneg u v).lt_or_eq with hC | hC
    · have hC' : 0 < N.C v u := by rw [N.C_symm]; exact hC
      unfold l19k
      by_cases hu' : u ∈ B <;> by_cases hv' : v ∈ B
      · simp [hu', hv']
      · simp [hu', hv']
        exact mul_le_mul_of_nonneg_left (htri u hu' v hv hv' hC) hC.le
      · simp [hu', hv']
        exact mul_le_mul_of_nonneg_left (htri' v hv' u hu hu' hC) hC.le
      · simp [hu', hv']
    · rw [← hC]; simp
  have hs := Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => hp u hu v hv
  simp only [Finset.sum_add_distrib] at hs
  rw [l19_sum_ind2 R B (fun u v => N.C u v * ℓ u v)] at hs
  unfold l19vol l19W
  linarith

lemma l19_toReal_tri {x y : ENNReal} {t : ℝ} (ht : 0 ≤ t) (hx : x ≠ ⊤)
    (h : y ≤ x + ENNReal.ofReal t) : y.toReal ≤ x.toReal + t := by
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hx, ENNReal.ofReal_ne_top⟩) h
  rwa [ENNReal.toReal_add hx ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ht] at this

lemma l19_grow (N : Network V) (ℓ : V → V → ℝ) (hℓ : ∀ u v, 0 ≤ ℓ u v)
    (hℓs : ∀ u v, ℓ u v = ℓ v u)
    (D : V → ENNReal) (R : Finset V) (c : V) (hc : c ∈ R) (hDc : D c = 0)
    (htri : ∀ u ∈ R, ∀ v ∈ R, 0 < N.C u v → D v ≤ D u + ENNReal.ofReal (ℓ u v))
    (σ Δ ε : ℝ) (hσ : 0 < σ) (hΔ : 0 < Δ)
    (hε : Real.log ((σ + l19W N ℓ R) / σ) ≤ ε * Δ) :
    ∃ a, 0 < a ∧ a ≤ Δ ∧ l19cut N R (l19ball D R a) ≤
      ε * (σ + l19W N ℓ R - l19W N ℓ (R \ l19ball D R a)) := by
  have hWnn : ∀ S : Finset V, 0 ≤ l19W N ℓ S := fun S => by
    unfold l19W; apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg _ _) (hℓ _ _)
  have hballR : ∀ a, l19ball D R a ⊆ R := fun a => Finset.filter_subset _ _
  have hmemball : ∀ a v, v ∈ l19ball D R a ↔ v ∈ R ∧ D v < ENNReal.ofReal a :=
    fun a v => Finset.mem_filter
  have hfin : ∀ a v, v ∈ l19ball D R a → D v ≠ ⊤ := fun a v hv =>
    ne_top_of_lt ((hmemball a v).1 hv).2
  have hlt : ∀ a v, v ∈ l19ball D R a → (D v).toReal < a := fun a v hv =>
    ENNReal.toReal_lt_of_lt_ofReal ((hmemball a v).1 hv).2
  have hεnn : 0 ≤ ε := by
    have h0 : 0 ≤ Real.log ((σ + l19W N ℓ R) / σ) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hσ]; linarith [hWnn R]
    by_contra h; push_neg at h; nlinarith
  have hout : ∀ a, 0 < a → ∀ u ∈ l19ball D R a, ∀ v ∈ R, v ∉ l19ball D R a → 0 < N.C u v →
      a - (D u).toReal ≤ ℓ u v := by
    intro a ha u hu v hv hvn hC
    have h1 := htri u (hballR a hu) v hv hC
    have h2 : ENNReal.ofReal a ≤ D v := by
      by_contra h; exact hvn ((hmemball a v).2 ⟨hv, lt_of_not_ge h⟩)
    have h4 := l19_toReal_tri (hℓ u v) (hfin a u hu) h1
    have hne : D v ≠ ⊤ := ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨hfin a u hu, ENNReal.ofReal_ne_top⟩) h1
    have h3 : a ≤ (D v).toReal := (ENNReal.ofReal_le_iff_le_toReal hne).1 h2
    linarith
  have hV4 : ∀ a, 0 < a → l19vol N ℓ D R σ (l19ball D R a) a ≤
      σ + l19W N ℓ R - l19W N ℓ (R \ l19ball D R a) := by
    intro a ha
    apply l19_vol_le N ℓ hℓ D R σ _ (hballR a) a (fun u hu => (hlt a u hu).le)
    · exact hout a ha
    · intro u hu v hv hvn hC
      rw [N.C_symm] at hC; rw [← hℓs]; exact hout a ha u hu v hv hvn hC
  set vol : ℝ → ℝ := fun a => l19vol N ℓ D R σ (l19ball D R a) a with hvol
  set cut : ℝ → ℝ := fun a => l19cut N R (l19ball D R a) with hcutdef
  have claim : ∀ k a, (l19ball D R a).card = k → 0 < a →
      (∀ a', 0 < a' → a' ≤ a → ε * vol a' < cut a') →
      Real.log σ + ε * a < Real.log (vol a) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro a hk ha hyp
    have hcmem : c ∈ l19ball D R a :=
      (hmemball a c).2 ⟨hc, by rw [hDc]; exact ENNReal.ofReal_pos.2 ha⟩
    obtain ⟨w, hw, hmax⟩ := (l19ball D R a).exists_max_image (fun v => (D v).toReal) ⟨c, hcmem⟩
    have hs0 : 0 ≤ (D w).toReal := ENNReal.toReal_nonneg
    have hsa : (D w).toReal < a := hlt a w hw
    set s := (D w).toReal with hs
    set B := l19ball D R a with hBdef
    set X := l19vol N ℓ D R σ B s with hXdef
    have hX : σ ≤ X := l19_vol_ge N ℓ hℓ D R σ B s (fun u hu => hmax u hu)
    have hlin : vol a = X + cut a * (a - s) := l19_vol_lin N ℓ D R σ B (hballR a) a s
    have hya := hyp a ha le_rfl
    have hvolpos : 0 < vol a := by
      have := l19_vol_ge N ℓ hℓ D R σ B a (fun u hu => (hlt a u hu).le); simp only [hvol]; linarith
    have hlog : Real.log X + ε * (a - s) < Real.log (vol a) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hvolpos (by linarith : 0 < X))
      rw [Real.log_div hvolpos.ne' (by linarith), inv_div] at h1
      have h2 : 1 - X / vol a = cut a * (a - s) / vol a := by
        field_simp; linarith [hlin]
      have h3 : ε * (a - s) < cut a * (a - s) / vol a := by
        rw [lt_div_iff₀ hvolpos]
        nlinarith [mul_lt_mul_of_pos_right hya (sub_pos.2 hsa)]
      linarith
    rcases hs0.lt_or_eq with hspos | hs0'
    · have hsub : l19ball D R s ⊆ B := fun v hv => (hmemball a v).2 ⟨hballR s hv,
        lt_trans ((hmemball s v).1 hv).2 (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hsa, ha⟩)⟩
      have hwn : w ∉ l19ball D R s := fun h => by have := hlt s w h; linarith
      have hcard : (l19ball D R s).card < k := hk ▸ Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hwn (h ▸ hw)⟩)
      have hIH := ih _ hcard s rfl hspos (fun a' h1 h2 => hyp a' h1 (h2.trans hsa.le))
      have hnew : ∀ u ∈ B, u ∉ l19ball D R s → (D u).toReal = s := by
        intro u hu hun
        apply le_antisymm (hmax u hu)
        have h2 : ENNReal.ofReal s ≤ D u := by
          by_contra h; exact hun ((hmemball s u).2 ⟨hballR a hu, lt_of_not_ge h⟩)
        exact (ENNReal.ofReal_le_iff_le_toReal (hfin a u hu)).1 h2
      have htj : ∀ u ∈ l19ball D R s, ∀ v ∈ B, v ∉ l19ball D R s → 0 < N.C u v →
          s - (D u).toReal ≤ ℓ u v := by
        intro u hu v hv hvn hC
        have h1 := htri u (hballR s hu) v (hballR a hv) hC
        have h4 := l19_toReal_tri (hℓ u v) (hfin s u hu) h1
        rw [hnew v hv hvn] at h4; linarith
      have hjump : vol s ≤ X := l19_vol_jump N ℓ hℓ D R σ _ B s hsub hnew htj (by
        intro u hu v hv hvn hC
        rw [N.C_symm] at hC; rw [← hℓs]; exact htj u hu v hv hvn hC)
      have hvs : 0 < vol s := by
        have := l19_vol_ge N ℓ hℓ D R σ (l19ball D R s) s (fun u hu => (hlt s u hu).le)
        simp only [hvol]; linarith
      have : Real.log (vol s) ≤ Real.log X := Real.log_le_log hvs hjump
      linarith
    · have : Real.log σ ≤ Real.log X := Real.log_le_log hσ hX
      rw [← hs0'] at hlog; linarith
  by_contra hneg
  push_neg at hneg
  have hyp : ∀ a', 0 < a' → a' ≤ Δ → ε * vol a' < cut a' := fun a' h1 h2 =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hV4 a' h1) hεnn) (hneg a' h1 h2)
  have h1 := claim _ Δ rfl hΔ hyp
  have h2 : vol Δ ≤ σ + l19W N ℓ R := by
    have := hV4 Δ hΔ; have := hWnn (R \ l19ball D R Δ); simp only [hvol]; linarith
  have hvpos : 0 < vol Δ := by
    have := l19_vol_ge N ℓ hℓ D R σ (l19ball D R Δ) Δ (fun u hu => (hlt Δ u hu).le)
    simp only [hvol]; linarith
  have h3 : Real.log (vol Δ) ≤ Real.log (σ + l19W N ℓ R) := Real.log_le_log hvpos h2
  rw [Real.log_div (by linarith [hWnn R]) hσ.ne'] at hε
  linarith

noncomputable def l19D (N : Network V) (ℓ : V → V → ℝ) (R : Finset V) (c y : V) : ENNReal :=
  ⨅ (p : N.graph.Walk c y) (_ : ∀ z ∈ p.support, z ∈ R), ENNReal.ofReal (walkLen ℓ p)

lemma l19_walkLen_nonneg (N : Network V) {ℓ : V → V → ℝ} (hℓ : ∀ u v, 0 ≤ ℓ u v)
    {u v : V} (p : N.graph.Walk u v) : 0 ≤ walkLen ℓ p := by
  unfold walkLen
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact hℓ _ _

lemma l19_walkLen_add (N : Network V) (d : V → V → ℝ) (α : ℝ) {u v : V}
    (p : N.graph.Walk u v) :
    walkLen (fun x y => d x y + α) p = walkLen d p + α * p.length := by
  unfold walkLen
  rw [← SimpleGraph.Walk.length_darts]
  induction p.darts with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring

lemma l19_D_self (N : Network V) (ℓ : V → V → ℝ) (R : Finset V) (c : V) (hc : c ∈ R) :
    l19D N ℓ R c c = 0 := by
  apply le_antisymm _ bot_le
  refine (iInf₂_le (SimpleGraph.Walk.nil : N.graph.Walk c c) (by simpa using hc)).trans ?_
  simp [walkLen]

lemma l19_D_tri (N : Network V) (ℓ : V → V → ℝ) (R : Finset V) (c : V)
    (u v : V) (hv : v ∈ R) (huv : 0 < N.C u v) :
    l19D N ℓ R c v ≤ l19D N ℓ R c u + ENNReal.ofReal (ℓ u v) := by
  have hadj : N.graph.Adj u v := by
    unfold Network.graph
    rw [SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl huv⟩
    rintro rfl
    rw [N.C_self] at huv
    exact lt_irrefl _ huv
  unfold l19D
  simp only [ENNReal.iInf_add]
  refine le_iInf fun p => le_iInf fun hp => ?_
  refine (iInf₂_le (p.concat hadj) ?_).trans ?_
  · intro z hz
    simp only [SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hp z hz
    · exact hv
  · have : walkLen ℓ (p.concat hadj) = walkLen ℓ p + ℓ u v := by
      simp [walkLen, SimpleGraph.Walk.darts_concat]
    rw [this]
    exact ENNReal.ofReal_add_le

lemma l19_D_prefix (N : Network V) (ℓ : V → V → ℝ) (hℓ : ∀ u v, 0 ≤ ℓ u v) (R : Finset V)
    (c y : V) (p : N.graph.Walk c y) (hp : ∀ z ∈ p.support, z ∈ R) (z : V)
    (hz : z ∈ p.support) : l19D N ℓ R c z ≤ ENNReal.ofReal (walkLen ℓ p) := by
  set q := p.takeUntil z hz
  have hsub : ∀ x ∈ q.support, x ∈ R := fun x hx =>
    hp x (SimpleGraph.Walk.support_takeUntil_subset_support p hz hx)
  refine (iInf₂_le q hsub).trans (ENNReal.ofReal_le_ofReal ?_)
  have hspec := SimpleGraph.Walk.take_spec p hz
  have : walkLen ℓ ((p.takeUntil z hz).append (p.dropUntil z hz)) =
      walkLen ℓ q + walkLen ℓ (p.dropUntil z hz) := by
    simp only [walkLen, SimpleGraph.Walk.darts_append, List.map_append, List.sum_append, q]
  rw [hspec] at this
  rw [this]
  linarith [l19_walkLen_nonneg N hℓ (p.dropUntil z hz)]

noncomputable def l19cross (N : Network V) (R : Finset V) (P : Finpartition R) : ℝ :=
  (1/2) * ∑ u ∈ R, ∑ v ∈ R, if P.part u = P.part v then 0 else N.C u v

lemma l19_region (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (α : ℝ)
    (hα : 0 < α) (R : Finset V) (c : V) (hc : c ∈ R) (σ Δ ε : ℝ) (hσ : 0 < σ) (hΔ : 0 < Δ)
    (hε : Real.log ((σ + l19W N (fun x y => d x y + α) R) / σ) ≤ ε * Δ) :
    ∃ B : Finset V, c ∈ B ∧ B ⊆ R ∧ HasRadii N d B (Δ / α) Δ ∧
      l19cut N R B ≤ ε * (σ + l19W N (fun x y => d x y + α) R -
        l19W N (fun x y => d x y + α) (R \ B)) := by
  set ℓ : V → V → ℝ := fun x y => d x y + α with hℓdef
  have hℓ : ∀ u v, 0 ≤ ℓ u v := fun u v => by simp only [hℓdef]; linarith [hd.1 u v]
  have hℓs : ∀ u v, ℓ u v = ℓ v u := fun u v => by simp only [hℓdef]; rw [hd.2]
  obtain ⟨a, ha, haΔ, hcut⟩ := l19_grow N ℓ hℓ hℓs (l19D N ℓ R c) R c hc
    (l19_D_self N ℓ R c hc) (fun u _ v hv h => l19_D_tri N ℓ R c u v hv h) σ Δ ε hσ hΔ hε
  have hcB : c ∈ l19ball (l19D N ℓ R c) R a := by
    unfold l19ball; rw [Finset.mem_filter, l19_D_self N ℓ R c hc]
    exact ⟨hc, ENNReal.ofReal_pos.2 ha⟩
  refine ⟨l19ball (l19D N ℓ R c) R a, hcB, Finset.filter_subset _ _, ⟨c, hcB, fun y hy => ?_⟩, hcut⟩
  unfold l19ball at hy
  rw [Finset.mem_filter] at hy
  obtain ⟨_, hDy⟩ := hy
  have hDy' := hDy
  unfold l19D at hDy'
  rw [iInf_lt_iff] at hDy'
  obtain ⟨p, hp⟩ := hDy'
  rw [iInf_lt_iff] at hp
  obtain ⟨hpR, hpl⟩ := hp
  have hpl' : walkLen ℓ p < a := (ENNReal.ofReal_lt_ofReal_iff ha).1 hpl
  have hsplit := l19_walkLen_add N d α p
  have hdnn := l19_walkLen_nonneg N hd.1 p
  have hlen0 : (0:ℝ) ≤ p.length := Nat.cast_nonneg _
  refine ⟨p, ?_, ?_, ?_⟩
  · intro z hz
    unfold l19ball
    rw [Finset.mem_filter]
    exact ⟨hpR z hz, (l19_D_prefix N ℓ hℓ R c y p hpR z hz).trans_lt hpl⟩
  · rw [le_div_iff₀ hα]
    have : walkLen ℓ p = walkLen d p + α * p.length := hsplit
    nlinarith
  · have : walkLen ℓ p = walkLen d p + α * p.length := hsplit
    nlinarith

lemma l19_part (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (α : ℝ)
    (hα : 0 < α) (σ Δ ε : ℝ) (hσ : 0 < σ) (hΔ : 0 < Δ) (hεnn : 0 ≤ ε)
    (hε : ∀ R : Finset V, Real.log ((σ + l19W N (fun x y => d x y + α) R) / σ) ≤ ε * Δ) :
    ∀ n, ∀ R : Finset V, R.card = n → R.Nonempty → ∃ P : Finpartition R,
      (∀ S ∈ P.parts, HasRadii N d S (Δ / α) Δ) ∧
      l19cross N R P ≤ ε * (((R.card : ℝ) - 1) * σ + l19W N (fun x y => d x y + α) R) := by
  set ℓ : V → V → ℝ := fun x y => d x y + α with hℓdef
  have hℓ : ∀ u v, 0 ≤ ℓ u v := fun u v => by simp only [hℓdef]; linarith [hd.1 u v]
  have hWnn : ∀ S : Finset V, 0 ≤ l19W N ℓ S := fun S => by
    unfold l19W; apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg _ _) (hℓ _ _)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hRn hR
  obtain ⟨c, hc⟩ := hR
  obtain ⟨B, hcB, hBR, hrad, hcut⟩ := l19_region N d hd α hα R c hc σ Δ ε hσ hΔ (hε R)
  have hR1 : (1:ℝ) ≤ R.card := by exact_mod_cast Finset.card_pos.2 ⟨c, hc⟩
  by_cases hRB : R \ B = ∅
  · have hBeq : B = R := Finset.Subset.antisymm hBR (Finset.sdiff_eq_empty_iff_subset.1 hRB)
    refine ⟨Finpartition.indiscrete (Finset.nonempty_iff_ne_empty.1 ⟨c, hc⟩), ?_, ?_⟩
    · intro S hS
      have : S = R := Finset.mem_singleton.1 hS
      rw [this, ← hBeq]; exact hrad
    · have h0 : l19cross N R (Finpartition.indiscrete (Finset.nonempty_iff_ne_empty.1 ⟨c, hc⟩)) = 0 := by
        unfold l19cross
        rw [Finset.sum_eq_zero, mul_zero]
        intro u hu
        apply Finset.sum_eq_zero
        intro v hv
        rw [if_pos]
        rw [Finpartition.part_eq_of_mem _ (Finset.mem_singleton_self R) hu,
          Finpartition.part_eq_of_mem _ (Finset.mem_singleton_self R) hv]
      rw [h0]
      apply mul_nonneg hεnn
      nlinarith [hWnn R]
  · have hR'ne : (R \ B).Nonempty := Finset.nonempty_iff_ne_empty.2 hRB
    have hcardeq := Finset.card_sdiff_add_card_eq_card hBR
    have hBpos : 0 < B.card := Finset.card_pos.2 ⟨c, hcB⟩
    have hlt : (R \ B).card < n := by omega
    obtain ⟨P', hP'rad, hP'cut⟩ := ih _ hlt (R \ B) rfl hR'ne
    have hBne : B ≠ ⊥ := Finset.nonempty_iff_ne_empty.1 ⟨c, hcB⟩
    let P : Finpartition R := P'.extend hBne Finset.sdiff_disjoint
      (Finset.sdiff_union_of_subset hBR)
    have hparts : P.parts = insert B P'.parts := rfl
    have hpartB : ∀ u ∈ B, P.part u = B := fun u hu =>
      P.part_eq_of_mem (by rw [hparts]; exact Finset.mem_insert_self _ _) hu
    have hpartR' : ∀ u ∈ R \ B, P.part u = P'.part u := fun u hu =>
      P.part_eq_of_mem (by rw [hparts]; exact Finset.mem_insert_of_mem (P'.part_mem.2 hu))
        (P'.mem_part hu)
    refine ⟨P, ?_, ?_⟩
    · intro S hS
      rw [hparts, Finset.mem_insert] at hS
      rcases hS with rfl | hS
      · exact hrad
      · exact hP'rad S hS
    · have hpt : ∀ u ∈ R, ∀ v ∈ R, (if P.part u = P.part v then 0 else N.C u v) ≤
          (if u ∈ B ∧ v ∉ B then N.C u v else 0) + (if v ∈ B ∧ u ∉ B then N.C u v else 0) +
          (if u ∉ B ∧ v ∉ B then (if P'.part u = P'.part v then 0 else N.C u v) else 0) := by
        intro u hu v hv
        have hC := N.C_nonneg u v
        have hite : (if P.part u = P.part v then 0 else N.C u v) ≤ N.C u v := by
          split_ifs <;> linarith
        by_cases hu' : u ∈ B <;> by_cases hv' : v ∈ B
        · rw [if_pos (by rw [hpartB u hu', hpartB v hv'])]; simp [hu', hv']
        · simpa [hu', hv'] using hite
        · simpa [hu', hv'] using hite
        · have h1 := hpartR' u (Finset.mem_sdiff.2 ⟨hu, hu'⟩)
          have h2 := hpartR' v (Finset.mem_sdiff.2 ⟨hv, hv'⟩)
          simp [hu', hv', h1, h2]
      have hs := Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => hpt u hu v hv
      simp only [Finset.sum_add_distrib] at hs
      rw [l19_sum_ind R B hBR (fun u v => N.C u v),
        Finset.sum_comm (f := fun u v => if v ∈ B ∧ u ∉ B then N.C u v else 0),
        l19_sum_ind R B hBR (fun v u => N.C u v), l19_cut_symm,
        l19_sum_ind2 R B (fun u v => if P'.part u = P'.part v then 0 else N.C u v)] at hs
      have hcutdef : ∑ u ∈ B, ∑ v ∈ R \ B, N.C u v = l19cut N R B := rfl
      rw [hcutdef] at hs
      have hc1 : (((R \ B).card : ℝ)) ≤ R.card - 1 := by
        have : ((R \ B).card : ℝ) + B.card = R.card := by exact_mod_cast hcardeq
        have : (1:ℝ) ≤ B.card := by exact_mod_cast hBpos
        linarith
      unfold l19cross at hP'cut ⊢
      have hεσ : ε * (((R \ B).card : ℝ) - 1) * σ ≤ ε * ((R.card : ℝ) - 1 - 1) * σ := by
        apply mul_le_mul_of_nonneg_right _ hσ.le
        apply mul_le_mul_of_nonneg_left _ hεnn; linarith
      nlinarith

lemma l19_main {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (Δ : ℝ) (hΔ : 0 < Δ) (hW : 0 < totalWeight N d) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, HasRadii N d S (Δ * totalCap N / totalWeight N d) Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d * Real.log (Fintype.card V : ℝ) / Δ := by
  set W := totalWeight N d with hWdef
  set Ct := totalCap N with hCtdef
  have hCt : 0 < Ct := by
    have hne : ∑ u, ∑ v, N.C u v * d u v ≠ 0 := by
      intro h; rw [hWdef, totalWeight, h, mul_zero] at hW; exact lt_irrefl _ hW
    obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
    have hCuv : 0 < N.C u v := lt_of_le_of_ne (N.C_nonneg _ _)
      (fun h => hv (by rw [← h, zero_mul]))
    have h1 : N.C u v ≤ ∑ v', N.C u v' := Finset.single_le_sum
      (f := fun v' => N.C u v') (fun _ _ => N.C_nonneg _ _) (Finset.mem_univ v)
    have h2 : ∑ v', N.C u v' ≤ ∑ u', ∑ v', N.C u' v' := Finset.single_le_sum
      (f := fun u' => ∑ v', N.C u' v')
      (fun _ _ => Finset.sum_nonneg fun _ _ => N.C_nonneg _ _) (Finset.mem_univ u)
    rw [hCtdef, totalCap]; linarith
  set α := W / Ct with hαdef
  have hα : 0 < α := div_pos hW hCt
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set σ := 2 * W / (n - 1) with hσdef
  have hσ : 0 < σ := div_pos (by linarith) (by linarith)
  have hn1 : n - 1 ≠ 0 := by linarith
  set ε := Real.log n / Δ with hεdef
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hεnn : 0 ≤ ε := div_nonneg hlogn.le hΔ.le
  set ℓ : V → V → ℝ := fun x y => d x y + α with hℓdef
  have hℓ : ∀ u v, 0 ≤ ℓ u v := fun u v => by simp only [hℓdef]; linarith [hd.1 u v]
  have hWuniv : l19W N ℓ Finset.univ = 2 * W := by
    unfold l19W
    simp only [hℓdef, mul_add, Finset.sum_add_distrib]
    have : ∑ u, ∑ v, N.C u v * α = α * ∑ u, ∑ v, N.C u v := by
      rw [Finset.mul_sum]; congr 1; ext u; rw [Finset.mul_sum]; congr 1; ext v; ring
    rw [this]
    have hW' : W = (1/2) * ∑ u, ∑ v, N.C u v * d u v := rfl
    have hC' : Ct = (1/2) * ∑ u, ∑ v, N.C u v := rfl
    have : α * Ct = W := by rw [hαdef]; field_simp
    nlinarith
  have hWle : ∀ R : Finset V, l19W N ℓ R ≤ l19W N ℓ Finset.univ := by
    intro R
    unfold l19W
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc ∑ u ∈ R, ∑ v ∈ R, N.C u v * ℓ u v ≤ ∑ u ∈ R, ∑ v, N.C u v * ℓ u v :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun v _ _ => mul_nonneg (N.C_nonneg _ _) (hℓ _ _))
      _ ≤ ∑ u, ∑ v, N.C u v * ℓ u v := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun u _ _ => Finset.sum_nonneg fun v _ =>
              mul_nonneg (N.C_nonneg _ _) (hℓ _ _))
  have hWnn : ∀ S : Finset V, 0 ≤ l19W N ℓ S := fun S => by
    unfold l19W; apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg _ _) (hℓ _ _)
  have hε : ∀ R : Finset V, Real.log ((σ + l19W N ℓ R) / σ) ≤ ε * Δ := by
    intro R
    have h1 : (σ + l19W N ℓ R) / σ ≤ n := by
      rw [div_le_iff₀ hσ]
      have := hWle R
      rw [hWuniv] at this
      have : 2 * W = (n - 1) * σ := by rw [hσdef]; field_simp
      nlinarith
    have h2 : 0 < (σ + l19W N ℓ R) / σ := div_pos (by linarith [hWnn R]) hσ
    rw [hεdef, div_mul_cancel₀ _ hΔ.ne']
    exact Real.log_le_log h2 h1
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [Finset.univ_nonempty_iff]; exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨P, hPrad, hPcut⟩ := l19_part N d hd α hα σ Δ ε hσ hΔ hεnn hε _ Finset.univ rfl hne
  refine ⟨P, ?_, ?_⟩
  · intro S hS
    have := hPrad S hS
    rwa [hαdef, div_div_eq_mul_div] at this
  · have hcr : crossCap N P = l19cross N Finset.univ P := rfl
    rw [hcr]
    refine hPcut.trans (le_of_eq ?_)
    rw [Finset.card_univ, ← hndef, hWuniv, hσdef, hεdef]
    field_simp
    ring

theorem lemma_19_core {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (Δ : ℝ) (hΔ : 0 < Δ) (hW : 0 < totalWeight N d) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, HasRadii N d S (Δ * totalCap N / totalWeight N d) Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d *
        Real.logb 2 (Fintype.card V : ℝ) / Δ := by
  obtain ⟨P, h1, h2⟩ := l19_main N hn d hd Δ hΔ hW
  refine ⟨P, h1, h2.trans ?_⟩
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlogn : 0 < Real.log (Fintype.card V : ℝ) := Real.log_pos (by linarith)
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : Real.log (Fintype.card V : ℝ) ≤ Real.logb 2 (Fintype.card V : ℝ) := by
    rw [Real.logb, le_div_iff₀ hl2']; nlinarith
  apply div_le_div_of_nonneg_right _ hΔ.le
  exact mul_le_mul_of_nonneg_left this (by linarith)

lemma l20_minCut_le (N : Network V) (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty) :
    minCut N * U.card * Uᶜ.card ≤ cutCap N U := by
  have hcnn : 0 ≤ cutCap N U :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => N.C_nonneg _ _
  have h : minCut N ≤ ratioCost N U := by
    unfold minCut
    refine ciInf_le (f := fun U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} => ratioCost N U.1)
      ⟨0, ?_⟩ ⟨U, hU, hUc⟩
    rintro _ ⟨W, rfl⟩
    unfold ratioCost
    apply div_nonneg _ (by positivity)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => N.C_nonneg _ _
  unfold ratioCost at h
  have hpos : (0:ℝ) < U.card * Uᶜ.card := by
    have h1 : (0:ℝ) < U.card := by exact_mod_cast hU.card_pos
    have h2 : (0:ℝ) < Uᶜ.card := by exact_mod_cast hUc.card_pos
    positivity
  rw [le_div_iff₀ hpos] at h; linarith

lemma l20_minCut_pos (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N) :
    0 < minCut N := by
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hvc : ({v}ᶜ : Finset V).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton]; omega
  haveI : Nonempty {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} :=
    ⟨⟨{v}, Finset.singleton_nonempty v, hvc⟩⟩
  obtain ⟨U, hU⟩ := exists_eq_ciInf_of_finite
    (f := fun U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} => ratioCost N U.1)
  unfold minCut; rw [← hU]
  unfold ratioCost
  have h1 : (0:ℝ) < U.1.card := by exact_mod_cast U.2.1.card_pos
  have h2 : (0:ℝ) < U.1ᶜ.card := by exact_mod_cast U.2.2.card_pos
  exact div_pos (hconn _ U.2.1 U.2.2) (by positivity)

theorem corollary_20_core {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hW : 0 < totalWeight N d)
    (hWS : totalWeight N d ≤ minCut N /
      (36 * Real.logb 2 (Fintype.card V : ℝ))) :
    ∃ T : Finset V,
      2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ) ∧
      HasRadii N d T
        (totalCap N / (2 * totalWeight N d * (Fintype.card V : ℝ) ^ 2))
        (1 / (2 * (Fintype.card V : ℝ) ^ 2)) := by
  have hS := l20_minCut_pos N hn hconn
  have hn2 : (2:ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set Δ : ℝ := 1 / (2 * n ^ 2) with hΔdef
  have hΔ : 0 < Δ := by positivity
  obtain ⟨P, hrad, hcross⟩ := l19_main N hn d hd Δ hΔ hW
  have hρ : Δ * totalCap N / totalWeight N d = totalCap N / (2 * totalWeight N d * n ^ 2) := by
    rw [hΔdef]; field_simp
  by_contra hneg
  push_neg at hneg
  have hsmall : ∀ S ∈ P.parts, 3 * (S.card : ℝ) < 2 * n := by
    intro S hS'
    by_contra h; push_neg at h
    apply hneg S h
    have := hrad S hS'
    rwa [hρ] at this
  have hexU : ∃ U : Finset V, (∀ u ∈ U, P.part u ⊆ U) ∧ n ≤ 3 * (U.card : ℝ) ∧
      3 * (U.card : ℝ) ≤ 2 * n := by
    by_cases hbig : ∃ S ∈ P.parts, n ≤ 3 * (S.card : ℝ)
    · obtain ⟨S, hS', hSn⟩ := hbig
      refine ⟨S, fun u hu => (P.part_eq_of_mem hS' hu).le, hSn, (hsmall S hS').le⟩
    · push_neg at hbig
      let C := (Finset.univ : Finset (Finset V)).filter
        (fun U => (∀ u ∈ U, P.part u ⊆ U) ∧ 3 * (U.card : ℝ) ≤ 2 * n)
      have hCne : C.Nonempty := ⟨∅, by
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by simp, by simp; positivity⟩⟩
      obtain ⟨U, hU, hmax⟩ := C.exists_max_image Finset.card hCne
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hU
      refine ⟨U, hU.1, ?_, hU.2⟩
      by_contra hlt; push_neg at hlt
      have hv : ∃ v, v ∉ U := by
        by_contra h; push_neg at h
        have hU' : U = Finset.univ := Finset.eq_univ_of_forall h
        rw [hU', Finset.card_univ] at hlt; linarith
      obtain ⟨v, hv⟩ := hv
      have hvp : v ∈ P.part v := P.mem_part (Finset.mem_univ v)
      have hpm : P.part v ∈ P.parts := P.part_mem.2 (Finset.mem_univ v)
      have hcl : ∀ w ∈ U ∪ P.part v, P.part w ⊆ U ∪ P.part v := by
        intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · exact (hU.1 w hw).trans Finset.subset_union_left
        · rw [P.part_eq_of_mem hpm hw]; exact Finset.subset_union_right
      have hcardU' : ((U ∪ P.part v).card : ℝ) ≤ U.card + (P.part v).card := by
        exact_mod_cast Finset.card_union_le _ _
      have hpv := hbig (P.part v) hpm
      have hU'C : U ∪ P.part v ∈ C := by
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hcl, by linarith⟩
      have h1 := hmax _ hU'C
      have h2 : U.card < (U ∪ P.part v).card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, fun h =>
          hv (h ▸ Finset.mem_union_right _ hvp)⟩)
      omega
  obtain ⟨U, hUcl, hU1, hU2⟩ := hexU
  have hUne : U.Nonempty := by
    rw [← Finset.card_pos]; have : (0:ℝ) < U.card := by linarith
    exact_mod_cast this
  have hUcard : ((Uᶜ).card : ℝ) = n - U.card := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ U)]
  have hUcne : Uᶜ.Nonempty := by
    rw [← Finset.card_pos]; have : (0:ℝ) < (Uᶜ).card := by rw [hUcard]; linarith
    exact_mod_cast this
  have hcutU := l20_minCut_le N U hUne hUcne
  have hge : cutCap N U ≤ crossCap N P := by
    have hpt : ∀ u ∈ (Finset.univ : Finset V), ∀ v ∈ (Finset.univ : Finset V),
        (if u ∈ U ∧ v ∉ U then N.C u v else 0) + (if v ∈ U ∧ u ∉ U then N.C u v else 0) ≤
        (if P.part u = P.part v then 0 else N.C u v) := by
      intro u _ v _
      have hC := N.C_nonneg u v
      by_cases hu : u ∈ U <;> by_cases hv : v ∈ U
      · simp [hu, hv]; split_ifs <;> linarith
      · have hne : P.part u ≠ P.part v := fun h =>
          hv (hUcl u hu (h ▸ P.mem_part (Finset.mem_univ v)))
        simp [hu, hv, hne]
      · have hne : P.part u ≠ P.part v := fun h =>
          hu (hUcl v hv (h.symm ▸ P.mem_part (Finset.mem_univ u)))
        simp [hu, hv, hne]
      · simp [hu, hv]; split_ifs <;> linarith
    have hs := Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => hpt u hu v hv
    simp only [Finset.sum_add_distrib] at hs
    rw [l19_sum_ind Finset.univ U (Finset.subset_univ U) (fun u v => N.C u v),
      Finset.sum_comm (f := fun u v => if v ∈ U ∧ u ∉ U then N.C u v else 0),
      l19_sum_ind Finset.univ U (Finset.subset_univ U) (fun v u => N.C u v),
      l19_cut_symm] at hs
    have hcc : cutCap N U = l19cut N Finset.univ U := by
      unfold cutCap l19cut; rw [Finset.compl_eq_univ_sdiff]
    have hcc' : ∑ u ∈ U, ∑ v ∈ Finset.univ \ U, N.C u v = l19cut N Finset.univ U := rfl
    rw [hcc'] at hs
    unfold crossCap
    rw [hcc]; linarith
  -- numerics
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlb : Real.log n < Real.logb 2 n := by
    rw [Real.logb, lt_div_iff₀ hl2']; nlinarith
  have hlbpos : 0 < Real.logb 2 n := lt_trans hlogn hlb
  have hWS' : 36 * totalWeight N d * Real.logb 2 n ≤ minCut N := by
    rw [le_div_iff₀ (by positivity)] at hWS; linarith
  have hcr : crossCap N P ≤ 8 * n ^ 2 * totalWeight N d * Real.log n := by
    refine hcross.trans (le_of_eq ?_)
    have e : Real.log (Fintype.card V : ℝ) = Real.log n := rfl
    rw [hΔdef]; field_simp; rw [e]; ring
  have hx : 2 * n ^ 2 ≤ 9 * ((U.card : ℝ) * (Uᶜ).card) := by
    rw [hUcard]; nlinarith
  have h1 : 8 * n ^ 2 * totalWeight N d * Real.log n <
      8 * n ^ 2 * totalWeight N d * Real.logb 2 n := by
    apply mul_lt_mul_of_pos_left hlb; positivity
  have h2 : 2 * n ^ 2 * minCut N ≤ 9 * (minCut N * U.card * (Uᶜ).card) := by
    nlinarith
  nlinarith

end LeightonRao.ShortPaths

open LeightonRao.ShortPaths


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hW : 0 < totalWeight N d)
    (hWS : totalWeight N d ≤ minCut N /
      (36 * Real.logb 2 (Fintype.card V : ℝ))) :
    ∃ T : Finset V,
      2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ) ∧
      HasRadii N d T
        (totalCap N / (2 * totalWeight N d * (Fintype.card V : ℝ) ^ 2))
        (1 / (2 * (Fintype.card V : ℝ) ^ 2)) := by
  exact corollary_20_core N hn hconn d hd hW hWS
