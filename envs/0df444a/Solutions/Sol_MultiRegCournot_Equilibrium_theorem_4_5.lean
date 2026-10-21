-- Prove2me | solution 1 for MultiRegCournot.Equilibrium.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T18:54:05.637819+00:00
-- url     : https://prove2.me/submissions/d8ad95cd-b5f5-4536-8513-bc3da8f170a0

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

open MultiRegCournot.Equilibrium

namespace MRCSol

/-! ## Properties of an inverse demand function -/

structure GoodP (p : ℝ → ℝ) : Prop where
  diff : Differentiable ℝ p
  cont_d : Continuous (deriv p)
  anti : StrictAntiOn p (Set.Ici 0)
  conc : ConcaveOn ℝ (Set.Ici 0) p

lemma goodP_of {p : ℝ → ℝ} (h1 : ContDiff ℝ 2 p) (h2 : StrictAntiOn p (Set.Ici 0))
    (h3 : ConcaveOn ℝ (Set.Ici 0) p) : GoodP p :=
  ⟨h1.differentiable (by norm_num), h1.continuous_deriv (by norm_num), h2, h3⟩

variable {p : ℝ → ℝ}

lemma GoodP.tangent (hp : GoodP p) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p y ≤ p x + deriv p x * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have := hp.conc.slope_le_deriv (x := x) (y := y) (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) h
      (hp.diff x)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hp.conc.deriv_le_slope (x := y) (y := x) (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) h
      (hp.diff x)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith

lemma GoodP.lt_of_pos (hp : GoodP p) {x : ℝ} (hx : 0 < x) : p x < p 0 :=
  hp.anti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx

lemma GoodP.le_zero (hp : GoodP p) {x : ℝ} (hx : 0 ≤ x) : p x ≤ p 0 := by
  rcases hx.lt_or_eq with h | h
  · exact (hp.lt_of_pos h).le
  · rw [← h]

lemma GoodP.anti_le (hp : GoodP p) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : p y ≤ p x := by
  rcases hxy.lt_or_eq with h | h
  · exact (hp.anti (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxy)) h).le
  · rw [h]

lemma GoodP.deriv_neg (hp : GoodP p) {x : ℝ} (hx : 0 < x) : deriv p x < 0 := by
  have h1 := hp.tangent hx.le (le_refl 0)
  have h2 := hp.lt_of_pos hx
  by_contra h
  push_neg at h
  nlinarith

lemma GoodP.deriv_anti (hp : GoodP p) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    deriv p y ≤ deriv p x :=
  hp.conc.antitoneOn_deriv (fun z _ => hp.diff z) (Set.mem_Ici.mpr hx)
    (Set.mem_Ici.mpr (hx.trans hxy)) hxy

lemma GoodP.deriv_nonpos (hp : GoodP p) {x : ℝ} (hx : 0 ≤ x) : deriv p x ≤ 0 := by
  have hd := ((hp.diff x).hasDerivAt).tendsto_slope_zero_right
  refine le_of_tendsto hd ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  have : p (x + t) < p x := hp.anti (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (by linarith))
    (by linarith)
  simp only [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht'.le) (by linarith)

lemma GoodP.exists_large (hp : GoodP p) (b : ℝ) : ∃ M > 0, p M < b := by
  have hd := hp.deriv_neg (x := 1) one_pos
  have hD : 0 < -deriv p 1 := by linarith
  set A := |p 1 - b| / (-deriv p 1) with hA
  have hA0 : 0 ≤ A := div_nonneg (abs_nonneg _) hD.le
  refine ⟨2 + A, by linarith, ?_⟩
  have ht := hp.tangent (x := 1) (y := 2 + A) zero_le_one (by linarith)
  have hne : -deriv p 1 ≠ 0 := by linarith
  have h1 : deriv p 1 * A = -|p 1 - b| := by
    rw [hA, mul_div_assoc', div_eq_iff hne]; ring
  have h2 : deriv p 1 * (2 + A - 1) = deriv p 1 + deriv p 1 * A := by ring
  rw [h2, h1] at ht
  have := le_abs_self (p 1 - b)
  linarith

/-! ## Single-region complementarity solutions -/

variable {N : ℕ}

/-- `q` solves the complementarity system of one region with effective costs `b`. -/
def RegSol (p : ℝ → ℝ) (b : Fin N → ℝ) (q : Fin N → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ ∀ j, deriv p (∑ k, q k) * q j + p (∑ k, q k) - b j ≤ 0 ∧
     q j * (deriv p (∑ k, q k) * q j + p (∑ k, q k) - b j) = 0

noncomputable def phi (p : ℝ → ℝ) (b X : ℝ) : ℝ := max 0 (p X - b) / (-deriv p X)

lemma phi_nonneg (hp : GoodP p) {b X : ℝ} (hX : 0 < X) : 0 ≤ phi p b X := by
  unfold phi
  have := hp.deriv_neg hX
  exact div_nonneg (le_max_left _ _) (by linarith)

lemma phi_anti_X (hp : GoodP p) {b X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    phi p b Y ≤ phi p b X := by
  unfold phi
  have h1 := hp.deriv_neg hX
  have h2 := hp.deriv_anti hX.le hXY
  have h3 := hp.anti_le hX.le hXY
  apply div_le_div₀ (le_max_left _ _) (max_le_max le_rfl (by linarith)) (by linarith)
    (by linarith)

lemma phi_anti_b (hp : GoodP p) {b b' X : ℝ} (hX : 0 < X) (hb : b ≤ b') :
    phi p b' X ≤ phi p b X := by
  unfold phi
  have h1 := hp.deriv_neg hX
  exact div_le_div_of_nonneg_right (max_le_max le_rfl (by linarith)) (by linarith)

lemma phi_strict_b (hp : GoodP p) {b b' X : ℝ} (hX : 0 < X) (hb : b < b') (hpos : b < p X) :
    phi p b' X < phi p b X := by
  unfold phi
  have h1 := hp.deriv_neg hX
  apply div_lt_div_of_pos_right _ (by linarith)
  rw [max_eq_right (a := (0:ℝ)) (b := p X - b) (by linarith)]
  exact max_lt (by linarith) (by linarith)

lemma phi_diff (hp : GoodP p) {b t X : ℝ} (hX : 0 < X) (ht : 0 ≤ t) :
    phi p b X - phi p (b + t) X ≤ t / (-deriv p X) := by
  unfold phi
  have h1 := hp.deriv_neg hX
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (by linarith)
  rcases le_total (p X - b) 0 with h | h
  · rw [max_eq_left h, max_eq_left (by linarith)]; linarith
  · rw [max_eq_right h]
    have := le_max_right 0 (p X - (b + t))
    linarith

section sol
variable {b b' q q' : Fin N → ℝ}

lemma RegSol.nonneg (h : RegSol p b q) (j : Fin N) : 0 ≤ q j := h.1 j

lemma RegSol.sum_nonneg (h : RegSol p b q) : 0 ≤ ∑ k, q k :=
  Finset.sum_nonneg (fun j _ => h.1 j)

lemma RegSol.le_sum (h : RegSol p b q) (j : Fin N) : q j ≤ ∑ k, q k :=
  Finset.single_le_sum (fun k _ => h.1 k) (Finset.mem_univ j)

lemma RegSol.eq_phi (hp : GoodP p) (h : RegSol p b q) (hX : 0 < ∑ k, q k) (j : Fin N) :
    q j = phi p (b j) (∑ k, q k) := by
  have hd := hp.deriv_neg hX
  obtain ⟨h1, h2⟩ := h.2 j
  unfold phi
  rcases (h.1 j).lt_or_eq with hq | hq
  · have h3 : deriv p (∑ k, q k) * q j + p (∑ k, q k) - b j = 0 := by
      rcases mul_eq_zero.mp h2 with h4 | h4
      · linarith
      · exact h4
    have h5 : 0 < p (∑ k, q k) - b j := by nlinarith
    rw [max_eq_right h5.le, eq_div_iff (by linarith)]
    linarith
  · rw [← hq] at h1 ⊢
    rw [max_eq_left (by linarith)]
    simp

lemma RegSol.seller (hp : GoodP p) (h : RegSol p b q) {j : Fin N} (hq : 0 < q j) :
    b j < p (∑ k, q k) := by
  have hX : 0 < ∑ k, q k := lt_of_lt_of_le hq (h.le_sum j)
  have hd := hp.deriv_neg hX
  obtain ⟨_, h2⟩ := h.2 j
  have h3 : deriv p (∑ k, q k) * q j + p (∑ k, q k) - b j = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · linarith
    · exact h4
  nlinarith

lemma RegSol.zero_of_sum (h : RegSol p b q) (hX : ∑ k, q k = 0) :
    (∀ j, q j = 0) ∧ ∀ j, p 0 ≤ b j := by
  have hz : ∀ j, q j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h.1 k)).mp hX j (Finset.mem_univ j)
  refine ⟨hz, fun j => ?_⟩
  have := (h.2 j).1
  rw [hX, hz j] at this
  linarith

lemma RegSol.eq_zero_of_le (hp : GoodP p) (h : RegSol p b q) {j : Fin N} (hb : p 0 ≤ b j) :
    q j = 0 := by
  by_contra hne
  have hq : 0 < q j := lt_of_le_of_ne (h.1 j) (Ne.symm hne)
  have h1 := h.seller hp hq
  have hX : 0 < ∑ k, q k := lt_of_lt_of_le hq (h.le_sum j)
  have := hp.lt_of_pos hX
  linarith

/-- Lemma A: raising effective costs lowers the regional total. -/
lemma RegSol.total_anti (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b' q')
    (hb : b ≤ b') : ∑ k, q' k ≤ ∑ k, q k := by
  by_contra hlt
  push_neg at hlt
  have hX' : 0 < ∑ k, q' k := lt_of_le_of_lt h.sum_nonneg hlt
  rcases h.sum_nonneg.lt_or_eq with hX | hX
  · have : ∑ k, q' k ≤ ∑ k, q k := by
      apply Finset.sum_le_sum
      intro j _
      rw [h'.eq_phi hp hX' j, h.eq_phi hp hX j]
      exact (phi_anti_b hp hX' (hb j)).trans (phi_anti_X hp hX hlt.le)
    linarith
  · obtain ⟨_, hz⟩ := h.zero_of_sum hX.symm
    have : ∀ j, q' j = 0 := fun j => h'.eq_zero_of_le hp ((hz j).trans (hb j))
    have : ∑ k, q' k = 0 := Finset.sum_eq_zero (fun j _ => this j)
    linarith

/-- Lemma B: a firm whose cost does not move sells weakly more when others' costs rise. -/
lemma RegSol.other_mono (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b' q')
    (hb : b ≤ b') {j : Fin N} (hj : b j = b' j) : q j ≤ q' j := by
  have hA := h.total_anti hp h' hb
  rcases h'.sum_nonneg.lt_or_eq with hX' | hX'
  · have hX : 0 < ∑ k, q k := lt_of_lt_of_le hX' hA
    rw [h'.eq_phi hp hX' j, h.eq_phi hp hX j, ← hj]
    exact phi_anti_X hp hX' hA
  · obtain ⟨hz, hb'⟩ := h'.zero_of_sum hX'.symm
    rw [hz j, h.eq_zero_of_le hp ((hb' j).trans hj.symm.le)]

/-- Lemma C: with equal regional totals, every firm sells weakly less at higher costs. -/
lemma RegSol.le_of_total_eq (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b' q')
    (hb : b ≤ b') (hX : ∑ k, q' k = ∑ k, q k) (j : Fin N) : q' j ≤ q j := by
  rcases h.sum_nonneg.lt_or_eq with hpos | hz
  · rw [h'.eq_phi hp (hX ▸ hpos) j, h.eq_phi hp hpos j, hX]
    exact phi_anti_b hp hpos (hb j)
  · rw [(h.zero_of_sum hz.symm).1 j, (h'.zero_of_sum (hX.trans hz.symm)).1 j]

lemma RegSol.lt_of_total_eq (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b' q')
    (hX : ∑ k, q' k = ∑ k, q k) {j : Fin N} (hbj : b j < b' j) (hq : 0 < q j) :
    q' j < q j := by
  have hpos : 0 < ∑ k, q k := lt_of_lt_of_le hq (h.le_sum j)
  rw [h'.eq_phi hp (hX ▸ hpos) j, h.eq_phi hp hpos j, hX]
  exact phi_strict_b hp hpos hbj (h.seller hp hq)

lemma RegSol.unique (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b q') : q = q' := by
  have h1 := h.total_anti hp h' le_rfl
  have h2 := h'.total_anti hp h le_rfl
  have hX : ∑ k, q' k = ∑ k, q k := le_antisymm h1 h2
  funext j
  exact le_antisymm (h'.le_of_total_eq hp h le_rfl hX.symm j)
    (h.le_of_total_eq hp h' le_rfl hX j)

/-- Own-cost monotonicity: if only firm `i`'s cost rises, firm `i` sells weakly less. -/
lemma RegSol.own_anti (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b' q')
    (hb : b ≤ b') {i : Fin N} (hother : ∀ j, j ≠ i → b j = b' j) : q' i ≤ q i := by
  have hA := h.total_anti hp h' hb
  have hs : ∑ j ∈ Finset.univ.erase i, q j ≤ ∑ j ∈ Finset.univ.erase i, q' j :=
    Finset.sum_le_sum (fun j hj => h.other_mono hp h' hb (hother j (Finset.ne_of_mem_erase hj)))
  have e1 := Finset.add_sum_erase Finset.univ q (Finset.mem_univ i)
  have e2 := Finset.add_sum_erase Finset.univ q' (Finset.mem_univ i)
  linarith

lemma RegSol.own_strict (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b' q')
    (hb : b ≤ b') {i : Fin N} (hother : ∀ j, j ≠ i → b j = b' j) (hbi : b i < b' i)
    (hq : 0 < q i) : q' i < q i := by
  have hA := h.total_anti hp h' hb
  rcases hA.lt_or_eq with hlt | heq
  · have hs : ∑ j ∈ Finset.univ.erase i, q j ≤ ∑ j ∈ Finset.univ.erase i, q' j :=
      Finset.sum_le_sum (fun j hj =>
        h.other_mono hp h' hb (hother j (Finset.ne_of_mem_erase hj)))
    have e1 := Finset.add_sum_erase Finset.univ q (Finset.mem_univ i)
    have e2 := Finset.add_sum_erase Finset.univ q' (Finset.mem_univ i)
    linarith
  · exact h.lt_of_total_eq hp h' heq hbi hq

/-- Lipschitz-type bound for an own-cost increase. -/
lemma RegSol.own_lip (hp : GoodP p) (h : RegSol p b q) (h' : RegSol p b' q')
    (hb : b ≤ b') {i : Fin N} {t : ℝ} (ht : 0 ≤ t) (hbi : b' i = b i + t)
    (hX : 0 < ∑ k, q k) : q i - q' i ≤ t / (-deriv p (∑ k, q k)) := by
  have hA := h.total_anti hp h' hb
  have hd := hp.deriv_neg hX
  rw [h.eq_phi hp hX i]
  rcases h'.sum_nonneg.lt_or_eq with hX' | hX'
  · rw [h'.eq_phi hp hX' i, hbi]
    have := phi_anti_X (b := b i + t) hp hX' hA
    have := phi_diff (b := b i) hp hX ht
    linarith
  · obtain ⟨hz, hb'⟩ := h'.zero_of_sum hX'.symm
    rw [hz i, sub_zero]
    unfold phi
    apply div_le_div_of_nonneg_right _ (by linarith)
    have h1 := hb' i
    have h2 := hp.lt_of_pos hX
    rw [hbi] at h1
    exact max_le ht (by linarith)

end sol

/-- Existence of a regional solution. -/
lemma RegSol.exists (hp : GoodP p) (b : Fin N → ℝ) : ∃ q, RegSol p b q := by
  by_cases hall : ∀ j, p 0 ≤ b j
  · refine ⟨0, fun j => le_rfl, fun j => ?_⟩
    simp only [Pi.zero_apply, Finset.sum_const_zero, mul_zero, zero_add, zero_mul, and_true]
    linarith [hall j]
  push_neg at hall
  obtain ⟨j0, hj0⟩ := hall
  set G : ℝ → ℝ := fun X => (∑ j, max 0 (p X - b j)) + deriv p X * X with hG
  have hGc : Continuous G := by
    apply Continuous.add
    · exact continuous_finset_sum _ (fun j _ =>
        continuous_const.max (hp.diff.continuous.sub continuous_const))
    · exact hp.cont_d.mul continuous_id
  have hG0 : 0 < G 0 := by
    simp only [hG, mul_zero, add_zero]
    have : max 0 (p 0 - b j0) ≤ ∑ j, max 0 (p 0 - b j) :=
      Finset.single_le_sum (f := fun j => max 0 (p 0 - b j)) (fun j _ => le_max_left _ _)
        (Finset.mem_univ j0)
    have h2 : 0 < max 0 (p 0 - b j0) := lt_max_of_lt_right (by linarith)
    linarith
  obtain ⟨M, hM, hpM⟩ := hp.exists_large (-(∑ j, |b j|))
  have hbig : ∀ j, p M < b j := by
    intro j
    have : |b j| ≤ ∑ k, |b k| :=
      Finset.single_le_sum (f := fun k => |b k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have := neg_abs_le (b j)
    linarith
  have hGM : G M < 0 := by
    simp only [hG]
    have : ∑ j, max 0 (p M - b j) = 0 :=
      Finset.sum_eq_zero (fun j _ => max_eq_left (by linarith [hbig j]))
    rw [this, zero_add]
    exact mul_neg_of_neg_of_pos (hp.deriv_neg hM) hM
  obtain ⟨X, hXmem, hGX⟩ := intermediate_value_Icc' hM.le hGc.continuousOn
    (⟨hGM.le, hG0.le⟩ : (0:ℝ) ∈ Set.Icc (G M) (G 0))
  have hX : 0 < X := by
    rcases hXmem.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hGX; linarith
  have hd := hp.deriv_neg hX
  set q : Fin N → ℝ := fun j => phi p (b j) X with hq
  have hsum : ∑ k, q k = X := by
    simp only [hq, phi]
    rw [← Finset.sum_div, div_eq_iff (by linarith)]
    simp only [hG] at hGX
    linarith
  refine ⟨q, fun j => phi_nonneg hp hX, fun j => ?_⟩
  rw [hsum]
  simp only [hq, phi]
  rcases le_total (p X - b j) 0 with h | h
  · rw [max_eq_left h]; simp; linarith
  · rw [max_eq_right h]
    have : deriv p X * ((p X - b j) / -deriv p X) = -(p X - b j) := by
      have hne : deriv p X ≠ 0 := ne_of_lt hd
      field_simp
    rw [this]
    constructor <;> ring_nf <;> simp


/-- Continuity of a firm's regional sale in its own cost parameter. -/
lemma RegSol.continuous_own (hp : GoodP p) {i : Fin N} (B : ℝ → Fin N → ℝ)
    (f : ℝ → Fin N → ℝ) (hf : ∀ x, RegSol p (B x) (f x))
    (hmono : ∀ x y, x ≤ y → B x ≤ B y)
    (hoth : ∀ x y j, j ≠ i → B x j = B y j)
    (hi : ∀ x y, B y i = B x i + (y - x)) :
    Continuous (fun x => f x i) := by
  rw [Metric.continuous_iff]
  intro x0 ε hε
  rcases (hf x0).sum_nonneg.lt_or_eq with hX0 | hX0
  · have hD := hp.deriv_neg hX0
    refine ⟨ε * (-deriv p (∑ k, f x0 k)), mul_pos hε (by linarith), fun x hx => ?_⟩
    rw [Real.dist_eq, abs_lt] at hx
    rw [Real.dist_eq, abs_lt]
    rcases le_total x0 x with hxx | hxx
    · have h1 := (hf x0).own_anti hp (hf x) (hmono _ _ hxx) (fun j hj => hoth _ _ j hj)
      have h2 := (hf x0).own_lip hp (hf x) (hmono _ _ hxx) (t := x - x0) (by linarith)
        (hi _ _) hX0
      have h3 : (x - x0) / (-deriv p (∑ k, f x0 k)) < ε := by
        rw [div_lt_iff₀ (by linarith)]; linarith
      constructor <;> linarith
    · have hXx : ∑ k, f x0 k ≤ ∑ k, f x k := (hf x).total_anti hp (hf x0) (hmono _ _ hxx)
      have hpos : 0 < ∑ k, f x k := lt_of_lt_of_le hX0 hXx
      have h1 := (hf x).own_anti hp (hf x0) (hmono _ _ hxx) (fun j hj => hoth _ _ j hj)
      have h2 := (hf x).own_lip hp (hf x0) (hmono _ _ hxx) (t := x0 - x) (by linarith)
        (hi _ _) hpos
      have hd2 := hp.deriv_anti hX0.le hXx
      have h3 : (x0 - x) / (-deriv p (∑ k, f x k)) ≤ (x0 - x) / (-deriv p (∑ k, f x0 k)) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
      have h4 : (x0 - x) / (-deriv p (∑ k, f x0 k)) < ε := by
        rw [div_lt_iff₀ (by linarith)]; linarith
      constructor <;> linarith
  · obtain ⟨hz, hb0⟩ := (hf x0).zero_of_sum hX0.symm
    refine ⟨p 0 - p ε, by linarith [hp.lt_of_pos hε], fun x hx => ?_⟩
    rw [Real.dist_eq, abs_lt] at hx
    rw [Real.dist_eq, hz i, sub_zero, abs_lt]
    have hn := (hf x).nonneg i
    rcases le_total x0 x with hxx | hxx
    · have h1 := (hf x0).own_anti hp (hf x) (hmono _ _ hxx) (fun j hj => hoth _ _ j hj)
      rw [hz i] at h1
      constructor <;> linarith
    · have hle := (hf x).le_sum i
      have hlt : ∑ k, f x k < ε := by
        by_contra hge
        push_neg at hge
        have hpos : 0 < ∑ k, f x k := lt_of_lt_of_le hε hge
        have hsum0 : ∑ k : Fin N, (0:ℝ) < ∑ k, f x k := by simpa using hpos
        obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt hsum0
        have hs := (hf x).seller hp hj
        have hpX := hp.lt_of_pos hpos
        have hpe := hp.anti_le hε.le hge
        by_cases hji : j = i
        · subst hji
          have e1 := hi x x0
          have e2 := hb0 j
          linarith
        · have e1 := hoth x x0 j hji
          have e2 := hb0 j
          linarith
      constructor <;> linarith

end MRCSol

namespace MRCSol

variable {N R : ℕ}

/-- Effective marginal cost of firm `i` in region `r` at marginal-profit vector `ρ`. -/
def bv (M : Market N R) (ρ : Fin N → ℝ) (r : Fin R) : Fin N → ℝ :=
  fun i => M.tc i r + M.ac i + ρ i

lemma cond_iff (M : Market N R) (ρ : Fin N → ℝ) (Q : Fin N → Fin R → ℝ) :
    ((∀ i r, 0 ≤ Q i r) ∧ ∀ i, M.Cond2 Q i (ρ i)) ↔
      ∀ r, RegSol (M.p r) (bv M ρ r) (fun i => Q i r) := by
  have key : ∀ i r, M.margProfit Q i r - ρ i =
      deriv (M.p r) (∑ k, Q k r) * Q i r + M.p r (∑ k, Q k r) - bv M ρ r i := by
    intro i r; simp only [Market.margProfit, qTotRegion, bv]; ring
  constructor
  · rintro ⟨h0, h2⟩ r
    refine ⟨fun i => h0 i r, fun i => ?_⟩
    obtain ⟨a, c⟩ := h2 i r
    rw [← key]; exact ⟨by linarith, c⟩
  · intro h
    refine ⟨fun i r => (h r).1 i, fun i r => ?_⟩
    obtain ⟨a, c⟩ := (h r).2 i
    rw [← key] at a c
    exact ⟨by linarith, c⟩

lemma hpr {M : Market N R} (hM : M.Standing) (r : Fin R) : GoodP (M.p r) :=
  goodP_of (hM.1 r).1 (hM.1 r).2.1 (hM.1 r).2.2.1

lemma exists_unique_sol (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) :
    ∃! Q : Fin N → Fin R → ℝ, (∀ i r, 0 ≤ Q i r) ∧ ∀ i, M.Cond2 Q i (ρ i) := by
  choose q hq using fun r => RegSol.exists (hpr hM r) (bv M ρ r)
  refine ⟨fun i r => q r i, (cond_iff M ρ _).mpr (fun r => hq r), fun Q hQ => ?_⟩
  have h := (cond_iff M ρ Q).mp hQ
  funext i r
  exact congrFun ((h r).unique (hpr hM r) (hq r)) i

lemma Qhat_spec (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) :
    (∀ i r, 0 ≤ M.Qhat ρ i r) ∧ ∀ i, M.Cond2 (M.Qhat ρ) i (ρ i) := by
  have h := exists_unique_sol M hM ρ
  unfold Market.Qhat
  rw [dif_pos h]
  exact h.exists.choose_spec

lemma Qhat_eq (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (Q : Fin N → Fin R → ℝ)
    (hQ : (∀ i r, 0 ≤ Q i r) ∧ ∀ i, M.Cond2 Q i (ρ i)) : M.Qhat ρ = Q :=
  (exists_unique_sol M hM ρ).unique (Qhat_spec M hM ρ) hQ

lemma hreg (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (r : Fin R) :
    RegSol (M.p r) (bv M ρ r) (fun i => M.Qhat ρ i r) :=
  (cond_iff M ρ _).mp (Qhat_spec M hM ρ) r

lemma bv_mono (M : Market N R) {ρ ρ' : Fin N → ℝ} (h : ρ ≤ ρ') (r : Fin R) :
    bv M ρ r ≤ bv M ρ' r := fun i => by simp only [bv]; linarith [h i]

lemma update_le_update {ρ : Fin N → ℝ} (i : Fin N) {x y : ℝ} (h : x ≤ y) :
    Function.update ρ i x ≤ Function.update ρ i y := by
  intro j
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [Function.update_of_ne hj]

lemma update_le_update' {ρ ρ' : Fin N → ℝ} (hρ : ρ ≤ ρ') (i : Fin N) (x : ℝ) :
    Function.update ρ i x ≤ Function.update ρ' i x := by
  intro j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj, hρ j]

/-- The firm-total quantity `x ↦ q^i_tot(x; ρ_{-i})`. -/
noncomputable def gq (M : Market N R) (ρ : Fin N → ℝ) (i : Fin N) (x : ℝ) : ℝ :=
  qTotFirm (M.Qhat (Function.update ρ i x)) i

lemma gq_nonneg (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    0 ≤ gq M ρ i x := by
  unfold gq qTotFirm
  exact Finset.sum_nonneg (fun r _ => (Qhat_spec M hM _).1 i r)

lemma gq_anti (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (i : Fin N) {x y : ℝ}
    (hxy : x ≤ y) : gq M ρ i y ≤ gq M ρ i x := by
  unfold gq qTotFirm
  apply Finset.sum_le_sum
  intro r _
  apply (hreg M hM _ r).own_anti (hpr hM r) (hreg M hM _ r)
    (bv_mono M (update_le_update i hxy) r)
  intro j hj
  simp [bv, Function.update_of_ne hj]

lemma gq_strict (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (i : Fin N) {x y : ℝ}
    (hxy : x < y) (hpos : 0 < gq M ρ i x) : gq M ρ i y < gq M ρ i x := by
  unfold gq qTotFirm at *
  have hsum0 : ∑ r : Fin R, (0:ℝ) < ∑ r, M.Qhat (Function.update ρ i x) i r := by
    simpa using hpos
  obtain ⟨r0, -, hr0⟩ := Finset.exists_lt_of_sum_lt hsum0
  apply Finset.sum_lt_sum
  · intro r _
    apply (hreg M hM _ r).own_anti (hpr hM r) (hreg M hM _ r)
      (bv_mono M (update_le_update i hxy.le) r)
    intro j hj
    simp [bv, Function.update_of_ne hj]
  · refine ⟨r0, Finset.mem_univ _, ?_⟩
    apply (hreg M hM _ r0).own_strict (hpr hM r0) (hreg M hM _ r0)
      (bv_mono M (update_le_update i hxy.le) r0)
    · intro j hj
      simp [bv, Function.update_of_ne hj]
    · simp [bv, hxy]
    · exact hr0

lemma gq_cont (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (i : Fin N) :
    Continuous (gq M ρ i) := by
  unfold gq qTotFirm
  apply continuous_finsetSum
  intro r _
  exact RegSol.continuous_own (hpr hM r) (i := i)
    (fun x => bv M (Function.update ρ i x) r) (fun x j => M.Qhat (Function.update ρ i x) j r)
    (fun x => hreg M hM _ r) (fun x y hxy => bv_mono M (update_le_update i hxy) r)
    (fun x y j hj => by simp [bv, Function.update_of_ne hj])
    (fun x y => by simp [bv])

lemma qtot_other_mono (M : Market N R) (hM : M.Standing) {ρ ρ' : Fin N → ℝ} (h : ρ ≤ ρ')
    {i : Fin N} (hi : ρ i = ρ' i) :
    qTotFirm (M.Qhat ρ) i ≤ qTotFirm (M.Qhat ρ') i := by
  unfold qTotFirm
  apply Finset.sum_le_sum
  intro r _
  exact (hreg M hM ρ r).other_mono (hpr hM r) (hreg M hM ρ' r) (bv_mono M h r)
    (by simp [bv, hi])

lemma gq_other_mono (M : Market N R) (hM : M.Standing) {ρ ρ' : Fin N → ℝ} (h : ρ ≤ ρ')
    (i : Fin N) (x : ℝ) : gq M ρ i x ≤ gq M ρ' i x :=
  qtot_other_mono M hM (update_le_update' h i x) (by simp)

lemma w_le_wbar (M : Market N R) (r : Fin R) : M.p r 0 ≤ M.wbar :=
  le_ciSup (f := M.w) (Finite.bddAbove_range _) r

lemma wbar_nonneg (M : Market N R) (hM : M.Standing) : 0 ≤ M.wbar :=
  Real.iSup_nonneg (fun r => (hM.1 r).2.2.2)

lemma gq_wbar (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (i : Fin N) :
    gq M ρ i M.wbar = 0 := by
  unfold gq qTotFirm
  apply Finset.sum_eq_zero
  intro r _
  apply (hreg M hM _ r).eq_zero_of_le (hpr hM r)
  simp only [bv, Function.update_self]
  linarith [w_le_wbar M r, (hM.2.1 i).1, hM.2.2 i r]

lemma gq_self (M : Market N R) (ρ : Fin N → ℝ) (i : Fin N) :
    gq M ρ i (ρ i) = qTotFirm (M.Qhat ρ) i := by
  simp [gq]

end MRCSol

namespace MRCSol

variable {N R : ℕ}

lemma Phi_eq (M : Market N R) (ρ : Fin N → ℝ) (i : Fin N) :
    M.Phi ρ i = if gq M ρ i 0 < M.kap i then 0
      else sInf {x | x ∈ Set.Icc 0 M.wbar ∧ gq M ρ i x = M.kap i} := rfl

lemma Phi_spec (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (i : Fin N) :
    0 ≤ M.Phi ρ i ∧ M.Phi ρ i ≤ M.wbar ∧ gq M ρ i (M.Phi ρ i) ≤ M.kap i ∧
      (0 < M.Phi ρ i → gq M ρ i (M.Phi ρ i) = M.kap i) := by
  have hk := (hM.2.1 i).2
  rw [Phi_eq]
  split_ifs with h
  · exact ⟨le_rfl, wbar_nonneg M hM, h.le, fun h' => absurd h' (lt_irrefl _)⟩
  · push_neg at h
    have hmem : M.kap i ∈ Set.Icc (gq M ρ i M.wbar) (gq M ρ i 0) :=
      ⟨by rw [gq_wbar M hM]; exact hk.le, h⟩
    obtain ⟨x0, hx0, hgx0⟩ := intermediate_value_Icc' (wbar_nonneg M hM)
      (gq_cont M hM ρ i).continuousOn hmem
    have hS : {x | x ∈ Set.Icc 0 M.wbar ∧ gq M ρ i x = M.kap i} = {x0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, hgx⟩
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := gq_strict M hM ρ i hlt (by rw [hgx]; exact hk); linarith
        · have := gq_strict M hM ρ i hlt (by rw [hgx0]; exact hk); linarith
      · rintro rfl; exact ⟨hx0, hgx0⟩
    rw [hS, csInf_singleton]
    exact ⟨hx0.1, hx0.2, hgx0.le, fun _ => hgx0⟩

lemma Phi_unique (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) (i : Fin N) {x : ℝ}
    (hx : 0 ≤ x) (hle : gq M ρ i x ≤ M.kap i) (heq : 0 < x → gq M ρ i x = M.kap i) :
    M.Phi ρ i = x := by
  obtain ⟨h0, -, h2, h3⟩ := Phi_spec M hM ρ i
  have hk := (hM.2.1 i).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hgx := heq (lt_of_le_of_lt h0 hlt)
    have h4 := gq_anti M hM ρ i hlt.le
    have hgy : 0 < gq M ρ i (M.Phi ρ i) := by linarith
    have := gq_strict M hM ρ i hlt hgy
    linarith
  · have hgy := h3 (lt_of_le_of_lt hx hlt)
    have h4 := gq_anti M hM ρ i hlt.le
    have hgx : 0 < gq M ρ i x := by linarith
    have := gq_strict M hM ρ i hlt hgx
    linarith

lemma Phi_box (M : Market N R) (hM : M.Standing) (ρ : Fin N → ℝ) : M.Phi ρ ∈ M.box :=
  Set.mem_Icc.mpr ⟨fun i => (Phi_spec M hM ρ i).1, fun i => (Phi_spec M hM ρ i).2.1⟩

lemma Phi_mono (M : Market N R) (hM : M.Standing) {ρ ρ' : Fin N → ℝ} (h : ρ ≤ ρ') :
    M.Phi ρ ≤ M.Phi ρ' := by
  intro i
  obtain ⟨h0, -, h2, h3⟩ := Phi_spec M hM ρ i
  obtain ⟨h0', -, h2', h3'⟩ := Phi_spec M hM ρ' i
  have hk := (hM.2.1 i).2
  by_contra hlt
  push_neg at hlt
  have hgy := h3 (lt_of_le_of_lt h0' hlt)
  have ha := gq_anti M hM ρ i hlt.le
  have hs := gq_strict M hM ρ i hlt (by linarith)
  have hm := gq_other_mono M hM h i (M.Phi ρ' i)
  linarith

/-- Complementarity of the marginal-profit vector with capacities. -/
def KKT (M : Market N R) (ρ : Fin N → ℝ) : Prop :=
  ∀ i, 0 ≤ ρ i ∧ qTotFirm (M.Qhat ρ) i ≤ M.kap i ∧
    (0 < ρ i → qTotFirm (M.Qhat ρ) i = M.kap i)

lemma kkt_of_fp (M : Market N R) (hM : M.Standing) {ρ : Fin N → ℝ} (h : M.Phi ρ = ρ) :
    KKT M ρ := by
  intro i
  obtain ⟨h0, -, h2, h3⟩ := Phi_spec M hM ρ i
  have e : M.Phi ρ i = ρ i := congrFun h i
  rw [e, gq_self] at h2 h3
  rw [e] at h0
  exact ⟨h0, h2, h3⟩

lemma fp_of_kkt (M : Market N R) (hM : M.Standing) {ρ : Fin N → ℝ} (h : KKT M ρ) :
    M.Phi ρ = ρ := by
  funext i
  obtain ⟨h0, h2, h3⟩ := h i
  exact Phi_unique M hM ρ i h0 (by rw [gq_self]; exact h2) (by rw [gq_self]; exact h3)

lemma greatest_fp (M : Market N R) (hM : M.Standing) :
    ∃ u ∈ M.box, M.Phi u = u ∧ ∀ ρ ∈ M.box, M.Phi ρ = ρ → ρ ≤ u := by
  set A := {ρ | ρ ∈ M.box ∧ ρ ≤ M.Phi ρ} with hA
  have hw := wbar_nonneg M hM
  have h0A : (0 : Fin N → ℝ) ∈ A :=
    ⟨Set.mem_Icc.mpr ⟨le_rfl, fun _ => hw⟩, (Set.mem_Icc.mp (Phi_box M hM 0)).1⟩
  have hbdd : ∀ i, BddAbove ((fun ρ : Fin N → ℝ => ρ i) '' A) := fun i =>
    ⟨M.wbar, by rintro _ ⟨ρ, hρ, rfl⟩; exact (Set.mem_Icc.mp hρ.1).2 i⟩
  have hne : ∀ i, ((fun ρ : Fin N → ℝ => ρ i) '' A).Nonempty := fun i =>
    ⟨_, Set.mem_image_of_mem _ h0A⟩
  set u : Fin N → ℝ := fun i => sSup ((fun ρ : Fin N → ℝ => ρ i) '' A) with hu
  have hle : ∀ a ∈ A, a ≤ u := fun a ha i =>
    le_csSup (hbdd i) (Set.mem_image_of_mem (fun ρ : Fin N → ℝ => ρ i) ha)
  have hu_box : u ∈ M.box := Set.mem_Icc.mpr ⟨fun i => hle 0 h0A i, fun i =>
    csSup_le (hne i) (by rintro _ ⟨ρ, hρ, rfl⟩; exact (Set.mem_Icc.mp hρ.1).2 i)⟩
  have hu1 : u ≤ M.Phi u := fun i => csSup_le (hne i) (by
    rintro _ ⟨a, ha, rfl⟩
    exact (ha.2 i).trans (Phi_mono M hM (hle a ha) i))
  have hu2 : M.Phi u ∈ A := ⟨Phi_box M hM u, Phi_mono M hM hu1⟩
  have hfix : M.Phi u = u := le_antisymm (hle _ hu2) hu1
  exact ⟨u, hu_box, hfix, fun ρ hρ hfp => hle ρ ⟨hρ, by rw [hfp]⟩⟩

lemma kkt_unique (M : Market N R) (hM : M.Standing) {ρ ρ' : Fin N → ℝ} (hle : ρ ≤ ρ')
    (h : KKT M ρ) (h' : KKT M ρ') : ρ = ρ' := by
  have hA : ∀ r, ∑ i, M.Qhat ρ' i r ≤ ∑ i, M.Qhat ρ i r := fun r =>
    (hreg M hM ρ r).total_anti (hpr hM r) (hreg M hM ρ' r) (bv_mono M hle r)
  have hF : ∀ i, qTotFirm (M.Qhat ρ) i ≤ qTotFirm (M.Qhat ρ') i := by
    intro i
    rcases (hle i).lt_or_eq with hlt | heq
    · rw [(h' i).2.2 (lt_of_le_of_lt (h i).1 hlt)]; exact (h i).2.1
    · exact qtot_other_mono M hM hle heq
  have hswap : ∀ Z : Fin N → Fin R → ℝ, ∑ i, qTotFirm Z i = ∑ r, ∑ i, Z i r := fun Z => by
    unfold qTotFirm; exact Finset.sum_comm
  have hs1 : ∑ i, qTotFirm (M.Qhat ρ) i ≤ ∑ i, qTotFirm (M.Qhat ρ') i :=
    Finset.sum_le_sum (fun i _ => hF i)
  rw [hswap, hswap] at hs1
  have hReq : ∀ r, ∑ i, M.Qhat ρ' i r = ∑ i, M.Qhat ρ i r := by
    intro r
    have hsum : ∑ r, (∑ i, M.Qhat ρ i r - ∑ i, M.Qhat ρ' i r) = 0 := by
      rw [Finset.sum_sub_distrib]
      have := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hA r)
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sub_nonneg.mpr (hA r))).mp hsum r
      (Finset.mem_univ r)
    linarith
  have hQle : ∀ i r, M.Qhat ρ' i r ≤ M.Qhat ρ i r := fun i r =>
    (hreg M hM ρ r).le_of_total_eq (hpr hM r) (hreg M hM ρ' r) (bv_mono M hle r) (hReq r) i
  have hFeq : ∀ i, qTotFirm (M.Qhat ρ') i = qTotFirm (M.Qhat ρ) i := fun i =>
    le_antisymm (Finset.sum_le_sum fun r _ => hQle i r) (hF i)
  have hQeq : ∀ i r, M.Qhat ρ' i r = M.Qhat ρ i r := by
    intro i r
    have hsum : ∑ r, (M.Qhat ρ i r - M.Qhat ρ' i r) = 0 := by
      rw [Finset.sum_sub_distrib]
      have := hFeq i
      unfold qTotFirm at this
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sub_nonneg.mpr (hQle i r))).mp hsum r
      (Finset.mem_univ r)
    linarith
  funext i
  by_contra hne
  have hlt : ρ i < ρ' i := lt_of_le_of_ne (hle i) hne
  have hκ := (h' i).2.2 (lt_of_le_of_lt (h i).1 hlt)
  have hk := (hM.2.1 i).2
  have hpos : ∑ r : Fin R, (0:ℝ) < ∑ r, M.Qhat ρ' i r := by
    simp only [Finset.sum_const_zero]
    unfold qTotFirm at hκ
    linarith
  obtain ⟨r, -, hr⟩ := Finset.exists_lt_of_sum_lt hpos
  have hQpos : 0 < M.Qhat ρ i r := by rw [← hQeq]; exact hr
  have := (hreg M hM ρ r).lt_of_total_eq (hpr hM r) (hreg M hM ρ' r) (hReq r) (j := i)
    (by simp [bv, hlt]) hQpos
  linarith [hQeq i r]

end MRCSol

namespace MRCSol

variable {N R : ℕ}

lemma sum_update_col (Q : Fin N → Fin R → ℝ) (i : Fin N) (x : Fin R → ℝ) (r : Fin R) :
    qTotRegion (Function.update Q i x) r = qTotRegion Q r - Q i r + x r := by
  unfold qTotRegion
  rw [← Finset.add_sum_erase Finset.univ (fun j => Function.update Q i x j r) (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => Q j r) (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, Function.update Q i x j r =
      ∑ j ∈ Finset.univ.erase i, Q j r :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  simp only [this, Function.update_self]
  ring

lemma profit_update (M : Market N R) (Q : Fin N → Fin R → ℝ) (i : Fin N) (x : Fin R → ℝ) :
    M.profit (Function.update Q i x) i =
      (∑ r, (M.p r (qTotRegion Q r - Q i r + x r) - M.tc i r) * x r) - M.ac i * ∑ r, x r := by
  simp only [Market.profit, qTotFirm, sum_update_col, Function.update_self]

lemma per_region_ineq {p : ℝ → ℝ} (hp : GoodP p) {s q t c : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q)
    (ht : 0 ≤ t) :
    (p (s + t) - c) * t - (p (s + q) - c) * q ≤
      (deriv p (s + q) * q + p (s + q) - c) * (t - q) := by
  have h1 := hp.tangent (x := s + q) (y := s + t) (by linarith) (by linarith)
  have h2 := hp.deriv_nonpos (x := s + q) (by linarith)
  have e : s + t - (s + q) = t - q := by ring
  rw [e] at h1
  have h3 : t * (p (s + t) - p (s + q)) ≤ t * (deriv p (s + q) * (t - q)) :=
    mul_le_mul_of_nonneg_left (by linarith) ht
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h2 (sq_nonneg (t - q))]

lemma qTotRegion_nonneg {Q : Fin N → Fin R → ℝ} (h0 : ∀ i r, 0 ≤ Q i r) (r : Fin R) :
    0 ≤ qTotRegion Q r :=
  Finset.sum_nonneg (fun j _ => h0 j r)

lemma others_nonneg {Q : Fin N → Fin R → ℝ} (h0 : ∀ i r, 0 ≤ Q i r) (i : Fin N) (r : Fin R) :
    0 ≤ qTotRegion Q r - Q i r := by
  unfold qTotRegion
  have e := Finset.add_sum_erase Finset.univ (fun j => Q j r) (Finset.mem_univ i)
  have : 0 ≤ ∑ j ∈ Finset.univ.erase i, Q j r := Finset.sum_nonneg (fun j _ => h0 j r)
  linarith

/-- Sufficiency: the allocation at a KKT marginal-profit vector is an equilibrium. -/
lemma eq_of_kkt (M : Market N R) (hM : M.Standing) {ρ : Fin N → ℝ} (h : KKT M ρ) :
    M.IsEquilibrium (M.Qhat ρ) := by
  obtain ⟨h0, hc⟩ := Qhat_spec M hM ρ
  set Q := M.Qhat ρ with hQdef
  refine ⟨fun i => ⟨fun r => h0 i r, (h i).2.1⟩, fun i x hx => ?_⟩
  obtain ⟨hx0, hxk⟩ := hx
  show M.profit (Function.update Q i x) i ≤ M.profit Q i
  rw [profit_update]
  have hQ : M.profit Q i = (∑ r, (M.p r (qTotRegion Q r - Q i r + Q i r) - M.tc i r) * Q i r)
      - M.ac i * ∑ r, Q i r := by
    simp only [Market.profit, qTotFirm, sub_add_cancel]
  rw [hQ]
  have key : ∀ r, (M.p r (qTotRegion Q r - Q i r + x r) - M.tc i r) * x r -
      (M.p r (qTotRegion Q r - Q i r + Q i r) - M.tc i r) * Q i r ≤
      (M.margProfit Q i r + M.ac i) * (x r - Q i r) := by
    intro r
    have := per_region_ineq (hpr hM r) (c := M.tc i r) (others_nonneg h0 i r) (h0 i r) (hx0 r)
    simp only [Market.margProfit, sub_add_cancel] at this ⊢
    linarith
  have hm1 : ∀ r, M.margProfit Q i r * x r ≤ ρ i * x r := fun r =>
    mul_le_mul_of_nonneg_right ((hc i r).1) (hx0 r)
  have hm2 : ∀ r, M.margProfit Q i r * Q i r = ρ i * Q i r := fun r => by
    linear_combination (hc i r).2
  have hρ : ρ i * (∑ r, x r) ≤ ρ i * qTotFirm Q i := by
    rcases (h i).1.lt_or_eq with hpos | hz
    · rw [(h i).2.2 hpos]; exact mul_le_mul_of_nonneg_left hxk hpos.le
    · rw [← hz]; simp
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => key r)
  rw [Finset.sum_sub_distrib] at hsum
  have e1 : ∑ r, (M.margProfit Q i r + M.ac i) * (x r - Q i r) =
      ∑ r, M.margProfit Q i r * x r - ∑ r, M.margProfit Q i r * Q i r +
        M.ac i * ∑ r, x r - M.ac i * ∑ r, Q i r := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have e2 : ∑ r, M.margProfit Q i r * Q i r = ρ i * qTotFirm Q i := by
    unfold qTotFirm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => hm2 r)
  have e3 : ∑ r, M.margProfit Q i r * x r ≤ ρ i * ∑ r, x r := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => hm1 r)
  rw [e1, e2] at hsum
  linarith

lemma deriv_nonpos_of_max {f : ℝ → ℝ} {D δ : ℝ} (hf : HasDerivAt f D 0) (hδ : 0 < δ)
    (hmax : ∀ ε, 0 < ε → ε < δ → f ε ≤ f 0) : D ≤ 0 := by
  have := hf.tendsto_slope_zero_right
  refine le_of_tendsto this ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le)
    (by linarith [hmax t ht.1 ht.2])

lemma hasDerivAt_dev (M : Market N R) (hM : M.Standing) (Q : Fin N → Fin R → ℝ) (i : Fin N)
    (d : Fin R → ℝ) :
    HasDerivAt (fun ε => M.profit (Function.update Q i (fun r => Q i r + ε * d r)) i)
      (∑ r, M.margProfit Q i r * d r) 0 := by
  simp only [profit_update]
  have hL : ∀ r, HasDerivAt (fun ε : ℝ => Q i r + ε * d r) (d r) 0 := fun r => by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (d r)).const_add (Q i r)
  have hU : ∀ r, HasDerivAt (fun ε : ℝ => qTotRegion Q r - Q i r + (Q i r + ε * d r)) (d r) 0 :=
    fun r => (hL r).const_add _
  have hP : ∀ r, HasDerivAt (fun ε : ℝ => M.p r (qTotRegion Q r - Q i r + (Q i r + ε * d r)))
      (deriv (M.p r) (qTotRegion Q r) * d r) 0 := by
    intro r
    have h1 := ((hpr hM r).diff (qTotRegion Q r - Q i r + (Q i r + 0 * d r))).hasDerivAt.comp
      (0:ℝ) (hU r)
    simp only [zero_mul, add_zero, sub_add_cancel] at h1
    exact h1
  have hT : ∀ r ∈ Finset.univ, HasDerivAt
      (fun ε : ℝ => (M.p r (qTotRegion Q r - Q i r + (Q i r + ε * d r)) - M.tc i r) *
        (Q i r + ε * d r))
      (deriv (M.p r) (qTotRegion Q r) * d r * (Q i r + 0 * d r) +
        (M.p r (qTotRegion Q r - Q i r + (Q i r + 0 * d r)) - M.tc i r) * d r) 0 :=
    fun r _ => ((hP r).sub_const (M.tc i r)).mul (hL r)
  have hS := (HasDerivAt.fun_sum hT).sub
    ((HasDerivAt.fun_sum (fun r (_ : r ∈ Finset.univ) => hL r)).const_mul (M.ac i))
  refine hS.congr_deriv ?_
  · simp only [zero_mul, add_zero, sub_add_cancel, Market.margProfit]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring

lemma dev_nonpos (M : Market N R) (hM : M.Standing) {Q : Fin N → Fin R → ℝ}
    (hQ : M.IsEquilibrium Q) (i : Fin N) (d : Fin R → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hfeas : ∀ ε, 0 < ε → ε < δ → (fun r => Q i r + ε * d r) ∈ M.feasible i) :
    ∑ r, M.margProfit Q i r * d r ≤ 0 := by
  apply deriv_nonpos_of_max (hasDerivAt_dev M hM Q i d) hδ
  intro ε h1 h2
  have := hQ.2 i _ (hfeas ε h1 h2)
  simp only [zero_mul, add_zero]
  have e : (Function.update Q i fun r => Q i r) = Q := Function.update_eq_self i Q
  rw [e]
  exact this

lemma sum_ite_mul (f : Fin R → ℝ) (r : Fin R) (c : ℝ) :
    ∑ s, f s * (if s = r then c else 0) = f r * c := by
  simp [mul_ite]

lemma sum_ite' (r : Fin R) (c : ℝ) : ∑ s : Fin R, (if s = r then c else 0) = c := by
  simp

lemma margProfit_le (M : Market N R) (hM : M.Standing) {Q : Fin N → Fin R → ℝ}
    (h0 : ∀ i r, 0 ≤ Q i r) (i : Fin N) (r : Fin R) : M.margProfit Q i r ≤ M.wbar := by
  have hX := qTotRegion_nonneg h0 r
  have h1 := (hpr hM r).deriv_nonpos hX
  have h2 := (hpr hM r).le_zero hX
  have h3 := w_le_wbar M r
  have h4 : deriv (M.p r) (qTotRegion Q r) * Q i r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 (h0 i r)
  unfold Market.margProfit
  linarith [(hM.2.1 i).1, hM.2.2 i r]

/-- Necessity (Lemmas 4.1 and 4.4): an equilibrium comes from a KKT marginal-profit vector. -/
lemma kkt_of_eq (M : Market N R) (hM : M.Standing) {Q : Fin N → Fin R → ℝ}
    (hQ : M.IsEquilibrium Q) : ∃ ρ ∈ M.box, KKT M ρ ∧ M.Qhat ρ = Q := by
  classical
  have hfe : ∀ i, Q i ∈ M.feasible i := hQ.1
  have h0 : ∀ i r, 0 ≤ Q i r := fun i r => (hfe i).1 r
  have hk : ∀ i, qTotFirm Q i ≤ M.kap i := fun i => (hfe i).2
  -- E2: a firm selling in a region has nonnegative marginal profit there
  have E2 : ∀ i r, 0 < Q i r → 0 ≤ M.margProfit Q i r := by
    intro i r hq
    have := dev_nonpos M hM hQ i (fun s => if s = r then -1 else 0) hq (by
      intro ε h1 h2
      refine ⟨fun s => ?_, ?_⟩
      · by_cases hs : s = r
        · subst hs; simp; linarith
        · simp [hs, h0 i s]
      · simp only [mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_add_distrib, sum_ite']
        have := hk i
        unfold qTotFirm at this
        linarith)
    rw [sum_ite_mul] at this
    linarith
  -- E3: a firm with slack capacity has nonpositive marginal profit everywhere
  have E3 : ∀ i r, qTotFirm Q i < M.kap i → M.margProfit Q i r ≤ 0 := by
    intro i r hlt
    have := dev_nonpos M hM hQ i (fun s => if s = r then 1 else 0) (sub_pos.mpr hlt) (by
      intro ε h1 h2
      refine ⟨fun s => ?_, ?_⟩
      · by_cases hs : s = r
        · subst hs; simp; linarith [h0 i s]
        · simp [hs, h0 i s]
      · simp only [mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, sum_ite']
        unfold qTotFirm at h2
        linarith)
    rw [sum_ite_mul] at this
    linarith
  -- E1: marginal profit is maximal in every region where the firm sells
  have E1 : ∀ i r r', 0 < Q i r → M.margProfit Q i r' ≤ M.margProfit Q i r := by
    intro i r r' hq
    by_cases hrr : r' = r
    · rw [hrr]
    have := dev_nonpos M hM hQ i
      (fun s => (if s = r' then 1 else 0) - (if s = r then 1 else 0)) hq (by
      intro ε h1 h2
      refine ⟨fun s => ?_, ?_⟩
      · by_cases hs : s = r
        · subst hs; simp [Ne.symm hrr]; linarith
        · by_cases hs' : s = r'
          · subst hs'; simp [hs]; linarith [h0 i s]
          · simp [hs, hs', h0 i s]
      · simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, sum_ite']
        have := hk i
        unfold qTotFirm at this
        linarith)
    simp only [mul_sub, Finset.sum_sub_distrib, sum_ite_mul, mul_one] at this
    linarith
  -- the marginal-profit vector
  set ρ : Fin N → ℝ := fun i =>
    if h : ∃ r, 0 < Q i r then M.margProfit Q i h.choose else 0 with hρ
  have hcond : ∀ i, M.Cond2 Q i (ρ i) := by
    intro i r
    by_cases h : ∃ r, 0 < Q i r
    · have hr0 := h.choose_spec
      simp only [hρ, dif_pos h]
      refine ⟨E1 i _ r hr0, ?_⟩
      rcases (h0 i r).lt_or_eq with hq | hq
      · have := E1 i r h.choose hq
        have := E1 i h.choose r hr0
        have : M.margProfit Q i r - M.margProfit Q i h.choose = 0 := by linarith
        rw [this, mul_zero]
      · rw [← hq, zero_mul]
    · push_neg at h
      have hz : ∀ s, Q i s = 0 := fun s => le_antisymm (h s) (h0 i s)
      simp only [hρ, dif_neg (not_exists.mpr (fun s hs => absurd hs (not_lt.mpr (h s))))]
      have htot : qTotFirm Q i < M.kap i := by
        unfold qTotFirm; simp only [hz, Finset.sum_const_zero]; exact (hM.2.1 i).2
      exact ⟨E3 i r htot, by rw [hz r, zero_mul]⟩
  have hQeq : M.Qhat ρ = Q := Qhat_eq M hM ρ Q ⟨h0, hcond⟩
  have hρ0 : ∀ i, 0 ≤ ρ i := by
    intro i
    by_cases h : ∃ r, 0 < Q i r
    · simp only [hρ, dif_pos h]; exact E2 i _ h.choose_spec
    · simp only [hρ, dif_neg h, le_refl]
  have hρw : ∀ i, ρ i ≤ M.wbar := by
    intro i
    by_cases h : ∃ r, 0 < Q i r
    · simp only [hρ, dif_pos h]; exact margProfit_le M hM h0 i _
    · simp only [hρ, dif_neg h]; exact wbar_nonneg M hM
  refine ⟨ρ, Set.mem_Icc.mpr ⟨hρ0, hρw⟩, fun i => ⟨hρ0 i, ?_, ?_⟩, hQeq⟩
  · rw [hQeq]; exact hk i
  · intro hpos
    rw [hQeq]
    by_contra hne
    have hlt : qTotFirm Q i < M.kap i := lt_of_le_of_ne (hk i) hne
    by_cases h : ∃ r, 0 < Q i r
    · have := E3 i h.choose hlt
      simp only [hρ, dif_pos h] at hpos
      linarith
    · simp only [hρ, dif_neg h, lt_irrefl] at hpos

end MRCSol

open MRCSol in
theorem solution {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∃ rhos ∈ M.box, M.Phi rhos = rhos ∧
      (∀ rho ∈ M.box, M.Phi rho = rho → rho = rhos) ∧
      ∀ Q : Fin N → Fin R → ℝ, M.IsEquilibrium Q ↔ Q = M.Qhat rhos := by
  obtain ⟨u, hu, hfix, hmax⟩ := greatest_fp M hM
  have huK := kkt_of_fp M hM hfix
  have huniq : ∀ rho ∈ M.box, M.Phi rho = rho → rho = u := fun rho hrho hfp =>
    kkt_unique M hM (hmax rho hrho hfp) (kkt_of_fp M hM hfp) huK
  refine ⟨u, hu, hfix, huniq, fun Q => ⟨fun hQ => ?_, fun hQ => ?_⟩⟩
  · obtain ⟨ρ, hρ, hK, hQρ⟩ := kkt_of_eq M hM hQ
    rw [← hQρ, huniq ρ hρ (fp_of_kkt M hM hK)]
  · rw [hQ]; exact eq_of_kkt M hM huK
