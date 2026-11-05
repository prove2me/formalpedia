-- Prove2me | solution 1 for MartOT.HN.graphs_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:42:28.405057+00:00
-- url     : https://prove2.me/submissions/94b8c0df-8a57-405c-bb29-fe09f01ac81d

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Opt_reroute_competitor

open MeasureTheory

lemma hn73gm_cost_eq (ρ : Measure (ℝ × ℝ)) :
    MartOT.Var.cost (fun x y => -|y - x|) ρ =
      -((∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂ρ : ENNReal) : EReal) := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ p : ℝ × ℝ, ((-|p.2 - p.1| : ℝ) : EReal).toENNReal = 0 := by
    intro p
    apply EReal.toENNReal_of_nonpos
    exact_mod_cast neg_nonpos.mpr (abs_nonneg _)
  have h2 : ∀ p : ℝ × ℝ, (-((-|p.2 - p.1| : ℝ) : EReal)).toENNReal =
      ENNReal.ofReal |p.2 - p.1| := fun p => by
    rw [← EReal.coe_neg, neg_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
      EReal.toReal_coe]
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, zero_sub]

lemma hn73gm_lint3 (a b c : ℝ × ℝ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂(ENNReal.ofReal r • Measure.dirac a +
      ENNReal.ofReal s • Measure.dirac b + Measure.dirac c)) =
      ENNReal.ofReal (r * |a.2 - a.1| + s * |b.2 - b.1| + |c.2 - c.1|) := by
  rw [lintegral_add_measure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lintegral_dirac, lintegral_dirac, smul_eq_mul,
    smul_eq_mul, ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul hs,
    ← ENNReal.ofReal_add (mul_nonneg hr (abs_nonneg _)) (mul_nonneg hs (abs_nonneg _)),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hr (abs_nonneg _))
      (mul_nonneg hs (abs_nonneg _))) (abs_nonneg _)]

/-- The rerouting improvement: three points of `Γ` for which the rerouted competitor is strictly
cheaper contradict the variational property. -/
lemma hn73gm_improve (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (X ym yp X' y' : ℝ) (hm : (X, ym) ∈ Γ) (hp : (X, yp) ∈ Γ) (h' : (X', y') ∈ Γ)
    (hy : ym < y' ∧ y' < yp) (hX : X ≠ X')
    (hlt : (y' - ym) / (yp - ym) * |yp - X| + (1 - (y' - ym) / (yp - ym)) * |ym - X| + |y' - X'| <
      (1 - (y' - ym) / (yp - ym)) * |ym - X'| + (y' - ym) / (yp - ym) * |yp - X'| + |y' - X|) :
    False := by
  set l := (y' - ym) / (yp - ym) with hl
  have hd : 0 < yp - ym := by linarith
  have hl0 : 0 < l := div_pos (by linarith) hd
  have hl1 : l < 1 := by rw [hl, div_lt_one hd]; linarith
  have hcomb : l * yp + (1 - l) * ym = y' := by
    rw [hl]; field_simp; ring
  have hcomp := MartOT.Opt.reroute_competitor X X' ym yp y' l hl0 hl1 hcomb
  -- write the three-point measure as a finite sum
  have hne1 : (X, yp) ≠ (X, ym) := fun h => by
    have := (Prod.mk.inj h).2; linarith
  have hne2 : (X, yp) ≠ (X', y') := fun h => hX (Prod.mk.inj h).1
  have hne3 : (X, ym) ≠ (X', y') := fun h => hX (Prod.mk.inj h).1
  set w : ℝ × ℝ → NNReal := fun p =>
    if p = (X, yp) then Real.toNNReal l else if p = (X, ym) then Real.toNNReal (1 - l) else 1
    with hw
  have hsum : (∑ p ∈ ({(X, yp), (X, ym), (X', y')} : Finset (ℝ × ℝ)),
      (w p : ENNReal) • Measure.dirac p) =
      ENNReal.ofReal l • Measure.dirac (X, yp) + ENNReal.ofReal (1 - l) • Measure.dirac (X, ym) +
        Measure.dirac (X', y') := by
    rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
      Finset.sum_singleton]
    simp only [hw, if_pos rfl, if_neg hne1.symm, if_neg hne2.symm, if_neg hne3.symm, ENNReal.coe_one,
      one_smul]
    rw [add_assoc]
    rfl
  have hsub : (↑({(X, yp), (X, ym), (X', y')} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ⊆ Γ := by
    intro q hq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have key := hΓ _ w hsub _ (by rw [hsum]; exact hcomp)
  rw [hsum, hn73gm_cost_eq, hn73gm_cost_eq, EReal.neg_le_neg_iff,
    EReal.coe_ennreal_le_coe_ennreal_iff, hn73gm_lint3 _ _ _ _ _ hl0.le (by linarith),
    hn73gm_lint3 _ _ _ _ _ (by linarith) hl0.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  simp only at key
  linarith

theorem solution (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (S : Set ℝ) (T₁ T₂ : ℝ → ℝ) (h₁ : ∀ x ∈ S, (x, T₁ x) ∈ Γ) (h₂ : ∀ x ∈ S, (x, T₂ x) ∈ Γ)
    (hT : ∀ x ∈ S, T₁ x ≤ x ∧ x ≤ T₂ x) :
    MonotoneOn T₁ S ∧ MonotoneOn T₂ S := by
  constructor
  · -- `T₁`: the pair sits at the larger point `x'`
    intro x hx x' hx' hxx'
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hxx' with h | hlt
    · subst h; exact lt_irrefl _ hcon
    obtain ⟨a1, a2⟩ := hT x hx
    obtain ⟨b1, b2⟩ := hT x' hx'
    -- ym = T₁ x' < y' = T₁ x ≤ x < x' ≤ T₂ x' = yp
    refine hn73gm_improve Γ hΓ x' (T₁ x') (T₂ x') x (T₁ x) (h₁ x' hx') (h₂ x' hx') (h₁ x hx)
      ⟨hcon, by linarith⟩ (ne_of_gt hlt) ?_
    set ym := T₁ x'; set yp := T₂ x'; set y' := T₁ x
    have hd : 0 < yp - ym := by linarith
    set l := (y' - ym) / (yp - ym) with hl
    have hl0 : 0 < l := div_pos (by linarith) hd
    have hl1 : l < 1 := by rw [hl, div_lt_one hd]; linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - x'), abs_of_nonpos (by linarith : ym - x' ≤ 0),
      abs_of_nonpos (by linarith : y' - x ≤ 0), abs_of_nonpos (by linarith : ym - x ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - x), abs_of_nonpos (by linarith : y' - x' ≤ 0)]
    nlinarith [mul_pos hl0 (by linarith : (0:ℝ) < x' - x)]
  · -- `T₂`: the pair sits at the smaller point `x`
    intro x hx x' hx' hxx'
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hxx' with h | hlt
    · subst h; exact lt_irrefl _ hcon
    obtain ⟨a1, a2⟩ := hT x hx
    obtain ⟨b1, b2⟩ := hT x' hx'
    -- ym = T₁ x ≤ x < x' ≤ y' = T₂ x' < yp = T₂ x
    refine hn73gm_improve Γ hΓ x (T₁ x) (T₂ x) x' (T₂ x') (h₁ x hx) (h₂ x hx) (h₂ x' hx')
      ⟨by linarith, hcon⟩ (ne_of_lt hlt) ?_
    set ym := T₁ x; set yp := T₂ x; set y' := T₂ x'
    have hd : 0 < yp - ym := by linarith
    set l := (y' - ym) / (yp - ym) with hl
    have hl0 : 0 < l := div_pos (by linarith) hd
    have hl1 : l < 1 := by rw [hl, div_lt_one hd]; linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - x), abs_of_nonpos (by linarith : ym - x ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y' - x'), abs_of_nonpos (by linarith : ym - x' ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - x'), abs_of_nonneg (by linarith : (0:ℝ) ≤ y' - x)]
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - l) (by linarith : (0:ℝ) < x' - x)]
