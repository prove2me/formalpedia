-- Prove2me | solution 1 for MartOT.HN.fibres_le_two_straddle
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:53:32.55556+00:00
-- url     : https://prove2.me/submissions/0e752a14-415b-43b7-962a-4b0fc2b82432

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Opt_reroute_competitor
import Theorems.Thm_MartOT_HN_lemma_3_2

open MeasureTheory

lemma hn73fs_cost_eq (ρ : Measure (ℝ × ℝ)) :
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

lemma hn73fs_lint3 (a b c : ℝ × ℝ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
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
lemma hn73fs_improve (Γ : Set (ℝ × ℝ))
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
  rw [hsum, hn73fs_cost_eq, hn73fs_cost_eq, EReal.neg_le_neg_iff,
    EReal.coe_ennreal_le_coe_ennreal_iff, hn73fs_lint3 _ _ _ _ _ hl0.le (by linarith),
    hn73fs_lint3 _ _ _ _ _ (by linarith) hl0.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  simp only at key
  linarith


/-- First forbidden configuration of (23), with `y⁻ < y' ≤ x' < x ≤ y⁺`. -/
lemma hn73fs_conf1 (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (X ym yp X' y' : ℝ) (hm : (X, ym) ∈ Γ) (hp : (X, yp) ∈ Γ) (h' : (X', y') ∈ Γ)
    (h1 : ym < y') (h2 : y' ≤ X') (h3 : X' < X) (h4 : X ≤ yp) : False := by
  refine hn73fs_improve Γ hΓ X ym yp X' y' hm hp h' ⟨h1, by linarith⟩ (ne_of_gt h3) ?_
  have hd : 0 < yp - ym := by linarith
  set l := (y' - ym) / (yp - ym) with hl
  have hl0 : 0 < l := div_pos (by linarith) hd
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - X), abs_of_nonpos (by linarith : ym - X ≤ 0),
    abs_of_nonpos (by linarith : y' - X' ≤ 0), abs_of_nonpos (by linarith : ym - X' ≤ 0),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - X'), abs_of_nonpos (by linarith : y' - X ≤ 0)]
  nlinarith [mul_pos hl0 (by linarith : (0:ℝ) < X - X')]

/-- Second forbidden configuration of (23), with `y⁻ ≤ x < x' ≤ y' < y⁺`. -/
lemma hn73fs_conf2 (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (X ym yp X' y' : ℝ) (hm : (X, ym) ∈ Γ) (hp : (X, yp) ∈ Γ) (h' : (X', y') ∈ Γ)
    (h1 : ym ≤ X) (h2 : X < X') (h3 : X' ≤ y') (h4 : y' < yp) : False := by
  refine hn73fs_improve Γ hΓ X ym yp X' y' hm hp h' ⟨by linarith, h4⟩ (ne_of_lt h2) ?_
  have hd : 0 < yp - ym := by linarith
  set l := (y' - ym) / (yp - ym) with hl
  have hl1 : l < 1 := by rw [hl, div_lt_one hd]; linarith
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - X), abs_of_nonpos (by linarith : ym - X ≤ 0),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ y' - X'), abs_of_nonpos (by linarith : ym - X' ≤ 0),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ yp - X'), abs_of_nonneg (by linarith : (0:ℝ) ≤ y' - X)]
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - l) (by linarith : (0:ℝ) < X' - X)]

theorem solution (μ : Measure ℝ) (hμc : ∀ x : ℝ, μ {x} = 0) (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (hstr : ∀ a y : ℝ, (a, y) ∈ Γ →
      (∃ y₁ : ℝ, (a, y₁) ∈ Γ ∧ y₁ ≤ a) ∧ (∃ y₂ : ℝ, (a, y₂) ∈ Γ ∧ a ≤ y₂)) :
    {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard}.Countable ∧
      μ {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard} = 0 := by
  set A := {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard} with hA
  have hAc : A.Countable := by
    by_contra hunc
    have hA3 : {a : ℝ | ((3 : ℕ) : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γ}.encard} = A := by
      ext a
      simp only [Set.mem_ofPred_eq, hA]
      constructor
      · intro h; exact lt_of_lt_of_le (by norm_num) h
      · intro h
        exact (ENat.add_one_le_iff (by decide : (2 : ℕ∞) ≠ ⊤)).mpr h
    obtain ⟨a, b, hb, hbΓ, happ⟩ := MartOT.HN.lemma_3_2 3 (by norm_num) Γ (by rw [hA3]; exact hunc)
    have h01 : b 0 < b 1 := hb (by decide)
    have h12 : b 1 < b 2 := hb (by decide)
    rcases lt_trichotomy (b 1) a with hlt | heq | hgt
    · -- `b < a`: a point of `Γ_a` above `a`, and a left approximation of `(a, b)`
      obtain ⟨-, y₂, hy₂, hay₂⟩ := hstr a (b 0) (hbΓ 0)
      set ε := min (b 1 - b 0) (a - b 1) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min (by linarith) (by linarith))
      have hε1 : ε ≤ (b 1 - b 0) / 2 := by rw [hε]; linarith [min_le_left (b 1 - b 0) (a - b 1)]
      have hε2 : ε ≤ (a - b 1) / 2 := by rw [hε]; linarith [min_le_right (b 1 - b 0) (a - b 1)]
      obtain ⟨a'', ha'', b'', -, hb''Γ, hda, hdb⟩ := (happ ε hε0).2
      have e1 := abs_lt.mp hda
      have e2 := abs_lt.mp (hdb 1)
      exact hn73fs_conf1 Γ hΓ a (b 0) y₂ a'' (b'' 1) (hbΓ 0) hy₂ (hb''Γ 1)
        (by linarith) (by linarith) ha'' hay₂
    · -- `b = a`
      set ε := min (a - b 0) (b 2 - a) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min (by linarith) (by linarith))
      have hε1 : ε ≤ (a - b 0) / 2 := by rw [hε]; linarith [min_le_left (a - b 0) (b 2 - a)]
      have hε2 : ε ≤ (b 2 - a) / 2 := by rw [hε]; linarith [min_le_right (a - b 0) (b 2 - a)]
      obtain ⟨a', ha', b', -, hb'Γ, hda, hdb⟩ := (happ ε hε0).1
      have e1 := abs_lt.mp hda
      have e0 := abs_lt.mp (hdb 0)
      have e2 := abs_lt.mp (hdb 1)
      have e3 := abs_lt.mp (hdb 2)
      by_cases hc : a' ≤ b' 1
      · exact hn73fs_conf2 Γ hΓ a (b 0) (b 2) a' (b' 1) (hbΓ 0) (hbΓ 2) (hb'Γ 1)
          (by linarith) ha' hc (by linarith)
      · push Not at hc
        have hmem : (a, a) ∈ Γ := heq ▸ hbΓ 1
        exact hn73fs_conf1 Γ hΓ a' (b' 0) (b' 2) a a (hb'Γ 0) (hb'Γ 2) hmem
          (by linarith) le_rfl ha' (by linarith)
    · -- `b > a`: a point of `Γ_a` below `a`, and a right approximation of `(a, b)`
      obtain ⟨⟨y₁, hy₁, hy₁a⟩, -⟩ := hstr a (b 0) (hbΓ 0)
      set ε := min (b 2 - b 1) (b 1 - a) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min (by linarith) (by linarith))
      have hε1 : ε ≤ (b 2 - b 1) / 2 := by rw [hε]; linarith [min_le_left (b 2 - b 1) (b 1 - a)]
      have hε2 : ε ≤ (b 1 - a) / 2 := by rw [hε]; linarith [min_le_right (b 2 - b 1) (b 1 - a)]
      obtain ⟨a', ha', b', -, hb'Γ, hda, hdb⟩ := (happ ε hε0).1
      have e1 := abs_lt.mp hda
      have e2 := abs_lt.mp (hdb 1)
      exact hn73fs_conf2 Γ hΓ a y₁ (b 2) a' (b' 1) hy₁ (hbΓ 2) (hb'Γ 1)
        hy₁a ha' (by linarith) (by linarith)
  refine ⟨hAc, ?_⟩
  rw [← Set.biUnion_of_singleton A]
  exact (measure_biUnion_null_iff hAc).2 fun a _ => hμc a
