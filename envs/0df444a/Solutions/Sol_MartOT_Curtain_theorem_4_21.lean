-- Prove2me | solution 1 for MartOT.Curtain.theorem_4_21
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:11:19.774117+00:00
-- url     : https://prove2.me/submissions/8a6f39d4-a6fe-4c91-82b7-7b2c20212d8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Curtain_lemma_1_11
import Theorems.Thm_MartOT_Curtain_curtain_minimizes_cst

open MeasureTheory

namespace LMart421

lemma integralE_of_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ x, ((f x : EReal)).toENNReal = ENNReal.ofReal (f x) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have h2 : ∀ x, (-(f x : EReal)).toENNReal = 0 := fun x => by
    apply EReal.toENNReal_of_nonpos
    rw [← EReal.coe_neg]; exact_mod_cast (neg_nonpos.mpr (hf x))
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

lemma map3 {f : ℝ × ℝ → ℝ} (hf : Measurable f) (a b c : ENNReal) (p q r : ℝ × ℝ) :
    (a • Measure.dirac p + (b • Measure.dirac q + c • Measure.dirac r)).map f =
      a • Measure.dirac (f p) + (b • Measure.dirac (f q) + c • Measure.dirac (f r)) := by
  simp [Measure.map_add _ _ hf, Measure.map_smul, Measure.map_dirac' hf]

lemma integrable3 (g : ℝ × ℝ → ℝ) (a b c : NNReal) (p q r : ℝ × ℝ) :
    Integrable g ((a : ENNReal) • Measure.dirac p + ((b : ENNReal) • Measure.dirac q +
      (c : ENNReal) • Measure.dirac r)) := by
  have hd : ∀ z : ℝ × ℝ, Integrable g (Measure.dirac z) := fun z =>
    integrable_dirac (by simp)
  refine (hd p).smul_measure (by simp) |>.add_measure ?_
  exact ((hd q).smul_measure (by simp)).add_measure ((hd r).smul_measure (by simp))

lemma integral3 (g : ℝ × ℝ → ℝ) (a b c : NNReal) (p q r : ℝ × ℝ) :
    ∫ z, g z ∂((a : ENNReal) • Measure.dirac p + ((b : ENNReal) • Measure.dirac q +
      (c : ENNReal) • Measure.dirac r)) = a * g p + (b * g q + c * g r) := by
  have hd : ∀ z : ℝ × ℝ, Integrable g (Measure.dirac z) := fun z =>
    integrable_dirac (by simp)
  rw [integral_add_measure ((hd p).smul_measure (by simp))
    (((hd q).smul_measure (by simp)).add_measure ((hd r).smul_measure (by simp))),
    integral_add_measure ((hd q).smul_measure (by simp)) ((hd r).smul_measure (by simp))]
  simp [integral_smul_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]

lemma lintegral3 (g : ℝ × ℝ → ENNReal) (a b c : ENNReal) (p q r : ℝ × ℝ) :
    ∫⁻ z, g z ∂(a • Measure.dirac p + (b • Measure.dirac q + c • Measure.dirac r)) =
      a * g p + (b * g q + c * g r) := by
  simp [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

/-- The cost `c_{s,t}`. -/
noncomputable def cst (s t : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => (Set.Iic s).indicator (fun _ => (1 : ℝ)) x * |y - t|

lemma cst_nonneg (s t x y : ℝ) : 0 ≤ cst s t x y := by
  unfold cst
  apply mul_nonneg _ (abs_nonneg _)
  by_cases h : x ∈ Set.Iic s <;> simp [h]

lemma cst_le (s t x y : ℝ) : cst s t x y ≤ |y - t| := by
  unfold cst
  by_cases h : x ∈ Set.Iic s <;> simp [h]

lemma cst_meas (s t : ℝ) : Measurable (Function.uncurry (cst s t)) := by
  unfold cst Function.uncurry
  refine Measurable.mul ?_ ?_
  · exact (measurable_const.indicator measurableSet_Iic).comp measurable_fst
  · exact (measurable_snd.sub_const t).abs

end LMart421

open LMart421

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (πlc : Measure (ℝ × ℝ)) (hlc : MartOT.Var.IsLeftCurtain μ ν πlc) :
    MartOT.Var.IsLeftMonotone πlc := by
  -- Γ_{s,t} from Lemma 1.11 for each rational pair
  have key : ∀ q : ℚ × ℚ, ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ πlc Γᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          MartOT.Var.cost (cst q.1 q.2) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
            MartOT.Var.cost (cst q.1 q.2) α' := by
    intro q
    have hopt := MartOT.Curtain.curtain_minimizes_cst μ ν hμν πlc hlc q.1 q.2
    refine MartOT.Curtain.lemma_1_11 μ ν hμν (cst q.1 q.2) (cst_meas _ _) ?_ πlc hopt ?_
    · exact ⟨0, 0, integrable_zero _ _ _, integrable_zero _ _ _,
        fun x y => by simpa using cst_nonneg q.1 q.2 x y⟩
    · unfold MartOT.Var.cost
      rw [integralE_of_nonneg _ _ (fun p => cst_nonneg _ _ _ _)]
      have hmarg : πlc.map Prod.snd = ν := hopt.1.1.2
      have hint : Integrable (fun p : ℝ × ℝ => |p.2 - (q.2 : ℝ)|) πlc := by
        have h1 : Integrable (fun y : ℝ => |y - (q.2 : ℝ)|) ν :=
          (hμν.2.1.2.sub (integrable_const _)).abs
        rw [← hmarg] at h1
        exact (integrable_map_measure h1.aestronglyMeasurable measurable_snd.aemeasurable).mp h1
      have hlt := hint.lintegral_lt_top
      have hle : ∫⁻ p, ENNReal.ofReal (cst q.1 q.2 p.1 p.2) ∂πlc ≤
          ∫⁻ p, ENNReal.ofReal |p.2 - (q.2 : ℝ)| ∂πlc :=
        lintegral_mono fun p => ENNReal.ofReal_le_ofReal (cst_le _ _ _ _)
      exact lt_top_iff_ne_top.mpr (fun h => (lt_of_le_of_lt hle hlt).ne (EReal.coe_ennreal_eq_top_iff.mp h))
  choose Γq hΓmeas hΓnull hΓopt using key
  refine ⟨⋂ q, Γq q, MeasurableSet.iInter hΓmeas, ?_, ?_⟩
  · rw [Set.compl_iInter]
    exact measure_iUnion_null hΓnull
  · intro x x' ym yp y' h1 h2 h3 ⟨hxx', hym, hyp⟩
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hxx'
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hyp
    have hd : 0 < yp - ym := by linarith
    set lr : ℝ := (y' - ym) / (yp - ym) with hlr
    set mr : ℝ := (yp - y') / (yp - ym) with hmr
    have hlr0 : 0 < lr := div_pos (by linarith) hd
    have hmr0 : 0 < mr := div_pos (by linarith) hd
    have hlm : lr + mr = 1 := by rw [hlr, hmr, ← add_div]; field_simp; ring
    have hy' : y' = lr * yp + mr * ym := by
      rw [hlr, hmr]; field_simp; ring
    set l : NNReal := ⟨lr, hlr0.le⟩
    set m : NNReal := ⟨mr, hmr0.le⟩
    have hlmN : (l : ENNReal) + (m : ENNReal) = 1 := by
      rw [← ENNReal.coe_add]
      have : l + m = 1 := NNReal.eq (by rw [NNReal.coe_add]; exact hlm)
      rw [this]; rfl
    set P1 : ℝ × ℝ := (x, yp)
    set P2 : ℝ × ℝ := (x, ym)
    set P3 : ℝ × ℝ := (x', y')
    have h12 : P1 ≠ P2 := by simp [P1, P2]; linarith
    have h13 : P1 ≠ P3 := by simp [P1, P3]; intro h; linarith
    have h23 : P2 ≠ P3 := by simp [P2, P3]; intro h; linarith
    let S : Finset (ℝ × ℝ) := {P1, P2, P3}
    let w : ℝ × ℝ → NNReal := fun p => if p = P1 then l else if p = P2 then m else 1
    have hS : (↑S : Set (ℝ × ℝ)) ⊆ ⋂ q, Γq q := by
      intro p hp
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    have hα : (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) =
        (l : ENNReal) • Measure.dirac P1 + ((m : ENNReal) • Measure.dirac P2 +
          ((1 : NNReal) : ENNReal) • Measure.dirac P3) := by
      have hn1 : P1 ∉ ({P2, P3} : Finset (ℝ × ℝ)) := by
        rw [Finset.mem_insert, Finset.mem_singleton]; exact not_or.mpr ⟨h12, h13⟩
      have hn2 : P2 ∉ ({P3} : Finset (ℝ × ℝ)) := by
        rw [Finset.mem_singleton]; exact h23
      rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton]
      have w1 : w P1 = l := if_pos rfl
      have w2 : w P2 = m := by
        show (if P2 = P1 then l else if P2 = P2 then m else 1) = m
        rw [if_neg h12.symm, if_pos rfl]
      have w3 : w P3 = 1 := by
        show (if P3 = P1 then l else if P3 = P2 then m else 1) = 1
        rw [if_neg h13.symm, if_neg h23.symm]
      rw [w1, w2, w3]
    set α' : Measure (ℝ × ℝ) := (l : ENNReal) • Measure.dirac (x', yp) +
        ((m : ENNReal) • Measure.dirac (x', ym) + ((1 : NNReal) : ENNReal) • Measure.dirac (x, y'))
    have hcomp : MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' := by
      rw [hα]
      refine ⟨?_, ?_, integrable3 _ _ _ _ _ _ _, integrable3 _ _ _ _ _ _ _, ?_⟩
      · rw [map3 measurable_fst, map3 measurable_fst]
        simp only [P1, P2, P3, ENNReal.coe_one, one_smul]
        rw [← add_assoc, ← add_smul, hlmN, one_smul, ← add_assoc, ← add_smul, hlmN, one_smul,
          add_comm]
      · rw [map3 measurable_snd, map3 measurable_snd]
      · intro ρ _ _
        rw [integral3, integral3]
        have hl' : (l : ℝ) = lr := rfl
        have hm' : (m : ℝ) = mr := rfl
        simp only [P1, P2, P3, NNReal.coe_one, one_mul]
        rw [hl', hm', hy']; ring
    have hle := hΓopt (s, t) S w (hS.trans (Set.iInter_subset _ _)) α' hcomp
    rw [hα] at hle
    unfold MartOT.Var.cost at hle
    rw [integralE_of_nonneg _ _ (fun p => cst_nonneg _ _ _ _),
      integralE_of_nonneg _ _ (fun p => cst_nonneg _ _ _ _)] at hle
    have hle' := EReal.coe_ennreal_le_coe_ennreal_iff.mp hle
    rw [lintegral3, lintegral3] at hle'
    simp only [P1, P2, P3, cst] at hle'
    have hxs : x ∈ Set.Iic (s : ℝ) := le_of_lt hs1
    have hx's : x' ∉ Set.Iic (s : ℝ) := by simp; exact hs2
    simp only [Set.indicator_of_mem hxs, Set.indicator_of_notMem hx's, one_mul, zero_mul,
      ENNReal.ofReal_zero, mul_zero, add_zero, zero_add, ENNReal.coe_one] at hle'
    rw [abs_of_pos (by linarith : (0:ℝ) < yp - t), abs_of_neg (by linarith : ym - (t:ℝ) < 0),
      abs_of_neg (by linarith : y' - (t:ℝ) < 0)] at hle'
    rw [ENNReal.coe_nnreal_eq, ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul l.coe_nonneg,
      ← ENNReal.ofReal_mul m.coe_nonneg, ← ENNReal.ofReal_add (mul_nonneg l.coe_nonneg (by linarith))
        (mul_nonneg m.coe_nonneg (by linarith)),
      ENNReal.ofReal_le_ofReal_iff (by linarith)] at hle'
    have hl' : (l : ℝ) = lr := rfl
    have hm' : (m : ℝ) = mr := rfl
    rw [hl', hm'] at hle'
    have hkey : lr * (yp - t) + mr * -(ym - t) - -(y' - t) = 2 * lr * (yp - t) := by
      rw [hy']; linear_combination (t:ℝ) * hlm
    nlinarith [mul_pos hlr0 (by linarith : (0:ℝ) < yp - t)]
