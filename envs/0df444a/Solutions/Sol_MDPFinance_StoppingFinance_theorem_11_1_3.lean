-- Prove2me | solution 1 for MDPFinance.StoppingFinance.theorem_11_1_3
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:58:16.776423+00:00
-- url     : https://prove2.me/submissions/0e960a89-3a23-4115-83d1-ad43a9b128b4

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_BinomialModel

open MeasureTheory Filter Topology MDPFinance.StoppingFinance

namespace PathLawAux

noncomputable def bern (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Measure Bool :=
  (PMF.bernoulli q.toNNReal (by simpa using hq1)).toMeasure

instance (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : IsProbabilityMeasure (bern q hq0 hq1) := by
  unfold bern; infer_instance

noncomputable def Qlaw (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bern q hq0 hq1)

theorem bern_single (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    bern q hq0 hq1 {b} = if b then ENNReal.ofReal q else ENNReal.ofReal (1 - q) := by
  unfold bern
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
  cases b
  · simp only [cond_false, Bool.false_eq_true, if_false]
    rw [ENNReal.ofReal]
    congr 1
    ext
    rw [NNReal.coe_sub (by simpa using hq1), Real.coe_toNNReal _ (by linarith)]
    simp [hq0, hq1]
  · simp only [cond_true, if_true]
    rfl

theorem cyl (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) (b : Fin n → Bool) :
    Qlaw q hq0 hq1 {w : ℕ → Bool | ∀ i : Fin n, w (i : ℕ) = b i}
      = ∏ i : Fin n, (if b i then ENNReal.ofReal q else ENNReal.ofReal (1 - q)) := by
  let bext : ℕ → Bool := fun i => if h : i < n then b ⟨i, h⟩ else true
  have hset : {w : ℕ → Bool | ∀ i : Fin n, w (i : ℕ) = b i} =
      Set.pi (↑(Finset.range n) : Set ℕ) (fun i => {bext i}) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
      Set.mem_singleton_iff]
    constructor
    · intro h i hi
      simp only [bext, dif_pos hi]
      exact h ⟨i, hi⟩
    · intro h i
      have := h i i.2
      simp only [bext, dif_pos i.2] at this
      exact this
  unfold Qlaw
  rw [hset, Measure.infinitePi_pi (μ := fun _ => bern q hq0 hq1) (s := Finset.range n)
    (t := fun i => {bext i}) (fun i _ => measurableSet_singleton _)]
  rw [← Fin.prod_univ_eq_prod_range (fun i => bern q hq0 hq1 {bext i})]
  congr 1
  funext i
  rw [bern_single]
  simp [bext]

theorem isPathLaw (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (Qlaw q hq0 hq1) := by
  unfold Qlaw; infer_instance

end PathLawAux

namespace PerpCex

open PathLawAux

noncomputable def M0 : BinomialModel where
  u := 3
  d := 1
  beta := 1 / 2
  q := 1 / 2
  K := 1
  E := Set.Ici 2
  d_lt_u := by norm_num
  d_pos := by norm_num
  beta_mem := by norm_num
  q_mem := by norm_num
  K_pos := by norm_num
  E_pos := fun x hx => by simp only [Set.mem_Ici] at hx; linarith
  E_up := fun x hx => by simp only [Set.mem_Ici] at hx ⊢; linarith
  E_down := fun x hx => by simp only [Set.mem_Ici] at hx ⊢; linarith
  riskNeutral := by norm_num

theorem J_zero (n : ℕ) : ∀ y : ℝ, 1 ≤ y → M0.J n y = 0 := by
  induction n with
  | zero =>
    intro y hy
    show max (1 - y) 0 = 0
    exact max_eq_right (by linarith)
  | succ n ih =>
    intro y hy
    show max (max (1 - y) 0) ((1 / 2 : ℝ) * ((1 / 2 : ℝ) * M0.J n (y * 3) +
      (1 - 1 / 2) * M0.J n (y * 1))) = 0
    rw [ih _ (by linarith), ih _ (by linarith), max_eq_right (by linarith : 1 - y ≤ 0)]
    norm_num

theorem Jlim_zero (y : ℝ) (hy : 1 ≤ y) : M0.Jlim y = 0 := by
  unfold BinomialModel.Jlim
  simp only [J_zero _ y hy, ciSup_const]

theorem hQ : M0.IsPathLaw (Qlaw (1 / 2) (by norm_num) (by norm_num)) :=
  ⟨isPathLaw _ _ _, fun n b => cyl _ _ _ n b⟩

end PerpCex

open PerpCex PathLawAux in
theorem solution : ¬ (∀ (M : BinomialModel) (Q : Measure (ℕ → Bool)) (hQ : M.IsPathLaw Q),
    (∀ x ∈ M.E, M.perpetualValue Q x = (M.Jlim x : EReal) ∧
      Tendsto (fun n => M.J n x) atTop (𝓝 (M.Jlim x))) ∧
    ((∀ x ∈ M.E, M.Jlim x = M.T M.Jlim x) ∧ ∀ x ∈ M.E, 0 ≤ M.Jlim x ∧ M.Jlim x ≤ M.K) ∧
    (M.Superharmonic M.Jlim ∧ (∀ x ∈ M.E, M.payoff x ≤ M.Jlim x) ∧
      ∀ V : ℝ → ℝ, M.Superharmonic V → (∀ x ∈ M.E, M.payoff x ≤ V x) →
        ∀ x ∈ M.E, M.Jlim x ≤ V x) ∧
    ((∀ x ∈ M.E, M.T (M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) x ≤
        M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} x) →
      ∀ x ∈ M.E, M.Jlim x = M.JfStar {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} x ∧
        IsStoppingTime (M.exerciseTime x {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) ∧
        M.EReward Q x (M.exerciseTime x {y | y ∈ M.E ∧ M.Jlim y = M.payoff y}) =
          M.perpetualValue Q x) ∧
    (∃ xstar : ℝ, 0 ≤ xstar ∧ xstar ≤ M.K ∧
      {y | y ∈ M.E ∧ M.Jlim y = M.payoff y} = {y | y ∈ M.E ∧ y ≤ xstar})) := by
  intro h
  obtain ⟨xs, _, hxK, hset⟩ := (h M0 _ hQ).2.2.2.2
  have h2 : (2 : ℝ) ∈ {y | y ∈ M0.E ∧ M0.Jlim y = M0.payoff y} := by
    refine ⟨show (2 : ℝ) ∈ Set.Ici 2 from Set.mem_Ici.mpr le_rfl, ?_⟩
    rw [Jlim_zero 2 (by norm_num)]
    show (0 : ℝ) = max (1 - 2) 0
    norm_num
  rw [hset] at h2
  have : (2 : ℝ) ≤ 1 := h2.2.trans hxK
  norm_num at this

#print axioms solution
