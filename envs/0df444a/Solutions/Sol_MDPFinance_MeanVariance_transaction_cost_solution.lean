-- Prove2me | solution 1 for MDPFinance.MeanVariance.transaction_cost_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:07:14.164083+00:00
-- url     : https://prove2.me/submissions/30a8a446-a8af-41af-a8e9-cf01383db4d3

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostOperators
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance Cardinal

namespace TCCex

theorem exists_nonmeasurable_real : ∃ S : Set ℝ, ¬ MeasurableSet S := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hle : #{t : Set ℝ | MeasurableSet t} ≤ 𝔠 := by
    have e : (Real.measurableSpace) = MeasurableSpace.generateFrom (⋃ a : ℚ, {Set.Iio (a : ℝ)}) := by
      rw [BorelSpace.measurable_eq (α := ℝ), Real.borel_eq_generateFrom_Iio_rat]
    have := MeasurableSpace.cardinal_measurableSet_le_continuum
      (s := ⋃ a : ℚ, {Set.Iio (a : ℝ)}) ?_
    · convert this using 3
      rw [e]
    · refine (Cardinal.mk_le_aleph0_iff.mpr ?_).trans aleph0_le_continuum
      exact Set.countable_iUnion (fun _ => Set.countable_singleton _) |>.to_subtype
  have huniv : {t : Set ℝ | MeasurableSet t} = Set.univ := Set.eq_univ_of_forall h
  rw [huniv, mk_univ, mk_set, mk_real] at hle
  exact absurd hle (not_le.mpr (cantor 𝔠))

noncomputable def UU (S : Set ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.sqrt x else S.indicator (fun _ => 1) (Real.log (-x))

theorem eqOn (S : Set ℝ) : Set.EqOn Real.sqrt (UU S) (Set.Ici 0) := by
  intro x hx
  simp only [Set.mem_Ici] at hx
  simp [UU, hx]

noncomputable def M0 (S : Set ℝ) : TransactionCostMarket Unit where
  measIP := Measure.dirac ()
  isProb := inferInstance
  N := 0
  i := fun _ => 0
  hi_pos := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  c := 0
  hc0 := le_rfl
  hc1 := one_pos
  Rtilde := fun _ _ => 1
  hRtilde_meas := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hRtilde_pos := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hRtilde_indep := iIndepFun.of_subsingleton
  hRtilde_int := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  γ := 1 / 2
  U := UU S
  hU_mono := by
    intro x hx y hy hxy
    rw [← eqOn S hx, ← eqOn S hy]
    exact Real.sqrt_lt_sqrt hx hxy
  hU_concave := Real.strictConcaveOn_sqrt.congr (eqOn S)
  hU_cont := Real.continuous_sqrt.continuousOn.congr (fun x hx => (eqOn S hx).symm)
  hU_hom := fun x hx lam hlam => by
    rw [← eqOn S (Set.mem_Ici.mpr hx), ← eqOn S (Set.mem_Ici.mpr (by positivity)),
      Real.sqrt_mul hlam.le, Real.sqrt_eq_rpow]

theorem V0 (S : Set ℝ) (x0 x1 : ℝ) : (M0 S).V 0 x0 x1 = UU S (x0 + x1) := by
  unfold TransactionCostMarket.V
  have hadm : ∀ π : ℕ → ℝ × ℝ → ℝ, (M0 S).IsAdmissible 0 π :=
    fun π k _ hk => absurd hk (Nat.not_lt_zero k)
  have hv : ∀ π : ℕ → ℝ × ℝ → ℝ, (M0 S).Vpi π 0 x0 x1 = UU S (x0 + x1) := by
    intro π
    show ∫ ω, UU S (((M0 S).terminalState π 0 0 x0 x1 ω).1 +
      ((M0 S).terminalState π 0 0 x0 x1 ω).2) ∂(Measure.dirac ()) = _
    simp [TransactionCostMarket.terminalState]
  simp only [Set.mem_setOf_eq]
  conv_lhs => arg 1; ext π; rw [ciSup_pos (hadm π), hv π]
  exact ciSup_const

end TCCex

open TCCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (M : TransactionCostMarket Ω),
    (∀ n ≤ M.N, IsInIM M.γ (fun x => M.V n x.1 x.2)) ∧
      (∀ x ∈ Estate, M.V M.N x.1 x.2 = M.U (x.1 + x.2)) ∧
      (∀ n < M.N, ∀ x ∈ Estate,
        M.V n x.1 x.2 = ⨆ a ∈ M.Arange x.1 x.2,
          ∫ ω, M.V (n + 1) (M.h x.1 x.2 a * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
      (∃ ap am : ℕ → ℝ, ∀ n < M.N,
        (ap n ∈ Set.Icc (0 : ℝ) 1 ∧
          (∀ a ∈ Set.Icc (0 : ℝ) 1,
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP ≤
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - ap n) * (1 + M.i (n + 1)))
              (ap n * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) 1,
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP =
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - ap n) * (1 + M.i (n + 1)))
              (ap n * M.Rtilde (n + 1) ω) ∂M.measIP → a ≤ ap n)) ∧
        (am n ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP ≤
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * am n) * (1 + M.i (n + 1)))
              (am n * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP =
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * am n) * (1 + M.i (n + 1)))
              (am n * M.Rtilde (n + 1) ω) ∂M.measIP → a ≤ am n)) ∧
        ∃ fstar : ℕ → ℝ × ℝ → ℝ,
          (∀ n < M.N, ∀ x ∈ Estate,
            let qp : EReal := if ap n < 1 then ((ap n / ((1 - M.c) * (1 - ap n)) : ℝ) : EReal) else ⊤
            let qm : EReal :=
              if am n < 1 / (1 + M.c) then ((am n / (1 - (1 + M.c) * am n) : ℝ) : EReal) else ⊤
            (qp < ratio x.1 x.2 → fstar n x = (x.2 + x.1 / (1 - M.c)) * ap n) ∧
            (qm ≤ ratio x.1 x.2 → ratio x.1 x.2 ≤ qp → fstar n x = x.2) ∧
            (ratio x.1 x.2 < qm → fstar n x = (x.1 + (1 + M.c) * x.2) * am n)) ∧
          M.IsAdmissible 0 fstar ∧
          ∀ x ∈ Estate, M.Vpi fstar 0 x.1 x.2 = M.V 0 x.1 x.2)) := by
  intro h
  obtain ⟨S, hS⟩ := exists_nonmeasurable_real
  have hm := ((h (M0 S)).1 0 le_rfl).1
  have e : (fun x : ℝ × ℝ => (M0 S).V 0 x.1 x.2) = fun x => UU S (x.1 + x.2) := by
    funext x; exact V0 S x.1 x.2
  rw [e] at hm
  apply hS
  have hg : Measurable (fun t : ℝ => ((-Real.exp t : ℝ), (0 : ℝ))) := by fun_prop
  have hcomp := hm.comp hg
  have : S = (fun t : ℝ => UU S ((-Real.exp t, (0 : ℝ)).1 + (-Real.exp t, (0 : ℝ)).2)) ⁻¹' {1} := by
    ext t
    have hneg : ¬ (0 ≤ -Real.exp t + 0) := by have := Real.exp_pos t; linarith
    simp only [Set.mem_preimage, Set.mem_singleton_iff, UU, hneg, if_false, add_zero, neg_neg,
      Real.log_exp]
    have hexp : ¬ Real.exp t ≤ 0 := not_le.mpr (Real.exp_pos t)
    by_cases ht : t ∈ S <;> simp [ht, hexp]
  rw [this]
  exact hcomp (measurableSet_singleton 1)

#print axioms solution
