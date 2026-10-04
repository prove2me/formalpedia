-- Prove2me | solution 1 for MDPFinance.MeanVariance.transaction_cost_structure_assumption
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:07:57.774289+00:00
-- url     : https://prove2.me/submissions/e43511e7-0921-4cf8-b714-2bf9e5b40eae

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostOperators

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance Cardinal

namespace TCSACex

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

end TCSACex

open TCSACex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
    (M : TransactionCostMarket Ω),
    IsInIM M.γ (fun x => M.U (x.1 + x.2)) ∧
      (∀ n < M.N, ∀ v : ℝ × ℝ → ℝ, IsInIM M.γ v → IsInIM M.γ (fun x => M.T n v x.1 x.2)) ∧
      (∀ n < M.N, ∀ v : ℝ × ℝ → ℝ, IsInIM M.γ v →
        ∃ f : ℝ × ℝ → ℝ, IsBuyHoldSellRule f ∧ Measurable f ∧
          ∀ x ∈ Estate, f x ∈ M.Arange x.1 x.2 ∧
            ∫ ω, v (M.h x.1 x.2 (f x) * (1 + M.i (n + 1)),
              f x * M.Rtilde (n + 1) ω) ∂M.measIP = M.T n v x.1 x.2)) := by
  intro h
  obtain ⟨S, hS⟩ := exists_nonmeasurable_real
  have hm : Measurable (fun x : ℝ × ℝ => UU S (x.1 + x.2)) := (h (M0 S)).1.1
  apply hS
  have hg : Measurable (fun t : ℝ => ((-Real.exp t : ℝ), (0 : ℝ))) := by fun_prop
  have hcomp := hm.comp hg
  have : S = (fun t : ℝ => UU S ((-Real.exp t, (0 : ℝ)).1 + (-Real.exp t, (0 : ℝ)).2)) ⁻¹' {1} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, UU, if_false, add_zero, neg_neg,
      Real.log_exp]
    have hexp : ¬ Real.exp t ≤ 0 := not_le.mpr (Real.exp_pos t)
    by_cases ht : t ∈ S <;> simp [ht, hexp]
  rw [this]
  exact hcomp (measurableSet_singleton 1)

#print axioms solution
