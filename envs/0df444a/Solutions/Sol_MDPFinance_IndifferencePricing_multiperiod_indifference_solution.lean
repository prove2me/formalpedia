-- Prove2me | solution 1 for MDPFinance.IndifferencePricing.multiperiod_indifference_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:50:43.525352+00:00
-- url     : https://prove2.me/submissions/8ad050ed-c7c7-4737-9de9-2b9658ca8200

import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_MultiperiodMarket

open MeasureTheory ProbabilityTheory MDPFinance.IndifferencePricing Cardinal

namespace IndiffCex

theorem exists_nonmeasurable_real : ∃ S : Set ℝ, ¬ MeasurableSet S := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hle : #{t : Set ℝ | MeasurableSet t} ≤ 𝔠 := by
    have e : (Real.measurableSpace) =
        MeasurableSpace.generateFrom (⋃ a : ℚ, {Set.Iio (a : ℝ)}) := by
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

noncomputable def μ4 : Measure (Fin 4) := (PMF.uniformOfFintype (Fin 4)).toMeasure

instance : IsProbabilityMeasure μ4 := by unfold μ4; infer_instance

theorem μ4_single (k : Fin 4) : μ4 {k} = ENNReal.ofReal (1 / 4) := by
  unfold μ4
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
  simp

noncomputable def Rt (ω : Fin 4) : ℝ := if ω.val < 2 then 2 else 1 / 2
noncomputable def Rh (ω : Fin 4) : ℝ := if ω.val % 2 = 0 then 2 else 1 / 2

noncomputable def M0 : MultiperiodIndifferenceMarket (Fin 4) where
  measIP := μ4
  isProb := inferInstance
  N := 1
  u := 2
  d := 1 / 2
  uhat := 2
  dhat := 1 / 2
  h0d := by norm_num
  hd1 := by norm_num
  h1u := by norm_num
  hdhat_uhat := by norm_num
  γ := 1
  hγ := one_pos
  Rtilde := fun _ => Rt
  Rhat := fun _ => Rh
  hRtilde_meas := fun _ => Measurable.of_discrete
  hRhat_meas := fun _ => Measurable.of_discrete
  p1 := 1 / 4
  p2 := 1 / 4
  p3 := 1 / 4
  p4 := 1 / 4
  hp_pos := by norm_num
  hp_sum := by norm_num
  hlaw1 := fun _ _ _ => by
    have : {ω : Fin 4 | Rt ω = 2 ∧ Rh ω = 2} = {0} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh] <;> norm_num
    rw [this, μ4_single]
  hlaw2 := fun _ _ _ => by
    have : {ω : Fin 4 | Rt ω = 2 ∧ Rh ω = 1 / 2} = {1} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh] <;> norm_num
    rw [this, μ4_single]
  hlaw3 := fun _ _ _ => by
    have : {ω : Fin 4 | Rt ω = 1 / 2 ∧ Rh ω = 2} = {2} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh] <;> norm_num
    rw [this, μ4_single]
  hlaw4 := fun _ _ _ => by
    have : {ω : Fin 4 | Rt ω = 1 / 2 ∧ Rh ω = 1 / 2} = {3} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh] <;> norm_num
    rw [this, μ4_single]
  hR_indep := iIndepFun.of_subsingleton

theorem VH_zero (x s ŝ : ℝ) : M0.VH (fun _ _ => 0) 0 x s ŝ = 0 := by
  obtain ⟨S, hS⟩ := exists_nonmeasurable_real
  let φbad : ℕ → ℝ × ℝ × ℝ → ℝ := fun _ p => S.indicator (fun _ => 1) p.1
  have hbad : ¬ M0.IsAdmissible 0 φbad := by
    intro h
    have hm : Measurable (φbad 0) := h 0 le_rfl (by show 0 < 1; norm_num)
    apply hS
    have : S = (fun x : ℝ => (x, (0 : ℝ), (0 : ℝ))) ⁻¹' ((φbad 0) ⁻¹' {1}) := by
      ext x
      simp [φbad, Set.indicator_apply]
    rw [this]
    exact (measurable_id.prodMk measurable_const) (hm (measurableSet_singleton 1))
  have hle : ∀ φ, (⨆ (_ : φ ∈ {φ : ℕ → ℝ × ℝ × ℝ → ℝ | M0.IsAdmissible 0 φ}),
      ∫ ω, (fun p => -Real.exp (-M0.γ * (p.1 - (fun _ _ => (0 : ℝ)) p.2.1 p.2.2)))
        (M0.terminalState φ (M0.N - 0) 0 x s ŝ ω) ∂M0.measIP) ≤ 0 := by
    intro φ
    refine Real.iSup_le (fun _ => integral_nonpos fun ω => ?_) le_rfl
    exact neg_nonpos.mpr (Real.exp_pos _).le
  unfold MultiperiodIndifferenceMarket.VH MultiperiodIndifferenceMarket.VHAt
  apply le_antisymm
  · exact Real.iSup_le hle le_rfl
  · refine le_trans (le_of_eq ?_) (le_ciSup ⟨0, ?_⟩ φbad)
    · haveI : IsEmpty (φbad ∈ {φ : ℕ → ℝ × ℝ × ℝ → ℝ | M0.IsAdmissible 0 φ}) := ⟨hbad⟩
      exact (Real.iSup_of_isEmpty _).symm
    · rintro _ ⟨φ, rfl⟩
      exact hle φ

theorem int_lb (a : ℝ) : 1 / 4 ≤ ∫ ω, Real.exp (-1 * a * (Rt ω - 1)) * 1 ∂μ4 := by
  rw [integral_fintype (Integrable.of_finite)]
  have hreal : ∀ k : Fin 4, μ4.real {k} = 1 / 4 := by
    intro k
    rw [Measure.real, μ4_single, ENNReal.toReal_ofReal (by norm_num)]
  simp only [hreal, smul_eq_mul, mul_one]
  have hnn : ∀ k : Fin 4, 0 ≤ 1 / 4 * Real.exp (-1 * a * (Rt k - 1)) :=
    fun k => by positivity
  rcases le_total 0 a with ha | ha
  · have h2 : 1 ≤ Real.exp (-1 * a * (Rt 2 - 1)) := by
      apply Real.one_le_exp
      simp [Rt]; nlinarith
    calc (1 : ℝ) / 4 ≤ 1 / 4 * Real.exp (-1 * a * (Rt 2 - 1)) := by nlinarith
      _ ≤ ∑ k, 1 / 4 * Real.exp (-1 * a * (Rt k - 1)) :=
        Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ 2)
  · have h0 : 1 ≤ Real.exp (-1 * a * (Rt 0 - 1)) := by
      apply Real.one_le_exp
      simp [Rt]; nlinarith
    calc (1 : ℝ) / 4 ≤ 1 / 4 * Real.exp (-1 * a * (Rt 0 - 1)) := by nlinarith
      _ ≤ ∑ k, 1 / 4 * Real.exp (-1 * a * (Rt k - 1)) :=
        Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ 0)

end IndiffCex

open IndiffCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
    (M : MultiperiodIndifferenceMarket Ω) (h : ℝ → ℝ → ℝ) (hh : ∀ s ŝ, 0 ≤ h s ŝ),
    ∃ dseq : ℕ → ℝ → ℝ → ℝ,
      (∀ s ŝ, dseq M.N s ŝ = Real.exp (M.γ * h s ŝ)) ∧
      (∀ n < M.N, ∀ s ŝ,
        dseq n s ŝ = ⨅ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rtilde (n + 1) ω - 1)) *
          dseq (n + 1) (s * M.Rtilde (n + 1) ω) (ŝ * M.Rhat (n + 1) ω) ∂M.measIP) ∧
      (∀ n ≤ M.N, ∀ x s ŝ, 0 < s → 0 < ŝ →
        M.VH h n x s ŝ = -Real.exp (-M.γ * x) * dseq n s ŝ) ∧
      (∀ n ≤ M.N, ∀ x s ŝ, 0 < s → 0 < ŝ →
        M.VH (fun _ _ => 0) n x s ŝ = -Real.exp (-M.γ * x) * M.vGeneric ^ (M.N - n)) ∧
      (∀ n ≤ M.N, ∀ s ŝ, 0 < s → 0 < ŝ →
        M.IsIndifferencePriceAt h M.N n s ŝ
          (1 / M.γ * Real.log (dseq n s ŝ / M.vGeneric ^ (M.N - n)))) ∧
      (∀ n < M.N, ∀ s ŝ, 0 < s → 0 < ŝ → ∀ vnext : ℝ → ℝ → ℝ,
        (∀ s' ŝ', 0 < s' → 0 < ŝ' → M.IsIndifferencePriceAt h M.N (n + 1) s' ŝ' (vnext s' ŝ')) →
        ∃ w : ℝ, M.IsIndifferencePriceAt vnext (n + 1) n s ŝ w ∧
          M.IsIndifferencePriceAt h M.N n s ŝ w)) := by
  intro hall
  obtain ⟨dseq, h1, h2, h3, _⟩ := hall M0 (fun _ _ => 0) (fun _ _ => le_rfl)
  have hd1 : ∀ s ŝ, dseq 1 s ŝ = 1 := fun s ŝ => by
    have := h1 s ŝ
    simpa [M0] using this
  have hd0 : dseq 0 1 1 = ⨅ a : ℝ, ∫ ω, Real.exp (-1 * a * (Rt ω - 1)) * 1 ∂μ4 := by
    rw [h2 0 (by show 0 < 1; norm_num) 1 1]
    congr 1
    funext a
    congr 1
    funext ω
    rw [hd1]
    rfl
  have hpos : 1 / 4 ≤ dseq 0 1 1 := by
    rw [hd0]
    exact le_ciInf int_lb
  have H := h3 0 (Nat.zero_le _) 0 1 1 one_pos one_pos
  rw [VH_zero] at H
  have : Real.exp (-M0.γ * 0) = 1 := by simp
  rw [this] at H
  linarith

#print axioms solution
