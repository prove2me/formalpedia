-- Prove2me | solution 1 for MDPFinance.MeanVariance.qp_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:52:05.314964+00:00
-- url     : https://prove2.me/submissions/06c44f37-c3c6-4b33-a98f-0c75c74d02a9

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary
import Definitions.Def_MDPFinance_MeanVariance_QPValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance Cardinal

namespace QPCex

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

noncomputable def μ2 : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure μ2 := by unfold μ2; infer_instance

theorem μ2_real (k : Bool) : μ2.real {k} = 1 / 2 := by
  unfold μ2
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]
  simp

def RR (ω : Bool) : ℝ := if ω then 2 else 0

theorem int_eq (f : Bool → ℝ) : ∫ ω, f ω ∂μ2 = 1 / 2 * f true + 1 / 2 * f false := by
  rw [integral_fintype Integrable.of_finite]
  simp [μ2_real]

noncomputable def M0 : MVMarket Bool 1 where
  measIP := μ2
  isProb := inferInstance
  N := 1
  i := fun _ => 0
  hi_pos := fun _ _ _ => by norm_num
  R := fun _ ω _ => RR ω
  hR_meas := fun _ _ _ => Measurable.of_discrete
  hR_indep := iIndepFun.of_subsingleton
  hR_L2 := fun _ _ _ _ => MemLp.of_discrete
  hR_mean_ne := fun _ _ _ h => by
    have := congrFun h 0
    simp only [int_eq, RR, Pi.zero_apply] at this
    norm_num at this
  hCov_posdef := fun _ _ _ => by
    have e : Matrix.of (fun j k : Fin 1 =>
        ∫ ω, (RR ω - ∫ ω', RR ω' ∂μ2) * (RR ω - ∫ ω', RR ω' ∂μ2) ∂μ2) =
        Matrix.diagonal (fun _ => (1 : ℝ)) := by
      ext j k
      fin_cases j; fin_cases k
      simp [int_eq, RR]
      norm_num
    rw [e]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => one_pos)
  x0 := 1
  hx0 := one_pos
  μ := 2
  hμ := by norm_num

theorem ell_eq : M0.ell 1 = 1 / 2 := by
  have hC : M0.Cmat 1 = Matrix.of (fun _ _ => (2 : ℝ)) := by
    ext j k
    show ∫ ω, RR ω * RR ω ∂μ2 = 2
    rw [int_eq]; simp [RR]
  have hE : M0.Evec 1 = fun _ => (1 : ℝ) := by
    funext j
    show ∫ ω, RR ω ∂μ2 = 1
    rw [int_eq]; simp [RR]
  have hinv : (Matrix.of (fun _ _ => (2 : ℝ)) : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ =
      Matrix.of (fun _ _ => (1 / 2 : ℝ)) := by
    apply Matrix.inv_eq_left_inv
    ext j k
    fin_cases j; fin_cases k
    simp [Matrix.mul_apply]
  unfold MVMarket.ell
  rw [hC, hE, hinv]
  simp [dotProduct, Matrix.mulVec]

theorem VQP_zero (b x : ℝ) : M0.VQP b 0 x = 0 := by
  obtain ⟨S, hS⟩ := exists_nonmeasurable_real
  let πbad : ℕ → ℝ → (Fin 1 → ℝ) := fun _ y _ => S.indicator (fun _ => 1) y
  have hbad : ¬ M0.IsAdmissibleFrom 0 x πbad := by
    intro h
    have hm : Measurable (πbad 0) := h.1 0 le_rfl (by show 0 < 1; norm_num)
    apply hS
    have : S = (fun y : ℝ => πbad 0 y 0) ⁻¹' {1} := by
      ext y
      simp [πbad, Set.indicator_apply]
    rw [this]
    exact (measurable_pi_apply 0 |>.comp hm) (measurableSet_singleton 1)
  have hge : ∀ π, 0 ≤ (⨅ (_ : π ∈ {π : ℕ → ℝ → (Fin 1 → ℝ) | M0.IsAdmissibleFrom 0 x π}),
      ∫ ω, (M0.terminalWealth π (M0.N - 0) 0 x ω - b) ^ 2 ∂M0.measIP) :=
    fun π => Real.iInf_nonneg fun _ => integral_nonneg fun ω => sq_nonneg _
  unfold MVMarket.VQP
  apply le_antisymm
  · refine le_trans (ciInf_le ⟨0, ?_⟩ πbad) (le_of_eq ?_)
    · rintro _ ⟨π, rfl⟩
      exact hge π
    · have : IsEmpty (πbad ∈ {π : ℕ → ℝ → (Fin 1 → ℝ) | M0.IsAdmissibleFrom 0 x π}) := ⟨hbad⟩
      exact Real.iInf_of_isEmpty _
  · exact Real.iInf_nonneg hge

end QPCex

open QPCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (b : ℝ)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))),
    (∀ n ≤ M.N, ∀ x : ℝ, M.VQP b n x = (x * M.S0 M.N / M.S0 n - b) ^ 2 * dseq n) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x : ℝ, fstar n x =
          fun k => (b * M.S0 n / M.S0 M.N - x) * ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k)) ∧
        M.IsOptimalQP b fstar ∧
        M.meanXN fstar = M.x0 * M.S0 M.N * dseq 0 + b * (1 - dseq 0) ∧
        M.meanXNsq fstar = (M.x0 * M.S0 M.N) ^ 2 * dseq 0 + b ^ 2 * (1 - dseq 0))) := by
  intro h
  let dseq : ℕ → ℝ := fun n => if n = 0 then 1 / 2 else 1
  have H := (h M0 1 dseq rfl (fun n hn => by
    have : n = 0 := by
      have : n < 1 := hn
      omega
    subst this
    show (1 / 2 : ℝ) = 1 * (1 - M0.ell 1)
    rw [ell_eq]; norm_num)).1 0 (Nat.zero_le _) 0
  rw [VQP_zero] at H
  simp [MVMarket.S0, dseq] at H

#print axioms solution
