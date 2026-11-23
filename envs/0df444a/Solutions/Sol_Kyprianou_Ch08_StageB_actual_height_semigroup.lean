-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_semigroup
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T04:04:44.561272+00:00
-- url     : https://prove2.me/submissions/1497f2f7-cfd0-4d12-a17e-5357d3983431
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
import Theorems.Thm_stageB_bpay_iSup
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_effective_event_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_no_drawdown_null_measurable_of_effective_event
import Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_effective_integral_of_nullmeas
import Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_barrier_support_integral_classical
import Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_raw_set_integral_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_barrier_integral_semigroup_classical
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

private theorem stageB_no_drawdown_event_ae_eq_filtered_raw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (A : SpectrallyNegativeLevy P 𝓕)
    (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω) (b h : ℝ) :
    {ω | NoDrawdownBeforeUpcrossing D.X b h ω} =ᵐ[P]
      {ω | NoDrawdownBeforeUpcrossing A.X b h ω} := by
  filter_upwards [hAX] with ω hω
  have ht : tauPlus A.X b ω = tauPlus D.X b ω := by simp [tauPlus, hω]
  have hr (t : ℝ≥0) : Kyprianou.Ch08.runningSup A.X t ω =
      Kyprianou.Ch08.runningSup D.X t ω := by
    unfold Kyprianou.Ch08.runningSup
    congr 1
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, hω u⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (hω u).symm⟩
  have href (t : ℝ≥0) : reflectAtSup A.X 0 t ω = reflectAtSup D.X 0 t ω := by
    simp [reflectAtSup, hr t, hω t]
  apply propext
  change (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < tauPlus D.X b ω →
      reflectAtSup D.X 0 t ω < h) ↔
    (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < tauPlus A.X b ω →
      reflectAtSup A.X 0 t ω < h)
  constructor
  · intro hD t htA
    simpa [href t] using hD t (by simpa [ht] using htA)
  · intro hA t htD
    simpa [href t] using hA t (by simpa [ht] using htD)

theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∀ a1 a2 h : ℝ, 0 < a1 → 0 < a2 → 0 < h →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X (a1 + a2) h ω},
        Real.exp (Phi ψ q * (a1 + a2)) * discountedAt q (tauPlus D.X (a1 + a2) ω) ∂P) =
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a1 h ω},
        Real.exp (Phi ψ q * a1) * discountedAt q (tauPlus D.X a1 ω) ∂P) *
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a2 h ω},
        Real.exp (Phi ψ q * a2) * discountedAt q (tauPlus D.X a2 ω) ∂P) := by
  classical
  intro a1 a2 h ha1 ha2 hh
  let s0 := source_result81_filtered_avram_model Ω P D ψ hψ
  let A := s0.choose_spec.choose
  let hAX := s0.choose_spec.choose_spec.1
  let e := fun b => Real.exp (Phi ψ q * b)
  let I := stageB_Bars h
  let K := fun b ω => ENNReal.ofReal (e b) * (⨆ r : I, stageB_bpay A (r : ℝ) b q ω)
  let N := fun b => {ω | NoDrawdownBeforeUpcrossing A.X b h ω}
  let E := fun b => {ω | twoSidedExitUpTime A b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing A.X b h ω}
  let S := fun b => {ω | NoDrawdownBeforeUpcrossing D.X b h ω}
  let gA := fun b ω => e b * discountedAt q (tauPlus A.X b ω)
  let gD := fun b ω => e b * discountedAt q (tauPlus D.X b ω)
  change (∫ ω in S (a1 + a2), gD (a1 + a2) ω ∂P) =
    (∫ ω in S a1, gD a1 ω ∂P) * (∫ ω in S a2, gD a2 ω ∂P)
  have hEA (b : ℝ) (hb : 0 < b) : MeasurableSet (E b) := by
    dsimp [E]
    exact actual_height_effective_event_measurable A b h hb hh
  have hNA (b : ℝ) (hb : 0 < b) : NullMeasurableSet (N b) P := by
    have hraw : NullMeasurableSet (S b) P := by
      exact actual_height_no_drawdown_null_measurable_of_effective_event A D hAX b h hb hh
        (by simpa [E] using hEA b hb)
    exact hraw.congr (stageB_no_drawdown_event_ae_eq_filtered_raw A D hAX b h)
  have he_nonneg (b : ℝ) : 0 ≤ e b := by
    dsimp [e]
    exact (Real.exp_pos _).le
  have hIS (b : ℝ) (hb : 0 < b) : ∀ ω : Ω,
      (⨆ r : I, stageB_bpay A (r : ℝ) b q ω) =
        if twoSidedExitUpTime A b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing A.X b h ω then
          ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime A b ω).toReal))) else 0 := by
    intro ω
    simpa [I] using stageB_bpay_iSup A b h q hb hh ω
  have hRed (b : ℝ) (hb : 0 < b) : (∫ ω in N b, gA b ω ∂P) =
      ∫ ω in {ω | tauPlus A.X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing A.X b h ω}, gA b ω ∂P := by
    simpa [N, gA] using stageB_filtered_effective_integral_of_nullmeas A b h (e b) q (hNA b hb)
  have hSupp (b : ℝ) (hb : 0 < b) : (∫ ω, (K b ω).toReal ∂P) = ∫ ω in N b, gA b ω ∂P := by
    simpa [K, N, E, gA, I] using
      stageB_filtered_barrier_support_integral_classical A b h q (e b) hb hh
        (he_nonneg b) (hEA b hb) (hNA b hb) (hIS b hb) (hRed b hb)
  have hRaw (b : ℝ) : (∫ ω in N b, gA b ω ∂P) = ∫ ω in S b, gD b ω ∂P := by
    simpa [N, S, gA, gD] using stageB_filtered_raw_set_integral_eq A D hAX b h q (e b)
  have Ek : e (a1 + a2) = e a1 * e a2 := by
    dsimp [e]
    rw [← Real.exp_add]
    congr 1
    ring
  have hAlg : (∫ ω, (K (a1 + a2) ω).toReal ∂P) =
      (∫ ω, (K a1 ω).toReal ∂P) * (∫ ω, (K a2 ω).toReal ∂P) := by
    simpa [K, I] using
      stageB_filtered_barrier_integral_semigroup_classical A a1 a2 h q (e a1) (e a2)
        (e (a1 + a2)) ha1 ha2 hh (he_nonneg a1) (he_nonneg a2)
        (he_nonneg (a1 + a2)) Ek (fun b hb => hIS b hb)
  calc
    (∫ ω in S (a1 + a2), gD (a1 + a2) ω ∂P) = ∫ ω, (K (a1 + a2) ω).toReal ∂P := by
      rw [← hRaw (a1 + a2), ← hSupp (a1 + a2) (add_pos ha1 ha2)]
    _ = (∫ ω, (K a1 ω).toReal ∂P) * (∫ ω, (K a2 ω).toReal ∂P) := hAlg
    _ = (∫ ω in S a1, gD a1 ω ∂P) * (∫ ω in S a2, gD a2 ω ∂P) := by
      rw [hSupp a1 ha1, hRaw a1, hSupp a2 ha2, hRaw a2]
