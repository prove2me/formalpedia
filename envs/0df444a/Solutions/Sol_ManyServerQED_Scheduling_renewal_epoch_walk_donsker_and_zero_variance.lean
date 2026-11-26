-- Prove2me | solution 1 for ManyServerQED.Scheduling.renewal_epoch_walk_donsker_and_zero_variance
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:58:29.115535+00:00
-- url     : https://prove2.me/submissions/9cad6c03-f8ec-4c06-8f55-81c61983534b

import Theorems.Thm_DurrettProbability_donsker
import Definitions.Def_ManyServerQED_Scheduling_Model

open MeasureTheory ProbabilityTheory Filter Topology Finset
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy DurrettProbability
open scoped ENNReal NNReal

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k)
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    letI : IsProbabilityMeasure M.P := M.isProb
    (0 < M.cU2 i →
      TendstoInDistribution (fun n : ℕ =>
        walkPath (fun j ω => (M.U i (j+1) ω-1)/Real.sqrt (M.cU2 i)) n)
        atTop (brownianPath B) (fun _ => M.P) P') ∧
    (M.cU2 i = 0 → ∀ᵐ ω ∂M.P, ∀ j : ℕ, M.U i (j+1) ω = 1) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let g : ℕ → (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k) := fun j => Sum.inl (i,j)
  have hg : Function.Injective g := fun _ _ h => congrArg Prod.snd (Sum.inl.inj h)
  have hiU : iIndepFun (fun j => M.U i (j+1)) M.P := (M.indep 0).precomp hg
  have hId (j : ℕ) : IdentDistrib (M.U i (j+1)) (M.U i 1) M.P M.P :=
    M.U_ident i (j+1) (by omega)
  have hMeas (j : ℕ) : Measurable (M.U i (j+1)) := M.U_meas _ _
  constructor
  · intro hσ
    let s := Real.sqrt (M.cU2 i)
    let Y (j : ℕ) (ω : Ω) := (M.U i (j+1) ω-1)/s
    have hs : 0 < s := Real.sqrt_pos.2 hσ
    have hY (j : ℕ) : Measurable (Y j) := ((hMeas j).sub_const 1).div_const s
    have hid (j : ℕ) : IdentDistrib (Y j) (Y 0) M.P M.P :=
      (hId j).comp ((measurable_id.sub_const 1).div_const s)
    have hind : iIndepFun Y M.P :=
      hiU.comp (fun _ (x:ℝ) => (x-1)/s) (fun _ => (measurable_id.sub_const 1).div_const s)
    have hmem := (M.U_memLp i).sub (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 M.P)
    have hy2 : MemLp (Y 0) 2 M.P := by
      have h := hmem.const_mul (1/s)
      convert h using 1
      funext ω
      simp [Y,div_eq_mul_inv,mul_comm]
    have hy0 : ∫ ω, Y 0 ω ∂M.P = 0 := by
      change (∫ ω, (M.U i 1 ω-1)/s ∂M.P) = 0
      rw [integral_div,integral_sub ((M.U_memLp i).integrable one_le_two) (integrable_const 1),
        M.U_mean]
      simp
    have hvar : ∫ ω, Y 0 ω^2 ∂M.P = 1 := by
      change (∫ ω, ((M.U i 1 ω-1)/s)^2 ∂M.P) = 1
      simp_rw [div_pow]
      rw [integral_div,Real.sq_sqrt hσ.le,div_eq_one_iff_eq hσ.ne']
      rw [SystemSequence.cU2, variance_eq_integral (M.U_meas i 1).aemeasurable, M.U_mean]
    exact DurrettProbability.donsker hY hind hid hy2.integrable_sq hy0 hvar hB hBc
  · intro hzero
    have he : evariance (M.U i 1) M.P = 0 := by
      have hne := (M.U_memLp i).evariance_ne_top
      exact ((ENNReal.toReal_eq_zero_iff _).1 hzero).resolve_right hne
    have hAE : M.U i 1 =ᵐ[M.P] fun _ => 1 := by
      simpa only [M.U_mean] using (evariance_eq_zero_iff (M.U_meas i 1).aemeasurable).1 he
    refine ae_all_iff.2 (fun j => ?_)
    have hl : M.P.map (M.U i 1) = Measure.dirac (1:ℝ) := by
      rw [Measure.map_congr hAE, Measure.map_const, measure_univ, one_smul]
    exact (show HasLaw (M.U i (j+1)) (Measure.dirac (1:ℝ)) M.P from
      ⟨(hMeas j).aemeasurable,(hId j).map_eq.trans hl⟩).ae_eq_of_dirac
