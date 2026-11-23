-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stageB_filtered_barrier_support_integral_classical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T05:17:28.086775+00:00
-- url     : https://prove2.me/submissions/36465b4a-7659-4ee1-bb93-de8e69e290cc

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
import Theorems.Thm_stageB_tauPlus_coe_eq
import Theorems.Thm_stageB_tauPlus_lt_iff
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (b h q c : ℝ) (hb : 0 < b) (hh : 0 < h)
    (hc : 0 ≤ c)
    (hE : MeasurableSet {ω : Ω |
      twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω})
    (hN : NullMeasurableSet {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω} P)
    (hIS : ∀ ω : Ω,
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω) =
        if twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω then
          ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0)
    (hRed : (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) =
      (∫ ω in {ω : Ω | tauPlus X.X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω},
        c * discountedAt q (tauPlus X.X b ω) ∂P)) :
    (∫ ω, (ENNReal.ofReal c *
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω)).toReal ∂P) =
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) := by
  classical
  let N : Set Ω := {ω | NoDrawdownBeforeUpcrossing X.X b h ω}
  let E : Set Ω := {ω | twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω}
  let K : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal c * (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω)
  have hSupp : (∫ ω, (K ω).toReal ∂P) = ∫ ω in E, (K ω).toReal ∂P := by
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ω hω
    have hEfalse : ¬ (twoSidedExitUpTime X b ω < ⊤ ∧
        NoDrawdownBeforeUpcrossing X.X b h ω) := by
      intro h
      exact hω (by simpa [E] using h)
    dsimp [K]
    rw [hIS ω, if_neg hEfalse]
    simp
  have hdisc (ω : Ω) (hωE : twoSidedExitUpTime X b ω < ⊤) :
      (ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))).toReal =
        discountedAt q (tauPlus X.X b ω) := by
    rw [stageB_tauPlus_coe_eq X b ω]
    cases hu : twoSidedExitUpTime X b ω with
    | top =>
        have htop : (⊤ : ℝ≥0∞) < ⊤ := by simpa [hu] using hωE
        exact False.elim (lt_irrefl _ htop)
    | coe t =>
        simp [discountedAt, hu, ENNReal.toReal_ofReal ((Real.exp_pos _).le)]
  have hclock (ω : Ω) :
      twoSidedExitUpTime X b ω < ⊤ ↔ tauPlus X.X b ω < ⊤ := by
    constructor
    · intro h
      cases hτ : tauPlus X.X b ω with
      | top =>
          obtain ⟨r, hr, _⟩ := (ENNReal.lt_iff_exists_nnreal_btwn).1 h
          have hrtau : (r : WithTop ℝ≥0) < tauPlus X.X b ω := by
            simpa [hτ] using (WithTop.coe_lt_top r)
          have hrclock : (r : ℝ≥0∞) < twoSidedExitUpTime X b ω :=
            (stageB_tauPlus_lt_iff X b ω (t := r)).1 hrtau
          exact False.elim ((not_lt_of_ge (le_of_lt hr)) hrclock)
      | coe t =>
          exact WithTop.coe_lt_top t
    · intro h
      cases hτ : tauPlus X.X b ω with
      | top =>
          exact False.elim (by simpa [hτ] using h)
      | coe t =>
          rw [← stageB_tauPlus_coe_eq X b ω]
          simpa [hτ] using (ENNReal.coe_lt_top : (t : ℝ≥0∞) < ⊤)
  have hset : E = {ω | tauPlus X.X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω} := by
    ext ω
    constructor
    · intro hω
      exact ⟨(hclock ω).1 hω.1, hω.2⟩
    · intro hω
      exact ⟨(hclock ω).2 hω.1, hω.2⟩
  calc
    (∫ ω, (ENNReal.ofReal c *
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω)).toReal ∂P) =
        ∫ ω, (K ω).toReal ∂P := by rfl
    _ = ∫ ω in E, (K ω).toReal ∂P := hSupp
    _ = ∫ ω in E, c * discountedAt q (tauPlus X.X b ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hE] with ω hω
      dsimp [K]
      rw [hIS ω]
      have hωE : twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω := by
        simpa [E] using hω
      rw [if_pos hωE]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, hdisc ω hωE.1]
    _ = ∫ ω in N, c * discountedAt q (tauPlus X.X b ω) ∂P := by
      rw [hset]
      simpa [N] using hRed.symm
