-- Prove2me | solution 1 for HedgePSNV.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T00:30:31.072236+00:00
-- url     : https://prove2.me/submissions/2d9da7ca-6cab-4e09-a891-fe25647c7ec6

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Theorems.Thm_HedgePSNV_proposition_5
import Theorems.Thm_HedgePSNV_proposition_4
import Theorems.Thm_HedgePSNV_riskneutral_nv_maximizer_exists

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNVGlue

open HedgePSNV

lemma ito_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ℱ : ℝ≥0 → MeasurableSpace Ω)
    (W : ℝ≥0 → Ω → ℝ) :
    EthierKurtz.HasBrownianItoIntegral P ℱ W (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun t ω => by simp, fun t => ⟨fun _ _ _ => 0, fun n k _ => measurable_const,
    fun n => ⟨0, fun k _ ω => by simp⟩, ?_, ?_⟩⟩
  · have h0 : ∀ (n : ℕ) (u : ℝ) (ω : Ω),
        EthierKurtz.itoStepValue t n (fun _ _ => (0 : ℝ)) u ω = 0 := by
      intro n u ω
      unfold EthierKurtz.itoStepValue
      exact Finset.sum_eq_zero (fun k _ => by split_ifs <;> rfl)
    intro ε hε
    simp [h0, hε.ne']
  · intro ε hε
    simp [EthierKurtz.itoStepSum, not_le.mpr hε]

lemma zero_mem_AX {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) :
    (((fun _ _ => (0 : ℝ)) : ℝ≥0 → Ω → ℝ), ((fun _ _ => (0 : ℝ)) : ℝ≥0 → Ω → ℝ)) ∈ M.AX := by
  refine ⟨isStronglyProgressive_const _ _, stronglyAdapted_const _ _,
    ⟨fun ω t _ => by simp, fun _ _ => 0, ?_, ?_⟩, ?_, ?_⟩
  · have h : (fun (t : ℝ≥0) (ω : Ω) => if t ≤ p.T then (0 : ℝ) * M.X t ω * M.σ t ω else 0)
        = fun _ _ => 0 := by
      funext t ω; simp
    rw [h]; exact ito_zero _ _ _
  · exact Filter.Eventually.of_forall (fun ω t _ => by simp)
  · exact MemLp.zero
  · intro Q _
    refine ⟨fun t _ => stronglyMeasurable_const, fun t _ => integrable_zero Ω ℝ Q,
      fun s t _ _ => ?_⟩
    show condExp (M.F s) Q (0 : Ω → ℝ) =ᵐ[Q] (0 : Ω → ℝ)
    rw [condExp_zero]

lemma H_memLp {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (hM : M.Standing)
    (hL2 : M.NegPartL2) (P R : ℝ) : MemLp (M.H P R) 2 M.P := by
  have := hM.prob
  have hCm : StronglyMeasurable (M.C p.T) := (hM.C_adapted p.T).mono (M.G.le p.T)
  have hBlaw : HasLaw (M.Bt p.T) (gaussianReal 0 p.T) M.P :=
    hM.brownBt.toIsPreBrownianReal.hasLaw_eval p.T
  have hBm : AEMeasurable (M.Bt p.T) M.P := hBlaw.aemeasurable
  have hB2 : MemLp (M.Bt p.T) 2 M.P := by
    have h := memLp_id_gaussianReal' (μ := 0) (v := p.T) 2 (by simp)
    rw [← hBlaw.map_eq] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hBm).1 h
  have hg : MemLp (fun ω => |R| + max (-(M.C p.T ω)) 0 + |p.σt| * |M.Bt p.T ω|) 2 M.P :=
    ((memLp_const |R|).add hL2).add (hB2.abs.const_mul |p.σt|)
  have hmeas : AEStronglyMeasurable
      (fun ω => max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0) M.P := by
    have hCa : AEMeasurable (M.C p.T) M.P := hCm.measurable.aemeasurable
    exact (by fun_prop : AEMeasurable
      (fun ω => max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0) M.P).aestronglyMeasurable
  have hmax : MemLp (fun ω => max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0) 2 M.P := by
    refine hg.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : -(p.σt * M.Bt p.T ω) ≤ |p.σt| * |M.Bt p.T ω| :=
      (neg_le_abs _).trans_eq (abs_mul _ _)
    have h2 := le_abs_self R
    have h3 := le_max_left (-(M.C p.T ω)) 0
    have h4 : (0 : ℝ) ≤ max (-(M.C p.T ω)) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (by positivity)
  have hH : M.H P R = fun ω => (P - p.c) * (R - p.b * P) -
      (P - p.s) * max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0 := by
    funext ω; rfl
  rw [hH]
  exact (memLp_const _).sub (hmax.const_mul (P - p.s))

lemma Bval_NV_lt_top {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (PNV RNV : ℝ) :
    M.Bval (nvValue p M.P M.AT PNV RNV) PNV RNV < ⊤ := by
  have := hM.prob
  refine lt_of_le_of_lt ?_ (evariance_lt_top (H_memLp M hM hL2 PNV RNV))
  unfold Model.Bval
  refine iInf₂_le_of_le ((fun _ _ => (0 : ℝ)), (fun _ _ => (0 : ℝ))) (zero_mem_AX M) ?_
  refine iInf_le_of_le ?_ ?_
  · simp [nvValue, Model.H]
  · simp

lemma negPart_int_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hL2 : M.NegPartL2) (h5 : M.Assumption5) : M.NegPartIntegrable M.PM := by
  unfold Model.NegPartIntegrable Model.PM
  have hZm : StronglyMeasurable (M.Z p.T) := (h5.1.1 p.T le_rfl).mono (M.F.le p.T)
  rw [integrable_withDensity_iff_integrable_smul' hZm.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hZpos : ∀ ω, 0 ≤ M.Z p.T ω := fun ω => by
    simp only [Model.Z]; exact (Real.exp_pos _).le
  simp_rw [ENNReal.toReal_ofReal (hZpos _), smul_eq_mul]
  exact (h5.2 p.T le_rfl).integrable_mul hL2

end HedgePSNVGlue

open HedgePSNV in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (h1P : Assumption1 (M.P.map M.AT)) (h1M : Assumption1 (M.PM.map M.AT))
    (PNV RNV : ℝ) (hNV : IsNVMaximizer p M.P M.AT PNV RNV)
    (h2 : Assumption2 p M.P M.AT PNV RNV) (h3 : Assumption3 p M.P M.AT PNV RNV)
    (hpos : StochasticOrders.Usual.UsualOrder M.PM M.P (M.C p.T) (M.C p.T))
    (P R : ℝ) (hPR : (P, R) ∈ decisionDomain p)
    (hmin : ∀ P' R' : ℝ, (P', R') ∈ decisionDomain p →
      M.Bval (nvValue p M.P M.AT PNV RNV) P R ≤ M.Bval (nvValue p M.P M.AT PNV RNV) P' R') :
    P ≤ PNV ∧ R ≤ RNV := by
  have hfin : M.Bval (nvValue p M.P M.AT PNV RNV) P R < ⊤ :=
    lt_of_le_of_lt (hmin PNV RNV hNV.1) (HedgePSNVGlue.Bval_NV_lt_top M hM hL2 PNV RNV)
  have hm : 0 ≤ nvValue p M.P M.AT PNV RNV := h2.2.2.le
  have hintM : M.NegPartIntegrable M.PM := HedgePSNVGlue.negPart_int_PM M hL2 h5
  obtain ⟨P', R', hNV'⟩ := HedgePSNV.riskneutral_nv_maximizer_exists p M hM hL2 h5 h1M
  have hA := HedgePSNV.proposition_5 p M hM hL2 h4 h5 h1P h1M PNV RNV hNV h2 h3 _ hm P R hPR
    hmin hfin P' R' hNV'
  have hB := (HedgePSNV.proposition_4 p M hM hintM h4 h5 h1P h1M PNV RNV hNV h2 h3 hpos).1
    P' R' hNV'
  exact ⟨hA.1.trans hB.1, hA.2.trans hB.2⟩
