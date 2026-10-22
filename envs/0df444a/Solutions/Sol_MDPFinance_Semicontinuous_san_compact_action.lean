-- Prove2me | solution 1 for MDPFinance.Semicontinuous.san_compact_action
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-11T16:36:55.79103+00:00
-- url     : https://prove2.me/submissions/cb48dcc0-7c51-45db-8c38-be2beb53d5ce

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Theorems.Thm_MDPFinance_Semicontinuous_measurable_maximizer_existence

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous

namespace MDPFinance.Semicontinuous.CompactActionSketch

lemma L_bound {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (c : ℝ) (hc : 0 ≤ c) (hvc : ∀ x, (v x ⊔ 0) ≤ ((c * b x : ℝ) : EReal))
    (xa : E × A) (hxa : xa ∈ M.D n) :
    L M n v xa ≤ (((cr + c * αb) * b xa.1 : ℝ) : EReal) := by
  have hP : ∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa) ≤ ENNReal.ofReal (c * (αb * b xa.1)) := by
    calc ∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa)
        ≤ ∫⁻ x', ENNReal.ofReal c * ENNReal.ofReal (b x') ∂(M.Q n xa) := by
          apply lintegral_mono
          intro x'
          have h1 := EReal.toENNReal_le_toENNReal (hvc x')
          rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe,
            ENNReal.ofReal_mul hc] at h1
          exact h1
      _ = ENNReal.ofReal c * ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q n xa) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (αb * b xa.1) := by
          gcongr; exact hb.hQ n hn xa hxa
      _ = ENNReal.ofReal (c * (αb * b xa.1)) := (ENNReal.ofReal_mul hc).symm
  have hI : erealIntegral (M.Q n xa) v ≤ ((c * (αb * b xa.1) : ℝ) : EReal) := by
    unfold erealIntegral
    have hneg : -((∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂(M.Q n xa) : ENNReal) : EReal) ≤ 0 :=
      by rw [EReal.neg_le, neg_zero]; exact EReal.coe_ennreal_nonneg _
    have hnn : 0 ≤ c * (αb * b xa.1) :=
      mul_nonneg hc (mul_nonneg hb.hαb (hb.hb_nonneg _))
    calc _ ≤ ((∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa) : ENNReal) : EReal) :=
          add_le_of_nonpos_right hneg
      _ ≤ ((ENNReal.ofReal (c * (αb * b xa.1)) : ENNReal) : EReal) :=
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hP
      _ = _ := by rw [EReal.coe_ennreal_ofReal, max_eq_left hnn]
  have hr : M.r n xa ≤ cr * b xa.1 := le_trans (le_max_left _ _) (hb.hr n hn xa hxa)
  unfold L
  calc (M.r n xa : EReal) + erealIntegral (M.Q n xa) v
      ≤ ((cr * b xa.1 : ℝ) : EReal) + ((c * (αb * b xa.1) : ℝ) : EReal) :=
        add_le_add (EReal.coe_le_coe_iff.2 hr) hI
    _ = _ := by rw [← EReal.coe_add]; congr 1; ring

lemma T_bound {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hTm : Measurable (T M n v)) :
    T M n v ∈ IBbPlus b := by
  obtain ⟨_, _, c, hc, hvc⟩ := hv
  have hK : 0 ≤ cr + c * αb := add_nonneg hb.hcr (mul_nonneg hc hb.hαb)
  have hle : ∀ x, T M n v x ≤ (((cr + c * αb) * b x : ℝ) : EReal) := by
    intro x
    exact iSup₂_le fun a ha => L_bound M b cr cg αb hb n hn v c hc hvc (x, a) ha
  refine ⟨hTm, fun x => ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle x), cr + c * αb, hK,
    fun x => sup_le (hle x) ?_⟩
  exact EReal.coe_nonneg.2 (mul_nonneg hK (hb.hb_nonneg x))

lemma g_mem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) :
    (fun x => (M.g x : EReal)) ∈ IBbPlus b := by
  refine ⟨measurable_coe_real_ereal.comp M.hg_meas, fun x => EReal.coe_ne_top _, cg, hb.hcg,
    fun x => ?_⟩
  have h := hb.hg x
  refine sup_le (EReal.coe_le_coe_iff.2 (le_trans (le_max_left _ _) h)) ?_
  exact EReal.coe_nonneg.2 (le_trans (le_max_right _ _) h)

/-- Fiberwise upper semicontinuity of `a ↦ L_n v(x,a)` from fiberwise upper semicontinuity of
the reward and of the integral term. -/
lemma L_usc_fiber {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace A]
    {N : ℕ} (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (x : E)
    (hQ : UpperSemicontinuousOn (fun a => erealIntegral (M.Q n (x, a)) v) (M.Dx n x))
    (hr : UpperSemicontinuousOn (fun a => M.r n (x, a)) (M.Dx n x)) :
    UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x) := by
  intro a ha
  have h1 : UpperSemicontinuousOn (fun a => ((M.r n (x, a) : ℝ) : EReal)) (M.Dx n x) :=
    continuous_coe_real_ereal.comp_upperSemicontinuousOn hr
      (fun a b h => EReal.coe_le_coe_iff.2 h)
  exact UpperSemicontinuousWithinAt.add' (h1 a ha) (hQ a ha)
    (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))

end MDPFinance.Semicontinuous.CompactActionSketch

open MDPFinance.Semicontinuous.CompactActionSketch

theorem solution {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (hD_compact : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hQ_usc : ∀ n < N, ∀ v ∈ IBbPlus b, ∀ x,
        UpperSemicontinuousOn (fun a => erealIntegral (M.Q n (x, a)) v) (M.Dx n x))
    (hr_usc : ∀ n < N, ∀ x, UpperSemicontinuousOn (fun a => M.r n (x, a)) (M.Dx n x)) :
    StructureAssumption M (fun _ => IBbPlus b) (fun n => {f | IsDecisionRule M n f}) := by
  have key : ∀ n < N, ∀ v ∈ IBbPlus b, Measurable (T M n v) ∧ ∃ f, IsMaximizer M n v f :=
    fun n hn v hv => measurable_maximizer_existence M b cr cg αb hb n hn v hv (hD_compact n hn)
      (fun x => L_usc_fiber M n v x (hQ_usc n hn v hv x) (hr_usc n hn x))
  refine ⟨fun _ v hv => ⟨hv.1, hv.2.1⟩, fun _ _ f hf => hf, g_mem M b cr cg αb hb,
    fun n hn v hv => T_bound M b cr cg αb hb n hn v hv (key n hn v hv).1,
    fun n hn v hv => ?_⟩
  obtain ⟨f, hf⟩ := (key n hn v hv).2
  exact ⟨f, hf.1, hf⟩
