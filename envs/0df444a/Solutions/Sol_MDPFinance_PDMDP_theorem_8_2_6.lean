-- Prove2me | solution 1 for MDPFinance.PDMDP.theorem_8_2_6
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:30:24.87887+00:00
-- url     : https://prove2.me/submissions/0022573d-6e4a-4f7a-83cf-57ec8aa3ff2b

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Bounding
import Definitions.Def_MDPFinance_PDMDP_Relaxed

open MeasureTheory ProbabilityTheory MDPFinance.PDMDP

namespace PDMDPCex

theorem pm_empty (μ : ProbabilityMeasure Empty) : False := by
  have h := μ.prop.measure_univ
  rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty] at h
  exact zero_ne_one h

instance : IsEmpty (ProbabilityMeasure Empty) := ⟨pm_empty⟩
instance : IsEmpty (ℝ → ProbabilityMeasure Empty) := ⟨fun α => pm_empty (α 0)⟩
instance : IsEmpty (ℝ → Empty) := ⟨fun α => (α 0).elim⟩
instance : IsEmpty (RelaxedControlFn Empty) := ⟨fun α => pm_empty (α.1 0)⟩

theorem cont_empty {X Y : Type} (tX : TopologicalSpace X) (tY : TopologicalSpace Y) [IsEmpty X]
    (f : X → Y) : @Continuous X Y tX tY f :=
  @Continuous.mk X Y tX tY f (fun s _ => by
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]
    exact @isOpen_empty X tX)

noncomputable def Mk0 : PDMDPModel ℝ Empty where
  μ := fun p => p.2.elim
  hμ_meas := fun s _ => by
    rw [Set.eq_empty_of_isEmpty ((fun p : ℝ × Empty => p.2.elim) ⁻¹' s)]
    exact MeasurableSet.empty
  φ := fun _ _ x => x
  hφ0 := fun _ _ => rfl
  hφ_ode := fun α => isEmptyElim α
  hφ_cont := fun _ _ => continuous_const
  hφ_meas := fun _ => measurable_snd
  φRel := fun _ _ x => x
  hφRel0 := fun _ _ => rfl
  hφRel_ode := fun α => isEmptyElim α
  hφRel_pt := fun _ α => isEmptyElim α
  Q := Kernel.const _ (Measure.dirac 0)
  isMarkovQ := inferInstance
  lam := 1
  hlam := one_pos
  r := fun _ => 0
  hr_meas := measurable_const
  β := 1
  hβ := zero_le_one

noncomputable def EmbR0 : EmbeddedKernelRelaxed Mk0 where
  QprimeR := fun p => isEmptyElim p.2
  hQprimeR_meas := fun s _ => by
    rw [Set.eq_empty_of_isEmpty (_ ⁻¹' s)]
    exact MeasurableSet.empty
  hQprimeR := fun xα => isEmptyElim xα.2

end PDMDPCex

open PDMDPCex in
theorem solution : ¬ (∀ {E U : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U]
    [TopologicalSpace.MetrizableSpace U] [SecondCountableTopology U] [StandardBorelSpace U]
    (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (b : E → ℝ)
    (hb_cont : Continuous b) (cr cQ cφ : ℝ) (hbound : IsUpperBoundingFunctionPDMDP Mk b cr cQ cφ)
    (hαb : cQ * cφ < 1) (hcc : ContinuityCompactnessAssumptions Mk b),
    (JrelInfSup Mk EmbR ∈ IBbPlus b ∧ UpperSemicontinuous (JrelInfSup Mk EmbR) ∧
        ∀ x, JrelInfSup Mk EmbR x = Trel Mk EmbR (JrelInfSup Mk EmbR) x) ∧
      ∃ f : E → RelaxedControlFn U, Measurable f ∧
        ∀ x, JinfEmbedRelaxed Mk EmbR (fun _ => f) x = JrelInfSup Mk EmbR x) := by
  intro h
  have hbound : IsUpperBoundingFunctionPDMDP Mk0 (fun _ => 0) 0 0 0 :=
    { hb_meas := measurable_const
      hb_nonneg := fun _ => le_rfl
      hcr := le_rfl
      hcQ := le_rfl
      hcφ := le_rfl
      hr := fun _ u => u.elim
      hQ := fun _ u => u.elim
      hφ := fun _ α => isEmptyElim α }
  have hcc : ContinuityCompactnessAssumptions Mk0 (fun _ => 0) := by
    refine ⟨isCompact_univ, ?_, ?_, fun _ _ _ p => p.2.elim, (upperSemicontinuous_const : UpperSemicontinuous fun _ : ℝ × Empty => (0:ℝ))⟩
    · intro p
      exact isEmptyElim p.2.1
    · exact cont_empty _ _ _
  obtain ⟨_, f, _, _⟩ := h Mk0 EmbR0 (fun _ => 0) continuous_const 0 0 0 hbound (by norm_num) hcc
  exact isEmptyElim (f 0)

#print axioms solution
