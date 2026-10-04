-- Prove2me | solution 1 for MDPFinance.PDMDP.theorem_8_2_7
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:31:42.69491+00:00
-- url     : https://prove2.me/submissions/d5c74839-ba77-4693-ba8c-0c4d51fcc9bf

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Bounding
import Definitions.Def_MDPFinance_PDMDP_Relaxed
import Definitions.Def_MDPFinance_PDMDP_Process

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

instance : IsEmpty (ControlFn Empty) := ⟨fun α => (α.1 0).elim⟩

noncomputable def Emb0 : EmbeddedKernel Mk0 where
  Qprime := fun p => isEmptyElim p.2
  hQprime_meas := fun s _ => by
    rw [Set.eq_empty_of_isEmpty (_ ⁻¹' s)]
    exact MeasurableSet.empty
  hQprime := fun xα => isEmptyElim xα.2

end PDMDPCex

open PDMDPCex in
theorem solution : ¬ (∀ {E U : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U]
    [TopologicalSpace.MetrizableSpace U] [SecondCountableTopology U] [StandardBorelSpace U]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (EmbR : EmbeddedKernelRelaxed Mk) (b : E → ℝ)
    (hb_cont : Continuous b) (cr cQ cφ : ℝ) (hbound : IsUpperBoundingFunctionPDMDP Mk b cr cQ cφ)
    (hαb : cQ * cφ < 1) (hcc : ContinuityCompactnessAssumptions Mk b)
    (Uemb : U → V) (hUemb_cont : Continuous Uemb) (hUemb_inj : Function.Injective Uemb)
    (hcase :
      (∀ t x (α α' : ℝ → U), Measurable α → Measurable α' → Mk.φ t α x = Mk.φ t α' x) ∨
        (Convex ℝ (Set.range Uemb) ∧
          (∀ x, ∃ Lx : V →ₗ[ℝ] E, ∀ u, Mk.μ (x, u) = Lx (Uemb u)) ∧
          ∀ x (u v w : U) (a c : ℝ), 0 ≤ a → 0 ≤ c → a + c = 1 →
            Uemb w = a • Uemb u + c • Uemb v →
            (a : EReal) * (((Mk.r (x, u) : ℝ) : EReal) +
                (Mk.lam : EReal) * erealIntegral (Mk.Q (x, u)) (JrelInfSup Mk EmbR)) +
              (c : EReal) * (((Mk.r (x, v) : ℝ) : EReal) +
                (Mk.lam : EReal) * erealIntegral (Mk.Q (x, v)) (JrelInfSup Mk EmbR)) ≤
            ((Mk.r (x, w) : ℝ) : EReal) +
              (Mk.lam : EReal) * erealIntegral (Mk.Q (x, w)) (JrelInfSup Mk EmbR))),
    ∃ f : E → ControlFn U, Measurable f ∧
      (∀ x, JinfEmbed Mk Emb (fun _ => f) x = JinfSup Mk Emb x) ∧
      (∀ x, JinfSup Mk Emb x = JrelInfSup Mk EmbR x) ∧
      ∀ x, JinfSup Mk Emb x = TEmbed Mk Emb (JinfSup Mk Emb) x) := by
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
    refine ⟨isCompact_univ, ?_, ?_, fun _ _ _ p => p.2.elim,
      (upperSemicontinuous_const : UpperSemicontinuous fun _ : ℝ × Empty => (0:ℝ))⟩
    · intro p
      exact isEmptyElim p.2.1
    · exact cont_empty _ _ _
  obtain ⟨f, _⟩ := h (V := ℝ) Mk0 Emb0 EmbR0 (fun _ => 0) continuous_const 0 0 0 hbound
    (by norm_num) hcc (fun u => u.elim) (cont_empty _ _ _) (fun u => u.elim)
    (Or.inl fun _ _ α => isEmptyElim α)
  exact isEmptyElim (f 0)

#print axioms solution
