-- Prove2me | solution 1 for MDPFinance.PDMDP.theorem_8_3_3
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:31:43.260415+00:00
-- url     : https://prove2.me/submissions/aff0ad35-fae8-4c8d-a26d-c5bd7085019d

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Chain

open MeasureTheory ProbabilityTheory MDPFinance.PDMDP

namespace ChainCex

theorem cont_empty {X Y : Type} (tX : TopologicalSpace X) (tY : TopologicalSpace Y) [IsEmpty X]
    (f : X → Y) : @Continuous X Y tX tY f :=
  @Continuous.mk X Y tX tY f (fun s _ => by
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]
    exact @isOpen_empty X tX)

theorem usc_empty (f : Empty → ℝ) : UpperSemicontinuous f := fun u => u.elim

noncomputable def Ch0 : MDChainFinite Unit Empty where
  q := fun _ _ u => u.elim
  hq_meas := fun _ _ s _ => by
    rw [Set.eq_empty_of_isEmpty (_ ⁻¹' s)]
    exact MeasurableSet.empty
  hq_offdiag := fun _ _ u => u.elim
  hq_summable := fun _ u => u.elim
  hq_conservative := fun _ u => u.elim
  lam := 1
  hlam := one_pos
  hq_bounded := fun _ u => u.elim
  r := fun _ => 0
  hr_meas := measurable_const
  g := fun _ => 0
  hg_meas := measurable_const
  Th := 1
  hTh := one_pos

end ChainCex

open ChainCex in
theorem solution : ¬ (∀ {E U : Type} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
    [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U] [TopologicalSpace.MetrizableSpace U]
    [SecondCountableTopology U] [StandardBorelSpace U]
    (Ch : MDChainFinite E U) (b : E → ℝ) (cr cg cQ : ℝ)
    (hbound : IsUpperBoundingFunctionChainFinite Ch b cr cg cQ)
    (hUcompact : IsCompact (Set.univ : Set U))
    (hqcont : ∀ x y, Continuous (Ch.q x y))
    (hbsum_cont : ∀ x, Continuous fun u => (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)).toReal)
    (hrusc : ∀ x, UpperSemicontinuous fun u => Ch.r (x, u)),
    (∃ fstar : ℝ → E → U, Measurable (fun p : ℝ × E => fstar p.1 p.2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x,
          ((Ch.r (x, fstar t x) : ℝ) : EReal) +
              (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x (fstar t x)) (Ch.Vinf t) -
                Ch.Vinf t x) =
            ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
              (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) (Ch.Vinf t) - Ch.Vinf t x))) ∧
        ∃ f : ℕ → ℝ → E → ControlFn U, IsChainPolicyFinite f ∧
          (∀ n t x s, (f n t x).1 s = fstar (t + s) x) ∧
          ∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x, Ch.Jinf f t x = Ch.Vinf t x) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) Ch.Th, ∀ x, Ch.Vinf t x = Ch.T Ch.Vinf t x) := by
  intro h
  obtain ⟨⟨fstar, _⟩, _⟩ := h Ch0 (fun _ => 0) 0 0 0
    ⟨measurable_const, fun _ => le_rfl, le_rfl, le_rfl, le_rfl, fun _ u => u.elim,
      fun _ => by simp [Ch0], fun _ u => u.elim⟩
    isCompact_univ (fun _ _ => cont_empty _ _ _) (fun _ => cont_empty _ _ _)
    (fun _ => usc_empty _)
  exact (fstar 0 ()).elim

#print axioms solution
