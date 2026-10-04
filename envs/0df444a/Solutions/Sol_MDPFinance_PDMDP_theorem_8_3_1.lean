-- Prove2me | solution 1 for MDPFinance.PDMDP.theorem_8_3_1
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:31:44.066575+00:00
-- url     : https://prove2.me/submissions/d97f82e2-2004-4699-a8d7-4aec04cc3e3f

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

noncomputable def Ch0 : MDChain Unit Empty where
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
  β := 1
  hβ := zero_le_one

end ChainCex

open ChainCex in
theorem solution : ¬ (∀ {E U : Type} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
    [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U] [TopologicalSpace.MetrizableSpace U]
    [SecondCountableTopology U] [StandardBorelSpace U]
    (Ch : MDChain E U) (b : E → ℝ) (cr cQ : ℝ)
    (hbound : IsUpperBoundingFunctionChain Ch b cr cQ) (hαb : cQ * (Ch.lam / (Ch.β + Ch.lam)) < 1)
    (hUcompact : IsCompact (Set.univ : Set U))
    (hqcont : ∀ x y, Continuous (Ch.q x y))
    (hbsum_cont : ∀ x, Continuous fun u => (∑' y, ENNReal.ofReal (Ch.Qy x y u * b y)).toReal)
    (hrusc : ∀ x, UpperSemicontinuous fun u => Ch.r (x, u)),
    (Ch.Vinf ∈ IBbPlus b ∧
        ∀ x, (Ch.β : EReal) * Ch.Vinf x = ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
          (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) Ch.Vinf - Ch.Vinf x))) ∧
      ∃ fstar : E → U, Measurable fstar ∧
        (∀ x, ((Ch.r (x, fstar x) : ℝ) : EReal) +
            (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x (fstar x)) Ch.Vinf - Ch.Vinf x) =
          ⨆ u : U, (((Ch.r (x, u) : ℝ) : EReal) +
            (Ch.lam : EReal) * (erealIntegral (Ch.Qmeas x u) Ch.Vinf - Ch.Vinf x))) ∧
        ∀ x, Ch.Jinf (fun _ => fstar) x = Ch.Vinf x) := by
  intro h
  obtain ⟨_, fstar, _⟩ := h Ch0 (fun _ => 0) 0 0
    ⟨measurable_const, fun _ => le_rfl, le_rfl, le_rfl, fun _ u => u.elim, fun _ u => u.elim⟩
    (by norm_num) isCompact_univ (fun _ _ => cont_empty _ _ _) (fun _ => cont_empty _ _ _)
    (fun _ => usc_empty _)
  exact (fstar ()).elim

#print axioms solution
