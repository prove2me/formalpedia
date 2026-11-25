-- Prove2me | solution 1 for GlobalTheory.DiagBlock.coeff_mul_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:08.629846+00:00
-- url     : https://prove2.me/submissions/0f120659-2bd0-4dfc-bb7b-dfa43de7a47b

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {C : Type} [Field C] {σ : Type} (p : σ → Prop)
    (G H : MvPowerSeries σ C)
    (hG : ∀ m, MvPowerSeries.coeff m G ≠ 0 → ∀ x ∈ m.support, p x)
    (hH : ∀ m, MvPowerSeries.coeff m H ≠ 0 → ∀ x ∈ m.support, ¬ p x)
    (a b : σ →₀ ℕ) (ha : ∀ x ∈ a.support, p x) (hb : ∀ x ∈ b.support, ¬ p x) :
    MvPowerSeries.coeff (a + b) (G * H) = MvPowerSeries.coeff a G * MvPowerSeries.coeff b H := by
  classical
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨u, v⟩ huv hne
    have huv' := Finset.HasAntidiagonal.mem_antidiagonal.1 huv
    simp only at huv'
    by_contra hprod
    have hu := hG u (left_ne_zero_of_mul hprod)
    have hv := hH v (right_ne_zero_of_mul hprod)
    apply hne
    have key : ∀ x, u x = a x ∧ v x = b x := by
      intro x
      have hx := congrArg (fun f => f x) huv'
      simp only [Finsupp.add_apply] at hx
      by_cases hpx : p x
      · have h1 : v x = 0 := by
          by_contra h0; exact hv x (Finsupp.mem_support_iff.2 h0) hpx
        have h2 : b x = 0 := by
          by_contra h0; exact hb x (Finsupp.mem_support_iff.2 h0) hpx
        omega
      · have h1 : u x = 0 := by
          by_contra h0; exact hpx (hu x (Finsupp.mem_support_iff.2 h0))
        have h2 : a x = 0 := by
          by_contra h0; exact hpx (ha x (Finsupp.mem_support_iff.2 h0))
        omega
    exact Prod.ext (Finsupp.ext fun x => (key x).1) (Finsupp.ext fun x => (key x).2)
  · intro h
    exact (h (by simp)).elim
end GlobalTheory.DiagBlock
