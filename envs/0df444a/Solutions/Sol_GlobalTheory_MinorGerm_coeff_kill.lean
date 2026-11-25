-- Prove2me | solution 1 for GlobalTheory.MinorGerm.coeff_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:12.368334+00:00
-- url     : https://prove2.me/submissions/d47ab47b-6fe7-4424-b4b0-9d63477ce3ec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
namespace GlobalTheory.MinorGerm
theorem _root_.solution (p : σ → Prop) [DecidablePred p] (m : σ →₀ ℕ) (hm : ∀ x ∈ m.support, p x)
    (P : MvPolynomial σ C) : MvPolynomial.coeff m (kill p P) = MvPolynomial.coeff m P := by
  classical
  refine MvPolynomial.induction_on' P (fun u a => ?_) (fun P Q hP hQ => ?_)
  · unfold kill
    rw [MvPolynomial.aeval_monomial]
    by_cases hu : ∀ x ∈ u.support, p x
    · have h : (u.prod fun i k => (if p i then MvPolynomial.X i else 0 : MvPolynomial σ C) ^ k) =
          u.prod fun i k => MvPolynomial.X i ^ k := by
        apply Finset.prod_congr rfl
        intro x hx
        dsimp only
        rw [if_pos (hu x hx)]
      rw [h, MvPolynomial.algebraMap_eq, ← MvPolynomial.monomial_eq]
    · push_neg at hu
      obtain ⟨x, hx, hpx⟩ := hu
      have hz : (u.prod fun i k => (if p i then MvPolynomial.X i else 0 : MvPolynomial σ C) ^ k) = 0 := by
        rw [Finsupp.prod]
        apply Finset.prod_eq_zero hx
        rw [if_neg hpx]
        exact zero_pow (Finsupp.mem_support_iff.1 hx)
      rw [hz, mul_zero, MvPolynomial.coeff_zero, MvPolynomial.coeff_monomial, if_neg]
      rintro rfl
      exact hpx (hm x hx)
  · rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ]
end GlobalTheory.MinorGerm
