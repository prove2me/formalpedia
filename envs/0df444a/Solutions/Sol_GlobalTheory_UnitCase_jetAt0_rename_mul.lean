-- Prove2me | solution 1 for GlobalTheory.UnitCase.jetAt0_rename_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:08:06.965993+00:00
-- url     : https://prove2.me/submissions/b256cf66-686f-49f3-8ba5-c6b1a2949835

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mfact_eq
import Theorems.Thm_GlobalTheory_UnitCase_jetAt0_sum
import Theorems.Thm_GlobalTheory_UnitCase_jetAt0_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution [Fintype κ] (p q : MvPolynomial κ ℤ) (G : MvPowerSeries (κ ⊕ κ) C) :
    jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) p) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q)) G =
      ∑ A ∈ p.support, ∑ B ∈ q.support,
        ((MvPolynomial.coeff A p : ℤ) : C) * (MvPolynomial.coeff B q : ℤ) *
          ((mfact A : C) * mfact B) * MvPowerSeries.coeff (Finsupp.sumElim A B) G := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [map_sum, Finset.sum_mul_sum, jetAt0_sum, MvPolynomial.map_monomial,
    MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, jetAt0_monomial,
    ← Finsupp.sumElim_eq_add, eq_intCast]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  congr 2
  rw [mfact_eq, mfact_eq, mfact_eq, Fintype.prod_sum_type, Nat.cast_mul]
  simp
end GlobalTheory.UnitCase
