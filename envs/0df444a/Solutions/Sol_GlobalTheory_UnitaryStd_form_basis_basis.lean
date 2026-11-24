-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.form_basis_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:00.089114+00:00
-- url     : https://prove2.me/submissions/d10508b9-aab2-4fdb-8ac7-5e0c8fea2f4b

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijective
import Theorems.Thm_GlobalTheory_UnitaryStd_basis_apply
import Theorems.Thm_GlobalTheory_UnitaryStd_form_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.UnitaryStd
namespace GlobalTheory.UnitaryStd
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (a c : Fin g ⊕ Fin g) :
    form ρ g S (basis ρ g (j, c)) (basis ρ g (i, a)) =
      S j i * (Matrix.J (Fin g) ℤ) a c := by
  rw [form_apply, Matrix.J]
  simp only [basis_apply, dotProduct]
  rcases a with k | k <;> rcases c with l | l <;>
    simp [Pi.single_apply, Prod.ext_iff, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  all_goals simp [ite_and, Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, mul_ite]
  all_goals (split_ifs <;> simp_all)
end GlobalTheory.UnitaryStd
