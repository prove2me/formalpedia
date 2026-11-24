-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.form_cx_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:51.539333+00:00
-- url     : https://prove2.me/submissions/5184698e-9ba1-4e79-9236-d9d124349a9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseCh
import Theorems.Thm_GlobalTheory_UnitaryStd_basis_repr
import Theorems.Thm_GlobalTheory_UnitaryStd_cx_apply
import Theorems.Thm_GlobalTheory_UnitaryStd_form_apply
import Theorems.Thm_GlobalTheory_UnitaryStd_neg_apply


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
variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
namespace GlobalTheory.UnitaryStd
theorem _root_.solution (S : Matrix (Fin r) (Fin r) ℤ) (y z : Lat ρ g) :
    form ρ g S (cx ρ g y) z = ∑ i, ∑ j, S i j *
      ∑ α : Fin g ⊕ Fin g, (basis ρ g).repr y (i, α) * (basis ρ g).repr z (j, α) := by
  rw [form_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [cx_apply, basis_repr, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, dotProduct,
    Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  ring
end GlobalTheory.UnitaryStd
