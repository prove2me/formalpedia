-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.form_cx_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:09.345802+00:00
-- url     : https://prove2.me/submissions/4bfb1180-9d43-4286-9e9c-5c983113b3c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseCh
import Theorems.Thm_GlobalTheory_UnitaryStd_form_cx_coord

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
theorem _root_.solution (S : Matrix (Fin r) (Fin r) ℤ) (p q : Fin r × (Fin g ⊕ Fin g)) :
    form ρ g S (cx ρ g (basis ρ g p)) (basis ρ g q) = if p.2 = q.2 then S p.1 q.1 else 0 := by
  rw [form_cx_coord]
  obtain ⟨i0, a⟩ := p
  obtain ⟨j0, b⟩ := q
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Prod.mk.injEq]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
end GlobalTheory.UnitaryStd
