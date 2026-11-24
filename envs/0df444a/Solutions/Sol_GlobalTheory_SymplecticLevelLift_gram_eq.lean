-- Prove2me | solution 1 for GlobalTheory.SymplecticLevelLift.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:41.243067+00:00
-- url     : https://prove2.me/submissions/aa25b7b7-f4f5-4db6-b17b-122b9b1da6da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticZmodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSymplecticBasisCongrLevelMod
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymplecticLevelLift
open Matrix Module
namespace GlobalTheory.SymplecticLevelLift
theorem _root_.solution {h : ℕ} {M : Type} [AddCommGroup M] {Ef : LinearMap.BilinForm ℤ M}
    {b : Basis (Fin h ⊕ Fin h) ℤ M} (hb : IsSymplecticBasis Ef b) (hE : Ef.IsAlt)
    (v : Fin h ⊕ Fin h → M) :
    (Matrix.of fun i j => Ef (v i) (v j)) =
      (b.toMatrix v)ᵀ * (-Matrix.J (Fin h) ℤ) * b.toMatrix v := by
  ext i j
  rw [of_apply, hb.apply_eq_sum hE]
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Basis.toMatrix_apply, Matrix.one_apply,
    Finset.sum_sub_distrib]
  ring
end GlobalTheory.SymplecticLevelLift
