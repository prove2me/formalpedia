-- Prove2me | solution 1 for GlobalTheory.TateMatrices.ev_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:44:49.268935+00:00
-- url     : https://prove2.me/submissions/194d1dcf-0fa7-4c37-b712-ab96c4180803

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}
namespace GlobalTheory.TateMatrices
theorem _root_.solution {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (h : B.gg →ₗ[R₀] (O : Type)) (b : B.gg ⊗[R₀] (O : Type)) :
    B.ev h b = ∑ a, (Module.Basis.baseChange (O : Type) gb).repr
      (TensorProduct.comm R₀ B.gg (O : Type) b) a * h (gb a) := by
  induction b using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul x r =>
    simp only [BX.ev, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply,
      TensorProduct.comm_tmul, Module.Basis.baseChange_repr_tmul]
    conv_lhs => rw [← gb.sum_repr x]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  | add a b ha hb =>
    simp only [BX.ev, map_add] at *
    rw [ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [Finsupp.add_apply]; ring
end GlobalTheory.TateMatrices
