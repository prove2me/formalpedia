-- Prove2me | solution 1 for GlobalTheory.ConvexCutOff.exists_perm_of_ofFn_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:05:13.982635+00:00
-- url     : https://prove2.me/submissions/d54bd3a6-011a-49d2-8602-c5865c53cea3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
import Theorems.Thm_GlobalTheory_FiberCardPermutation_exists_perm_of_ofFn_perm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff
namespace GlobalTheory.ConvexCutOff
theorem _root_.solution {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ σ : Equiv.Perm (Fin n), v = w ∘ σ := by
  first
  | exact @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | (apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm ..)
end GlobalTheory.ConvexCutOff
