-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:12.868206+00:00
-- url     : https://prove2.me/submissions/819c1114-9b43-488e-95fa-f3256b780cd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
open NumberField Complex
open scoped nonZeroDivisors ContDiff
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
theorem _root_.solution (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 =
      FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ, coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv,
    Units.val_inv_eq_inv_val]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
