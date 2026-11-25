-- Prove2me | solution 1 for GlobalTheory.NL.Model.conv_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:15:31.833656+00:00
-- url     : https://prove2.me/submissions/c0a05f3d-a156-43a8-a495-13e0694dc05b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
open TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.NL.Model
namespace _root_.GlobalTheory.NL.Model
theorem _root_.solution (e : PowerSeries L) {u : ℤ → M} {m : ℤ}
    (hm : ∀ k < m, u k = 0) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j e • u (k - (j : ℤ))).Finite := by
  refine (Set.finite_Iic (k - m).toNat).subset fun j hj => ?_
  simp only [Function.mem_support] at hj
  simp only [Set.mem_Iic]
  by_contra hlt
  push_neg at hlt
  exact hj (by rw [hm _ (by omega), smul_zero])
end _root_.GlobalTheory.NL.Model
end GlobalTheory.NL.Model
