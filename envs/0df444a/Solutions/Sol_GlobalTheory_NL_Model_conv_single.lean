-- Prove2me | solution 1 for GlobalTheory.NL.Model.conv_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:51:02.743969+00:00
-- url     : https://prove2.me/submissions/313ce8d2-a68c-4268-8267-949934c1b34f

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
namespace GlobalTheory.NL.Model
theorem _root_.solution (e : PowerSeries L) (a : ℤ) (d : M) (k : ℤ) :
    conv e (Pi.single a d : ℤ → M) k =
      if a ≤ k then PowerSeries.coeff (k - a).toNat e • d else 0 := by
  unfold conv
  split_ifs with h
  · rw [finsum_eq_single _ (k - a).toNat]
    · have : k - ((k - a).toNat : ℤ) = a := by omega
      rw [this, Pi.single_eq_same]
    · intro j hj
      have : k - (j : ℤ) ≠ a := by omega
      rw [Pi.single_eq_of_ne this, smul_zero]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have : k - (j : ℤ) ≠ a := by omega
    rw [Pi.single_eq_of_ne this, smul_zero]
end GlobalTheory.NL.Model
