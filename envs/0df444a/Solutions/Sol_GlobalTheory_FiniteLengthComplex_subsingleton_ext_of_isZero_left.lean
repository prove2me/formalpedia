-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.subsingleton_ext_of_isZero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:03:21.003886+00:00
-- url     : https://prove2.me/submissions/8ca8348c-6285-45cd-9694-f4bea2529f2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution {X : ModuleCat.{0} R} (h : IsZero X) (Y : ModuleCat.{0} R)
    (n : ℕ) : Subsingleton (Abelian.Ext.{0} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.mk₀_id_comp x, h.eq_zero_of_src (𝟙 X), Ext.mk₀_zero, Ext.zero_comp]
end GlobalTheory.FiniteLengthComplex
