-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.subsingleton_ext_of_isFiniteLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:36.994725+00:00
-- url     : https://prove2.me/submissions/21d52da5-d1fe-4a85-8f75-de49d7aead82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_of_isZero_left
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_shortExact_submodule
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_nonempty_iso_residue

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
theorem _root_.solution [IsLocalRing R] (Y : ModuleCat.{0} R) (n : ℕ)
    (hk : Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of R M) Y n) := by
  induction hM with
  | of_subsingleton =>
    exact subsingleton_ext_of_isZero_left (ModuleCat.isZero_of_subsingleton _) Y n
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨e⟩ := nonempty_iso_residue (R := R) (M ⧸ N)
    have h3 := (extCongrLeft e Y n).symm.toEquiv.subsingleton
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₂ (shortExact_submodule N) Y x
      (@Subsingleton.elim _ ih _ _)
    rw [@Subsingleton.elim _ h3 y 0]
    exact Ext.comp_zero _ _ _ _ _
end GlobalTheory.FiniteLengthComplex
