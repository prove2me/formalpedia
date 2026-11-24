-- Prove2me | solution 1 for GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:59.140749+00:00
-- url     : https://prove2.me/submissions/ed3a9b0a-2adf-49b1-ae80-378fb50395ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
import Theorems.Thm_GlobalTheory_ClosedResidueExt_exists_unramified_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
namespace GlobalTheory.ClosedResidueExt
namespace _root_.GlobalTheory.ClosedResidueExt
theorem _root_.solution : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W],
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        IsAlgClosed (IsLocalRing.ResidueField R) := by
  intro W _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨R, i1, i2, i3, i4, h1, h2, _, h4⟩ := _root_.GlobalTheory.ClosedResidueExt.exists_unramified_ext W hπ
  exact ⟨R, i1, i2, i3, i4, h1, h2, h4⟩
end _root_.GlobalTheory.ClosedResidueExt
end GlobalTheory.ClosedResidueExt
