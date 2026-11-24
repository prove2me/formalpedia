-- Prove2me | solution 1 for GlobalTheory.NormEq.isUnit_of_v_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:26.790791+00:00
-- url     : https://prove2.me/submissions/6a6d9796-bf5a-4e13-afc1-abe4fe092f2e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution (y : intL L) (hy : Valued.v (y : L) = 1) : IsUnit y := by
  have hy0 : (y : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hy; exact zero_ne_one hy
  have hinv : (y : L)⁻¹ ∈ intL L := by
    change Valued.v ((y : L)⁻¹) ≤ 1
    rw [map_inv₀, hy, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hy0])⟩
end GlobalTheory.NormEq
