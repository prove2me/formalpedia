-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:57.332573+00:00
-- url     : https://prove2.me/submissions/511bbbe1-ae3a-4f66-8938-1e80014f3f18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
variable {T Y S : Scheme.{u}}
variable {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {A : Type u} [CommRing A] [_root_.IsReduced A] {a : A}
    (h : ∀ (k : Type u) [Field k] (φ : A →+* k), φ a = 0) : a = 0 :=
  IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun p _ =>
    Ideal.algebraMap_residueField_eq_zero.mp (h p.ResidueField (algebraMap A _)))
end GlobalTheory
