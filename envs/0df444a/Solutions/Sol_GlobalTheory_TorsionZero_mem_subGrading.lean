-- Prove2me | solution 1 for GlobalTheory.TorsionZero.mem_subGrading
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:20.455199+00:00
-- url     : https://prove2.me/submissions/e186e048-f700-4252-b2d1-62dd02b8ff86

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]
namespace GlobalTheory.TorsionZero
theorem _root_.solution {𝒜 : ℕ → Submodule K R} {N : ℕ} {T : Subalgebra K R} {e : ℕ} {y : T} :
    y ∈ subGrading 𝒜 N T e ↔ (y : R) ∈ 𝒜 (N * e) := Iff.rfl
end GlobalTheory.TorsionZero
