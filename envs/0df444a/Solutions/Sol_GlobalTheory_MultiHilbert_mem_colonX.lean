-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.mem_colonX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:50.614878+00:00
-- url     : https://prove2.me/submissions/c2389d85-a09e-4053-9118-fa2d7a017a86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution {I : Ideal (MvPolynomial σ K)} {i : σ} {G : MvPolynomial σ K} :
    G ∈ colonX I i ↔ X i * G ∈ I := Iff.rfl
end GlobalTheory.MultiHilbert
