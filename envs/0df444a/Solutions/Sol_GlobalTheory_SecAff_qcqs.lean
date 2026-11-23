-- Prove2me | solution 1 for GlobalTheory.SecAff.qcqs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:46.656488+00:00
-- url     : https://prove2.me/submissions/d361bd9a-a00f-43af-a9bb-07e3ab8e0026

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
omit [GrpObj A]
namespace GlobalTheory.SecAff
theorem _root_.solution [IsProper A.hom] [IsAffine T.left] :
    CompactSpace (T ⊗ A).left ∧ QuasiSeparatedSpace (T ⊗ A).left := by
  have : IsProper (fst T A).left := inferInstanceAs (IsProper (pullback.fst T.hom A.hom))
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (fst T A).left,
    quasiSeparatedSpace_of_quasiSeparated (fst T A).left⟩
end GlobalTheory.SecAff
