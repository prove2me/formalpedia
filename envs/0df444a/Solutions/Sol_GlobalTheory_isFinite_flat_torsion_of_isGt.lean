-- Prove2me | solution 1 for GlobalTheory.isFinite_flat_torsion_of_isGt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:07.92657+00:00
-- url     : https://prove2.me/submissions/9a4c84ce-d9b3-4808-94d9-052e653cbf88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsFiniteFlatTorsionOfIsGt
import Theorems.Thm_GlobalTheory_ExtensionTorsion_torsionHom_of_mulN
import Theorems.Thm_GlobalTheory_Diag_flat_mulN
import Theorems.Thm_GlobalTheory_Diag_isFinite_mulN
import Theorems.Thm_GlobalTheory_flat_descendsAlong_fpqc
import Theorems.Thm_GlobalTheory_isAffineHom_descendsAlong_fpqc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open ExtensionTorsion
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G], E.IsGt G → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion E.B N).hom → Flat (torsion E.B N).hom → IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom := by
  rintro S E G _ _ ⟨D⟩ N hN h1 h2
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have a1 : Flat (torsionHom D.q N).left :=
    torsionHom_of_mulN @Flat D.i D.q D.isKernel N hl
  have a2 : IsAffineHom (torsionHom D.q N).left :=
    torsionHom_of_mulN @IsAffineHom D.i D.q D.isKernel N inferInstance
  have a3 : UniversallyClosed (torsionHom D.q N).left :=
    torsionHom_of_mulN @UniversallyClosed D.i D.q D.isKernel N inferInstance
  have a4 : LocallyOfFiniteType (torsionHom D.q N).left :=
    torsionHom_of_mulN @LocallyOfFiniteType D.i D.q D.isKernel N inferInstance
  have a5 : IsFinite (torsionHom D.q N).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  rw [← Over.w (torsionHom D.q N)]
  exact ⟨inferInstance, inferInstance⟩
end GlobalTheory
