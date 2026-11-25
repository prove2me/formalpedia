-- Prove2me | solution 1 for GlobalTheory.ExtensionTorsion.torsionHom_of_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:28:43.237183+00:00
-- url     : https://prove2.me/submissions/9da2c6f6-9d4c-4c2e-856a-1acc5c20874e

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
import Theorems.Thm_GlobalTheory_ExtensionTorsion_exists_isPullback_mulN

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
open GlobalTheory.ExtensionTorsion
open KernelNoTorsion
variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
namespace GlobalTheory.ExtensionTorsion
theorem _root_.solution (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ) (h : Pr (mulN T N).left) :
    Pr (torsionHom q N).left := by
  have hP := IsPullback.of_hasPullback q (torsion.ι B N)
  have hQ := IsPullback.of_hasPullback (pullback.snd q (torsion.ι B N)) (torsionHom q N)
  obtain ⟨c, t, H⟩ := exists_isPullback_mulN i q hk N hP hQ
  have hP' := hP.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h
end GlobalTheory.ExtensionTorsion
