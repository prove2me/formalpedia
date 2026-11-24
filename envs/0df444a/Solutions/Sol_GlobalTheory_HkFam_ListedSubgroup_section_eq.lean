-- Prove2me | solution 1 for GlobalTheory.HkFam.ListedSubgroup.section_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:12.338982+00:00
-- url     : https://prove2.me/submissions/86b2b741-4848-4731-b37f-75275919dc9b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupEqRangeOfLists
import Theorems.Thm_GlobalTheory_GrpTangent_finiteEtale_mulN_torsion
import Theorems.Thm_GlobalTheory_LatticeTorsion_existsUnique_torsion
import Theorems.Thm_GlobalTheory_eq_of_preconnected_of_unramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
open GlobalTheory GlobalTheory.HkFam GlobalTheory.HkFam.ListedSubgroup
variable {S : Scheme.{0}}
namespace GlobalTheory.HkFam.ListedSubgroup
theorem _root_.solution [ConnectedSpace S] (G : Over S) [GrpObj G] [IsAbelianScheme G] {N : ℕ}
    (hN : IsUnit (N : Γ(S, ⊤))) {a b : 𝟙_ (Over S) ⟶ G} (ha : a ^ N = 1) (hb : b ^ N = 1)
    {k : Type} [Field k] (x : Sp k ⟶ S) (h : x ≫ a.left = x ≫ b.left) : a = b := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  obtain ⟨a', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N a ha
  obtain ⟨b', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N b hb
  have hx : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) = (toUnit (Over.mk x) ≫ b') ≫ torsion.ι G N := by
    rw [Category.assoc, Category.assoc]
    exact Over.OverMorphism.ext h
  have hpow : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) ^ N = 1 := by
    rw [Category.assoc, ← MonObj.comp_pow, ha, MonObj.comp_one]
  have hab : toUnit (Over.mk x) ≫ a' = toUnit (Over.mk x) ≫ b' :=
    (LatticeTorsion.existsUnique_torsion G N _ hpow).unique rfl hx.symm
  have : a' = b' := Over.OverMorphism.ext
    (eq_of_preconnected_of_unramified (T := S) (torsion G N).hom ((Over.w a').trans (Over.w b').symm) x
      (congrArg CommaMorphism.left hab))
  rw [this]
end GlobalTheory.HkFam.ListedSubgroup
