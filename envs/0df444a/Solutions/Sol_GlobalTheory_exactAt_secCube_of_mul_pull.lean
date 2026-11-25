-- Prove2me | solution 1 for GlobalTheory.exactAt_secCube_of_mul_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:44:24.16624+00:00
-- url     : https://prove2.me/submissions/01bd950d-d75e-496a-98d3-f38a1c954c6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
import Theorems.Thm_GlobalTheory_TraceDescent_exactAt_of_pull
import Theorems.Thm_GlobalTheory_torsion_invariant_descends


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
namespace GlobalTheory
theorem _root_.solution : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  intro L K _ _ P m N I _ _ D p hm _ H
  classical
  haveI := P.isAb.comm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => hm (by rw [h, Nat.cast_zero])
  let G : Subgroup (𝟙_ (Over (Sp K)) ⟶ P.A) := (powMonoidHom m).ker
  have hc : Nat.card G = m ^ (2 * P.g) := (L.mulN _ P m hm1).2.2.2.2 K (𝟙 _) hm
  haveI : Finite G := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega))
  haveI : Fintype G := Fintype.ofFinite G
  have hgal := GlobalTheory.torsion_invariant_descends (fun S _ P n hn =>
    have h := L.mulN S P n hn
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) K P m hm
  refine GlobalTheory.TraceDescent.exactAt_of_pull (Out.mulA P.A m).left N (G := G)
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
    (fun U f hf => hgal U f fun y hy e => hf ⟨y, hy⟩ e) (fun y z => ?_) _ _ ?_ D p H
  · have hy : y.1 ^ m = 1 := y.2
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
      MonObj.comp_one, _root_.one_mul]
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
      Subgroup.coe_mul, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit P.A ≫ z.1)]
  · rw [← Nat.card_eq_fintype_card, hc, Nat.cast_pow]
    exact (IsUnit.mk0 _ hm).pow _
end GlobalTheory
