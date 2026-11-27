-- Prove2me | solution 1 for GlobalTheory.points_divisible_and_torsion_of_valuation_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:34.61122+00:00
-- url     : https://prove2.me/submissions/a167c21c-c389-47f0-8594-6ee9c427fa22

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsDivisibleAndTorsionOfValuationIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private theorem torsVal_valuationRing {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) : ValuationRing O := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inr hc.symm⟩
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inl hc.symm⟩
private theorem torsVal_exists_point {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : Spec (CommRingCat.of Ω) ⟶ A) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ P, p ≫ ψ = x := by
  have hJ : JacobsonSpace ↥(Limits.pullback ψ x) :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd ψ x)
  obtain ⟨w⟩ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨z₀, -⟩ := (Limits.pullback.snd ψ x).surjective w
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback ψ x)))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (Limits.pullback.snd ψ x) z hz ≫ Limits.pullback.fst _ _, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, pointOfClosedPoint_comp_assoc]
private theorem torsVal_lift {R₀ : Type} [CommRing R₀] {X Y : Over (Spec (CommRingCat.of R₀))}
    (m : X ⟶ Y) [IsFinite m.left] {O C : Type} [CommRing O] [Field C] [Algebra R₀ O] [Algebra O C]
    [Algebra R₀ C] [IsScalarTower R₀ O C] {v : Valuation C NNReal} (hv : v.Integers O)
    (x : sp (R₀ := R₀) O ⟶ Y) (z : sp (R₀ := R₀) C ⟶ X)
    (h : z ≫ m = spMap (IsScalarTower.toAlgHom R₀ O C) ≫ x) :
    ∃! y : sp (R₀ := R₀) O ⟶ X, y ≫ m = x ∧ spMap (IsScalarTower.toAlgHom R₀ O C) ≫ y = z := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := torsVal_valuationRing hv
  haveI : IsFractionRing O C := hv.isFractionRing
  have hE : ValuativeCriterion.Existence m.left := by
    have h : UniversallyClosed m.left := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness m.left := IsSeparated.valuativeCriterion m.left
  let S : ValuativeCommSq m.left :=
    { R := O, K := C, i₁ := z.left, i₂ := x.left, commSq := ⟨congrArg Over.Hom.left h⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  have hw : l ≫ X.hom = (sp (R₀ := R₀) O).hom := by
    rw [← Over.w m, ← Category.assoc, h2]
    exact Over.w x
  refine ⟨Over.homMk l hw, ⟨Over.OverMorphism.ext h2, Over.OverMorphism.ext h1⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have := (hU S).elim ⟨y.left, congrArg Over.Hom.left hy2, congrArg Over.Hom.left hy1⟩ ⟨l, h1, h2⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)
private theorem torsVal_comp_pow {R₀ : Type} [CommRing R₀] {G T : Over (Spec (CommRingCat.of R₀))}
    [GrpObj G] (y : T ⟶ G) (p : ℕ) : y ≫ ((𝟙 G) ^ p : G ⟶ G) = y ^ p := by
  rw [MonObj.comp_pow, Category.comp_id]
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) := by
  intro R₀ _ G _ _ O C _ _ _ v _ _ _ p hv hfin hsurj
  refine ⟨fun x => ?_, fun z hz => ?_⟩
  · obtain ⟨w, hw⟩ := torsVal_exists_point ((𝟙 G) ^ p : G ⟶ G).left
      (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ x).left
    have hw' : w ≫ G.hom = (sp (R₀ := R₀) C).hom := by
      rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hw]
      exact Over.w _
    obtain ⟨y, ⟨hy, -⟩, -⟩ := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv x (Over.homMk w hw')
      (Over.OverMorphism.ext hw)
    exact ⟨y, by rw [← torsVal_comp_pow, hy]⟩
  · have := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv 1 z
      (by rw [torsVal_comp_pow, hz, MonObj.comp_one])
    simpa only [torsVal_comp_pow] using this
end GlobalTheory
