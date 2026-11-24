-- Prove2me | solution 1 for GlobalTheory.DegKer.card_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:21:59.394011+00:00
-- url     : https://prove2.me/submissions/bdee7aad-b740-4324-b6c9-7e9444585320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Theorems.Thm_GlobalTheory_DegKer_exists_descent

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer
namespace GlobalTheory.DegKer
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A]
    [LocallyOfFiniteType A.hom] (α : A ⟶ A) [IsMonHom α] [IsFinite α.left] (Ω : Type) [Field Ω]
    (s : Sp Ω ⟶ Sp K) :
    Nat.card {x : Out.baseOver (Sp K) ⟶ A // x ≫ α = 1} =
      Nat.card {y : Over.mk s ⟶ A // y ≫ α = 1} := by
  let t : Over.mk s ⟶ Out.baseOver (Sp K) := Over.homMk s (Category.comp_id _)
  have hinj : ∀ x x' : Out.baseOver (Sp K) ⟶ A, t ≫ x = t ≫ x' → x = x' := by
    intro x x' h
    ext1
    refine ext_of_apply_closedPoint_eq A.hom (Over.w x) (Over.w x') ?_
    have h1 : x.left (s (IsLocalRing.closedPoint Ω)) = x'.left (s (IsLocalRing.closedPoint Ω)) :=
      congr(($h).left (IsLocalRing.closedPoint Ω))
    rwa [Subsingleton.elim (s (IsLocalRing.closedPoint Ω)) (IsLocalRing.closedPoint K)] at h1
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨t ≫ x.1, by rw [Category.assoc, x.2, comp_one]⟩) ⟨?_, ?_⟩)
  · intro x x' h
    exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    let o : Out.baseOver (Sp K) ⟶ A := 1
    have ho : IsClosed {o.left (IsLocalRing.closedPoint K)} :=
      ((pointEquivClosedPoint A.hom) ⟨o.left, Over.w o⟩).2
    have h1 : y ≫ α = t ≫ o := by rw [hy, comp_one]
    have h2 : α.left (y.left (IsLocalRing.closedPoint Ω)) = o.left (IsLocalRing.closedPoint K) := by
      have h3 : α.left (y.left (IsLocalRing.closedPoint Ω)) =
          o.left (s (IsLocalRing.closedPoint Ω)) := congr(($h1).left (IsLocalRing.closedPoint Ω))
      rwa [Subsingleton.elim (s (IsLocalRing.closedPoint Ω)) (IsLocalRing.closedPoint K)] at h3
    have hc : IsClosed {y.left (IsLocalRing.closedPoint Ω)} :=
      isClosed_of_subset_discrete_closed (Set.singleton_subset_iff.mpr h2)
        (α.left.isDiscrete_preimage_singleton (o.left (IsLocalRing.closedPoint K)))
        (ho.preimage α.left.continuous)
    let x : Out.baseOver (Sp K) ⟶ A :=
      Over.homMk (pointOfClosedPoint A.hom _ hc) (pointOfClosedPoint_comp A.hom _ hc)
    have hx : t ≫ x = y := by
      ext1
      have h4 := exists_descent A.hom Ω y.left hc
      rw [Over.w y] at h4
      exact h4
    refine ⟨⟨x, hinj _ _ ?_⟩, Subtype.ext hx⟩
    rw [← Category.assoc, hx, hy, comp_one]
end GlobalTheory.DegKer
