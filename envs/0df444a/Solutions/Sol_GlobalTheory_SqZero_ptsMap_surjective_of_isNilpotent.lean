-- Prove2me | solution 1 for GlobalTheory.SqZero.ptsMap_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:19.94066+00:00
-- url     : https://prove2.me/submissions/920bc38a-0773-4ad6-af58-33c55c076e5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_reduction_surjective_of_isNilpotent
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : IsLieBasis v) (q : A →ₐ[R] A')
    (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q)) :
    Function.Surjective (pointsMap G q) := by
  intro y₀
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  obtain ⟨y, hy⟩ := reduction_surjective_of_isNilpotent hv hn (spMap (e.symm : A' →ₐ[R] _) ≫ y₀)
  refine ⟨y, ?_⟩
  rw [ptsMap_apply] at hy ⊢
  have he : q = (e : _ →ₐ[R] A').comp (Ideal.Quotient.mkₐ R (RingHom.ker q)) := by ext x; rfl
  rw [he, ← spMap_comp]
  simp only [Category.assoc]
  rw [hy, ← Category.assoc, spMap_comp, AlgEquiv.comp_symm, spMap_id, Category.id_comp]
end GlobalTheory.SqZero
