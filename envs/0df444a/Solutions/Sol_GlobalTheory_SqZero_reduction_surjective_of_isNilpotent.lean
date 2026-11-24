-- Prove2me | solution 1 for GlobalTheory.SqZero.reduction_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:59.309918+00:00
-- url     : https://prove2.me/submissions/c7b49119-53b0-4003-bf5d-baf897dc0331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_reduction_surjective
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
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
theorem _root_.solution (hv : IsLieBasis v) (hJ : IsNilpotent J) :
    Function.Surjective (pointsMap G (Ideal.Quotient.mkₐ R J)) := by
  have main : ∀ k : ℕ, ∀ (B : Type) [CommRing B] [Algebra R B] (I : Ideal B), I ^ (k + 1) = ⊥ →
      Function.Surjective (pointsMap G (Ideal.Quotient.mkₐ R I)) := by
    intro k
    induction k with
    | zero =>
      intro B _ _ I hI
      refine reduction_surjective hv (le_bot_iff.1 ?_)
      rw [← hI]; exact Ideal.pow_le_pow_right (by norm_num)
    | succ k ih =>
      intro B _ _ I hI
      have hle : I ^ (k + 1) ≤ I := Ideal.pow_le_self (by omega)
      have hsq : (I ^ (k + 1)) ^ 2 = ⊥ := by
        rw [← pow_mul]; exact le_bot_iff.1 (hI ▸ Ideal.pow_le_pow_right (by omega))
      have hmap : (I.map (Ideal.Quotient.mkₐ R (I ^ (k + 1)))) ^ (k + 1) = ⊥ := by
        rw [← Ideal.map_pow]
        exact (Ideal.map_eq_bot_iff_le_ker _).2 (by
          intro x hx
          simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hx)
      intro y₀
      let e := DoubleQuot.quotQuotEquivQuotOfLEₐ R hle
      obtain ⟨y₂, hy₂⟩ := ih _ _ hmap (spMap (e.symm : (B ⧸ I) →ₐ[R] _) ≫ y₀)
      obtain ⟨y, hy⟩ := reduction_surjective hv hsq y₂
      refine ⟨y, ?_⟩
      rw [ptsMap_apply] at hy₂ hy ⊢
      have he : Ideal.Quotient.mkₐ R I = (e : _ →ₐ[R] B ⧸ I).comp
          ((Ideal.Quotient.mkₐ R (I.map (Ideal.Quotient.mkₐ R (I ^ (k + 1))))).comp (Ideal.Quotient.mkₐ R (I ^ (k + 1)))) := by
        ext x; rfl
      rw [he, ← spMap_comp, ← spMap_comp]
      simp only [Category.assoc]
      rw [hy, hy₂, ← Category.assoc, spMap_comp, AlgEquiv.comp_symm, spMap_id, Category.id_comp]
  obtain ⟨k, hk⟩ := hJ
  refine main k A J (le_bot_iff.1 ?_)
  rw [← Ideal.zero_eq_bot, ← hk]
  exact Ideal.pow_le_pow_right (by omega)
end GlobalTheory.SqZero
