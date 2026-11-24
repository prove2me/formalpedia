-- Prove2me | solution 1 for GlobalTheory.SqZero.isLiftAlong_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:14.468527+00:00
-- url     : https://prove2.me/submissions/f9861101-506f-4307-a05e-ccf6a7805a1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
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
theorem _root_.solution {X : Over (Spec (CommRingCat.of R))}
    {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X} {φ : A →ₐ[R] T} {y : sp T ⟶ X}
    (h : spMap (Ideal.Quotient.mkₐ R (J.map φ)) ≫ y =
      spMap (Ideal.quotientMapₐ (J.map φ) φ Ideal.le_comap_map) ≫ y₀) : IsLiftAlong y₀ φ y := by
  intro T₀ _ _ q q₀ hq
  have hker : ∀ a ∈ J.map φ, q a = 0 := (fun a ha => RingHom.mem_ker.1 (Ideal.map_le_iff_le_comap.2 (fun b hb => Ideal.mem_comap.2 (RingHom.mem_ker.2 (by
        have := AlgHom.congr_fun hq b
        simpa [Ideal.Quotient.eq_zero_iff_mem.2 hb] using this))) ha))
  obtain ⟨q', rfl⟩ : ∃ q' : (T ⧸ J.map φ) →ₐ[R] T₀, q = q'.comp (Ideal.Quotient.mkₐ R _) :=
    ⟨Ideal.Quotient.liftₐ _ q hker, by ext a; rfl⟩
  have e2 : q₀ = q'.comp (Ideal.quotientMapₐ (J.map φ) φ Ideal.le_comap_map) := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (AlgHom.congr_fun hq a).symm
  subst e2
  rw [← spMap_comp, ← spMap_comp, Category.assoc, h, Category.assoc]
end GlobalTheory.SqZero
