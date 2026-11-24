-- Prove2me | solution 1 for GlobalTheory.LaurentConst.eq_const_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:41.233819+00:00
-- url     : https://prove2.me/submissions/2cd5fd37-1ae2-4ee7-b30c-43f91e91e2fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_eq_const
import Theorems.Thm_GlobalTheory_exists_specMap_fromSpec_eq
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {R : Type}
    [CommRing R] (g : Spec (.of (AddMonoidAlgebra R ℤ)) ⟶ Y) (g₀ g₁ : Spec (.of (PowerSeries R)) ⟶ Y)
    (hg : Set.range g ⊆ U) (hg₀ : Set.range g₀ ⊆ U) (hg₁ : Set.range g₁ ⊆ U)
    (h₀ : Spec.map (CommRingCat.ofHom (atZero R)) ≫ g =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ g₀)
    (h₁ : Spec.map (CommRingCat.ofHom (atInf R)) ≫ g =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ g₁) :
    g = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫
      Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫ g₀ := by
  obtain ⟨φ, rfl⟩ := exists_specMap_fromSpec_eq g hU hg
  obtain ⟨φ₀, rfl⟩ := exists_specMap_fromSpec_eq g₀ hU hg₀
  obtain ⟨φ₁, rfl⟩ := exists_specMap_fromSpec_eq g₁ hU hg₁
  simp only [← Spec.map_comp_assoc, cancel_mono, Spec.map_inj] at h₀ h₁ ⊢
  ext1
  refine RingHom.ext fun u ↦ ?_
  exact eq_const (congrArg (fun ψ ↦ ψ.hom u) h₀) (congrArg (fun ψ ↦ ψ.hom u) h₁)
end GlobalTheory.LaurentConst
