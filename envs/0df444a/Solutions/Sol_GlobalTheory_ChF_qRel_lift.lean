-- Prove2me | solution 1 for GlobalTheory.ChF.qRel_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:36.07146+00:00
-- url     : https://prove2.me/submissions/eee3c902-b4e3-46a1-8728-a3f9af342ea2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_QRelExistsUniqueMulNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AbelianPartLiftSquareZeroUnitPoint
import Theorems.Thm_GlobalTheory_ChF_qRel_existsUnique_mul_nat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torsor_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_dim
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
namespace GlobalTheory.ChF
private theorem lift_of_smooth_affine {G B : Scheme.{0}} (q : G ⟶ B) [Smooth q] [IsAffineHom q]
    {S S' : Type} [CommRing S] [CommRing S'] (π : S →+* S') (hπ : Function.Surjective π)
    (hk : IsNilpotent (RingHom.ker π)) (y : Spec (CommRingCat.of S) ⟶ B) (x : Spec (CommRingCat.of S') ⟶ G)
    (h : x ≫ q = Spec.map (CommRingCat.ofHom π) ≫ y) :
    ∃ w : Spec (CommRingCat.of S) ⟶ G, w ≫ q = y ∧ Spec.map (CommRingCat.ofHom π) ≫ w = x := by
  have : IsAffine (pullback q y) := isAffine_of_isAffineHom (pullback.snd q y)
  let e := (pullback q y).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (pullback.lift x _ h ≫ e.hom)
  obtain ⟨α, hα⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q y)
  have hs : RingHom.Smooth α.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hα]
    infer_instance
  have hφα : α ≫ φ = CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]
  letI : Algebra S Γ(pullback q y, ⊤) := α.hom.toAlgebra
  letI : Algebra S S' := π.toAlgebra
  haveI : Algebra.Smooth S Γ(pullback q y, ⊤) := hs
  let φ' : Γ(pullback q y, ⊤) →ₐ[S] S' := ⟨φ.hom, fun r => congr($hφα r)⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  have hψ : (Algebra.ofId S S').comp ψ = φ' :=
    Algebra.FormallySmooth.comp_liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  let ψ' : Γ(pullback q y, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom ψ.toRingHom
  have h₁ : α ≫ ψ' = 𝟙 _ := by
    ext r
    exact ψ.commutes r
  have h₂ : ψ' ≫ CommRingCat.ofHom π = φ := by
    ext a
    exact congr($hψ a)
  refine ⟨Spec.map ψ' ≫ e.inv ≫ pullback.fst q y, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, ← hα, ← Category.assoc,
      ← Spec.map_comp, h₁, Spec.map_id, Category.id_comp]
  · rw [← Category.assoc, ← Spec.map_comp, h₂, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
end GlobalTheory.ChF
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S') (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ → ∀ y : sp (R₀ := R) S ⟶ D.P.A, spMap ρ ≫ y = 1 → ∃ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 ∧ QRel c S z y := by
  intro R _ _ I D k G _ _ c S _ _ hS S' _ _ ρ σ hρσ hk y hy
  have hS' : Kills I k S' := fun t ht => by rw [← ρ.commutes, hS t ht, map_zero]
  obtain ⟨hex, hmul⟩ := (qRel_existsUnique_mul_nat R I D k G c).1 S' hS'
  obtain ⟨y₀, hy₀, hu⟩ := hex 1
  have h1 : y₀ = 1 := by
    have h := hmul 1 1 y₀ y₀ hy₀ hy₀
    rw [_root_.mul_one] at h
    exact mul_eq_left.1 (hu _ h)
  subst h1
  obtain ⟨x, hx₁, hx₂⟩ := hy₀
  have := c.q_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have := (H1.torus_dim (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).smooth
  have : Smooth c.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let y' : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k D.P.A).left :=
    pullback.lift y.left t ((Over.w y).trans ht.symm)
  have hy' : y' ≫ pullback.fst D.P.A.hom (Out.thick R I k) = y.left := pullback.lift_fst _ _ _
  have hyl : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ y.left = (1 : sp (R₀ := R) S' ⟶ D.P.A).left :=
    congrArg (·.left) hy
  obtain ⟨w, hw₁, hw₂⟩ := lift_of_smooth_affine c.q.left ρ.toRingHom
    (fun a => ⟨σ a, congr($hρσ a)⟩) ⟨2, hk⟩ y' x (by
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans hx₂).trans
        (hyl.symm.trans ((congrArg (_ ≫ ·) hy'.symm).trans (Category.assoc _ _ _).symm)))
  have hq : w ≫ c.pG.left = y.left := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hw₁).trans hy')
  have hz : (w ≫ (Out.fstG I k G).left) ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    have a : (Out.fstG I k G).left ≫ G.hom = c.pG.left ≫ D.P.A.hom := (Over.w _).trans (Over.w _).symm
    exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) a).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.P.A.hom) hq).trans (Over.w y))))
  refine ⟨Over.homMk (w ≫ (Out.fstG I k G).left) hz, ?_, w, rfl, hq⟩
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hw₂).trans hx₁)
end GlobalTheory.ChF
