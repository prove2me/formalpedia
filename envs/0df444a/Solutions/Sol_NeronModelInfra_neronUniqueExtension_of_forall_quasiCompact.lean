-- Prove2me | solution 1 for NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7de891a7-10c2-5cb2-82e1-ec693ded46ed

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra"

namespace NeronModelInfra
p2m_export "NeronModelInfra" "specGenericFibreInclusion SchemeHomOver genericFibreRestrict NeronUniqueExtension genericFibreRestrict_coe_comp_snd genericFibreRestrict_coe_comp_fst genericFibreRestrict_injective_of_flat_of_isSeparated"
namespace NeronUniqueExtensionOfQC
p2m_open "NeronModelInfra"

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]

noncomputable def fibreShift {Y Y' : Scheme.{u}} (r : Y ⟶ Y')
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) :
    pullback tY (specGenericFibreInclusion R K) ⟶ pullback tY' (specGenericFibreInclusion R K) :=
  pullback.lift (pullback.fst tY (specGenericFibreInclusion R K) ≫ r)
    (pullback.snd tY (specGenericFibreInclusion R K)) (by rw [Category.assoc, hr, pullback.condition])

@[reassoc (attr := simp)]
theorem fibreShift_fst {Y Y' : Scheme.{u}} (r : Y ⟶ Y')
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) :
    fibreShift R K r hr ≫ pullback.fst tY' (specGenericFibreInclusion R K) =
      pullback.fst tY (specGenericFibreInclusion R K) ≫ r :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreShift_snd {Y Y' : Scheme.{u}} (r : Y ⟶ Y')
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) :
    fibreShift R K r hr ≫ pullback.snd tY' (specGenericFibreInclusion R K) =
      pullback.snd tY (specGenericFibreInclusion R K) :=
  pullback.lift_snd _ _ _

theorem fibreShift_comp {Y Y' Y'' : Scheme.{u}} (r : Y ⟶ Y') (r' : Y' ⟶ Y'')
    {tY'' : Y'' ⟶ Spec (CommRingCat.of R)} {tY' : Y' ⟶ Spec (CommRingCat.of R)}
    {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) (hr' : r' ≫ tY'' = tY') :
    fibreShift R K r hr ≫ fibreShift R K r' hr' =
      fibreShift R K (r ≫ r') (by rw [Category.assoc, hr', hr]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreShift_fst, fibreShift_fst_assoc]
  · simp only [Category.assoc, fibreShift_snd]

theorem fibreShift_congr {Y Y' : Scheme.{u}} {r r' : Y ⟶ Y'}
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)}
    (hrr : r = r') (hr : r ≫ tY' = tY) :
    fibreShift R K r hr = fibreShift R K r' (hrr ▸ hr) := by
  subst hrr; rfl

def chartRestrict {X T T' : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {s : T' ⟶ Spec (CommRingCat.of R)}
    (w : T' ⟶ T) (hs : w ≫ t = s) (φ : SchemeHomOver t fX) : SchemeHomOver s fX :=
  ⟨w ≫ φ.1, by rw [Category.assoc, φ.2, hs]⟩

@[scoped simp]
theorem chartRestrict_coe {X T T' : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {s : T' ⟶ Spec (CommRingCat.of R)} (w : T' ⟶ T) (hs : w ≫ t = s)
    (φ : SchemeHomOver t fX) : (chartRestrict R fX w hs φ).1 = w ≫ φ.1 :=
  rfl

theorem genericFibreRestrict_chartRestrict {X T T' : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {s : T' ⟶ Spec (CommRingCat.of R)} (w : T' ⟶ T) (hs : w ≫ t = s)
    (φ : SchemeHomOver t fX) :
    (genericFibreRestrict R K fX s (chartRestrict R fX w hs φ)).1 =
      fibreShift R K w hs ≫ (genericFibreRestrict R K fX t φ).1 := by
  apply pullback.hom_ext
  · simp only [genericFibreRestrict_coe_comp_fst, chartRestrict_coe, Category.assoc, fibreShift_fst_assoc]
  · simp only [genericFibreRestrict_coe_comp_snd, Category.assoc, fibreShift_snd]

theorem chartSolution_restrict_eq {X T Y Z : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} (w : Y ⟶ T)
    (ψ : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd fX (specGenericFibreInclusion R K)))
    (φw : SchemeHomOver (w ≫ t) fX)
    (hφw : (genericFibreRestrict R K fX (w ≫ t) φw).1 = fibreShift R K w rfl ≫ ψ.1)
    (r : Z ⟶ Y) (n : Z ⟶ T) (hn : r ≫ w = n) :
    (genericFibreRestrict R K fX (n ≫ t) (chartRestrict R fX r (by rw [← Category.assoc, hn]) φw)).1 =
      fibreShift R K n rfl ≫ ψ.1 := by
  rw [genericFibreRestrict_chartRestrict, hφw, ← Category.assoc, fibreShift_comp, fibreShift_congr R K hn]

theorem exists_pulledChart_compare {T Y : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : Y ⟶ T) :
    ∃ h : pullback (pullback.fst t (specGenericFibreInclusion R K)) w ⟶
        pullback (w ≫ t) (specGenericFibreInclusion R K),
      h ≫ pullback.fst (w ≫ t) (specGenericFibreInclusion R K) =
        pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ∧
      h ≫ pullback.snd (w ≫ t) (specGenericFibreInclusion R K) =
        pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
          pullback.snd t (specGenericFibreInclusion R K) := by
  have hcond : pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ≫ (w ≫ t) =
      (pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        pullback.snd t (specGenericFibreInclusion R K)) ≫ specGenericFibreInclusion R K := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, pullback.condition, Category.assoc]
  exact ⟨pullback.lift _ _ hcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem pulledChart_fst_glue_eq {X T Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) (w : Y ⟶ T)
    (ψ : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd fX (specGenericFibreInclusion R K)))
    (φw : SchemeHomOver (w ≫ t) fX)
    (hφw : (genericFibreRestrict R K fX (w ≫ t) φw).1 = fibreShift R K w rfl ≫ ψ.1)
    (glue : T ⟶ X) (hglue : w ≫ glue = φw.1) :
    pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        (pullback.fst t (specGenericFibreInclusion R K) ≫ glue) =
      pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        (ψ.1 ≫ pullback.fst fX (specGenericFibreInclusion R K)) := by
  obtain ⟨h, hh1, hh2⟩ := exists_pulledChart_compare R K t w
  have hshift : h ≫ fibreShift R K w rfl = pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w := by
    apply pullback.hom_ext
    · rw [Category.assoc, fibreShift_fst, ← Category.assoc, hh1, ← pullback.condition]
    · rw [Category.assoc, fibreShift_snd, hh2]
  calc pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        (pullback.fst t (specGenericFibreInclusion R K) ≫ glue)
      = (pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ≫ w) ≫ glue := by
        rw [← Category.assoc, pullback.condition]
    _ = pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ≫ φw.1 := by
        rw [Category.assoc, hglue]
    _ = h ≫ ((genericFibreRestrict R K fX (w ≫ t) φw).1 ≫
          pullback.fst fX (specGenericFibreInclusion R K)) := by
        rw [genericFibreRestrict_coe_comp_fst, ← Category.assoc, hh1]
    _ = (h ≫ fibreShift R K w rfl) ≫ (ψ.1 ≫ pullback.fst fX (specGenericFibreInclusion R K)) := by
        rw [hφw]; simp only [Category.assoc]
    _ = _ := by rw [hshift]

end NeronModelInfra.NeronUniqueExtensionOfQC
p2m_reactivate "P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra.NeronUniqueExtensionOfQC"
p2m_reactivate "P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.NeronModelInfra"

open NeronModelInfra.NeronUniqueExtensionOfQC in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t → QuasiCompact t →
      Function.Bijective (genericFibreRestrict R K f t)) :
    NeronUniqueExtension R K f := by
  intro T t ht
  haveI := ht

  have hsm : ∀ i : T.affineCover.I₀, Smooth (T.affineCover.f i ≫ t) := fun i => inferInstance
  have hqc : ∀ i : T.affineCover.I₀, QuasiCompact (T.affineCover.f i ≫ t) := fun i => by
    haveI : IsAffine (T.affineCover.X i) := by dsimp [Scheme.affineCover]; infer_instance
    infer_instance
  constructor
  ·
    exact NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f t
  · intro ψ
    choose φ hφ using fun i : T.affineCover.I₀ =>
      (h _ (T.affineCover.f i ≫ t) (hsm i) (hqc i)).surjective
        ⟨fibreShift R K (T.affineCover.f i) rfl ≫ ψ.1, by rw [Category.assoc, ψ.2, fibreShift_snd]⟩
    have hcompat : ∀ i j : T.affineCover.I₀,
        pullback.fst (T.affineCover.f i) (T.affineCover.f j) ≫ (φ i).1 =
          pullback.snd (T.affineCover.f i) (T.affineCover.f j) ≫ (φ j).1 := by
      intro i j

      let n : pullback (T.affineCover.f i) (T.affineCover.f j) ⟶ T := pullback.fst _ _ ≫ T.affineCover.f i
      haveI : Flat (n ≫ t) := inferInstance
      have e₁ := chartSolution_restrict_eq R K f (T.affineCover.f i) ψ (φ i) (congrArg Subtype.val (hφ i))
        (pullback.fst _ _) n rfl
      have hn₂ : pullback.snd (T.affineCover.f i) (T.affineCover.f j) ≫ T.affineCover.f j = n :=
        pullback.condition.symm
      have e₂ := chartSolution_restrict_eq R K f (T.affineCover.f j) ψ (φ j) (congrArg Subtype.val (hφ j))
        (pullback.snd _ _) n hn₂
      have key := NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f (n ≫ t)
        (Subtype.ext (e₁.trans e₂.symm))
      simpa only [chartRestrict_coe] using congrArg Subtype.val key
    have hover : Scheme.Cover.glueMorphisms T.affineCover (fun i => (φ i).1) hcompat ≫ f = t := by
      apply Scheme.Cover.hom_ext T.affineCover
      intro i
      simp only [Scheme.Cover.ι_glueMorphisms_assoc]
      exact (φ i).2
    refine ⟨⟨Scheme.Cover.glueMorphisms T.affineCover (fun i => (φ i).1) hcompat, hover⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst]
      apply Scheme.Cover.hom_ext (Precoverage.ZeroHypercover.pullback₁
        (pullback.fst t (specGenericFibreInclusion R K)) T.affineCover)
      intro i
      exact pulledChart_fst_glue_eq R K f t (T.affineCover.f i) ψ (φ i) (congrArg Subtype.val (hφ i)) _
        (Scheme.Cover.ι_glueMorphisms _ _ hcompat i)
    · rw [genericFibreRestrict_coe_comp_snd, ψ.2]

end S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact
end P2MW
export P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact (solution)
