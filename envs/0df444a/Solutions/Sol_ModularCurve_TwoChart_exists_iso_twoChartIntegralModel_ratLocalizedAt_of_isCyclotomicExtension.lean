-- Prove2me | solution 1 for ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ccde2157-c20c-5fa2-b29b-7ca91b5d6200

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Theorems.Thm_IsCyclotomicExtension_Rat_isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace TwoBaseIso

theorem ringHom_ext (p : ℕ) {B : Type*} [CommRing B] [IsDomain B] [CharZero B] (f g : ↥(GaloisRep.ratLocalizedAt p) →+* B) :
    f = g := by
  ext x
  have hd : ((x : ℚ).den : B) ≠ 0 := Nat.cast_ne_zero.mpr (x : ℚ).den_ne_zero
  have hx : x * ((x : ℚ).den : ↥(GaloisRep.ratLocalizedAt p)) = ((x : ℚ).num : ↥(GaloisRep.ratLocalizedAt p)) :=
    Subtype.ext (by push_cast; exact Rat.mul_den_eq_num (x : ℚ))
  have hf : f x * ((x : ℚ).den : B) = ((x : ℚ).num : B) := by rw [← map_natCast f, ← map_mul, hx, map_intCast]
  have hg : g x * ((x : ℚ).den : B) = ((x : ℚ).num : B) := by rw [← map_natCast g, ← map_mul, hx, map_intCast]
  exact mul_right_cancel₀ hd (hf.trans hg.symm)

theorem mem_chartAlg_iff_of_isIntegral {R₀ A F : Type} [CommRing R₀] [CommRing A] [Field F]
    [Algebra R₀ A] [Algebra R₀ F] [Algebra A F] [IsScalarTower R₀ A F] [Algebra.IsIntegral R₀ A] (S : Set F) (x : F) :
    x ∈ ModularCurve.TwoChart.chartAlg A F S ↔ x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg R₀ F S := by
  rw [ModularCurve.TwoChart.mem_chartAlg_iff, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]

  have hsub : (Algebra.adjoin R₀ S).toSubring ≤ (Algebra.adjoin A S).toSubring := by
    have : Algebra.adjoin R₀ S ≤ (Algebra.adjoin A S).restrictScalars R₀ := Algebra.adjoin_le Algebra.subset_adjoin
    exact fun y hy => this hy
  constructor
  · intro hx

    have hgen : ∀ z ∈ Algebra.adjoin A S, _root_.IsIntegral ↥(Algebra.adjoin R₀ S) z := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem s hs => exact isIntegral_algebraMap (x := (⟨s, Algebra.subset_adjoin hs⟩ : ↥(Algebra.adjoin R₀ S)))
      | algebraMap a =>
          have h0 : _root_.IsIntegral R₀ (algebraMap A F a) := (Algebra.IsIntegral.isIntegral (R := R₀) a).map (IsScalarTower.toAlgHom R₀ A F)
          exact h0.tower_top
      | add y z _ _ hy hz => exact hy.add hz
      | mul y z _ _ hy hz => exact hy.mul hz

    let C := integralClosure ↥(Algebra.adjoin R₀ S) F
    have hRC : (Algebra.adjoin A S).toSubring ≤ C.toSubring := fun z hz => hgen z hz
    have hxC : _root_.IsIntegral ↥C x := hx.map_of_comp_eq (Subring.inclusion hRC) (RingHom.id F) (by ext; rfl)
    exact isIntegral_trans (R := ↥(Algebra.adjoin R₀ S)) (A := ↥C) x hxC
  · intro hx
    exact hx.map_of_comp_eq (Subring.inclusion hsub) (RingHom.id F) (by ext; rfl)

section Frame

variable (p : ℕ) [Fact p.Prime]
  (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
  (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
  [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]

include L in

theorem isIntegral_A (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) : Algebra.IsIntegral ↥(GaloisRep.ratLocalizedAt p) A := by
  have _hL := (inferInstance : CharZero L)
  constructor
  intro a
  have h : _root_.IsIntegral ↥(GaloisRep.ratLocalizedAt p) (algebraMap A L a) :=
    (IsCyclotomicExtension.Rat.isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing p L A hAp _).mpr ⟨a, rfl⟩
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) A L) (IsFractionRing.injective A L)).mp h

variable (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ L] [IsDiscreteValuationRing A] [IsFractionRing A L]
  [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L] in

scoped instance tower : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A ↥K :=
  IsScalarTower.of_algebraMap_eq' (ringHom_ext p _ _)

end Frame

theorem spec_map_comp_eq_id {A B : Type} [CommRing A] [CommRing B] (a : A →+* B) (b : B →+* A)
    (hab : ∀ x, a (b x) = x) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show a.comp b = RingHom.id B from RingHom.ext hab, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem preimage_range_eq {X X' U U' : Scheme} (w : X ⟶ X') (w' : X' ⟶ X) (i : U ⟶ X) (i' : U' ⟶ X') (s : U ⟶ U') (s' : U' ⟶ U)
    (h : i ≫ w = s ≫ i') (h' : i' ≫ w' = s' ≫ i) (hww : w ≫ w' = 𝟙 X) :
    w.base ⁻¹' Set.range i'.base = Set.range i.base := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have hx : x = w'.base (w.base x) := by
      change x = (w ≫ w').base x
      rw [hww]; rfl
    refine ⟨s'.base y, ?_⟩
    change (s' ≫ i).base y = x
    rw [← h']
    change w'.base (i'.base y) = x
    rw [hy, ← hx]
  · rintro ⟨y, rfl⟩
    refine ⟨s.base y, ?_⟩
    change (s ≫ i').base y = w.base (i.base y)
    rw [← h]
    rfl

abbrev R₀ (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)

section Frame2

variable (p : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra ↥(GaloisRep.ratLocalizedAt p) A]
  (K : Type) [Field K] [CharZero K] [Algebra A K] [Algebra ↥(GaloisRep.ratLocalizedAt p) K]
  [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A K] [Algebra.IsIntegral ↥(GaloisRep.ratLocalizedAt p) A]
  (j : K) [Fact (j ≠ 0)]

theorem mem_iff (S : Set K) (x : K) :
    x ∈ ModularCurve.TwoChart.chartAlg A K S ↔ x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S :=
  mem_chartAlg_iff_of_isIntegral (R₀ := R₀ p) (A := A) S x

def toHom (S : Set K) : ↥(ModularCurve.TwoChart.chartAlg A K S) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S) :=
  ((ModularCurve.TwoChart.chartAlg A K S).val.toRingHom).codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S)
    (fun x => (mem_iff p A K S x).mp x.2)

def invHom (S : Set K) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S) →+* ↥(ModularCurve.TwoChart.chartAlg A K S) :=
  ((AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S).val.toRingHom).codRestrict (ModularCurve.TwoChart.chartAlg A K S)
    (fun x => (mem_iff p A K S x).mpr x.2)

theorem coe_toHom (S : Set K) (x : ↥(ModularCurve.TwoChart.chartAlg A K S)) :
    ((toHom p A K S x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S)) : K) = x :=
  RingHom.codRestrict_apply _ _ _ x

theorem coe_invHom (S : Set K) (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S)) :
    ((invHom p A K S x : ↥(ModularCurve.TwoChart.chartAlg A K S)) : K) = x :=
  RingHom.codRestrict_apply _ _ _ x

theorem toHom_comp_invHom (S : Set K) : (toHom p A K S).comp (invHom p A K S) = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (by rw [RingHom.comp_apply, coe_toHom, coe_invHom]; rfl)

theorem invHom_comp_toHom (S : Set K) : (invHom p A K S).comp (toHom p A K S) = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (by rw [RingHom.comp_apply, coe_invHom, coe_toHom]; rfl)

def chartEquiv (S : Set K) :
    ↥(ModularCurve.TwoChart.chartAlg A K S) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S) :=
  RingEquiv.ofRingHom (toHom p A K S) (invHom p A K S) (toHom_comp_invHom p A K S) (invHom_comp_toHom p A K S)

theorem chartEquiv_toRingHom (S : Set K) : (chartEquiv p A K S).toRingHom = toHom p A K S := rfl

theorem chartEquiv_symm_toRingHom (S : Set K) : (chartEquiv p A K S).symm.toRingHom = invHom p A K S := rfl

theorem coe_chartEquiv (S : Set K) (x : ↥(ModularCurve.TwoChart.chartAlg A K S)) :
    ((chartEquiv p A K S x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S)) : K) = x :=
  coe_toHom p A K S x

theorem coe_chartEquiv_symm (S : Set K) (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S)) :
    (((chartEquiv p A K S).symm x : ↥(ModularCurve.TwoChart.chartAlg A K S)) : K) = x :=
  coe_invHom p A K S x

theorem comp_inclFin_symm :
    (ModularCurve.TwoChart.inclFin A K j).toRingHom.comp (chartEquiv p A K {j}).symm.toRingHom =
      (chartEquiv p A K {j, (j)⁻¹}).symm.toRingHom.comp (AlgebraicCurve.TwoChartIntegralModel.inclFin (R₀ p) K j).toRingHom := by
  rw [chartEquiv_symm_toRingHom, chartEquiv_symm_toRingHom]
  refine RingHom.ext fun x => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe,
    ModularCurve.TwoChart.coe_chartIncl, coe_invHom, coe_invHom, AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl]

theorem comp_inclInf_symm :
    (ModularCurve.TwoChart.inclInf A K j).toRingHom.comp (chartEquiv p A K {(j)⁻¹}).symm.toRingHom =
      (chartEquiv p A K {j, (j)⁻¹}).symm.toRingHom.comp (AlgebraicCurve.TwoChartIntegralModel.inclInf (R₀ p) K j).toRingHom := by
  rw [chartEquiv_symm_toRingHom, chartEquiv_symm_toRingHom]
  refine RingHom.ext fun x => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe,
    ModularCurve.TwoChart.coe_chartIncl, coe_invHom, coe_invHom, AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl]

theorem comp_inclFin :
    (AlgebraicCurve.TwoChartIntegralModel.inclFin (R₀ p) K j).toRingHom.comp (chartEquiv p A K {j}).toRingHom =
      (chartEquiv p A K {j, (j)⁻¹}).toRingHom.comp (ModularCurve.TwoChart.inclFin A K j).toRingHom := by
  rw [chartEquiv_toRingHom, chartEquiv_toRingHom]
  refine RingHom.ext fun x => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl, coe_toHom, coe_toHom, ModularCurve.TwoChart.coe_chartIncl]

theorem comp_inclInf :
    (AlgebraicCurve.TwoChartIntegralModel.inclInf (R₀ p) K j).toRingHom.comp (chartEquiv p A K {(j)⁻¹}).toRingHom =
      (chartEquiv p A K {j, (j)⁻¹}).toRingHom.comp (ModularCurve.TwoChart.inclInf A K j).toRingHom := by
  rw [chartEquiv_toRingHom, chartEquiv_toRingHom]
  refine RingHom.ext fun x => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl, coe_toHom, coe_toHom, ModularCurve.TwoChart.coe_chartIncl]

theorem sqF : ModularCurve.TwoChart.fFin A K j ≫ Spec.map (CommRingCat.ofHom (chartEquiv p A K {j}).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {j, (j)⁻¹}).symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.fFin (R₀ p) K j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comp_inclFin_symm]

theorem sqI : ModularCurve.TwoChart.fInf A K j ≫ Spec.map (CommRingCat.ofHom (chartEquiv p A K {(j)⁻¹}).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {j, (j)⁻¹}).symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.fInf (R₀ p) K j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comp_inclInf_symm]

theorem sqF' : AlgebraicCurve.TwoChartIntegralModel.fFin (R₀ p) K j ≫ Spec.map (CommRingCat.ofHom (chartEquiv p A K {j}).toRingHom) =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {j, (j)⁻¹}).toRingHom) ≫ ModularCurve.TwoChart.fFin A K j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comp_inclFin]

theorem sqI' : AlgebraicCurve.TwoChartIntegralModel.fInf (R₀ p) K j ≫ Spec.map (CommRingCat.ofHom (chartEquiv p A K {(j)⁻¹}).toRingHom) =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {j, (j)⁻¹}).toRingHom) ≫ ModularCurve.TwoChart.fInf A K j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comp_inclInf]

noncomputable def hom₁ : ModularCurve.TwoChartModel A K j ⟶ AlgebraicCurve.TwoChartIntegralModel (R₀ p) K j :=
  pushout.map _ _ _ _ (Spec.map (CommRingCat.ofHom (chartEquiv p A K {j}).symm.toRingHom))
    (Spec.map (CommRingCat.ofHom (chartEquiv p A K {(j)⁻¹}).symm.toRingHom))
    (Spec.map (CommRingCat.ofHom (chartEquiv p A K {j, (j)⁻¹}).symm.toRingHom)) (sqF p A K j) (sqI p A K j)

noncomputable def hom₂ : AlgebraicCurve.TwoChartIntegralModel (R₀ p) K j ⟶ ModularCurve.TwoChartModel A K j :=
  pushout.map _ _ _ _ (Spec.map (CommRingCat.ofHom (chartEquiv p A K {j}).toRingHom))
    (Spec.map (CommRingCat.ofHom (chartEquiv p A K {(j)⁻¹}).toRingHom))
    (Spec.map (CommRingCat.ofHom (chartEquiv p A K {j, (j)⁻¹}).toRingHom)) (sqF' p A K j) (sqI' p A K j)

theorem ιFin_hom₁ : ModularCurve.TwoChart.ιFin A K j ≫ hom₁ p A K j =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {j}).symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin (R₀ p) K j :=
  pushout.inl_desc _ _ _

theorem ιInf_hom₁ : ModularCurve.TwoChart.ιInf A K j ≫ hom₁ p A K j =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {(j)⁻¹}).symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf (R₀ p) K j :=
  pushout.inr_desc _ _ _

theorem ιFin_hom₂ : AlgebraicCurve.TwoChartIntegralModel.ιFin (R₀ p) K j ≫ hom₂ p A K j =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {j}).toRingHom) ≫ ModularCurve.TwoChart.ιFin A K j :=
  pushout.inl_desc _ _ _

theorem ιInf_hom₂ : AlgebraicCurve.TwoChartIntegralModel.ιInf (R₀ p) K j ≫ hom₂ p A K j =
    Spec.map (CommRingCat.ofHom (chartEquiv p A K {(j)⁻¹}).toRingHom) ≫ ModularCurve.TwoChart.ιInf A K j :=
  pushout.inr_desc _ _ _

theorem hom₁_hom₂ : hom₁ p A K j ≫ hom₂ p A K j = 𝟙 _ := by
  apply pushout.hom_ext
  · show ModularCurve.TwoChart.ιFin A K j ≫ hom₁ p A K j ≫ hom₂ p A K j = ModularCurve.TwoChart.ιFin A K j ≫ 𝟙 _
    rw [← Category.assoc, ιFin_hom₁, Category.assoc, ιFin_hom₂, ← Category.assoc,
      spec_map_comp_eq_id _ _ (fun x => (chartEquiv p A K {j}).symm_apply_apply x), Category.id_comp, Category.comp_id]
  · show ModularCurve.TwoChart.ιInf A K j ≫ hom₁ p A K j ≫ hom₂ p A K j = ModularCurve.TwoChart.ιInf A K j ≫ 𝟙 _
    rw [← Category.assoc, ιInf_hom₁, Category.assoc, ιInf_hom₂, ← Category.assoc,
      spec_map_comp_eq_id _ _ (fun x => (chartEquiv p A K {(j)⁻¹}).symm_apply_apply x), Category.id_comp, Category.comp_id]

theorem hom₂_hom₁ : hom₂ p A K j ≫ hom₁ p A K j = 𝟙 _ := by
  apply pushout.hom_ext
  · show AlgebraicCurve.TwoChartIntegralModel.ιFin (R₀ p) K j ≫ hom₂ p A K j ≫ hom₁ p A K j = AlgebraicCurve.TwoChartIntegralModel.ιFin (R₀ p) K j ≫ 𝟙 _
    rw [← Category.assoc, ιFin_hom₂, Category.assoc, ιFin_hom₁, ← Category.assoc,
      spec_map_comp_eq_id _ _ (fun x => (chartEquiv p A K {j}).apply_symm_apply x), Category.id_comp, Category.comp_id]
  · show AlgebraicCurve.TwoChartIntegralModel.ιInf (R₀ p) K j ≫ hom₂ p A K j ≫ hom₁ p A K j = AlgebraicCurve.TwoChartIntegralModel.ιInf (R₀ p) K j ≫ 𝟙 _
    rw [← Category.assoc, ιInf_hom₂, Category.assoc, ιInf_hom₁, ← Category.assoc,
      spec_map_comp_eq_id _ _ (fun x => (chartEquiv p A K {(j)⁻¹}).apply_symm_apply x), Category.id_comp, Category.comp_id]

noncomputable def iso : ModularCurve.TwoChartModel A K j ≅ AlgebraicCurve.TwoChartIntegralModel (R₀ p) K j :=
  ⟨hom₁ p A K j, hom₂ p A K j, hom₁_hom₂ p A K j, hom₂_hom₁ p A K j⟩

theorem base_ringHom_eq (S : Set K) :
    (chartEquiv p A K S).symm.toRingHom.comp (algebraMap (R₀ p) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg (R₀ p) K S)) =
      (algebraMap A ↥(ModularCurve.TwoChart.chartAlg A K S)).comp (algebraMap (R₀ p) A) :=
  ringHom_ext p _ _

theorem hom₁_toBase : hom₁ p A K j ≫ AlgebraicCurve.TwoChartIntegralModel.toBase (R₀ p) K j =
    ModularCurve.TwoChart.modelTo A K j ≫ Spec.map (CommRingCat.ofHom (algebraMap (R₀ p) A)) := by
  apply pushout.hom_ext
  · show ModularCurve.TwoChart.ιFin A K j ≫ hom₁ p A K j ≫ AlgebraicCurve.TwoChartIntegralModel.toBase (R₀ p) K j =
      ModularCurve.TwoChart.ιFin A K j ≫ ModularCurve.TwoChart.modelTo A K j ≫ Spec.map (CommRingCat.ofHom (algebraMap (R₀ p) A))
    rw [← Category.assoc, ιFin_hom₁, Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase, ← Category.assoc,
      ModularCurve.TwoChart.ιFin_modelTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      base_ringHom_eq]
  · show ModularCurve.TwoChart.ιInf A K j ≫ hom₁ p A K j ≫ AlgebraicCurve.TwoChartIntegralModel.toBase (R₀ p) K j =
      ModularCurve.TwoChart.ιInf A K j ≫ ModularCurve.TwoChart.modelTo A K j ≫ Spec.map (CommRingCat.ofHom (algebraMap (R₀ p) A))
    rw [← Category.assoc, ιInf_hom₁, Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase, ← Category.assoc,
      ModularCurve.TwoChart.ιInf_modelTo, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      base_ringHom_eq]

theorem preimage_ιFin : hom₁ p A K j ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιFin (R₀ p) K j).opensRange = (ModularCurve.TwoChart.ιFin A K j).opensRange :=
  TopologicalSpace.Opens.ext (preimage_range_eq _ _ _ _ _ _ (ιFin_hom₁ p A K j) (ιFin_hom₂ p A K j) (hom₁_hom₂ p A K j))

theorem preimage_ιInf : hom₁ p A K j ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιInf (R₀ p) K j).opensRange = (ModularCurve.TwoChart.ιInf A K j).opensRange :=
  TopologicalSpace.Opens.ext (preimage_range_eq _ _ _ _ _ _ (ιInf_hom₁ p A K j) (ιInf_hom₂ p A K j) (hom₁_hom₂ p A K j))

end Frame2

end TwoBaseIso
p2m_reactivate "P2MW.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension.TwoBaseIso"

open TwoBaseIso in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] :
    ∃ (w : ModularCurve.TwoChartModel A (↥K) j ≅ AlgebraicCurve.TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) (↥K) j)
      (eFin : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j))
      (eInf : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j)),

      (∀ x : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((eFin x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j)) : ↥K) = (x : ↥K)) ∧
      (∀ x : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        ((eInf x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j)) : ↥K) = (x : ↥K)) ∧

      w.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)) ∧

      ModularCurve.TwoChart.ιFin A (↥K) j ≫ w.hom =
        Spec.map (CommRingCat.ofHom eFin.symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j ∧
      ModularCurve.TwoChart.ιInf A (↥K) j ≫ w.hom =
        Spec.map (CommRingCat.ofHom eInf.symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j ∧

      w.hom ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange ∧
      w.hom ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j).opensRange = (ModularCurve.TwoChart.ιInf A (↥K) j).opensRange := by
  haveI : Algebra.IsIntegral ↥(GaloisRep.ratLocalizedAt p) A := isIntegral_A p L A hAp
  exact ⟨iso p A (↥K) j, chartEquiv p A (↥K) {j}, chartEquiv p A (↥K) {(j)⁻¹}, coe_chartEquiv p A (↥K) {j},
    coe_chartEquiv p A (↥K) {(j)⁻¹}, hom₁_toBase p A (↥K) j, ιFin_hom₁ p A (↥K) j, ιInf_hom₁ p A (↥K) j,
    preimage_ιFin p A (↥K) j, preimage_ιInf p A (↥K) j⟩

end S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension
end P2MW
export P2MW.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension (solution)
