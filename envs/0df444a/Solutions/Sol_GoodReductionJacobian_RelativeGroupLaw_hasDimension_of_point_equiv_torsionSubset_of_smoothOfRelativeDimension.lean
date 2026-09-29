-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5e35334e-d3bf-5958-b14e-22191ae423db

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgHom_exists_cotangent_linearMap_of_fst_eq
import Theorems.Thm_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TrivSqZeroExt NeronModelInfra GoodReductionJacobian

namespace BTDim

noncomputable section

section SqZero

variable (R : Type) [CommRing R]
variable (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

scoped instance isLocalRing_tsze [IsLocalRing R] : IsLocalRing (TrivSqZeroExt R M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst with h | h
    · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h)
    · refine Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ?_)
      rwa [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]

scoped instance isLocalRing_tsze' [IsLocalRing R] : IsLocalRing (CommRingCat.of (TrivSqZeroExt R M)) :=
  isLocalRing_tsze R M

abbrev tS : Spec (CommRingCat.of (TrivSqZeroExt R M)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R M)))

abbrev tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R))

theorem tR_eq_id : tR R = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (RingHom.id R)) = _
  rw [CommRingCat.ofHom_id]
  exact Spec.map_id _

abbrev bS : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (TrivSqZeroExt R M)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)

theorem bS_tS : bS R M ≫ tS R M = tR R := by
  rw [← Spec.map_comp]
  rfl

variable {M}
variable {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
variable {N' : Type} [AddCommGroup N'] [Module R N'] [Module Rᵐᵒᵖ N'] [IsCentralScalar R N']

abbrev mS (φ : M →ₗ[R] N) :
    Spec (CommRingCat.of (TrivSqZeroExt R N)) ⟶ Spec (CommRingCat.of (TrivSqZeroExt R M)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map φ).toRingHom)

theorem mS_tS (φ : M →ₗ[R] N) : mS R φ ≫ tS R M = tS R N := by
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact (TrivSqZeroExt.map φ).commutes a

theorem bS_mS (φ : M →ₗ[R] N) : bS R N ≫ mS R φ = bS R M := by
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  exact TrivSqZeroExt.fst_map φ a

theorem mS_id : mS R (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  rw [mS, TrivSqZeroExt.map_id, ← Spec.map_id]
  rfl

theorem mS_comp (φ : M →ₗ[R] N) (ψ : N →ₗ[R] N') : mS R (ψ ∘ₗ φ) = mS R ψ ≫ mS R φ := by
  rw [mS, mS, mS, ← Spec.map_comp, TrivSqZeroExt.map_comp_map]
  rfl

end SqZero

section Points

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem schemeHomOverComp_comp {T T' T'' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (ψ' : T'' ⟶ T') (hψ' : ψ' ≫ t' = t'') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ' hψ' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp (ψ' ≫ ψ) (by rw [Category.assoc, hψ, hψ']) x :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem schemeHomOverComp_congr {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {ψ ψ' : T' ⟶ T} (h : ψ = ψ') (hψ : ψ ≫ t = t')
    (hψ' : ψ' ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ x = schemeHomOverComp ψ' hψ' x := by
  subst h; rfl

theorem schemeHomOverComp_id {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (h : 𝟙 T ≫ t = t) (x : SchemeHomOver t f) : schemeHomOverComp (𝟙 T) h x = x :=
  Subtype.ext (Category.id_comp _)

end Points

section Tangent

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

abbrev eR : SchemeHomOver (tR R) f := L.one (tR R)

theorem eR_comp : (eR L).1 ≫ f = 𝟙 _ := by rw [(eR L).2, tR_eq_id]

variable (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

def TJ : Type :=
  { t : SchemeHomOver (tS R M) f // schemeHomOverComp (bS R M) (bS_tS R M) t = eR L }

variable {L M}
variable {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
variable {N' : Type} [AddCommGroup N'] [Module R N'] [Module Rᵐᵒᵖ N'] [IsCentralScalar R N']

namespace TJ

@[scoped ext] theorem ext {t t' : TJ L M} (h : t.1.1 = t'.1.1) : t = t' := Subtype.ext (Subtype.ext h)

theorem bS_comp (t : TJ L M) : bS R M ≫ t.1.1 = (eR L).1 := congrArg Subtype.val t.2

def one : TJ L M := ⟨L.one _, L.one_natural (tS R M) (tR R) (bS R M) (bS_tS R M)⟩

def mul (t t' : TJ L M) : TJ L M :=
  ⟨L.mul _ t.1 t'.1, by rw [L.mul_natural, t.2, t'.2]; exact L.mul_one _ _⟩

@[scoped simp] theorem one_val : (one : TJ L M).1 = L.one _ := rfl
@[scoped simp] theorem mul_val (t t' : TJ L M) : (mul t t').1 = L.mul _ t.1 t'.1 := rfl

theorem mul_one (t : TJ L M) : mul t one = t := Subtype.ext (L.mul_one _ _)
theorem one_mul (t : TJ L M) : mul one t = t := Subtype.ext (L.one_mul _ _)

def map (φ : M →ₗ[R] N) (t : TJ L M) : TJ L N :=
  ⟨schemeHomOverComp (mS R φ) (mS_tS R φ) t.1, by
    rw [schemeHomOverComp_comp, schemeHomOverComp_congr (bS_mS R φ) _ (bS_tS R M)]
    exact t.2⟩

@[scoped simp] theorem map_val_val (φ : M →ₗ[R] N) (t : TJ L M) : (map φ t).1.1 = mS R φ ≫ t.1.1 := rfl

theorem map_one (φ : M →ₗ[R] N) : map φ (one : TJ L M) = one :=
  Subtype.ext (L.one_natural (tS R M) (tS R N) (mS R φ) (mS_tS R φ))

theorem map_mul (φ : M →ₗ[R] N) (t t' : TJ L M) : map φ (mul t t') = mul (map φ t) (map φ t') :=
  Subtype.ext (L.mul_natural (tS R M) (tS R N) (mS R φ) (mS_tS R φ) _ _)

theorem map_id (t : TJ L M) : map LinearMap.id t = t :=
  TJ.ext (by rw [map_val_val, mS_id, Category.id_comp])

theorem map_comp (φ : M →ₗ[R] N) (ψ : N →ₗ[R] N') (t : TJ L M) : map (ψ ∘ₗ φ) t = map ψ (map φ t) :=
  TJ.ext (by rw [map_val_val, map_val_val, map_val_val, mS_comp, Category.assoc])

end TJ
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ"

section Stalk

variable [IsLocalRing R]

variable (L) in

abbrev jpt : J := (eR L).1.base (closedPoint R)

scoped instance stalkAlgebra : Algebra R (J.presheaf.stalk (jpt L)) :=
  ((J.presheaf.germ ⊤ (jpt L) trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra

theorem algebraMap_stalk (a : R) : algebraMap R (J.presheaf.stalk (jpt L)) a =
    (J.presheaf.germ ⊤ (jpt L) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) :=
  rfl

variable (L) in

abbrev π : J.presheaf.stalk (jpt L) →+* R := (Scheme.stalkClosedPointTo (eR L).1).hom

theorem π_algebraMap (a : R) : π L (algebraMap R _ a) = a := by
  rw [algebraMap_stalk]
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ J.presheaf.germ ⊤ (jpt L) trivial ≫
    Scheme.stalkClosedPointTo (eR L).1).hom a = a
  have h1 : J.presheaf.germ ⊤ (jpt L) trivial ≫ Scheme.stalkClosedPointTo (eR L).1 =
      (eR L).1.appTop ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (closedPoint R) trivial ≫
        (stalkClosedPointIso (CommRingCat.of R)).hom := by
    rw [Scheme.stalkClosedPointTo, Scheme.Hom.germ_stalkMap_assoc]
    rfl
  have h2 : f.appTop ≫ (eR L).1.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, eR_comp, Scheme.Hom.id_appTop]
  rw [h1, ← Category.assoc f.appTop, h2, Category.id_comp, germ_stalkClosedPointIso_hom, Iso.inv_hom_id]
  rfl

variable (L) in

def πₐ : J.presheaf.stalk (jpt L) →ₐ[R] R :=
  { π L with commutes' := π_algebraMap }

@[scoped simp] theorem πₐ_apply (r : J.presheaf.stalk (jpt L)) : πₐ L r = π L r := rfl

variable (L) in

abbrev ωJ : Type := (RingHom.ker (πₐ L)).Cotangent

section Local

variable {A : Type} [CommRing A] [IsLocalRing A]

abbrev Λ₀ (L : RelativeGroupLaw R f) (φ : J.presheaf.stalk (jpt L) ⟶ CommRingCat.of A) :
    Spec (CommRingCat.of A) ⟶ J :=
  Spec.map φ ≫ J.fromSpecStalk (jpt L)

theorem Λ₀_injective {φ φ' : J.presheaf.stalk (jpt L) ⟶ CommRingCat.of A} [IsLocalHom φ.hom]
    [IsLocalHom φ'.hom] (h : Λ₀ L φ = Λ₀ L φ') : φ = φ' := by
  have h1 : (SpecToEquivOfLocalRing J (CommRingCat.of A)).symm ⟨jpt L, φ, inferInstance⟩ =
      (SpecToEquivOfLocalRing J (CommRingCat.of A)).symm ⟨jpt L, φ', inferInstance⟩ := h
  have h2 := (SpecToEquivOfLocalRing J (CommRingCat.of A)).symm.injective h1
  simp only [Sigma.mk.injEq, heq_eq_eq, Subtype.mk.injEq, true_and] at h2
  exact h2

omit [IsLocalRing A] in
theorem appTop_Λ₀_comp (φ : J.presheaf.stalk (jpt L) ⟶ CommRingCat.of A) :
    (Λ₀ L φ ≫ f).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom =
      f.appTop ≫ J.presheaf.germ ⊤ (jpt L) trivial ≫ φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc]
  congr 1
  have hle : (homOfLE (le_top : (⊤ : (Spec (J.presheaf.stalk (jpt L))).Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [hle, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

omit [IsLocalRing A] in
theorem Λ₀_comp_eq_Spec_map (φ : J.presheaf.stalk (jpt L) ⟶ CommRingCat.of A) (g : R →+* A)
    (hfg : ∀ a : R, φ.hom (algebraMap R _ a) = g a) :
    Λ₀ L φ ≫ f = Spec.map (CommRingCat.ofHom g) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of A)).hom, appTop_Λ₀_comp, Scheme.ΓSpecIso_naturality,
    ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id_assoc]
  ext a
  exact hfg a

omit [IsLocalRing A] in
theorem apply_algebraMap_of_Λ₀_comp_eq (φ : J.presheaf.stalk (jpt L) ⟶ CommRingCat.of A) (g : R →+* A)
    (h : Λ₀ L φ ≫ f = Spec.map (CommRingCat.ofHom g)) (a : R) :
    φ.hom (algebraMap R _ a) = g a := by
  have h1 := appTop_Λ₀_comp (L := L) φ
  rw [h, Scheme.ΓSpecIso_naturality, ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv,
    Iso.inv_hom_id_assoc] at h1
  exact (congrArg (fun ψ : CommRingCat.of R ⟶ CommRingCat.of A => ψ.hom a) h1).symm

end Local
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ"

def liftHom (g : ωJ L →ₗ[R] M) : J.presheaf.stalk (jpt L) →ₐ[R] TrivSqZeroExt R M :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L) g).choose

theorem fst_liftHom (g : ωJ L →ₗ[R] M) (r : J.presheaf.stalk (jpt L)) : (liftHom g r).fst = π L r :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L) g).choose_spec.1.1 r

theorem snd_liftHom (g : ωJ L →ₗ[R] M) (a : RingHom.ker (πₐ L)) :
    (liftHom g (a : J.presheaf.stalk (jpt L))).snd = g ((RingHom.ker (πₐ L)).toCotangent a) :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L) g).choose_spec.1.2 a

theorem liftHom_unique (g : ωJ L →ₗ[R] M) (ψ : J.presheaf.stalk (jpt L) →ₐ[R] TrivSqZeroExt R M)
    (h1 : ∀ r, (ψ r).fst = π L r)
    (h2 : ∀ a : RingHom.ker (πₐ L), (ψ (a : J.presheaf.stalk (jpt L))).snd =
      g ((RingHom.ker (πₐ L)).toCotangent a)) :
    ψ = liftHom g :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L) g).unique ⟨h1, h2⟩
    (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (πₐ L) g).choose_spec.1

theorem exists_eq_liftHom (ψ : J.presheaf.stalk (jpt L) →ₐ[R] TrivSqZeroExt R M)
    (h1 : ∀ r, (ψ r).fst = π L r) : ∃ g, ψ = liftHom g := by
  obtain ⟨g, hg⟩ := AlgHom.exists_cotangent_linearMap_of_fst_eq (πₐ L) ψ h1
  exact ⟨g, liftHom_unique g ψ h1 hg⟩

theorem liftHom_injective : Function.Injective (liftHom (L := L) (M := M)) := by
  intro g g' hgg'
  apply LinearMap.ext
  intro c
  obtain ⟨a, rfl⟩ := (RingHom.ker (πₐ L)).toCotangent_surjective c
  rw [← snd_liftHom, ← snd_liftHom, hgg']

theorem map_comp_liftHom (φ : M →ₗ[R] N) (g : ωJ L →ₗ[R] M) :
    (TrivSqZeroExt.map φ).comp (liftHom g) = liftHom (φ ∘ₗ g) := by
  refine liftHom_unique _ _ (fun r => ?_) (fun a => ?_)
  · rw [AlgHom.comp_apply, TrivSqZeroExt.fst_map, fst_liftHom]
  · rw [AlgHom.comp_apply, TrivSqZeroExt.snd_map, snd_liftHom, LinearMap.comp_apply]

theorem isLocalHom_of_fst_eq (ψ : J.presheaf.stalk (jpt L) →+* TrivSqZeroExt R M)
    (h1 : ∀ r, (ψ r).fst = π L r) : IsLocalHom ψ := by
  constructor
  intro r hr
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, h1] at hr
  exact (isUnit_map_iff (π L) r).mp hr

scoped instance isLocalHom_liftHom (g : ωJ L →ₗ[R] M) :
    IsLocalHom (CommRingCat.ofHom (liftHom g).toRingHom).hom :=
  isLocalHom_of_fst_eq (liftHom g).toRingHom (fst_liftHom g)

omit [IsLocalRing R] in
theorem isLocalHom_fstHom : IsLocalHom (TrivSqZeroExt.fstHom R R M).toRingHom :=
  ⟨fun _ ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩

scoped instance isLocalHom_fstHom' : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom).hom :=
  isLocalHom_fstHom

def pointOf (g : ωJ L →ₗ[R] M) : TJ L M :=
  ⟨⟨Λ₀ L (CommRingCat.ofHom (liftHom g).toRingHom),
    Λ₀_comp_eq_Spec_map _ _ (fun a => (liftHom g).commutes a)⟩, by
      apply Subtype.ext
      change bS R M ≫ Λ₀ L (CommRingCat.ofHom (liftHom g).toRingHom) = (eR L).1
      rw [bS, ← Spec.map_comp_assoc]
      convert Scheme.Spec_stalkClosedPointTo_fromSpecStalk (eR L).1 using 3
      exact CommRingCat.hom_ext (RingHom.ext fun r => fst_liftHom g r)⟩

@[scoped simp] theorem pointOf_val_val (g : ωJ L →ₗ[R] M) :
    (pointOf g).1.1 = Λ₀ L (CommRingCat.ofHom (liftHom g).toRingHom) := rfl

theorem pointOf_injective : Function.Injective (pointOf (L := L) (M := M)) := by
  intro g g' hgg'
  have h : (pointOf g).1.1 = (pointOf g').1.1 := by rw [hgg']
  rw [pointOf_val_val, pointOf_val_val] at h
  have h2 := Λ₀_injective h
  apply liftHom_injective
  apply AlgHom.ext
  intro r
  exact congrArg (fun ψ : J.presheaf.stalk (jpt L) ⟶ CommRingCat.of (TrivSqZeroExt R M) => ψ.hom r) h2

theorem pointOf_map (φ : M →ₗ[R] N) (g : ωJ L →ₗ[R] M) :
    pointOf (φ ∘ₗ g) = TJ.map φ (pointOf g) := by
  apply TJ.ext
  rw [pointOf_val_val, TJ.map_val_val, pointOf_val_val, mS, ← Spec.map_comp_assoc,
    ← map_comp_liftHom]
  rfl

theorem pointOf_surjective : Function.Surjective (pointOf (L := L) (M := M)) := by
  intro t
  obtain ⟨⟨q, φ₀, hφ₀⟩, ht⟩ :
      ∃ z, (SpecToEquivOfLocalRing J (CommRingCat.of (TrivSqZeroExt R M))).symm z = t.1.1 :=
    (SpecToEquivOfLocalRing J (CommRingCat.of (TrivSqZeroExt R M))).symm.surjective t.1.1
  have hq : q = jpt L := by
    have h1 : ((SpecToEquivOfLocalRing J (CommRingCat.of (TrivSqZeroExt R M))).symm ⟨q, φ₀, hφ₀⟩).base
        (closedPoint (TrivSqZeroExt R M)) = q := by
      rw [SpecToEquivOfLocalRing_symm_apply, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
        Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    rw [← h1, ht]
    have h2 : (bS R M).base (closedPoint R) = closedPoint (TrivSqZeroExt R M) := Spec_closedPoint
    rw [← h2, ← Scheme.Hom.comp_apply, t.bS_comp]
  subst hq
  have ht' : t.1.1 = Λ₀ L φ₀ := ht.symm
  have hcomm : ∀ a : R, φ₀.hom (algebraMap R _ a) = algebraMap R (TrivSqZeroExt R M) a :=
    apply_algebraMap_of_Λ₀_comp_eq φ₀ _ (by rw [← ht']; exact t.1.2)
  let ψ : J.presheaf.stalk (jpt L) →ₐ[R] TrivSqZeroExt R M := { φ₀.hom with commutes' := hcomm }
  have hfst : ∀ r, (ψ r).fst = π L r := by
    haveI := hφ₀
    haveI : IsLocalHom (φ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom).hom := by
      change IsLocalHom ((TrivSqZeroExt.fstHom R R M).toRingHom.comp φ₀.hom)
      haveI := isLocalHom_fstHom (R := R) (M := M)
      exact RingHom.isLocalHom_comp _ _
    have h1 : Λ₀ L (φ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom) =
        Λ₀ L (Scheme.stalkClosedPointTo (eR L).1) := by
      rw [Λ₀, Λ₀, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Spec.map_comp, Category.assoc]
      change bS R M ≫ Λ₀ L φ₀ = (eR L).1
      rw [← ht', t.bS_comp]
    have h2 := Λ₀_injective h1
    intro r
    exact congrArg (fun χ : J.presheaf.stalk (jpt L) ⟶ CommRingCat.of R => χ.hom r) h2
  obtain ⟨g, hg⟩ := exists_eq_liftHom ψ hfst
  refine ⟨g, TJ.ext ?_⟩
  rw [pointOf_val_val, ht', ← hg]
  rfl

variable (L M) in

def γJ : TJ L M ≃ (ωJ L →ₗ[R] M) :=
  (Equiv.ofBijective pointOf ⟨pointOf_injective, pointOf_surjective⟩).symm

theorem γJ_symm_apply (g : ωJ L →ₗ[R] M) : (γJ L M).symm g = pointOf g := rfl

theorem γJ_pointOf (g : ωJ L →ₗ[R] M) : γJ L M (pointOf g) = g :=
  (γJ L M).apply_symm_apply g

theorem γJ_map (φ : M →ₗ[R] N) (t : TJ L M) : γJ L N (TJ.map φ t) = φ ∘ₗ γJ L M t := by
  obtain ⟨g, rfl⟩ := (γJ L M).symm.surjective t
  rw [γJ_symm_apply, ← pointOf_map, γJ_pointOf, γJ_pointOf]

section Additive

theorem TJ_punit_eq_one (t : TJ L PUnit) : t = TJ.one :=
  (γJ L PUnit).injective (Subsingleton.elim _ _)

theorem TJ_map_zero (t : TJ L M) : TJ.map (0 : M →ₗ[R] N) t = TJ.one := by
  have h0 : (0 : M →ₗ[R] N) = (0 : PUnit →ₗ[R] N) ∘ₗ (0 : M →ₗ[R] PUnit) := rfl
  rw [h0, TJ.map_comp, TJ_punit_eq_one (TJ.map 0 t), TJ.map_one]

theorem γJ_mul (t t' : TJ L M) : γJ L M (TJ.mul t t') = γJ L M t + γJ L M t' := by
  let z : TJ L (M × M) := TJ.mul (TJ.map (LinearMap.inl R M M) t) (TJ.map (LinearMap.inr R M M) t')
  have h1 : TJ.map (LinearMap.fst R M M) z = t := by
    change TJ.map _ (TJ.mul _ _) = t
    rw [TJ.map_mul, ← TJ.map_comp, ← TJ.map_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr,
      TJ.map_id, TJ_map_zero, TJ.mul_one]
  have h2 : TJ.map (LinearMap.snd R M M) z = t' := by
    change TJ.map _ (TJ.mul _ _) = t'
    rw [TJ.map_mul, ← TJ.map_comp, ← TJ.map_comp, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      TJ.map_id, TJ_map_zero, TJ.one_mul]
  have h3 : TJ.map (LinearMap.fst R M M + LinearMap.snd R M M) z = TJ.mul t t' := by
    change TJ.map _ (TJ.mul _ _) = _
    have e1 : (LinearMap.fst R M M + LinearMap.snd R M M) ∘ₗ LinearMap.inl R M M = LinearMap.id := by
      rw [LinearMap.add_comp, LinearMap.fst_comp_inl, LinearMap.snd_comp_inl, add_zero]
    have e2 : (LinearMap.fst R M M + LinearMap.snd R M M) ∘ₗ LinearMap.inr R M M = LinearMap.id := by
      rw [LinearMap.add_comp, LinearMap.fst_comp_inr, LinearMap.snd_comp_inr, zero_add]
    rw [TJ.map_mul, ← TJ.map_comp, ← TJ.map_comp, e1, e2, TJ.map_id, TJ.map_id]
  have k1 : LinearMap.fst R M M ∘ₗ γJ L (M × M) z = γJ L M t := by rw [← γJ_map, h1]
  have k2 : LinearMap.snd R M M ∘ₗ γJ L (M × M) z = γJ L M t' := by rw [← γJ_map, h2]
  rw [← h3, γJ_map, LinearMap.add_comp, k1, k2]

theorem γJ_one : γJ L M TJ.one = 0 := by
  have h := γJ_mul (TJ.one : TJ L M) TJ.one
  rw [TJ.mul_one] at h
  exact left_eq_add.mp h

def TJ.nsmul (n : ℕ) (t : TJ L M) : TJ L M := Nat.rec TJ.one (fun _ ih => TJ.mul ih t) n

omit [IsLocalRing R] in
theorem TJ.nsmul_val (n : ℕ) (t : TJ L M) : (TJ.nsmul n t).1 = L.nsmul (tS R M) n t.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change L.mul _ (TJ.nsmul n t).1 t.1 = L.mul _ (L.nsmul (tS R M) n t.1) t.1
      rw [ih]

theorem γJ_nsmul (n : ℕ) (t : TJ L M) : γJ L M (TJ.nsmul n t) = n • γJ L M t := by
  induction n with
  | zero => rw [zero_smul]; exact γJ_one
  | succ n ih =>
      change γJ L M (TJ.mul (TJ.nsmul n t) t) = _
      rw [γJ_mul, ih, add_smul, one_smul]

theorem isTorsionPoint_iff_smul_γJ (n : ℕ) (t : TJ L M) :
    L.IsTorsionPoint (tS R M) n t.1 ↔ (n : R) • γJ L M t = 0 := by
  rw [RelativeGroupLaw.isTorsionPoint_def, ← TJ.nsmul_val, ← TJ.one_val, Nat.cast_smul_eq_nsmul R,
    ← γJ_nsmul, ← γJ_one (L := L) (M := M), (γJ L M).apply_eq_iff_eq]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end Additive
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ"

section Free

open TensorProduct KaehlerDifferential

variable (L)

theorem f_jpt : f.base (jpt L) = closedPoint R := by
  change ((eR L).1 ≫ f).base (closedPoint R) = closedPoint R
  rw [eR_comp]
  rfl

theorem nonempty_ωJ_equiv (d : ℕ) [SmoothOfRelativeDimension d f] : Nonempty (ωJ L ≃ₗ[R] (Fin d → R)) := by
  obtain ⟨U, hU, V, hV, hjV, hle, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := f) (jpt L)

  have hUtop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp (by rw [← f_jpt L]; exact hle hjV)
  subst hUtop

  let O := J.presheaf.stalk (jpt L)
  let B := Γ(J, V)
  let ρ : R →+* B := (f.appLE ⊤ V hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI algRB : Algebra R B := ρ.toAlgebra
  haveI hB : Algebra.IsStandardSmoothOfRelativeDimension d R B :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (f.appLE ⊤ V hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv hsm
  haveI : Algebra.IsStandardSmooth R B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d

  letI algBO : Algebra B O := TopCat.Presheaf.algebra_section_stalk J.presheaf ⟨jpt L, hjV⟩
  haveI : IsLocalization.AtPrime O (hV.primeIdealOf ⟨jpt L, hjV⟩).asIdeal := hV.isLocalization_stalk ⟨jpt L, hjV⟩
  haveI : Algebra.FormallyEtale B O :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨jpt L, hjV⟩).asIdeal.primeCompl
  haveI : IsScalarTower R B O := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change (J.presheaf.germ ⊤ (jpt L) trivial).hom (f.appTop.hom _) =
      (J.presheaf.germ V (jpt L) hjV).hom ((f.app ⊤ ≫ J.presheaf.map (homOfLE hle).op).hom _)
    rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply _ (J.presheaf.germ V (jpt L) hjV),
      TopCat.Presheaf.germ_res]
    rfl
  haveI : Nontrivial B := (algebraMap B O).domain_nontrivial

  let EΩ : O ⊗[B] Ω[B⁄R] ≃ₗ[O] Ω[O⁄R] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B O
  haveI : Module.Free O Ω[O⁄R] := Module.Free.of_equiv EΩ
  have hrkB : Module.rank B Ω[B⁄R] = d := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d
  have hrkO : Module.rank O Ω[O⁄R] = d := by
    rw [← EΩ.rank_eq, Module.rank_baseChange, hrkB]
    simp

  letI algOR : Algebra O R := (πₐ L).toRingHom.toAlgebra
  haveI : IsScalarTower R O R := IsScalarTower.of_algebraMap_eq' (πₐ L).comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap O R) := fun r => ⟨algebraMap R O r, π_algebraMap r⟩
  have hexact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R O R hsurj
  haveI : Subsingleton Ω[R⁄R] := KaehlerDifferential.subsingleton_of_surjective R R Function.surjective_id
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := R) (P := O) (S := R) hsurj).symm
    ⟨Algebra.ofId R _, Subsingleton.elim _ _⟩
  have hbij : Function.Bijective (kerCotangentToTensor R O R) := by
    refine ⟨fun x y hxy => ?_, fun z => (hexact z).mp (Subsingleton.elim _ _)⟩
    have := congrArg l hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hl] at this
  let E1 : ωJ L ≃ₗ[O] R ⊗[O] Ω[O⁄R] := LinearEquiv.ofBijective _ hbij

  have hrkR : Module.rank R (R ⊗[O] Ω[O⁄R]) = Module.rank R (Fin d → R) := by
    rw [Module.rank_baseChange, hrkO, rank_fin_fun]
    simp
  obtain ⟨E2⟩ := nonempty_linearEquiv_of_rank_eq hrkR
  exact ⟨(E1.restrictScalars R).trans E2⟩

end Free
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ"

end Stalk
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ"

end Tangent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ"

section GSide

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (v : ℕ)
variable (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

def TG : Type :=
  { x : G.Point (TrivSqZeroExt R M) v // G.pointMap (TrivSqZeroExt.fstHom R R M) v x = 1 }

variable {G v M}
variable {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

theorem pointMap_fstHom_eq_one_iff (x : G.Point (TrivSqZeroExt R M) v) :
    G.pointMap (TrivSqZeroExt.fstHom R R M) v x = 1 ↔
      ∀ a, (PDivisibleGroup.Point.toAlgHom x a).fst = Coalgebra.counit (R := R) a := by
  constructor
  · intro hx a
    have := congrArg (fun y => PDivisibleGroup.Point.toAlgHom y a) hx
    simp at this
    exact this
  · intro hx
    exact PDivisibleGroup.Point.ext fun a => by have h__af := hx a; simp at h__af ⊢; exact h__af

namespace TG

@[scoped ext] theorem ext {x x' : TG G v M} (hxx' : x.1 = x'.1) : x = x' := Subtype.ext hxx'

def map (φ : M →ₗ[R] N) (x : TG G v M) : TG G v N :=
  ⟨G.pointMap (TrivSqZeroExt.map φ) v x.1, by
    rw [← MonoidHom.comp_apply, ← PDivisibleGroup.pointMap_comp]
    have hc : (TrivSqZeroExt.fstHom R R N).comp (TrivSqZeroExt.map φ) = TrivSqZeroExt.fstHom R R M :=
      AlgHom.ext fun a => TrivSqZeroExt.fst_map φ a
    rw [hc]
    exact x.2⟩

@[scoped simp] theorem map_val (φ : M →ₗ[R] N) (x : TG G v M) :
    (map φ x).1 = G.pointMap (TrivSqZeroExt.map φ) v x.1 := rfl

end TG
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TG"

def liftG (g : G.Cotangent v →ₗ[R] M) : G.level v →ₐ[R] TrivSqZeroExt R M :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
    (Bialgebra.counitAlgHom R (G.level v)) g).choose

theorem fst_liftG (g : G.Cotangent v →ₗ[R] M) (a : G.level v) :
    (liftG g a).fst = Coalgebra.counit (R := R) a :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
    (Bialgebra.counitAlgHom R (G.level v)) g).choose_spec.1.1 a

theorem snd_liftG (g : G.Cotangent v →ₗ[R] M) (a : G.augIdeal v) :
    (liftG g (a : G.level v)).snd = g ((G.augIdeal v).toCotangent a) :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
    (Bialgebra.counitAlgHom R (G.level v)) g).choose_spec.1.2 a

theorem liftG_unique (g : G.Cotangent v →ₗ[R] M) (ψ : G.level v →ₐ[R] TrivSqZeroExt R M)
    (h1 : ∀ a, (ψ a).fst = Coalgebra.counit (R := R) a)
    (h2 : ∀ a : G.augIdeal v, (ψ (a : G.level v)).snd = g ((G.augIdeal v).toCotangent a)) :
    ψ = liftG g :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
    (Bialgebra.counitAlgHom R (G.level v)) g).unique ⟨h1, h2⟩
    (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
      (Bialgebra.counitAlgHom R (G.level v)) g).choose_spec.1

theorem exists_eq_liftG (ψ : G.level v →ₐ[R] TrivSqZeroExt R M)
    (h1 : ∀ a, (ψ a).fst = Coalgebra.counit (R := R) a) : ∃ g : G.Cotangent v →ₗ[R] M, ψ = liftG g := by
  obtain ⟨g, hg⟩ := AlgHom.exists_cotangent_linearMap_of_fst_eq (Bialgebra.counitAlgHom R (G.level v)) ψ h1
  exact ⟨g, liftG_unique g ψ h1 hg⟩

theorem liftG_injective : Function.Injective (liftG (G := G) (v := v) (M := M)) := by
  intro g g' hgg'
  apply LinearMap.ext
  intro c
  obtain ⟨a, rfl⟩ := (G.augIdeal v).toCotangent_surjective c
  rw [← snd_liftG, ← snd_liftG, hgg']

theorem map_comp_liftG (φ : M →ₗ[R] N) (g : G.Cotangent v →ₗ[R] M) :
    (TrivSqZeroExt.map φ).comp (liftG g) = liftG (φ ∘ₗ g) := by
  refine liftG_unique _ _ (fun r => ?_) (fun a => ?_)
  · rw [AlgHom.comp_apply, TrivSqZeroExt.fst_map, fst_liftG]
  · rw [AlgHom.comp_apply, TrivSqZeroExt.snd_map, snd_liftG, LinearMap.comp_apply]

def pointOfG (g : G.Cotangent v →ₗ[R] M) : TG G v M :=
  ⟨PDivisibleGroup.Point.ofAlgHom (liftG g), (pointMap_fstHom_eq_one_iff _).mpr (fst_liftG g)⟩

@[scoped simp] theorem pointOfG_val (g : G.Cotangent v →ₗ[R] M) :
    (pointOfG g).1 = PDivisibleGroup.Point.ofAlgHom (liftG g) := rfl

theorem pointOfG_injective : Function.Injective (pointOfG (G := G) (v := v) (M := M)) := fun _ _ hgg' =>
  liftG_injective (congrArg (fun x : TG G v M => PDivisibleGroup.Point.toAlgHom x.1) hgg')

theorem pointOfG_surjective : Function.Surjective (pointOfG (G := G) (v := v) (M := M)) := by
  intro x
  obtain ⟨g, hg⟩ := exists_eq_liftG (PDivisibleGroup.Point.toAlgHom x.1) ((pointMap_fstHom_eq_one_iff _).mp x.2)
  exact ⟨g, TG.ext (by rw [pointOfG_val, ← hg]; rfl)⟩

theorem pointOfG_map (φ : M →ₗ[R] N) (g : G.Cotangent v →ₗ[R] M) :
    pointOfG (φ ∘ₗ g) = TG.map φ (pointOfG g) :=
  TG.ext (by rw [pointOfG_val, TG.map_val, pointOfG_val, ← map_comp_liftG]; rfl)

variable (G v M) in

def γG : TG G v M ≃ (G.Cotangent v →ₗ[R] M) :=
  (Equiv.ofBijective pointOfG ⟨pointOfG_injective, pointOfG_surjective⟩).symm

theorem γG_symm_apply (g : G.Cotangent v →ₗ[R] M) : (γG G v M).symm g = pointOfG g := rfl

theorem γG_map (φ : M →ₗ[R] N) (x : TG G v M) : γG G v N (TG.map φ x) = φ ∘ₗ γG G v M x := by
  obtain ⟨g, rfl⟩ := (γG G v M).symm.surjective x
  rw [γG_symm_apply, ← pointOfG_map]
  exact ((γG G v N).apply_symm_apply _).trans (congrArg _ ((γG G v M).apply_symm_apply g)).symm

end GSide
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TG"

section Bridge

variable {R : Type} [CommRing R] [IsLocalRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  {L : RelativeGroupLaw R f} {p h : ℕ} {G : PDivisibleGroup R p h}
  (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
  (he_mul : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v),
    ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val)
  (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (x : G.Point T v),
    ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1)
  {v : ℕ}
  {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

include he_mul in
omit [IsLocalRing R] in

theorem e_one (T : Type) [CommRing T] [Algebra R T] : ((e v T 1).val : SchemeHomOver _ f) = L.one _ := by
  set x := ((e v T 1).val : SchemeHomOver _ f)
  have hx : x = L.mul _ x x := by simpa using he_mul v T 1 1
  calc x = L.mul _ (L.one _) x := (L.one_mul _ x).symm
    _ = L.mul _ (L.mul _ (L.inv _ x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul _ (L.inv _ x) (L.mul _ x x) := L.mul_assoc _ _ _ _
    _ = L.mul _ (L.inv _ x) x := by rw [← hx]
    _ = L.one _ := L.inv_mul_cancel _ x

include he_mul he_nat in
omit [IsLocalRing R] in

theorem pointMap_fstHom_eq_one_iff_comp (x : G.Point (TrivSqZeroExt R M) v) :
    G.pointMap (TrivSqZeroExt.fstHom R R M) v x = 1 ↔
      bS R M ≫ ((e v (TrivSqZeroExt R M) x).val : SchemeHomOver _ f).1 = (eR L).1 := by
  rw [← he_nat v _ R (TrivSqZeroExt.fstHom R R M) x]
  constructor
  · intro hx
    rw [hx, e_one e he_mul R]
  · intro hx
    apply (e v R).injective
    apply Subtype.ext
    apply Subtype.ext
    rw [hx, e_one e he_mul R]

def bridge : TG G v M ≃ { t : TJ L M // L.IsTorsionPoint (tS R M) (p ^ v) t.1 } where
  toFun x := ⟨⟨(e v (TrivSqZeroExt R M) x.1).val,
      Subtype.ext ((pointMap_fstHom_eq_one_iff_comp e he_mul he_nat x.1).mp x.2)⟩, (e v _ x.1).2⟩
  invFun t := ⟨(e v (TrivSqZeroExt R M)).symm ⟨t.1.1, t.2⟩,
      (pointMap_fstHom_eq_one_iff_comp e he_mul he_nat _).mpr (by rw [Equiv.apply_symm_apply]; exact t.1.bS_comp)⟩
  left_inv x := TG.ext (by simp)
  right_inv t := Subtype.ext (TJ.ext (by simp))

omit [IsLocalRing R] in
@[scoped simp] theorem bridge_apply_val_val (x : TG G v M) :
    ((bridge e he_mul he_nat x).1 : TJ L M).1 = (e v (TrivSqZeroExt R M) x.1).val := rfl

include he_nat in
omit [IsLocalRing R] in

theorem bridge_map (φ : M →ₗ[R] N) (x : TG G v M) :
    ((bridge e he_mul he_nat (TG.map φ x)).1 : TJ L N) = TJ.map φ (bridge e he_mul he_nat x).1 :=
  TJ.ext (he_nat v _ _ (TrivSqZeroExt.map φ) x.1)

variable (L) (p) (v) in

abbrev KJ : Submodule R (ωJ L) := Ideal.span {(p : R) ^ v} • ⊤

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
theorem KJ_le_ker_iff (ψ : ωJ L →ₗ[R] M) : KJ L p v ≤ LinearMap.ker ψ ↔ ((p ^ v : ℕ) : R) • ψ = 0 := by
  rw [Nat.cast_pow]
  constructor
  · intro hle
    ext w
    rw [LinearMap.smul_apply, LinearMap.zero_apply, ← ψ.map_smul]
    exact hle (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  · intro hψ
    refine Submodule.smul_le.mpr fun r hr w _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hw : ψ (((p : R) ^ v) • w) = 0 := by
      have := LinearMap.congr_fun hψ w
      rwa [LinearMap.smul_apply, LinearMap.zero_apply, ← ψ.map_smul] at this
    rw [LinearMap.mem_ker, mul_smul, ψ.map_smul, hw, smul_zero]

def liftKJ : (ωJ L ⧸ KJ L p v →ₗ[R] M) ≃ { ψ : ωJ L →ₗ[R] M // ((p ^ v : ℕ) : R) • ψ = 0 } where
  toFun g := ⟨g ∘ₗ (KJ L p v).mkQ, (KJ_le_ker_iff _).mp (by
    rw [LinearMap.ker_comp]; exact (Submodule.ker_mkQ _).symm.le.trans (Submodule.comap_mono bot_le))⟩
  invFun ψ := (KJ L p v).liftQ ψ.1 ((KJ_le_ker_iff _).mpr ψ.2)
  left_inv g := LinearMap.ext fun w => by
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ w
    rfl
  right_inv ψ := Subtype.ext (LinearMap.ext fun w => rfl)

def α : (G.Cotangent v →ₗ[R] M) ≃ (ωJ L ⧸ KJ L p v →ₗ[R] M) :=
  (γG G v M).symm.trans <| (bridge e he_mul he_nat).trans <|
    (Equiv.subtypeEquiv (γJ L M) (fun t => isTorsionPoint_iff_smul_γJ (p ^ v) t)).trans liftKJ.symm

theorem α_apply_mkQ (g : G.Cotangent v →ₗ[R] M) :
    (α e he_mul he_nat g) ∘ₗ (KJ L p v).mkQ = γJ L M (bridge e he_mul he_nat ((γG G v M).symm g)).1 := rfl

include he_nat in

theorem α_map (φ : M →ₗ[R] N) (g : G.Cotangent v →ₗ[R] M) :
    α e he_mul he_nat (φ ∘ₗ g) = φ ∘ₗ α e he_mul he_nat g := by
  apply LinearMap.ext
  intro w
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ w
  change ((α e he_mul he_nat (φ ∘ₗ g)) ∘ₗ (KJ L p v).mkQ) w = φ (((α e he_mul he_nat g) ∘ₗ (KJ L p v).mkQ) w)
  rw [α_apply_mkQ, α_apply_mkQ]
  have h1 : (γG G v N).symm (φ ∘ₗ g) = TG.map φ ((γG G v M).symm g) := by
    apply (γG G v N).injective
    rw [Equiv.apply_symm_apply, γG_map, Equiv.apply_symm_apply]
  rw [h1, bridge_map e he_mul he_nat, γJ_map]
  rfl

end Bridge
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TG"

section Assembly

variable {R : Type} [CommRing R]

abbrev opModule (M : Type) [AddCommGroup M] [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom

theorem isCentralScalar_opModule (M : Type) [AddCommGroup M] [Module R M] :
    @IsCentralScalar R M _ (opModule M).toSMul :=
  @IsCentralScalar.mk R M _ (opModule M).toSMul fun _ _ => rfl

theorem nonempty_linearEquiv_of_natural (W W' : Type) [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (β : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M],
      (W →ₗ[R] M) ≃ (W' →ₗ[R] M))
    (hβ : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
      (N : Type) [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
      (φ : M →ₗ[R] N) (g : W →ₗ[R] M), β N (φ ∘ₗ g) = φ ∘ₗ β M g) :
    Nonempty (W ≃ₗ[R] W') := by
  letI := opModule (R := R) W
  haveI := isCentralScalar_opModule (R := R) W
  letI := opModule (R := R) W'
  haveI := isCentralScalar_opModule (R := R) W'
  let u : W' →ₗ[R] W := β W LinearMap.id
  let u' : W →ₗ[R] W' := (β W').symm LinearMap.id
  have hu : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
      (g : W →ₗ[R] M), β M g = g ∘ₗ u := fun M _ _ _ _ g => by
    rw [← hβ, LinearMap.comp_id]
  have h1 : u' ∘ₗ u = LinearMap.id := by
    rw [← hu]
    exact (β W').apply_symm_apply _
  have h2 : u ∘ₗ u' = LinearMap.id := (β W).injective (by
    rw [hu, hu, LinearMap.comp_assoc, h1, LinearMap.comp_id, LinearMap.id_comp])
  exact ⟨LinearEquiv.ofLinear u' u h1 h2⟩

def piQuotEquiv (d : ℕ) (a : R) :
    ((Fin d → R) ⧸ (Ideal.span {a} • (⊤ : Submodule R (Fin d → R)))) ≃ₗ[R] (Fin d → R ⧸ Ideal.span {a}) := by
  let Φ : (Fin d → R) →ₗ[R] (Fin d → R ⧸ Ideal.span {a}) :=
    LinearMap.pi fun i => (Submodule.mkQ (Ideal.span {a})) ∘ₗ LinearMap.proj i
  have hΦ : Function.Surjective Φ := fun y =>
    ⟨fun i => Quotient.out (y i), funext fun i => Quotient.out_eq (y i)⟩
  have hker : LinearMap.ker Φ = Ideal.span {a} • ⊤ := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      have hxi : ∀ i, ∃ c, c * a = x i := fun i => by
        have := congrFun hx i
        change Submodule.mkQ (Ideal.span {a}) (x i) = 0 at this
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.mp this
      choose c hc using hxi
      have hx' : x = a • c := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hc]
      rw [hx']
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top
    · refine Submodule.smul_le.mpr fun r hr x _ => ?_
      rw [LinearMap.mem_ker]
      funext i
      change Submodule.mkQ (Ideal.span {a}) ((r • x) i) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hΦ)

end Assembly
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TG"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TG"

end BTDim
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TJ P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim.TG P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.BTDim"

open BTDim in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    {p h : ℕ} (G : PDivisibleGroup R p h)
    (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
      G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
    (he_mul : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v),
      ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val)
    (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (x : G.Point T v),
      ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1) :
    G.HasDimension d := by
  intro v

  obtain ⟨E1⟩ := nonempty_linearEquiv_of_natural (R := R) (G.Cotangent v) (ωJ L ⧸ KJ L p v)
    (fun M _ _ _ _ => α (v := v) (M := M) e he_mul he_nat)
    (fun M _ _ _ _ N _ _ _ _ φ g => α_map e he_mul he_nat φ g)

  obtain ⟨E2⟩ := nonempty_ωJ_equiv L d
  have hK : (KJ L p v).map (E2 : ωJ L →ₗ[R] (Fin d → R)) = Ideal.span {(p : R) ^ v} • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact ⟨E1.trans <| (Submodule.Quotient.equiv _ _ E2 hK).trans (piQuotEquiv d ((p : R) ^ v))⟩

end S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension (solution)
