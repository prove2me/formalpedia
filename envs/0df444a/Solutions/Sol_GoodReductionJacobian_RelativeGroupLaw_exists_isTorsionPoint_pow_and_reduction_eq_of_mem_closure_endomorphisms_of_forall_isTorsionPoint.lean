-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6518ab3b-e915-5ed5-b9ec-3cb7bae41a1d

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul
import Theorems.Thm_ValuationRing_exists_algHom_lift_residue_of_finite_flat
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_isSeparated_of_valuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TweakGlue

section Pow
variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem nsmul_eq_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointGroup t; L.nsmul t n x = x ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, pow_succ, ← ih]; rfl

theorem isTorsionPoint_iff_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointGroup t; L.IsTorsionPoint t n x ↔ x ^ n = 1 := by
  rw [RelativeGroupLaw.isTorsionPoint_def, nsmul_eq_pow]; rfl

@[reducible] def pointCommGroup
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (SchemeHomOver t f) :=
  { L.pointGroup t with mul_comm := hcomm t }

noncomputable def compHom {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := L.pointGroup t; letI := L.pointGroup t'
    SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := L.pointGroup t; letI := L.pointGroup t'
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := L.one_natural t t' ψ hψ
    map_mul' := fun x y => L.mul_natural t t' ψ hψ x y }

noncomputable def endoHom (𝒯 : SchemeHomOver f f)
    (h𝒯 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) 𝒯 =
        L.mul t (NeronModelInfra.schemeHomOverComp x 𝒯) (NeronModelInfra.schemeHomOverComp y 𝒯))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := L.pointGroup t; SchemeHomOver t f →* SchemeHomOver t f :=
  letI := L.pointGroup t
  MonoidHom.mk' (fun x => NeronModelInfra.schemeHomOverComp x 𝒯) (fun x y => h𝒯 t x y)

end Pow

section Ext
variable {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
  {Ω : Type u} [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra R Ω] [IsScalarTower R A Ω]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) [IsSeparated f]
  (ext : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f →
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
  (hext : ∀ x, Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ (ext x).1 = x.1)

omit [IsDomain A] [ValuationRing A] [IsFractionRing A Ω] [IsSeparated f] in
theorem spec_RAΩ : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
    Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

omit [IsDomain A] [ValuationRing A] [IsFractionRing A Ω] [IsSeparated f] in
include hext in

theorem comp_ext (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f) :
    GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap A Ω))) (spec_RAΩ) (ext x) = x :=
  Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hext])

include hext in

theorem ext_eq_of_comp (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (p : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (hp : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ p.1 = x.1) : ext x = p :=
  AlgebraicGeometry.SchemeHomOver.ext_of_isSeparated_of_valuationRing A Ω (ext x) p (by rw [hext, hp])

include hext in
theorem ext_mul (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f) :
    ext (L.mul _ x y) = L.mul _ (ext x) (ext y) := by
  apply ext_eq_of_comp ext hext
  have h := L.mul_natural _ _ (Spec.map (CommRingCat.ofHom (algebraMap A Ω))) spec_RAΩ (ext x) (ext y)
  rw [comp_ext ext hext, comp_ext ext hext] at h
  have := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

include hext in
theorem ext_endo (𝒯 : SchemeHomOver f f) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f) :
    ext (NeronModelInfra.schemeHomOverComp x 𝒯) = NeronModelInfra.schemeHomOverComp (ext x) 𝒯 := by
  apply ext_eq_of_comp ext hext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc, hext]

noncomputable def extHom :
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f →*
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f :=
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  MonoidHom.mk' ext (fun x y => ext_mul L ext hext x y)

@[scoped simp] theorem extHom_apply (x) : extHom L ext hext x = ext x := rfl

end Ext

theorem exists_mul_eq_one_add {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℕ} (hc : ¬ ℓ ∣ c) (k : ℕ) :
    ∃ u v : ℕ, c * u = 1 + ℓ ^ k * v := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, c - 1, ?_⟩
    have : 0 < c := Nat.pos_of_ne_zero fun h => hc (h ▸ dvd_zero ℓ)
    simp; omega
  · have hcop : Nat.Coprime c (ℓ ^ k) := Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hc).symm
    have h1 : 1 < ℓ ^ k := Nat.one_lt_pow hk.ne' hℓ.one_lt
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨u, c * u / ℓ ^ k, ?_⟩
    have := Nat.div_add_mod (c * u) (ℓ ^ k)
    rw [hu] at this
    linarith [this, Nat.mul_comm (ℓ ^ k) (c * u / ℓ ^ k)]

section Helpers
variable {R : Type u} [CommRing R]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
  (i : SchemeHomOver g f)
  (hihom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
          L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i))

include hihom

lemma hom_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (LB.one t) i = L.one t := by
  letI := L.pointGroup t
  have h : NeronModelInfra.schemeHomOverComp (LB.one t) i * NeronModelInfra.schemeHomOverComp (LB.one t) i
      = NeronModelInfra.schemeHomOverComp (LB.one t) i * 1 := by
    show L.mul t _ _ = _
    rw [← hihom, LB.one_mul]; exact (mul_one _).symm
  exact mul_left_cancel h

lemma hom_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ) (x : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp (LB.nsmul t m x) i = L.nsmul t m (NeronModelInfra.schemeHomOverComp x i) := by
  induction m with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]; exact hom_one L LB i hihom t
  | succ m ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hihom, ih]

omit hihom in
lemma comp_injective [IsClosedImmersion i.1] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (fun x : SchemeHomOver t g => NeronModelInfra.schemeHomOverComp x i) := by
  intro x x' h
  apply Subtype.ext
  have h1 := congrArg Subtype.val h
  simp only [NeronModelInfra.schemeHomOverComp_coe] at h1
  exact (cancel_mono i.1).mp h1

lemma isTorsionPoint_of_comp [IsClosedImmersion i.1] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m : ℕ) (x : SchemeHomOver t g)
    (h : L.IsTorsionPoint t m (NeronModelInfra.schemeHomOverComp x i)) : LB.IsTorsionPoint t m x := by
  rw [RelativeGroupLaw.isTorsionPoint_def] at h ⊢
  apply comp_injective i t
  show NeronModelInfra.schemeHomOverComp (LB.nsmul t m x) i = NeronModelInfra.schemeHomOverComp (LB.one t) i
  rw [hom_nsmul L LB i hihom, hom_one L LB i hihom]; exact h

lemma isTorsionPoint_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m : ℕ) (x : SchemeHomOver t g) (h : LB.IsTorsionPoint t m x) :
    L.IsTorsionPoint t m (NeronModelInfra.schemeHomOverComp x i) := by
  rw [RelativeGroupLaw.isTorsionPoint_def] at h ⊢
  rw [← hom_nsmul L LB i hihom, h, hom_one L LB i hihom]

omit hihom in

lemma comp_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x i) =
      NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ x) i := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

end Helpers

section Cast
variable {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (LB : RelativeGroupLaw R g) {T : Scheme.{u}}

def castOver {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x : SchemeHomOver t g) :
    SchemeHomOver t' g := ⟨x.1, x.2.trans h⟩

@[scoped simp] lemma castOver_coe {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x : SchemeHomOver t g) :
    (castOver h x).1 = x.1 := rfl

lemma isTorsionPoint_castOver {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (m : ℕ)
    (x : SchemeHomOver t g) : LB.IsTorsionPoint t' m (castOver h x) ↔ LB.IsTorsionPoint t m x := by
  subst h; rfl

end Cast

section LiftTorsion
variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]

@[reducible] noncomputable def resAlgebra : Algebra R (IsLocalRing.ResidueField A) :=
  ((IsLocalRing.residue A).comp (algebraMap R A)).toAlgebra

attribute [local instance] resAlgebra

scoped instance resScalarTower : IsScalarTower R A (IsLocalRing.ResidueField A) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

lemma algebraMap_res : algebraMap R (IsLocalRing.ResidueField A) = (IsLocalRing.residue A).comp (algebraMap R A) :=
  rfl

lemma spec_res :
    Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField A))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [algebraMap_res, CommRingCat.ofHom_comp, Spec.map_comp]

variable {A}
variable [IsNoetherianRing R] [IsDomain A] [ValuationRing A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra R Ω] [IsScalarTower R A Ω]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)

omit [IsNoetherianRing R] in

lemma exists_torsion_lift (n : ℕ)
    (hH :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃
            LB.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n,
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ g) =
            LB.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (a : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          ((e T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ g).1 =
            Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e T φ).val.1))
    (bκ : SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) g)
    (hbκ : LB.IsTorsionPoint _ n bκ) :
    ∃ (bA' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) g)
      (zB : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) g),
      LB.IsTorsionPoint _ n zB ∧
      zB.1 = Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ bA'.1 ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ bA'.1 = bκ.1 := by
  obtain ⟨H, _, _, hHfin, hHflat, -, e, he_mul, he_nat⟩ := hH

  have hκ := spec_res (R := R) A
  let φbar : WithConv (H →ₐ[R] IsLocalRing.ResidueField A) :=
    (e _).symm ⟨castOver hκ.symm bκ,
      (RelativeGroupLaw.mem_torsionSubset _ _ _ _).mpr ((isTorsionPoint_castOver LB hκ.symm n bκ).mpr hbκ)⟩
  have hφbar : ((e _ φbar).val : SchemeHomOver _ g).1 = bκ.1 := by
    simp only [φbar, Equiv.apply_symm_apply, castOver_coe]

  haveI : Module.Finite A (TensorProduct R A H) := Module.Finite.base_change R A H
  haveI : Module.Flat A (TensorProduct R A H) := Module.Flat.baseChange R A H
  let φlift : TensorProduct R A H →ₐ[A] IsLocalRing.ResidueField A :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) φbar.ofConv (fun _ _ => Commute.all _ _)
  obtain ⟨ψ', hψ'⟩ := ValuationRing.exists_algHom_lift_residue_of_finite_flat (K := Ω) φlift
  let ψ : H →ₐ[R] A := (ψ'.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hψres : ∀ h : H, IsLocalRing.residue A (ψ h) = φbar.ofConv h := by
    intro h
    show IsLocalRing.residue A (ψ' ((1 : A) ⊗ₜ[R] h)) = _
    rw [hψ']
    show Algebra.TensorProduct.lift (Algebra.ofId A _) φbar.ofConv _ ((1 : A) ⊗ₜ[R] h) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  let resAlg : A →ₐ[R] IsLocalRing.ResidueField A := (Algebra.ofId A _).restrictScalars R
  have hres_comp : WithConv.toConv (resAlg.comp (WithConv.toConv ψ).ofConv) = φbar := by
    show WithConv.toConv (resAlg.comp ψ) = φbar
    congr 1
    apply AlgHom.ext; intro h; exact hψres h
  let toΩ : A →ₐ[R] Ω := IsScalarTower.toAlgHom R A Ω
  refine ⟨(e A (.toConv ψ)).val, (e Ω (.toConv (toΩ.comp ψ))).val, (e Ω (.toConv (toΩ.comp ψ))).property,
    ?_, ?_⟩
  · have := he_nat A Ω toΩ (.toConv ψ)
    simp at this
    exact this
  · have := he_nat A _ resAlg (.toConv ψ)
    rw [hres_comp, hφbar] at this
    exact this.symm

end LiftTorsion

section Main

set_option maxHeartbeats 25600000 in
theorem tweakF
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [Algebra R Ω] [IsScalarTower R A Ω]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (hfin : ∀ k : ℕ, IsFinite (L.schemeNsmul (ℓ ^ k)))
    (htors : ∀ x : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) f,
      ∃ n : ℕ, 0 < n ∧ L.IsTorsionPoint _ n x)
    (S : Set (SchemeHomOver f f))
    (hS : ∀ 𝒯 ∈ S, ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) 𝒯 =
        L.mul t (NeronModelInfra.schemeHomOverComp x 𝒯) (NeronModelInfra.schemeHomOverComp y 𝒯))
    (ext : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (hext : ∀ x, Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ (ext x).1 = x.1)
    (k : ℕ)
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hy : letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)));
      y ∈ Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯})
    (hred : L.IsTorsionPoint
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))) (ℓ ^ k)
      (GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext y))) :
    ∃ (m : ℕ) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f),
      k ≤ m ∧
      (letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)));
        z ∈ Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯}) ∧
      L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (ℓ ^ m) z ∧
      GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext z) =
        GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext y) := by

  let tΩ := Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  let tA := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let ρ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  letI GΩ : CommGroup (SchemeHomOver tΩ f) := pointCommGroup L hcomm tΩ
  letI GA : CommGroup (SchemeHomOver tA f) := pointCommGroup L hcomm tA
  letI Gκ : CommGroup (SchemeHomOver (ρ ≫ tA) f) := pointCommGroup L hcomm (ρ ≫ tA)
  haveI : IsSeparated f := hJ.proper.toIsSeparated
  have hℓ : ℓ.Prime := Fact.out

  let E : SchemeHomOver tΩ f →* SchemeHomOver tA f := extHom L ext hext
  let Rd : SchemeHomOver tA f →* SchemeHomOver (ρ ≫ tA) f := compHom L tA (ρ ≫ tA) ρ rfl
  have hRd : ∀ p, Rd p = GoodReductionJacobian.schemeHomOverComp ρ rfl p := fun _ => rfl
  let Γ : Subgroup (SchemeHomOver tΩ f) := Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯}

  let P : SchemeHomOver tΩ f → Prop := fun w =>
    ∃ (a c : ℕ) (z : SchemeHomOver tΩ f), ¬ ℓ ∣ c ∧ z ∈ Γ ∧ z ^ (ℓ ^ a) = 1 ∧ Rd (E z) = (Rd (E w)) ^ c
  have hP : ∀ w ∈ Γ, P w := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ => P w) ?_ ?_ ?_ ?_ hw
    ·
      rintro _ ⟨𝒯, h𝒯, x, rfl⟩
      let T𝒯 := fun {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) => endoHom L 𝒯 (hS 𝒯 h𝒯) t

      obtain ⟨N, hN, hNx⟩ := htors (Rd (E x))
      obtain ⟨a, c, hc, hNeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' ℓ hℓ.ne_one

      have hx' : L.IsTorsionPoint _ (ℓ ^ a) ((Rd (E x)) ^ c) := by
        rw [isTorsionPoint_iff_pow, ← pow_mul, mul_comm, ← hNeq]
        exact (isTorsionPoint_iff_pow L _ N _).mp hNx

      have hpos : 0 < ℓ ^ a := pow_pos hℓ.pos a
      have hflat := GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
        L hJ hcomm (ℓ ^ a) hpos (hfin a)
      have hH := GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul
        L hcomm (ℓ ^ a) (hfin a) hflat
      obtain ⟨bA', zB, hzB_tors, hzB_gen, hbA'_sp⟩ := exists_torsion_lift (Ω := Ω) L (ℓ ^ a) hH ((Rd (E x)) ^ c) hx'
      have hEz : E zB = bA' := ext_eq_of_comp ext hext zB bA' hzB_gen.symm
      have hRb : Rd bA' = (Rd (E x)) ^ c :=
        Subtype.ext (by rw [hRd, GoodReductionJacobian.schemeHomOverComp_coe, hbA'_sp])
      have e1 : ∀ w, Rd (E (NeronModelInfra.schemeHomOverComp w 𝒯)) = T𝒯 _ (Rd (E w)) := fun w => by
        show GoodReductionJacobian.schemeHomOverComp ρ rfl (ext (NeronModelInfra.schemeHomOverComp w 𝒯)) =
          NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ρ rfl (ext w)) 𝒯
        rw [ext_endo ext hext, comp_comp]
      refine ⟨a, c, NeronModelInfra.schemeHomOverComp zB 𝒯, hc, Subgroup.subset_closure ⟨𝒯, h𝒯, zB, rfl⟩, ?_, ?_⟩
      · have hz := (isTorsionPoint_iff_pow L _ _ _).mp hzB_tors
        show (T𝒯 tΩ zB) ^ (ℓ ^ a) = 1
        rw [← map_pow, hz, map_one]
      · rw [e1, e1, hEz, hRb, map_pow]
    · exact ⟨0, 1, 1, fun h => hℓ.ne_one (Nat.dvd_one.mp h), Γ.one_mem, one_pow _, (pow_one _).symm⟩
    · rintro w₁ w₂ - - ⟨a₁, c₁, z₁, hc₁, hz₁, ht₁, hr₁⟩ ⟨a₂, c₂, z₂, hc₂, hz₂, ht₂, hr₂⟩
      refine ⟨a₁ + a₂, c₁ * c₂, z₁ ^ c₂ * z₂ ^ c₁, ?_, Γ.mul_mem (Γ.pow_mem hz₁ _) (Γ.pow_mem hz₂ _), ?_, ?_⟩
      · exact fun h => (hℓ.dvd_mul.mp h).elim hc₁ hc₂
      · have e1 : z₁ ^ (ℓ ^ (a₁ + a₂)) = 1 := by rw [pow_add, pow_mul, ht₁, one_pow]
        have e2 : z₂ ^ (ℓ ^ (a₁ + a₂)) = 1 := by rw [pow_add, mul_comm, pow_mul, ht₂, one_pow]
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm c₂, mul_comm c₁, pow_mul, pow_mul, e1, e2, one_pow, one_pow,
          one_mul]
      · rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hr₁, hr₂, map_mul, map_mul, mul_pow,
          ← pow_mul, ← pow_mul, mul_comm c₂ c₁]
    · rintro w - ⟨a, c, z, hc, hz, ht, hr⟩
      exact ⟨a, c, z⁻¹, hc, Γ.inv_mem hz, by rw [inv_pow, ht, inv_one], by rw [map_inv, map_inv, hr, map_inv, map_inv, inv_pow]⟩

  obtain ⟨a, c, z₀, hc, hz₀, ht₀, hr₀⟩ := hP y hy
  obtain ⟨u, v, huv⟩ := exists_mul_eq_one_add hℓ hc k
  have hyk : (Rd (E y)) ^ (ℓ ^ k) = 1 := (isTorsionPoint_iff_pow L _ _ _).mp hred
  refine ⟨max k a, z₀ ^ u, le_max_left _ _, Γ.pow_mem hz₀ _, ?_, ?_⟩
  · rw [isTorsionPoint_iff_pow, ← pow_mul]
    obtain ⟨d, hd⟩ : ℓ ^ a ∣ u * ℓ ^ max k a := Dvd.dvd.mul_left (pow_dvd_pow ℓ (le_max_right k a)) u
    rw [hd, pow_mul, ht₀, one_pow]
  · show Rd (E (z₀ ^ u)) = Rd (E y)
    rw [map_pow, map_pow, hr₀, ← pow_mul, huv, pow_add, pow_one, pow_mul, hyk, one_pow, mul_one]

end Main

end TweakGlue
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint.TweakGlue"

open TweakGlue in
set_option maxHeartbeats 3200000 in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [Algebra R Ω] [IsScalarTower R A Ω]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (hfin : ∀ k : ℕ, IsFinite (L.schemeNsmul (ℓ ^ k)))
    (htors : ∀ x : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) f,
      ∃ n : ℕ, 0 < n ∧ L.IsTorsionPoint _ n x)
    (S : Set (SchemeHomOver f f))
    (hS : ∀ 𝒯 ∈ S, ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) 𝒯 =
        L.mul t (NeronModelInfra.schemeHomOverComp x 𝒯) (NeronModelInfra.schemeHomOverComp y 𝒯))
    (ext : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (hext : ∀ x, Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ (ext x).1 = x.1)
    (k : ℕ)
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hy : letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)));
      y ∈ Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯})
    (hred : L.IsTorsionPoint
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))) (ℓ ^ k)
      (GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext y))) :
    ∃ (m : ℕ) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f),
      k ≤ m ∧
      (letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)));
        z ∈ Subgroup.closure {z | ∃ 𝒯 ∈ S, ∃ x, z = NeronModelInfra.schemeHomOverComp x 𝒯}) ∧
      L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (ℓ ^ m) z ∧
      GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext z) =
        GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) rfl (ext y) := by
  exact TweakGlue.tweakF ℓ L hJ hcomm hfin htors S hS ext hext k y hy hred

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint (solution)
