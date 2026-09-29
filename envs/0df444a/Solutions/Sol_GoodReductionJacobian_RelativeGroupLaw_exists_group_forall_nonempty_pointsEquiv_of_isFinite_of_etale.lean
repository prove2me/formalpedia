-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/15185f55-9279-558b-a9e7-e2f0e226d569

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

namespace LevelFibreBody

noncomputable section

section Points

abbrev ΓC (C : Scheme.{u}) : CommRingCat.{u} := Γ(C, ⊤)

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  {C : Scheme.{u}} (lev : C ⟶ A) [IsAffine C]

variable (f) in

def ψ : CommRingCat.of R ⟶ (ΓC C) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (lev ≫ f).appTop

theorem lev_f_eq : lev ≫ f = C.isoSpec.hom ≫ Spec.map (ψ f lev) := by
  rw [ψ, Spec.map_comp, Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

theorem isoSpec_inv_lev_f : C.isoSpec.inv ≫ lev ≫ f = Spec.map (ψ f lev) := by
  rw [lev_f_eq (f := f) lev, Iso.inv_hom_id_assoc]

variable (T : Type u) [CommRing T] (φ : R →+* T)

variable (f) in

abbrev CP : Type u :=
  {x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) f // ∃ z : Spec (CommRingCat.of T) ⟶ C, z ≫ lev = x.1}

variable (f) in

abbrev HP : Type u :=
  {χ : (ΓC C) ⟶ CommRingCat.of T // ψ f lev ≫ χ = CommRingCat.ofHom φ}

variable {T φ}
variable [Mono lev]

def toHP (x : CP f lev T φ) : HP f lev T φ :=
  ⟨Spec.preimage (x.2.choose ≫ C.isoSpec.hom), by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Category.assoc, ← lev_f_eq (f := f) lev, ← Category.assoc,
      x.2.choose_spec, x.1.2]⟩

theorem Spec_map_toHP (x : CP f lev T φ) (z : Spec (CommRingCat.of T) ⟶ C) (hz : z ≫ lev = x.1.1) :
    Spec.map (toHP lev x).1 = z ≫ C.isoSpec.hom := by
  change Spec.map (Spec.preimage _) = _
  rw [Spec.map_preimage]
  congr 1
  rw [← cancel_mono lev, x.2.choose_spec, hz]

omit [Mono lev] in

def ofHP (χ : HP f lev T φ) : CP f lev T φ :=
  ⟨⟨(Spec.map χ.1 ≫ C.isoSpec.inv) ≫ lev, by
      rw [Category.assoc, Category.assoc, isoSpec_inv_lev_f (f := f) lev, ← Spec.map_comp, χ.2]⟩,
    ⟨Spec.map χ.1 ≫ C.isoSpec.inv, rfl⟩⟩

omit [Mono lev] in
@[scoped simp] theorem ofHP_val_val (χ : HP f lev T φ) : (ofHP lev χ).1.1 = (Spec.map χ.1 ≫ C.isoSpec.inv) ≫ lev := rfl

theorem toHP_ofHP (χ : HP f lev T φ) : toHP lev (ofHP lev χ) = χ := by
  apply Subtype.ext
  apply Spec.map_injective
  rw [Spec_map_toHP lev (ofHP lev χ) (Spec.map χ.1 ≫ C.isoSpec.inv) rfl, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

theorem ofHP_toHP (x : CP f lev T φ) : ofHP lev (toHP lev x) = x := by
  apply Subtype.ext; apply Subtype.ext
  rw [ofHP_val_val, Spec_map_toHP lev x x.2.choose x.2.choose_spec]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact x.2.choose_spec

def cpEquiv : CP f lev T φ ≃ HP f lev T φ :=
  ⟨toHP lev, ofHP lev, ofHP_toHP lev, toHP_ofHP lev⟩

theorem ofHP_injective : Function.Injective (ofHP (f := f) lev (T := T) (φ := φ)) :=
  (cpEquiv lev).symm.injective

variable {T' : Type u} [CommRing T'] (h : T →+* T')

omit [IsAffine C] [Mono lev] in
theorem base_comp (φ : R →+* T) :
    Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (h.comp φ)) := by
  rw [← Spec.map_comp]; rfl

variable (φ) in

def push (x : CP f lev T φ) : CP f lev T' (h.comp φ) :=
  ⟨schemeHomOverComp (Spec.map (CommRingCat.ofHom h)) (base_comp h φ) x.1,
    ⟨Spec.map (CommRingCat.ofHom h) ≫ x.2.choose, by rw [Category.assoc, x.2.choose_spec]; rfl⟩⟩

omit [IsAffine C] [Mono lev] in
@[scoped simp] theorem push_val_val (x : CP f lev T φ) : (push lev φ h x).1.1 = Spec.map (CommRingCat.ofHom h) ≫ x.1.1 :=
  rfl

omit [Mono lev] in
theorem push_ofHP (χ : HP f lev T φ) :
    push lev φ h (ofHP lev χ) = ofHP lev ⟨χ.1 ≫ CommRingCat.ofHom h, by rw [← Category.assoc, χ.2]; rfl⟩ := by
  apply Subtype.ext; apply Subtype.ext
  rw [push_val_val, ofHP_val_val, ofHP_val_val, Spec.map_comp]
  simp only [Category.assoc]

end Points

section Standard

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
  {R' : Type u} [CommRing R'] [Algebra R R'] {n : ℕ} (ε : (R' ⊗[R] B) ≃ₐ[R'] (Fin n → R'))
  (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]

def std (i : Fin n) : B →ₐ[R] T :=
  ((IsScalarTower.toAlgHom R R' T).comp ((Pi.evalAlgHom R' (fun _ : Fin n => R') i).restrictScalars R)).comp
    ((ε.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight)

theorem std_apply (i : Fin n) (b : B) : std ε T i b = algebraMap R' T (ε (1 ⊗ₜ b) i) := rfl

def extend (χ : B →ₐ[R] T) : (Fin n → R') →ₐ[R'] T :=
  (Algebra.TensorProduct.lift (Algebra.ofId R' T) χ (fun _ _ => Commute.all _ _)).comp ε.symm.toAlgHom

theorem extend_ε_tmul (χ : B →ₐ[R] T) (b : B) : extend ε T χ (ε (1 ⊗ₜ b)) = χ b := by
  rw [extend, AlgHom.comp_apply]
  change Algebra.TensorProduct.lift _ _ _ (ε.symm (ε (1 ⊗ₜ b))) = χ b
  rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

variable {T}

theorem exists_eq_eval [IsDomain T] (θ : (Fin n → R') →ₐ[R'] T) :
    ∃ i : Fin n, ∀ v : Fin n → R', θ v = algebraMap R' T (v i) := by
  classical
  let e : Fin n → (Fin n → R') := fun i => Pi.single i 1
  have he_orth : ∀ i j, i ≠ j → θ (e i) * θ (e j) = 0 := fun i j hij => by
    rw [← map_mul]
    have : e i * e j = 0 := by
      ext l
      simp only [e, Pi.mul_apply, Pi.single_apply, Pi.zero_apply]
      by_cases h1 : l = i
      · subst h1; rw [if_neg hij]; exact mul_zero _
      · rw [if_neg h1]; exact zero_mul _
    rw [this, map_zero]
  have he_sum : ∑ i, θ (e i) = 1 := by
    rw [← map_sum]
    have : ∑ i, e i = (1 : Fin n → R') := by
      ext j
      rw [Finset.sum_apply, Pi.one_apply, Finset.sum_eq_single j]
      · simp [e]
      · intro l _ hl; simp [e, Ne.symm hl]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [this, map_one]
  have hex : ∃ i, θ (e i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : (∑ i, θ (e i)) = 0 := Finset.sum_eq_zero fun i _ => hcon i
    rw [he_sum] at this
    exact one_ne_zero this
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ j, j ≠ i → θ (e j) = 0 := fun j hj =>
    (mul_eq_zero.mp (he_orth i j (Ne.symm hj))).resolve_left hi
  have hone : θ (e i) = 1 := by
    rw [← he_sum, Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun h => absurd (Finset.mem_univ i) h)]
  refine ⟨i, fun v => ?_⟩
  have hv : v = ∑ j, v j • e j := by
    ext l
    rw [Finset.sum_apply, Finset.sum_eq_single l]
    · simp [e]
    · intro j _ hj; simp [e, Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ l) h
  calc θ v = θ (∑ j, v j • e j) := by rw [← hv]
    _ = ∑ j, θ (v j • e j) := map_sum _ _ _
    _ = θ (v i • e i) :=
        Finset.sum_eq_single i (fun j _ hj => by rw [map_smul, hzero j hj, smul_zero])
          (fun h => absurd (Finset.mem_univ i) h)
    _ = algebraMap R' T (v i) := by rw [map_smul, hone, Algebra.smul_def, mul_one]

theorem exists_eq_std [IsDomain T] (χ : B →ₐ[R] T) : ∃ i : Fin n, χ = std ε T i := by
  obtain ⟨i, hi⟩ := exists_eq_eval (extend ε T χ)
  refine ⟨i, AlgHom.ext fun b => ?_⟩
  rw [std_apply, ← extend_ε_tmul ε T χ b, hi]

theorem std_injective [Nontrivial T] : Function.Injective (std ε T) := by
  classical
  intro i j hij
  by_contra hne

  let Θ : Fin n → ((R' ⊗[R] B) →ₐ[R'] T) := fun l =>
    (IsScalarTower.toAlgHom R' R' T).comp ((Pi.evalAlgHom R' (fun _ : Fin n => R') l).comp ε.toAlgHom)
  have hΘ : ∀ l (b : B), Θ l (1 ⊗ₜ b) = std ε T l b := fun l b => rfl
  have hij' : Θ i = Θ j := by
    apply Algebra.TensorProduct.ext'
    intro a b
    have h1 : ∀ l, Θ l (a ⊗ₜ b) = algebraMap R' T a * Θ l (1 ⊗ₜ b) := fun l => by
      rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, h1, hΘ, hΘ, hij]
  have h2 : Θ i (ε.symm (Pi.single i 1)) = Θ j (ε.symm (Pi.single i 1)) := by rw [hij']
  change algebraMap R' T (ε (ε.symm _) i) = algebraMap R' T (ε (ε.symm _) j) at h2
  rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), map_one, map_zero] at h2
  exact one_ne_zero h2

end Standard

section Factor

theorem exists_ringHom_comp_algebraMap_eq {R : Type u} [CommRing R] {T : Type u} [CommRing T] [IsDomain T]
    [Algebra R T] [Algebra.IsIntegral R T] (hinj : Function.Injective (algebraMap R T))
    (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k) :
    ∃ hk : T →+* k, hk.comp (algebraMap R T) = sk := by
  haveI : (RingHom.ker sk).IsPrime := RingHom.ker_isPrime sk
  obtain ⟨Q, -, hQ, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := T) (RingHom.ker sk) ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hQ

  let P : Ideal R := Q.comap (algebraMap R T)
  have hPk : ∀ a ∈ P, sk a = 0 := fun a ha => by
    have : a ∈ RingHom.ker sk := by rw [← hQcomap]; exact ha
    exact this
  letI algPk : Algebra (R ⧸ P) k := (Ideal.Quotient.lift P sk hPk).toAlgebra
  haveI : IsDomain (T ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.IsTorsionFree (R ⧸ P) (T ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (R ⧸ P) k := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    exact (Ideal.injective_lift_iff hPk).mpr hQcomap.symm
  haveI : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  haveI : Algebra.IsAlgebraic (R ⧸ P) (T ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (T ⧸ Q) →ₐ[R ⧸ P] k := IsAlgClosed.lift
  refine ⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap R T r) = algebraMap (R ⧸ P) (T ⧸ Q) (Ideal.Quotient.mk P r) := rfl
  rw [RingHom.comp_apply, RingHom.comp_apply, h1]
  change σ _ = _
  rw [AlgHom.commutes]
  exact Ideal.Quotient.lift_mk P sk hPk

end Factor

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {C : Scheme.{u}} (lev : C ⟶ A) [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)]

def stdPt {R' : Type u} [CommRing R'] [Algebra R R'] {n : ℕ} [IsAffine C]
    (ε : letI := (ψ f lev).hom.toAlgebra; (R' ⊗[R] (ΓC C)) ≃ₐ[R'] (Fin n → R'))
    (T : Type u) [CommRing T] (g : R' →+* T) (i : Fin n) : CP f lev T (g.comp (algebraMap R R')) :=
  letI := (ψ f lev).hom.toAlgebra
  letI := (g.comp (algebraMap R R')).toAlgebra
  letI := g.toAlgebra
  haveI : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  ofHP lev ⟨CommRingCat.ofHom (std ε T i).toRingHom, by
    ext r
    exact (std ε T i).commutes r⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)] in
theorem stdPt_val_val {R' : Type u} [CommRing R'] [Algebra R R'] {n : ℕ} [IsAffine C]
    (ε : letI := (ψ f lev).hom.toAlgebra; (R' ⊗[R] (ΓC C)) ≃ₐ[R'] (Fin n → R'))
    (T : Type u) [CommRing T] (g : R' →+* T) (i : Fin n) :
    (stdPt lev ε T g i).1.1 =
      (Spec.map (CommRingCat.ofHom
        (letI := (ψ f lev).hom.toAlgebra
         letI := (g.comp (algebraMap R R')).toAlgebra
         letI := g.toAlgebra
         haveI : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
         (std ε T i).toRingHom)) ≫ C.isoSpec.inv) ≫ lev :=
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)] in

theorem stdPt_bijective {R' : Type u} [CommRing R'] [Algebra R R'] {n : ℕ} [IsAffine C]
    (ε : letI := (ψ f lev).hom.toAlgebra; (R' ⊗[R] (ΓC C)) ≃ₐ[R'] (Fin n → R'))
    (T : Type u) [CommRing T] [IsDomain T] (g : R' →+* T) : Function.Bijective (stdPt lev ε T g) := by
  letI := (ψ f lev).hom.toAlgebra
  letI := (g.comp (algebraMap R R')).toAlgebra
  letI := g.toAlgebra
  haveI : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  constructor
  · intro i j hij
    have h1 := congrArg Subtype.val (ofHP_injective lev hij)
    have h2 : (std ε T i).toRingHom = (std ε T j).toRingHom :=
      congrArg CommRingCat.Hom.hom h1
    exact std_injective ε (AlgHom.ext fun b => RingHom.congr_fun h2 b)
  · intro x
    let χ : (ΓC C) →ₐ[R] T :=
      { (toHP lev x).1.hom with
        commutes' := fun r => by
          have h := congrArg (fun η => η.hom r) (toHP lev x).2
          exact h }
    obtain ⟨i, hi⟩ := exists_eq_std ε χ
    refine ⟨i, ?_⟩
    rw [← ofHP_toHP lev x]
    change ofHP lev _ = ofHP lev _
    congr 1
    apply Subtype.ext
    change CommRingCat.ofHom (std ε T i).toRingHom = (toHP lev x).1
    rw [← hi]
    rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)] in

theorem push_stdPt {R' : Type u} [CommRing R'] [Algebra R R'] {n : ℕ} [IsAffine C]
    (ε : letI := (ψ f lev).hom.toAlgebra; (R' ⊗[R] (ΓC C)) ≃ₐ[R'] (Fin n → R'))
    (T : Type u) [CommRing T] (g : R' →+* T) {T' : Type u} [CommRing T'] (h : T →+* T') (i : Fin n) :
    (push lev (g.comp (algebraMap R R')) h (stdPt lev ε T g i)).1.1 = (stdPt lev ε T' (h.comp g) i).1.1 := by
  rw [push_val_val, stdPt_val_val, stdPt_val_val, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem main
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∃ z : T ⟶ C, z ≫ lev = (L.one t).1)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ z : T ⟶ C, z ≫ lev = x.1) → (∃ z : T ⟶ C, z ≫ lev = y.1) → ∃ z : T ⟶ C, z ≫ lev = (L.mul t x y).1) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G),
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
        ∃ e : G ≃ {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1},
          ∀ a b : G,
            ((e (a * b) : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1}) :
                SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f) =
              L.mul (Spec.map (CommRingCat.ofHom sk)) (e a) (e b) := by

  haveI : IsAffine C := isAffine_of_isAffineHom (lev ≫ f)
  have hSpec : Spec.map (ψ f lev) = C.isoSpec.inv ≫ lev ≫ f := (isoSpec_inv_lev_f lev).symm
  haveI : IsFinite (Spec.map (ψ f lev)) := by rw [hSpec]; infer_instance
  haveI : Etale (Spec.map (ψ f lev)) := by rw [hSpec]; infer_instance
  have hfin : (ψ f lev).hom.Finite := (IsFinite.SpecMap_iff (ψ f lev)).mp inferInstance
  have het : (ψ f lev).hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance
  letI algB : Algebra R (ΓC C) := (ψ f lev).hom.toAlgebra
  haveI : Module.Finite R (ΓC C) := hfin
  haveI : Algebra.Etale R (ΓC C) := het

  obtain ⟨R', _, _, _, _, _, _, ⟨ε⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi R (ΓC C)

  obtain ⟨⟨𝔮, h𝔮⟩, h𝔮0⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R') ⟨⊥, Ideal.isPrime_bot⟩
  have h𝔮0' : 𝔮.comap (algebraMap R R') = ⊥ := congrArg PrimeSpectrum.asIdeal h𝔮0
  haveI := h𝔮
  let T₀ : Type u := R' ⧸ 𝔮
  haveI : IsDomain T₀ := Ideal.Quotient.isDomain 𝔮
  let g₀ : R' →+* T₀ := Ideal.Quotient.mk 𝔮
  have hφ₀ : algebraMap R T₀ = g₀.comp (algebraMap R R') := rfl
  haveI : Module.Finite R T₀ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R 𝔮).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral R T₀ := Algebra.IsIntegral.of_finite R T₀
  have hinj : Function.Injective (algebraMap R T₀) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot, hφ₀, ← Ideal.comap_comap]
    have : Ideal.comap g₀ ⊥ = 𝔮 := by
      rw [← RingHom.ker_eq_comap_bot]; exact Ideal.mk_ker
    rw [this, h𝔮0']

  let t₀ : Spec (CommRingCat.of T₀) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (g₀.comp (algebraMap R R')))
  letI grp : Group (SchemeHomOver t₀ f) := L.pointGroup t₀
  have hmul_def : ∀ x y : SchemeHomOver t₀ f, x * y = L.mul t₀ x y := fun _ _ => rfl
  let pt₀ := stdPt lev ε T₀ g₀
  have hpt₀ : Function.Bijective pt₀ := stdPt_bijective lev ε T₀ g₀
  haveI hfinCP : Finite (CP f lev T₀ (g₀.comp (algebraMap R R'))) :=
    Finite.of_equiv _ (Equiv.ofBijective pt₀ hpt₀)
  let H : Subgroup (SchemeHomOver t₀ f) :=
    { carrier := {x | ∃ z : Spec (CommRingCat.of T₀) ⟶ C, z ≫ lev = x.1}
      mul_mem' := fun {x y} hx hy => hmul t₀ x y hx hy
      one_mem' := hone t₀
      inv_mem' := fun {x} hx => by
        let m : CP f lev T₀ (g₀.comp (algebraMap R R')) → CP f lev T₀ (g₀.comp (algebraMap R R')) :=
          fun y => ⟨x * y.1, hmul t₀ x y.1 hx y.2⟩
        have hm : Function.Injective m := fun y y' hyy' =>
          Subtype.ext (mul_left_cancel (congrArg Subtype.val hyy'))
        obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hm) ⟨1, hone t₀⟩
        have hy' : x * y.1 = 1 := congrArg Subtype.val hy
        have : x⁻¹ = y.1 := inv_eq_of_mul_eq_one_right hy'
        rw [Set.mem_setOf_eq, this]
        exact y.2 }
  let eH : ↥H ≃ CP f lev T₀ (g₀.comp (algebraMap R R')) :=
    ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩
  refine ⟨↥H, inferInstance, Finite.of_equiv _ eH.symm, ?_⟩

  intro k _ _ sk
  obtain ⟨hk, hcomp⟩ := exists_ringHom_comp_algebraMap_eq hinj k sk
  subst hcomp
  let ptk := stdPt lev ε k (hk.comp g₀)
  have hptk : Function.Bijective ptk := stdPt_bijective lev ε k (hk.comp g₀)

  let pu : CP f lev T₀ (g₀.comp (algebraMap R R')) → CP f lev k (hk.comp (algebraMap R T₀)) :=
    push lev (g₀.comp (algebraMap R R')) hk
  have hpu : ∀ i, pu (pt₀ i) = ptk i := fun i =>
    Subtype.ext (Subtype.ext (push_stdPt lev ε T₀ g₀ hk i))
  have hpu_bij : Function.Bijective pu := by
    have : pu = ptk ∘ (Equiv.ofBijective pt₀ hpt₀).symm := by
      funext x
      obtain ⟨i, rfl⟩ := hpt₀.2 x
      rw [Function.comp_apply, Equiv.ofBijective_symm_apply_apply]
      exact hpu i
    rw [this]
    exact hptk.comp (Equiv.ofBijective pt₀ hpt₀).symm.bijective
  refine ⟨eH.trans (Equiv.ofBijective pu hpu_bij), fun a b => ?_⟩
  change (pu (eH (a * b))).1 = L.mul _ (pu (eH a)).1 (pu (eH b)).1
  exact L.mul_natural t₀ _ (Spec.map (CommRingCat.ofHom hk)) (base_comp hk _) a.1 b.1

end Main

end

end LevelFibreBody
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale.LevelFibreBody"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {C : Scheme.{u}} (lev : C ⟶ A) [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)]
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∃ z : T ⟶ C, z ≫ lev = (L.one t).1)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ z : T ⟶ C, z ≫ lev = x.1) → (∃ z : T ⟶ C, z ≫ lev = y.1) → ∃ z : T ⟶ C, z ≫ lev = (L.mul t x y).1) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G),
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
        ∃ e : G ≃ {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1},
          ∀ a b : G,
            ((e (a * b) : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1}) :
                SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f) =
              L.mul (Spec.map (CommRingCat.ofHom sk)) (e a) (e b) :=
  LevelFibreBody.main L lev hone hmul

end S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale (solution)
