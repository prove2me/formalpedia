-- Prove2me | solution 1 for HopfAlgebra.eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/00225cf0-2137-50c4-8be2-36e6c87c89d7

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_FinFlatHopf_dualPoints_equiv_monoidHom
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace WAaux

def liftEquiv {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x) :
    AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ

theorem liftEquiv_apply {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x)
    (z : AlgebraicClosure ℚ) : liftEquiv σ hσ z = σ z := rfl

theorem liftEquiv_symm_apply_apply {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x)
    (z : AlgebraicClosure ℚ) : σ ((liftEquiv σ hσ).symm z) = z :=
  (liftEquiv σ hσ).apply_symm_apply z

def unitsChar {M K : Type} [Monoid M] [Field K] (q : ℕ) (hq : 0 < q) (hM : ∀ f : M, f ^ q = 1) (φ : M →* K) : M →* Kˣ where
  toFun f := Units.ofPowEqOne (φ f) q (by rw [← map_pow, hM, map_one]) hq.ne'
  map_one' := Units.ext (by simp)
  map_mul' f g := Units.ext (by simp)

@[scoped simp] theorem val_unitsChar_apply {M K : Type} [Monoid M] [Field K] (q : ℕ) (hq : 0 < q) (hM : ∀ f : M, f ^ q = 1)
    (φ : M →* K) (f : M) : ((unitsChar q hq hM φ f : Kˣ) : K) = φ f := rfl

end WAaux
p2m_reactivate "P2MW.S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant.WAaux"

open WAaux in

theorem WA_exists_dualPoint
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)] [FaithfulSMul O (AlgebraicClosure ℚ)]
    (hOA : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : O, algebraMap O (AlgebraicClosure ℚ) x = y)
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
    (hHOq : ∀ f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ), f ^ q = 1)
    (φ : WithConv (HO →ₐ[O] AlgebraicClosure ℚ) →* AlgebraicClosure ℚ)
    (hφ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (HO →ₐ[O] AlgebraicClosure ℚ),
      (∀ h : HO, g h = σ (f h)) → φ g = φ f) :
    ∃ (_ : Module.Free O HO)
      (e : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ) ≃* (WithConv (HO →ₐ[O] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ))
      (ψ : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ)),

      (∀ (g : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ)) (f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ)),
        ((e g f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          Algebra.TensorProduct.productMap (WithConv.ofConv g) (AlgHom.id O (AlgebraicClosure ℚ))
            ((TensorProduct.congr (CartierDual.ofDual O HO) (LinearEquiv.refl O (AlgebraicClosure ℚ)))
              ((dualTensorHomEquiv O HO (AlgebraicClosure ℚ)).symm (WithConv.ofConv f).toLinearMap))) ∧

      (∀ f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ), ((e ψ f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = φ f) ∧

      ψ ^ q = 1 ∧

      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
        ∀ ψ' : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ), (∀ y : CartierDual O HO, ψ' y = σ (ψ y)) →
          ψ' = ψ ^ c) := by
  classical

  haveI : IsPrincipalIdealRing O := inferInstance
  haveI : Module.IsTorsionFree O HO := Module.Flat.isTorsionFree
  haveI hfree : Module.Free O HO := Module.free_of_finite_type_torsion_free'

  have hcard : Nat.card (WithConv (HO →ₐ[O] AlgebraicClosure ℚ)) = Module.finrank O HO := by
    rw [Nat.card_congr (WithConv.equiv (HO →ₐ[O] AlgebraicClosure ℚ))]
    exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O HO (AlgebraicClosure ℚ)
  obtain ⟨e, he, heτ⟩ := FinFlatHopf.dualPoints_equiv_monoidHom O HO (AlgebraicClosure ℚ) hcard

  have hq : 0 < q := (Fact.out : q.Prime).pos
  let φu : WithConv (HO →ₐ[O] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ := unitsChar q hq hHOq φ
  let ψ : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ) := e.symm φu
  have hψ : e ψ = φu := e.apply_symm_apply φu
  have hψφ : ∀ f, ((e ψ f : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = φ f := fun f => by rw [hψ]; rfl

  have hψq : ψ ^ q = 1 := by
    apply e.injective
    rw [map_pow, hψ, map_one]
    ext f
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one, val_unitsChar_apply,
      ← map_pow, hHOq, map_one]
  refine ⟨hfree, e, ψ, he, hψφ, hψq, ?_⟩

  intro σ hσ c hc ψ' hψ'
  have hfix : ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x := (hOfix σ).1 hσ
  set τ : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ := liftEquiv σ hfix with hτ

  have hψ'eq : ψ' = WithConv.toConv (τ.toAlgHom.comp (WithConv.ofConv ψ)) := by
    refine WithConv.ext (AlgHom.ext fun y => ?_)
    rw [hψ' y]
    rfl
  apply e.injective
  refine MonoidHom.ext fun f => Units.ext ?_

  have hL := heτ τ ψ f
  rw [← hψ'eq] at hL

  set f₀ : WithConv (HO →ₐ[O] AlgebraicClosure ℚ) := WithConv.toConv (τ.symm.toAlgHom.comp (WithConv.ofConv f)) with hf₀
  have hff₀ : ∀ h : HO, f h = σ (f₀ h) := fun h => (liftEquiv_symm_apply_apply σ hfix (f h)).symm
  have hinv : φ f = φ f₀ := hφ σ hσ f₀ f hff₀
  rw [hL, hψφ, ← hinv, map_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hψφ]

  have hroot : (φ f) ^ q = 1 := by rw [← map_pow, hHOq, map_one]
  exact hc (φ f) hroot

open WAaux in

theorem WA_exists_constQuot
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)] [FaithfulSMul O (AlgebraicClosure ℚ)]
    (hOA : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : O, algebraMap O (AlgebraicClosure ℚ) x = y)
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Free O HO] [Coalgebra.IsCocomm O HO]
    (e : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ) ≃* (WithConv (HO →ₐ[O] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ)ˣ))
    (ψ : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ)) (hψq : ψ ^ q = 1)
    (hψcyc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
        ∀ ψ' : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ), (∀ y : CartierDual O HO, ψ' y = σ (ψ y)) →
          ψ' = ψ ^ c) :
    ∃ (a : ℕ) (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))),
      Function.Surjective p₀ ∧
      ∃ g₀ : MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] AlgebraicClosure ℚ,
        g₀.comp (p₀ : CartierDual O HO →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) = WithConv.ofConv ψ := by
  classical

  have hcardpow : ∃ a : ℕ, Nat.card ↥(Submonoid.powers ψ) = q ^ a := by
    have hq : 0 < q := (Fact.out : q.Prime).pos

    let ψu : (WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ))ˣ := Units.ofPowEqOne ψ q hψq hq.ne'
    have hψu : (Units.coeHom _ ψu : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ)) = ψ := rfl
    have hinj : Function.Injective (Units.coeHom (WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ))) :=
      fun a b h => Units.ext h
    have h1 : Nat.card ↥(Submonoid.powers ψ) = Nat.card ↥(Submonoid.powers ψu) := by
      rw [← hψu, ← Submonoid.map_powers]
      exact (Nat.card_congr ((Submonoid.powers ψu).equivMapOfInjective _ hinj).toEquiv).symm
    rw [h1, Nat.card_submonoidPowers]
    have hψuq : ψu ^ q = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hψq)
    have hdvd : orderOf ψu ∣ q := orderOf_dvd_of_pow_eq_one hψuq
    rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd _ hdvd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨a, ha⟩ := hcardpow

  have hD : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f ∈ Submonoid.powers ψ, ∀ g : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ),
        (∀ h : CartierDual O HO, g h = σ (f h)) → g = f ^ c := by
    intro σ hσ c hc f hf g hg
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hf
    have hfix : ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x := (hOfix σ).1 hσ
    set τ : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ := liftEquiv σ hfix with hτ

    let Φ : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ) →* WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ) :=
      { toFun := fun x => WithConv.toConv (τ.toAlgHom.comp (WithConv.ofConv x))
        map_one' := by
          refine WithConv.ext (AlgHom.ext fun y => ?_)
          show τ (algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit y)) = algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit y)
          exact τ.commutes _
        map_mul' := fun x x' => by
          refine WithConv.ext ?_
          show τ.toAlgHom.comp (x * x').ofConv = _
          rw [AlgHom.comp_convMul_distrib] }
    have hΦ : ∀ x : WithConv (CartierDual O HO →ₐ[O] AlgebraicClosure ℚ), ∀ y, Φ x y = σ (x y) := fun x y => rfl
    have hg' : g = Φ (ψ ^ k) := WithConv.ext (AlgHom.ext fun y => by rw [hg y]; rfl)
    rw [hg', map_pow, hψcyc σ hσ c hc (Φ ψ) (hΦ ψ), ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨p₀, hp₀, hfac⟩ :=
    HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid q hq2 A O hOA hOdvr hOirr hOfix hOmax
      (CartierDual O HO) (Submonoid.powers ψ) a ha hD
  refine ⟨a, p₀, hp₀, ?_⟩
  exact (hfac (WithConv.ofConv ψ)).2 (Submonoid.mem_powers _)

namespace CartierDual
p2m_export "CartierDual" "toDual ofDual ext one_def one_apply comul_pairing counit_apply"
p2m_open "CartierDual~map~pairing~congr"

theorem toDual_apply' {R : Type} {A : Type} [CommRing R] [CommRing A] [Bialgebra R A] (φ : CartierDual R A) (a : A) :
    CartierDual.toDual R A φ a = φ a := rfl

theorem toDual_ofDual' {R : Type} {A : Type} [CommRing R] [CommRing A] [Bialgebra R A] (x : Module.Dual R A) :
    CartierDual.toDual R A (CartierDual.ofDual R A x) = x :=
  LinearEquiv.apply_symm_apply _ _

theorem ofDual_apply' {R : Type} {A : Type} [CommRing R] [CommRing A] [Bialgebra R A] (x : Module.Dual R A) (a : A) :
    CartierDual.ofDual R A x a = x a := by
  rw [← toDual_apply', toDual_ofDual']

end CartierDual
p2m_reactivate "P2MW.S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant.WAaux"

namespace WAaux

open scoped TensorProduct

variable {O : Type} [CommRing O] {HO : Type} [CommRing HO] [HopfAlgebra O HO] [Module.Finite O HO] [Module.Free O HO]
  [Coalgebra.IsCocomm O HO] {Γ : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ]

def coeffAt (γ : Γ) : MonoidAlgebra O Γ →ₗ[O] O :=
  Finsupp.lapply γ ∘ₗ (MonoidAlgebra.coeffLinearEquiv O).toLinearMap

theorem coeffAt_single (γ γ' : Γ) (c : O) : coeffAt (O := O) γ (MonoidAlgebra.single γ' c) = if γ' = γ then c else 0 := by
  show (MonoidAlgebra.single γ' c).coeff γ = _
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem eq_sum_single_coeffAt (m : MonoidAlgebra O Γ) : m = ∑ γ, MonoidAlgebra.single γ (coeffAt γ m) := by
  calc m = (MonoidAlgebra.coeffLinearEquiv O).symm (∑ γ, Finsupp.single γ (m.coeff γ)) := by
        rw [Finsupp.univ_sum_single]; rfl
    _ = ∑ γ, MonoidAlgebra.single γ (coeffAt γ m) := by rw [map_sum]; rfl

def coeffFun (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) (γ : Γ) : CartierDual O HO →ₗ[O] O :=
  (coeffAt γ) ∘ₗ (p₀ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ).toLinearMap

theorem coeffFun_apply (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) (γ : Γ) (θ : CartierDual O HO) :
    coeffFun p₀ γ θ = coeffAt γ (p₀ θ) := rfl

def coeffElem (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) (γ : Γ) : HO :=
  ∑ i, coeffFun p₀ γ (CartierDual.ofDual O HO ((Module.Free.chooseBasis O HO).coord i)) • (Module.Free.chooseBasis O HO) i

theorem eq_sum_smul_ofDual_coord (θ : CartierDual O HO) :
    θ = ∑ i, θ ((Module.Free.chooseBasis O HO) i) • CartierDual.ofDual O HO ((Module.Free.chooseBasis O HO).coord i) := by
  set b := Module.Free.chooseBasis O HO
  apply (CartierDual.toDual O HO).injective
  rw [map_sum]
  simp_rw [map_smul, CartierDual.toDual_ofDual']
  exact (b.sum_dual_apply_smul_coord ((CartierDual.toDual O HO) θ)).symm

theorem apply_coeffElem (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) (γ : Γ) (θ : CartierDual O HO) :
    θ (coeffElem p₀ γ) = coeffAt γ (p₀ θ) := by
  classical
  set b := Module.Free.chooseBasis O HO with hb
  unfold coeffElem
  rw [map_sum]
  simp_rw [map_smul, smul_eq_mul]
  rw [← coeffFun_apply]
  conv_rhs => rw [eq_sum_smul_ofDual_coord θ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

end WAaux
p2m_reactivate "P2MW.S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant.WAaux"

namespace WAaux

open scoped TensorProduct

variable {O : Type} [CommRing O] {HO : Type} [CommRing HO] [HopfAlgebra O HO] [Module.Finite O HO] [Module.Free O HO]
  [Coalgebra.IsCocomm O HO] {Γ : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ]

theorem eq_zero_of_forall_ofDual_coord (x : HO)
    (hx : ∀ i, CartierDual.ofDual O HO ((Module.Free.chooseBasis O HO).coord i) x = 0) : x = 0 := by
  refine (Module.Free.chooseBasis O HO).forall_coord_eq_zero_iff.1 fun i => ?_
  rw [← CartierDual.ofDual_apply']
  exact hx i

theorem eq_of_forall_cartierDual_apply (x y : HO) (h : ∀ θ : CartierDual O HO, θ x = θ y) : x = y := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_ofDual_coord (O := O) _ fun i => ?_
  rw [map_sub, h, sub_self]

theorem counit_coeffElem (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) (γ : Γ) :
    Coalgebra.counit (R := O) (coeffElem p₀ γ) = if γ = 1 then 1 else 0 := by
  have h := apply_coeffElem p₀ γ (1 : CartierDual O HO)
  rw [map_one, MonoidAlgebra.one_def, coeffAt_single] at h
  rw [CartierDual.one_def, CartierDual.ofDual_apply'] at h
  rw [h]
  by_cases hγ : γ = 1
  · subst hγ; simp
  · rw [if_neg (Ne.symm hγ), if_neg hγ]

omit [DecidableEq Γ] in

theorem counit_eq_sum_coeffAt (m : MonoidAlgebra O Γ) : Coalgebra.counit (R := O) m = ∑ γ, coeffAt γ m := by
  classical
  have hm : m = ∑ γ, MonoidAlgebra.single γ (coeffAt γ m) := eq_sum_single_coeffAt m
  conv_lhs => rw [hm, map_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]

theorem sum_coeffElem (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) : ∑ γ, coeffElem p₀ γ = 1 := by
  refine eq_of_forall_cartierDual_apply (O := O) _ _ fun θ => ?_
  rw [map_sum]
  simp_rw [apply_coeffElem]
  rw [← counit_eq_sum_coeffAt]
  have h := LinearMap.congr_fun (CoalgHomClass.counit_comp (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ)) θ
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  rw [show Coalgebra.counit (R := O) (p₀ θ) = Coalgebra.counit (R := O) θ from h, CartierDual.counit_apply]

theorem mul'_map_coeffAt_comul (α β : Γ) (m : MonoidAlgebra O Γ) :
    LinearMap.mul' O O (TensorProduct.map (coeffAt α) (coeffAt β) (Coalgebra.comul (R := O) m)) =
      if α = β then coeffAt α m else 0 := by
  classical
  have hm : m = ∑ γ, MonoidAlgebra.single γ (coeffAt γ m) := eq_sum_single_coeffAt m
  conv_lhs => rw [hm]
  rw [map_sum, map_sum, map_sum]
  have hterm : ∀ γ : Γ, LinearMap.mul' O O (TensorProduct.map (coeffAt α) (coeffAt β)
      (Coalgebra.comul (R := O) (MonoidAlgebra.single γ (coeffAt γ m)))) =
        if γ = α then (if γ = β then coeffAt γ m else 0) else 0 := by
    intro γ
    rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply]
    change coeffAt α (MonoidAlgebra.single γ (1 : O)) * coeffAt β (MonoidAlgebra.single γ (coeffAt γ m)) = _
    rw [coeffAt_single, coeffAt_single]
    by_cases h1 : γ = α <;> by_cases h2 : γ = β <;> simp [h1, h2]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' Finset.univ α, if_pos (Finset.mem_univ α)]

theorem coeffElem_mul_coeffElem (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) (α β : Γ) :
    coeffElem p₀ α * coeffElem p₀ β = if α = β then coeffElem p₀ α else 0 := by
  refine eq_of_forall_cartierDual_apply (O := O) _ _ fun θ => ?_

  rw [← CartierDual.comul_pairing θ]

  have key : ∀ (Pm : CartierDual O HO →ₗ[O] MonoidAlgebra O Γ), (∀ θ' : CartierDual O HO, Pm θ' = p₀ θ') →
      ∀ t : CartierDual O HO ⊗[O] CartierDual O HO,
      TensorProduct.dualDistrib O HO HO (TensorProduct.map (CartierDual.toDual O HO : CartierDual O HO →ₗ[O] Module.Dual O HO)
        (CartierDual.toDual O HO : CartierDual O HO →ₗ[O] Module.Dual O HO) t) (coeffElem p₀ α ⊗ₜ[O] coeffElem p₀ β) =
      LinearMap.mul' O O (TensorProduct.map (coeffAt α) (coeffAt β) (TensorProduct.map Pm Pm t)) := by
    intro Pm hPm t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul θ₁ θ₂ =>
      simp only [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, LinearMap.mul'_apply, LinearEquiv.coe_coe]
      rw [CartierDual.toDual_apply', CartierDual.toDual_apply', apply_coeffElem, apply_coeffElem, hPm, hPm]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

  have hco : TensorProduct.map p₀.toCoalgHom.toLinearMap
      p₀.toCoalgHom.toLinearMap (Coalgebra.comul (R := O) θ) =
      Coalgebra.comul (R := O) (p₀ θ) := by
    have h := LinearMap.congr_fun p₀.map_comp_comul θ
    first | simpa only [LinearMap.coe_comp, Function.comp_apply] using h | exact h
  rw [key p₀.toCoalgHom.toLinearMap (fun _ => rfl)]
  show LinearMap.mul' O O (TensorProduct.map (coeffAt α) (coeffAt β)
    (TensorProduct.map p₀.toCoalgHom.toLinearMap p₀.toCoalgHom.toLinearMap (Coalgebra.comul (R := O) θ))) = _
  rw [hco, mul'_map_coeffAt_comul]
  by_cases hαβ : α = β
  · subst hαβ
    rw [if_pos rfl, if_pos rfl, apply_coeffElem]
  · rw [if_neg hαβ, if_neg hαβ, map_zero]

end WAaux
p2m_reactivate "P2MW.S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant.WAaux"

namespace WAaux

open scoped TensorProduct

variable {O : Type} [CommRing O] {HO : Type} [CommRing HO] [HopfAlgebra O HO] [Module.Finite O HO] [Module.Free O HO]
  [Coalgebra.IsCocomm O HO] {Γ : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ]
  {L : Type} [CommRing L] [Algebra O L]

theorem dualTensorHomEquiv_symm_eq (f : HO →ₐ[O] L) :
    (dualTensorHomEquiv O HO L).symm f.toLinearMap =
      ∑ i, (Module.Free.chooseBasis O HO).coord i ⊗ₜ[O] f ((Module.Free.chooseBasis O HO) i) := by
  classical
  set b := Module.Free.chooseBasis O HO with hb
  have hw : dualTensorHom O HO L (∑ i, b.coord i ⊗ₜ[O] f (b i)) = f.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    rw [map_sum, LinearMap.sum_apply]
    simp_rw [dualTensorHom_apply]
    conv_rhs => rw [AlgHom.toLinearMap_apply, ← b.sum_repr x, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Module.Basis.coord_apply]
  rw [← hw]
  first
    | exact (dualTensorHomEquiv O HO L).symm_apply_apply _
    | exact dualTensorHomEquivOfBasis_symm_cancel_left (N := L) b _
    | exact dualTensorHomEquivOfBasis_symm_cancel_left b _

theorem algHom_monoidAlgebra_apply (g₀ : MonoidAlgebra O Γ →ₐ[O] L) (m : MonoidAlgebra O Γ) :
    g₀ m = ∑ γ, coeffAt γ m • g₀ (MonoidAlgebra.single γ 1) := by
  classical
  have hm : m = ∑ γ, coeffAt γ m • MonoidAlgebra.single γ (1 : O) := by
    conv_lhs => rw [eq_sum_single_coeffAt (O := O) m]
    refine Finset.sum_congr rfl fun γ _ => ?_
    show MonoidAlgebra.single γ (coeffAt γ m) = (coeffAt γ m) • MonoidAlgebra.single γ (1 : O)
    rw [MonoidAlgebra.smul_single', mul_one]
  conv_lhs => rw [hm, map_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_smul]

theorem pairing_eq_sum (p₀ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ) (g₀ : MonoidAlgebra O Γ →ₐ[O] L) (f : HO →ₐ[O] L) :
    Algebra.TensorProduct.productMap (g₀.comp (p₀ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ)) (AlgHom.id O L)
      ((TensorProduct.congr (CartierDual.ofDual O HO) (LinearEquiv.refl O L))
        ((dualTensorHomEquiv O HO L).symm f.toLinearMap)) =
      ∑ γ, g₀ (MonoidAlgebra.single γ 1) * f (coeffElem p₀ γ) := by
  classical
  rw [dualTensorHomEquiv_symm_eq]

  set Λ₁ : Module.Dual O HO ⊗[O] L →ₗ[O] L :=
    (Algebra.TensorProduct.productMap (g₀.comp (p₀ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ)) (AlgHom.id O L)).toLinearMap ∘ₗ
      (TensorProduct.congr (CartierDual.ofDual O HO) (LinearEquiv.refl O L)).toLinearMap with hΛ₁
  have hΛ₁app : ∀ w : Module.Dual O HO ⊗[O] L,
      Algebra.TensorProduct.productMap (g₀.comp (p₀ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ)) (AlgHom.id O L)
        ((TensorProduct.congr (CartierDual.ofDual O HO) (LinearEquiv.refl O L)) w) = Λ₁ w := fun w => rfl
  have hΛ₁t : ∀ (θ : Module.Dual O HO) (l : L), Λ₁ (θ ⊗ₜ[O] l) = g₀ (p₀ (CartierDual.ofDual O HO θ)) * l := by
    intro θ l
    show Algebra.TensorProduct.productMap (g₀.comp (p₀ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ)) (AlgHom.id O L)
      ((TensorProduct.congr (CartierDual.ofDual O HO) (LinearEquiv.refl O L)) (θ ⊗ₜ[O] l)) = _
    rw [TensorProduct.congr_tmul]
    erw [Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  rw [hΛ₁app, map_sum]
  simp_rw [hΛ₁t]

  have hexp : ∀ i, g₀ (p₀ (CartierDual.ofDual O HO ((Module.Free.chooseBasis O HO).coord i))) =
      ∑ γ, coeffFun p₀ γ (CartierDual.ofDual O HO ((Module.Free.chooseBasis O HO).coord i)) •
        g₀ (MonoidAlgebra.single γ 1) := fun i => by
    rw [algHom_monoidAlgebra_apply]
    rfl
  simp_rw [hexp, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_

  unfold coeffElem
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_mul_assoc, mul_smul_comm]

end WAaux
p2m_reactivate "P2MW.S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant.WAaux"

open WAaux in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)] [FaithfulSMul O (AlgebraicClosure ℚ)]
    (hOA : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (hOfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ (algebraMap O (AlgebraicClosure ℚ) x) = algebraMap O (AlgebraicClosure ℚ) x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : O, algebraMap O (AlgebraicClosure ℚ) x = y)
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
    (hHOq : ∀ f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ), f ^ q = 1)
    (φ : WithConv (HO →ₐ[O] AlgebraicClosure ℚ) →* AlgebraicClosure ℚ)
    (hφ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (HO →ₐ[O] AlgebraicClosure ℚ),
      (∀ h : HO, g h = σ (f h)) → φ g = φ f)
    (f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ))
    (hf : ∀ h : HO, A.valuation (f h - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) :
    φ f = 1 := by
  classical
  obtain ⟨hfree, e, ψ, he, hψφ, hψq, hψcyc⟩ :=
    WA_exists_dualPoint q hq2 A O hOA hOdvr hOirr hOfix hOmax HO hHOq φ hφ
  haveI : Module.Free O HO := hfree
  obtain ⟨a, p₀, hp₀, g₀, hg₀⟩ := WA_exists_constQuot q hq2 A O hOA hOdvr hOirr hOfix hOmax HO e ψ hψq hψcyc

  have hpair : φ f = ∑ γ, g₀ (MonoidAlgebra.single γ 1) * (WithConv.ofConv f) (coeffElem p₀ γ) := by
    rw [← hψφ f, he ψ f]
    have hψ' : WithConv.ofConv ψ = g₀.comp (p₀ : CartierDual O HO →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) :=
      hg₀.symm
    rw [hψ']
    exact pairing_eq_sum p₀ g₀ (WithConv.ofConv f)
  rw [hpair]

  set x : HO →ₐ[O] AlgebraicClosure ℚ := WithConv.ofConv f with hx
  have hidem : ∀ γ, x (coeffElem p₀ γ) * x (coeffElem p₀ γ) = x (coeffElem p₀ γ) := fun γ => by
    rw [← map_mul, coeffElem_mul_coeffElem, if_pos rfl]
  have horth : ∀ γ γ', γ ≠ γ' → x (coeffElem p₀ γ) * x (coeffElem p₀ γ') = 0 := fun γ γ' h => by
    rw [← map_mul, coeffElem_mul_coeffElem, if_neg h, map_zero]

  have h1 : x (coeffElem p₀ 1) = 1 := by
    have hv := hf (coeffElem p₀ 1)
    rw [counit_coeffElem, if_pos rfl, map_one] at hv

    rcases mul_left_eq_self₀.mp (hidem 1) with h1' | h0
    · exact h1'
    · exfalso
      rw [show (f : WithConv (HO →ₐ[O] AlgebraicClosure ℚ)) (coeffElem p₀ 1) = x (coeffElem p₀ 1) from rfl, h0, zero_sub,
        Valuation.map_neg, Valuation.map_one] at hv
      exact lt_irrefl _ hv

  have h0 : ∀ γ, γ ≠ 1 → x (coeffElem p₀ γ) = 0 := fun γ hγ => by
    have := horth γ 1 hγ
    rwa [h1, mul_one] at this
  rw [Finset.sum_eq_single (1 : Multiplicative (Fin a → ZMod q))]
  · rw [show (WithConv.ofConv f) (coeffElem p₀ 1) = x (coeffElem p₀ 1) from rfl, h1, mul_one,
      ← MonoidAlgebra.one_def, map_one]
  · intro γ _ hγ
    rw [show (WithConv.ofConv f) (coeffElem p₀ γ) = x (coeffElem p₀ γ) from rfl, h0 γ hγ, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end
end S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant
end P2MW
export P2MW.S_HopfAlgebra_eq_one_of_forall_valuation_sub_counit_lt_one_of_inertiaInvariant (solution)
