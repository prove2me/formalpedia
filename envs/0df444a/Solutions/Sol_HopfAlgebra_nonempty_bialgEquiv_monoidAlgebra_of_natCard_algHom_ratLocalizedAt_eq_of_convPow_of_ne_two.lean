-- Prove2me | solution 1 for HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0c404240-b04c-5d53-80b8-922752ac9aee

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
import Theorems.Thm_GaloisRep_cartierDual_points_of_galoisCyclotomic
import Theorems.Thm_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct
open WithConv

namespace LOCQ

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem nonempty_bialgEquiv_monoidAlgebra_of_bijective (S : Type*) [CommRing S]
    {G G' : Type*} [Monoid G] [Monoid G'] (f : G →* G') (hf : Function.Bijective f) :
    Nonempty (MonoidAlgebra S G ≃ₐc[S] MonoidAlgebra S G') := by
  refine ⟨BialgEquiv.ofBijective (MonoidAlgebra.mapDomainBialgHom S f) ?_⟩
  have hcoe : ∀ x : MonoidAlgebra S G,
      MonoidAlgebra.mapDomainBialgHom S f x = MonoidAlgebra.mapDomain f x := fun x => rfl
  constructor
  · intro x y hxy
    rw [hcoe, hcoe] at hxy
    exact MonoidAlgebra.mapDomain_injective hf.1 hxy
  · intro y
    obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf.2 y.coeff
    refine ⟨.ofCoeff x, MonoidAlgebra.coeff_injective ?_⟩
    rw [hcoe]
    exact hx

theorem isUnit_toConv {S A B : Type*} [CommRing S] [CommRing A] [HopfAlgebra S A]
    [CommRing B] [Algebra S B] (f : A →ₐ[S] B) : IsUnit (toConv f) := by
  let Salg : A →ₐ[S] A := AlgHom.ofLinearMap (HopfAlgebra.antipode S) HopfAlgebra.antipode_one
      (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])
  have hSalg : ∀ a, Salg a = HopfAlgebra.antipode S a := fun a => rfl
  rw [isUnit_iff_exists]
  refine ⟨toConv (f.comp Salg), ?_, ?_⟩
  · refine WithConv.ext (AlgHom.ext fun c => ?_)
    show (toConv f * toConv (f.comp Salg)) c = (1 : WithConv (A →ₐ[S] B)) c
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift f (f.comp Salg) (fun _ _ => Commute.all _ _)).toLinearMap =
        f.toLinearMap ∘ₗ LinearMap.mul' S A ∘ₗ (HopfAlgebra.antipode S (A := A)).lTensor A := by
      refine TensorProduct.ext' fun x y => ?_
      simp [hSalg]
    have happ := congrArg (fun g : A ⊗[S] A →ₗ[S] B => g (Coalgebra.comul (R := S) c)) key
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at happ
    simp only [ofConv_toConv] at happ ⊢
    rw [happ, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]
  · refine WithConv.ext (AlgHom.ext fun c => ?_)
    show (toConv (f.comp Salg) * toConv f) c = (1 : WithConv (A →ₐ[S] B)) c
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift (f.comp Salg) f (fun _ _ => Commute.all _ _)).toLinearMap =
        f.toLinearMap ∘ₗ LinearMap.mul' S A ∘ₗ (HopfAlgebra.antipode S (A := A)).rTensor A := by
      refine TensorProduct.ext' fun x y => ?_
      simp [hSalg]
    have happ := congrArg (fun g : A ⊗[S] A →ₗ[S] B => g (Coalgebra.comul (R := S) c)) key
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at happ
    simp only [ofConv_toConv] at happ ⊢
    rw [happ, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

local notation "Pts[" q ", " H "]" =>
  WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)

theorem main
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    (hgenq : Nat.card (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) = q)
    (hgal : ∀ (σ : ℚ̄ ≃+* ℚ̄) (nσ : ℕ),
      (∀ ζ : ℚ̄, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) (h : H),
        σ (ψ h) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) h) :
    Nonempty (H ≃ₐc[GaloisRep.ratLocalizedAt q]
      MonoidAlgebra (GaloisRep.ratLocalizedAt q) (Multiplicative (ZMod q))) := by
  classical
  have hq : q.Prime := Fact.out
  have hq0 : q ≠ 0 := hq.ne_zero
  haveI : NeZero q := ⟨hq0⟩
  haveI : IsPrincipalIdealRing (GaloisRep.ratLocalizedAt q) :=
    GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
  haveI : Module.Free (GaloisRep.ratLocalizedAt q) H := inferInstance
  have hinj : Function.Injective (algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄) := by
    intro a b h
    have : ((a : ℚ) : ℚ̄) = ((b : ℚ) : ℚ̄) := h
    exact Subtype.ext (by exact_mod_cast this)

  have hunit : ∀ f : Pts[q, H], IsUnit f := fun f => isUnit_toConv f.ofConv
  letI instGrp : Group Pts[q, H] := groupOfIsUnit hunit
  have hcardP : Nat.card Pts[q, H] = q := by
    rw [Nat.card_congr (WithConv.equiv _), hgenq]
  haveI : Finite Pts[q, H] := Nat.finite_of_card_ne_zero (by rw [hcardP]; exact hq0)
  haveI hcycP : IsCyclic Pts[q, H] := isCyclic_of_prime_card hcardP
  letI instCG : CommGroup Pts[q, H] := IsCyclic.commGroup

  letI instSMul : SMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Additive Pts[q, H]) :=
    ⟨fun σ x => Additive.ofMul (toConv
      ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q)).comp (Additive.toMul x).ofConv))⟩
  have smul_def : ∀ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : Additive Pts[q, H]), σ • x = Additive.ofMul (toConv
      ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q)).comp (Additive.toMul x).ofConv)) :=
    fun _ _ => rfl
  letI instDMA : DistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Additive Pts[q, H]) :=
    { one_smul := fun x => by
        apply Additive.toMul.injective
        exact WithConv.ext (AlgHom.ext fun h => rfl)
      mul_smul := fun σ τ x => by
        apply Additive.toMul.injective
        exact WithConv.ext (AlgHom.ext fun h => rfl)
      smul_zero := fun σ => by
        apply Additive.toMul.injective
        refine WithConv.ext (AlgHom.ext fun h => ?_)
        change (σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q))
            (algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ (Coalgebra.counit h)) =
          algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ (Coalgebra.counit h)
        exact AlgHom.commutes _ _
      smul_add := fun σ x y => by
        apply Additive.toMul.injective
        change toConv ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q)).comp
            (Additive.toMul x * Additive.toMul y).ofConv) =
          toConv ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q)).comp
            (Additive.toMul x).ofConv) *
          toConv ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q)).comp
            (Additive.toMul y).ofConv)
        rw [AlgHom.comp_convMul_distrib] }
  have he_act : ∀ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (f g : Pts[q, H]),
      (∀ x : H, g x = σ (f x)) → Additive.ofMul g = σ • Additive.ofMul f := by
    intro σ f g hfg
    apply Additive.toMul.injective
    exact WithConv.ext (AlgHom.ext fun x => hfg x)

  have hcocomm : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H := by
    haveI : IsReduced (ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) :=
      HopfAlgebra.isReduced_of_finiteType_of_charZero ℚ̄ _
    exact HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv
      (GaloisRep.ratLocalizedAt q) ℚ̄ hinj H (N := Additive Pts[q, H]) Additive.ofMul (fun _ _ => rfl)
  haveI := hcocomm

  have hrank : Module.finrank (GaloisRep.ratLocalizedAt q) H = q := by
    obtain ⟨L, hL⟩ : ∃ L : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[ℚ̄] (Pts[q, H] → ℚ̄),
        Function.Bijective L := ⟨_, GaloisRep.bijective_lift_pi_algHom_of_finiteFlatHopf q H⟩
    haveI : Fintype Pts[q, H] := Fintype.ofFinite _
    have e := LinearEquiv.ofBijective L.toLinearMap hL
    have h1 := e.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card] at h1
    rw [h1, ← Nat.card_eq_fintype_card, hcardP]

  let n : (ℚ̄ ≃ₐ[ℚ] ℚ̄) → ℕ := fun σ => (modularCyclotomicCharacter.toFun q (σ : ℚ̄ ≃+* ℚ̄)).val
  have hn1 : ∀ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (ζ : ℚ̄), ζ ^ q = 1 → σ ζ = ζ ^ n σ := by
    intro σ ζ hζ
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp [zero_pow hq0] at hζ
    set t : ℚ̄ˣ := Units.mk0 ζ hζ0 with ht
    have htmem : t ∈ rootsOfUnity q ℚ̄ := by
      rw [mem_rootsOfUnity]; ext; simp [ht, hζ]
    have := modularCyclotomicCharacter.toFun_spec' (σ : ℚ̄ ≃+* ℚ̄) htmem
    simpa [ht, Units.val_pow_eq_pow_val] using this
  have hn : ∀ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (ζ : ℚ̄), ζ ^ q ^ 1 = 1 → σ ζ = ζ ^ n σ := by
    intro σ ζ hζ; rw [pow_one] at hζ; exact hn1 σ ζ hζ
  have hcyc : ∀ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (m : Additive Pts[q, H]), σ • m = n σ • m := by
    intro σ m
    apply Additive.toMul.injective
    change toConv ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt q)).comp
      (Additive.toMul m).ofConv) = (Additive.toMul m) ^ n σ
    refine WithConv.ext (AlgHom.ext fun h => ?_)
    have := hgal (σ : ℚ̄ ≃+* ℚ̄) (n σ) (fun ζ hζ => hn1 σ ζ hζ) (Additive.toMul m).ofConv h
    simpa using this
  have htors : ∀ m : Additive Pts[q, H], q ^ 1 • m = 0 := by
    intro m
    rw [pow_one]
    apply Additive.toMul.injective
    change (Additive.toMul m) ^ q = 1
    have := pow_card_eq_one' (G := Pts[q, H]) (x := Additive.toMul m)
    rwa [hcardP] at this
  have hcard : Nat.card (Additive Pts[q, H]) = Module.finrank (GaloisRep.ratLocalizedAt q) H := by
    rw [hrank]; exact hcardP

  obtain ⟨φ, -⟩ :=
    GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic q hq2 H
      (M := Additive Pts[q, H]) Additive.ofMul (fun _ _ => rfl) he_act 1 htors n hn hcyc hcard
  obtain ⟨-, hpow', hcard'⟩ :=
    GaloisRep.cartierDual_points_of_galoisCyclotomic q H
      (M := Additive Pts[q, H]) Additive.ofMul (fun _ _ => rfl) he_act 1 htors n hn hcyc hcard

  have hunit' : ∀ ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄),
      IsUnit ψ := fun ψ => IsUnit.of_pow_eq_one (hpow' ψ) (pow_ne_zero 1 hq0)
  letI instGrp' : Group (WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :=
    groupOfIsUnit hunit'
  have hcardP' : Nat.card (WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) = q :=
    hcard'.trans hrank
  have hcardZ : Nat.card (Multiplicative (ZMod q)) = q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let eG := mulEquivOfPrimeCardEq (p := q) hcardP' hcardZ
  obtain ⟨ε⟩ := nonempty_bialgEquiv_monoidAlgebra_of_bijective (GaloisRep.ratLocalizedAt q)
    eG.toMonoidHom eG.bijective
  exact ⟨φ.trans ε⟩

end LOCQ

open LOCQ in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    (hgenq : Nat.card (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) (h : H),
        σ (ψ h) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) h) :
    Nonempty (H ≃ₐc[GaloisRep.ratLocalizedAt q]
      MonoidAlgebra (GaloisRep.ratLocalizedAt q) (Multiplicative (ZMod q))) :=
  LOCQ.main q hq2 H hgenq hgal

end S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two (solution)
