-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3138307b-a022-535c-9c7d-89aaf1a03dff

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open Polynomial ModularCurve ModularCurve.HpoolLevelRing
open scoped TensorProduct

namespace FibreIdUni

section KA
variable (k : Type) [Field k] (A : Type) [CommRing A]

def KA : Type := k ⊗[ℤ] A

noncomputable scoped instance KA.instCommRing : CommRing (KA k A) := inferInstanceAs (CommRing (k ⊗[ℤ] A))
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient.FibreIdUni.KA"
noncomputable scoped instance KA.instAlgebra : Algebra k (KA k A) := inferInstanceAs (Algebra k (k ⊗[ℤ] A))

p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient.FibreIdUni.KA"

noncomputable def KA.equiv : KA k A ≃ₐ[k] (k ⊗[ℤ] A) := AlgEquiv.refl

noncomputable def KA.ι : A →+* KA k A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] (k ⊗[ℤ] A)).toRingHom

theorem KA.equiv_ι (a : A) : KA.equiv k A (KA.ι k A a) = (1 : k) ⊗ₜ[ℤ] a := rfl

variable {k A}
variable {C : Type} [CommRing C] [Algebra k C]

noncomputable def KA.lift (g : A →+* C) : KA k A →ₐ[k] C :=
  (Algebra.TensorProduct.lift (R := ℤ) (S := k) (A := k) (B := A) (C := C) (Algebra.ofId k C) g.toIntAlgHom
    (fun _ _ => Commute.all _ _)).comp (KA.equiv k A).toAlgHom

theorem KA.lift_ι (g : A →+* C) (a : A) : KA.lift g (KA.ι k A a) = g a := by
  change Algebra.TensorProduct.lift (R := ℤ) (S := k) (A := k) (B := A) (C := C) (Algebra.ofId k C) g.toIntAlgHom
    (fun _ _ => Commute.all _ _) ((1 : k) ⊗ₜ[ℤ] a) = g a
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

theorem KA.algHom_ext {φ ψ : KA k A →ₐ[k] C} (h : ∀ a, φ (KA.ι k A a) = ψ (KA.ι k A a)) : φ = ψ := by
  have : φ.comp (KA.equiv k A).symm.toAlgHom = ψ.comp (KA.equiv k A).symm.toAlgHom := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext a
      exact h a
  ext x
  have := congrArg (fun χ => χ (KA.equiv k A x)) this
  simpa using this

end KA
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient.FibreIdUni.KA"

section Main

variable (A : Type) [CommRing A] (f : ℤ) (K : Type) [CommRing K] [Algebra (Localization.Away f) K]
  (k : Type) [Field k] [Algebra k K]

local notation "Rf" => Localization.Away f
local notation "Af" => Localization.Away (algebraMap ℤ A f)
local notation "T₂" => K ⊗[k] KA k A
local notation "T₁" => K ⊗[Rf] Af

noncomputable scoped instance algebraRAf : Algebra Rf Af := (Localization.awayMap (algebraMap ℤ A) f).toAlgebra

theorem isUnit_algebraMap_f : IsUnit (algebraMap ℤ Rf f) := IsLocalization.Away.algebraMap_isUnit f

noncomputable scoped instance algebraRT2 : Algebra Rf T₂ :=
  Algebra.ofModule
    (fun r x y => by rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (x * y), smul_mul_assoc])
    (fun r x y => by rw [← IsScalarTower.algebraMap_smul K r y, ← IsScalarTower.algebraMap_smul K r (x * y), mul_smul_comm])

theorem algebraMap_R_T2 (r : Rf) : algebraMap Rf T₂ r = algebraMap K T₂ (algebraMap Rf K r) :=
  calc algebraMap Rf T₂ r = r • (1 : T₂) := rfl
    _ = algebraMap Rf K r • (1 : T₂) := (IsScalarTower.algebraMap_smul K r (1 : T₂)).symm
    _ = algebraMap K T₂ (algebraMap Rf K r) := (Algebra.algebraMap_eq_smul_one _).symm

noncomputable scoped instance algebrakT1 : Algebra k T₁ :=
  Algebra.ofModule
    (fun r x y => by rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (x * y), smul_mul_assoc])
    (fun r x y => by rw [← IsScalarTower.algebraMap_smul K r y, ← IsScalarTower.algebraMap_smul K r (x * y), mul_smul_comm])

theorem algebraMap_k_T1 (c : k) : algebraMap k T₁ c = algebraMap K T₁ (algebraMap k K c) :=
  calc algebraMap k T₁ c = c • (1 : T₁) := rfl
    _ = algebraMap k K c • (1 : T₁) := (IsScalarTower.algebraMap_smul K c (1 : T₁)).symm
    _ = algebraMap K T₁ (algebraMap k K c) := (Algebra.algebraMap_eq_smul_one _).symm

noncomputable def legA2 : A →+* T₂ :=
  (Algebra.TensorProduct.includeRight : KA k A →ₐ[k] T₂).toRingHom.comp (KA.ι k A)

theorem legA2_apply (a : A) : legA2 A K k a = (1 : K) ⊗ₜ[k] (KA.ι k A a) := rfl

theorem isUnit_legA2_f : IsUnit (legA2 A K k (algebraMap ℤ A f)) := by
  have h := (isUnit_algebraMap_f f).map ((algebraMap K T₂).comp (algebraMap Rf K))
  have e : (legA2 A K k).comp (algebraMap ℤ A) = ((algebraMap K T₂).comp (algebraMap Rf K)).comp (algebraMap ℤ Rf) :=
    Subsingleton.elim _ _
  have e' := RingHom.congr_fun e f
  rw [RingHom.comp_apply, RingHom.comp_apply] at e'
  rw [e']
  exact h

noncomputable def legAf2 : Af →+* T₂ :=
  IsLocalization.Away.lift (S := Af) (algebraMap ℤ A f) (g := legA2 A K k) (isUnit_legA2_f A f K k)

theorem legAf2_algebraMap (a : A) : legAf2 A f K k (algebraMap A Af a) = legA2 A K k a :=
  IsLocalization.Away.lift_eq (S := Af) (algebraMap ℤ A f) (g := legA2 A K k) (isUnit_legA2_f A f K k) a

theorem legAf2_comp_algebraMap_R : (legAf2 A f K k).comp (algebraMap Rf Af) = algebraMap Rf T₂ :=
  IsLocalization.ringHom_ext (Submonoid.powers f) (Subsingleton.elim _ _)

noncomputable def legAf2ₐ : Af →ₐ[Rf] T₂ :=
  { legAf2 A f K k with commutes' := fun r => RingHom.congr_fun (legAf2_comp_algebraMap_R A f K k) r }

theorem legAf2ₐ_apply (y : Af) : legAf2ₐ A f K k y = legAf2 A f K k y := rfl

noncomputable def phi : T₁ →ₐ[K] T₂ :=
  Algebra.TensorProduct.lift (R := Rf) (S := K) (A := K) (B := Af) (C := T₂) (Algebra.ofId K T₂) (legAf2ₐ A f K k)
    (fun _ _ => Commute.all _ _)

theorem phi_tmul (x : K) (y : Af) : phi A f K k (x ⊗ₜ[Rf] y) = algebraMap K T₂ x * legAf2 A f K k y := by
  simp only [phi, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, legAf2ₐ_apply]

noncomputable def legA1 : A →+* T₁ :=
  (Algebra.TensorProduct.includeRight : Af →ₐ[Rf] T₁).toRingHom.comp (algebraMap A Af)

theorem legA1_apply (a : A) : legA1 A f K a = (1 : K) ⊗ₜ[Rf] (algebraMap A Af a) := rfl

noncomputable def legkA1 : KA k A →ₐ[k] T₁ := KA.lift (legA1 A f K)

theorem legkA1_ι (a : A) : legkA1 A f K k (KA.ι k A a) = (1 : K) ⊗ₜ[Rf] (algebraMap A Af a) :=
  KA.lift_ι _ a

noncomputable def psi : T₂ →ₐ[K] T₁ :=
  Algebra.TensorProduct.lift (R := k) (S := K) (A := K) (B := KA k A) (C := T₁) (Algebra.ofId K T₁) (legkA1 A f K k)
    (fun _ _ => Commute.all _ _)

theorem psi_tmul (x : K) (z : KA k A) : psi A f K k (x ⊗ₜ[k] z) = algebraMap K T₁ x * legkA1 A f K k z := by
  simp only [psi, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem psi_phi_tmul (x : K) (a : A) :
    psi A f K k (phi A f K k (x ⊗ₜ[Rf] algebraMap A Af a)) = x ⊗ₜ[Rf] algebraMap A Af a := by
  rw [phi_tmul, legAf2_algebraMap, legA2_apply, map_mul, AlgHom.commutes, psi_tmul, map_one, one_mul, legkA1_ι,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

theorem phi_psi_tmul (x : K) (a : A) :
    phi A f K k (psi A f K k (x ⊗ₜ[k] KA.ι k A a)) = x ⊗ₜ[k] KA.ι k A a := by
  rw [psi_tmul, legkA1_ι, map_mul, AlgHom.commutes, phi_tmul, map_one, one_mul, legAf2_algebraMap, legA2_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

theorem psi_comp_phi : (psi A f K k).comp (phi A f K k) = AlgHom.id K T₁ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply AlgHom.coe_ringHom_injective
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap ℤ A f)) ?_
    ext a
    change psi A f K k (phi A f K k ((1 : K) ⊗ₜ[Rf] algebraMap A Af a)) = (1 : K) ⊗ₜ[Rf] algebraMap A Af a
    exact psi_phi_tmul A f K k 1 a

theorem phi_comp_psi : (phi A f K k).comp (psi A f K k) = AlgHom.id K T₂ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply KA.algHom_ext
    intro a
    change phi A f K k (psi A f K k ((1 : K) ⊗ₜ[k] KA.ι k A a)) = (1 : K) ⊗ₜ[k] KA.ι k A a
    exact phi_psi_tmul A f K k 1 a

noncomputable def e0 : T₁ ≃ₐ[K] T₂ :=
  AlgEquiv.ofAlgHom (phi A f K k) (psi A f K k) (phi_comp_psi A f K k) (psi_comp_phi A f K k)

theorem e0_apply (y : T₁) : e0 A f K k y = phi A f K k y := rfl

theorem e0_symm_apply (z : T₂) : (e0 A f K k).symm z = psi A f K k z := rfl

theorem e0_tmul_algebraMap (x : K) (a : A) : e0 A f K k (x ⊗ₜ[Rf] algebraMap A Af a) = x ⊗ₜ[k] KA.ι k A a := by
  rw [e0_apply, phi_tmul, legAf2_algebraMap, legA2_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

variable (u : A) (g : Polynomial ℤ)

local notation "J" => (Ideal.span {Polynomial.aeval (algebraMap A Af u) g} : Ideal Af)
local notation "Lv" => Af ⧸ J

local notation "Iq" => (Ideal.span {KA.ι k A (Polynomial.aeval u g)} : Ideal (KA k A))
local notation "Q" => KA k A ⧸ Iq

noncomputable def e : K ⊗[Rf] Lv ≃ₐ[K] K ⊗[k] Q :=

  (Algebra.TensorProduct.tensorQuotientEquiv (R := Rf) K Af K J).trans <|

  (Ideal.quotientEquivAlg ((J).map (Algebra.TensorProduct.includeRight : Af →ₐ[Rf] T₁))
      ((Iq).map (Algebra.TensorProduct.includeRight : KA k A →ₐ[k] T₂)) (e0 A f K k) (by
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 1
    rw [Set.singleton_eq_singleton_iff]
    change (1 : K) ⊗ₜ[k] KA.ι k A (Polynomial.aeval u g) = e0 A f K k ((1 : K) ⊗ₜ[Rf] Polynomial.aeval (algebraMap A Af u) g)
    rw [Polynomial.aeval_algebraMap_apply Af u g, e0_tmul_algebraMap])).trans <|

  (Algebra.TensorProduct.tensorQuotientEquiv (R := k) K (KA k A) K Iq).symm

theorem transfers [Nontrivial K] :
    (Algebra.Etale k Q → Algebra.Etale K (K ⊗[Rf] Lv)) ∧
      Module.finrank K (K ⊗[Rf] Lv) = Module.finrank k Q := by
  refine ⟨fun hQ => ?_, ?_⟩
  · haveI := hQ
    haveI : Algebra.Etale K (K ⊗[k] Q) := inferInstance
    exact Algebra.Etale.of_equiv (e A f K k u g).symm
  · rw [LinearEquiv.finrank_eq (e A f K k u g).toLinearEquiv, Module.finrank_baseChange]

theorem transfers' [Nontrivial K] :
    (Algebra.Etale k ((k ⊗[ℤ] A) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] Polynomial.aeval u g}) → Algebra.Etale K (K ⊗[Rf] Lv)) ∧
      Module.finrank K (K ⊗[Rf] Lv) = Module.finrank k ((k ⊗[ℤ] A) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] Polynomial.aeval u g}) :=
  transfers A f K k u g

end Main
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient.FibreIdUni.KA"

end FibreIdUni
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient.FibreIdUni.KA P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient.FibreIdUni"

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (f : ℤ) (u : Afin p) (g : ℤ[X])
    (P : Ideal (Localization.Away f)) [P.IsPrime]
    (k : Type) [Field k] [Algebra k P.ResidueField] :
    (Algebra.Etale k ((k ⊗[ℤ] Afin p) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] Polynomial.aeval u g}) →
        Algebra.Etale P.ResidueField (P.Fiber (levelRing p f u g))) ∧
    Module.finrank P.ResidueField (P.Fiber (levelRing p f u g)) =
      Module.finrank k ((k ⊗[ℤ] Afin p) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] Polynomial.aeval u g}) := by
  exact FibreIdUni.transfers' (Afin p) f P.ResidueField k u g

end S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_etale_fiber_levelRing_and_finrank_eq_of_tensorProduct_quotient (solution)
