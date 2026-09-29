-- Prove2me | solution 1 for HopfAlgebra.exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/42bb77de-ff91-5542-830a-9d7c82e96d3f

import Mathlib
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Definitions.Def_HopfAlgebra_HopfTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u

section LocalFactor

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

namespace HopfAlgebra p2m_export "HopfAlgebra" "mk counit_antipode antipodeAlgHom antipodeAlgHom_apply convMul_comp_antipodeAlgHom quotientBialgHom quotientBialgHom_surjective HopfTower.antipodeAlgHom HopfTower.convMul_comp_antipodeAlgHom HopfTower.translate HopfTower.counit_translate HopfTower.translateEquiv HopfTower.comp_translate" end HopfAlgebra
p2m_open_scoped "HopfAlgebra" in

def HopfAlgebra.pointKerIdealHOMOG (f : B →ₐ[k] k) : Ideal B where
  carrier := {x | ∃ s : B, f s ≠ 0 ∧ s * x = 0}
  add_mem' := by
    rintro x y ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩
    refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [mul_add, mul_assoc, mul_comm t x, ← mul_assoc, hsx, zero_mul, zero_add, mul_assoc, hty, mul_zero]
  zero_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, mul_zero 1⟩
  smul_mem' := by
    rintro c x ⟨s, hs, hsx⟩
    exact ⟨s, hs, by rw [smul_eq_mul, mul_left_comm, hsx, mul_zero]⟩

p2m_open_scoped "HopfAlgebra" in
theorem HopfAlgebra.mem_pointKerIdealHOMOG_iff (f : B →ₐ[k] k) (x : B) :
    x ∈ HopfAlgebra.pointKerIdealHOMOG f ↔ ∃ s : B, f s ≠ 0 ∧ s * x = 0 := Iff.rfl

p2m_open_scoped "HopfAlgebra" in
theorem HopfAlgebra.pointKerIdealHOMOG_le_ker (f : B →ₐ[k] k) :
    HopfAlgebra.pointKerIdealHOMOG f ≤ RingHom.ker f := by
  rintro x ⟨s, hs, hsx⟩
  rw [RingHom.mem_ker]
  have h := congrArg f hsx
  rw [map_mul, map_zero] at h
  exact (mul_eq_zero.1 h).resolve_left hs

p2m_open_scoped "HopfAlgebra" in

theorem HopfAlgebra.pointKerIdealHOMOG_eq_ker_algebraMap (f : B →ₐ[k] k) (𝔭 : Ideal B) [𝔭.IsPrime]
    (h𝔭 : RingHom.ker f = 𝔭) :
    HopfAlgebra.pointKerIdealHOMOG f = RingHom.ker (algebraMap B (Localization.AtPrime 𝔭)) := by
  ext x
  rw [HopfAlgebra.mem_pointKerIdealHOMOG_iff, RingHom.mem_ker, IsLocalization.map_eq_zero_iff 𝔭.primeCompl]
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨⟨s, show s ∉ 𝔭 from fun h => hs ?_⟩, hsx⟩
    rw [← h𝔭] at h
    exact h
  · rintro ⟨⟨s, hs⟩, hsx⟩
    refine ⟨s, fun h => hs ?_, hsx⟩
    rw [← h𝔭]
    exact h

end LocalFactor

section TensorLocal

variable {k : Type u} [Field k] {C : Type u} [CommRing C] [Algebra k C]

namespace Algebra p2m_export "Algebra" "ofId commutes TensorProduct.includeRight TensorProduct.tmul_mul_tmul TensorProduct.lift_tmul mk algebraMap TensorProduct.lift TensorProduct.map_tmul TensorProduct.algebraMap_apply algebraMap_self TensorProduct.ext' TensorProduct.includeLeft id mem_bot restrictScalars TensorProduct.map TensorProduct.algebraMap_apply'" end Algebra
p2m_open_scoped "Algebra" in

theorem Algebra.isUnit_tensorProduct_of_lift_ne_zero_HOMOG [Module.Finite k C] [IsLocalRing C]
    (f : C →ₐ[k] k) (z : C ⊗[k] C)
    (hz : Algebra.TensorProduct.lift f f (fun _ _ => Commute.all _ _) z ≠ 0) : IsUnit z := by
  classical
  haveI : IsArtinianRing C := IsArtinianRing.of_finite k C

  have hsurj : Function.Surjective f := fun c => ⟨algebraMap k C c, f.commutes c⟩
  have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hker : RingHom.ker f = IsLocalRing.maximalIdeal C := IsLocalRing.eq_maximalIdeal hmax
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal C) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal C) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hxnil : ∀ x : C, f x = 0 → IsNilpotent x := by
    intro x hx
    obtain ⟨n, hn⟩ := hnil
    have hxm : x ∈ IsLocalRing.maximalIdeal C := by rw [← hker, RingHom.mem_ker]; exact hx
    refine ⟨n, ?_⟩
    have h1 : x ^ n ∈ (IsLocalRing.maximalIdeal C) ^ n := Ideal.pow_mem_pow hxm n
    rw [hn] at h1
    exact (Submodule.mem_bot C).1 h1
  let φ : C ⊗[k] C →ₐ[k] k := Algebra.TensorProduct.lift f f (fun _ _ => Commute.all _ _)
  have hφ : ∀ a b : C, φ (a ⊗ₜ[k] b) = f a * f b := fun a b => Algebra.TensorProduct.lift_tmul _ _ _ a b

  have hdec : ∀ w : C ⊗[k] C, IsNilpotent (w - algebraMap k (C ⊗[k] C) (φ w)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, sub_zero]; exact IsNilpotent.zero
    | tmul a b =>
      have ha : IsNilpotent (a - algebraMap k C (f a)) :=
        hxnil _ (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
      have hb : IsNilpotent (b - algebraMap k C (f b)) :=
        hxnil _ (by rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
      have hA : IsNilpotent (a ⊗ₜ[k] (1 : C) - algebraMap k (C ⊗[k] C) (f a)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, ← TensorProduct.sub_tmul]
        exact ha.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := C) (B := C))
      have hB : IsNilpotent ((1 : C) ⊗ₜ[k] b - algebraMap k (C ⊗[k] C) (f b)) := by
        rw [Algebra.TensorProduct.algebraMap_apply', ← TensorProduct.tmul_sub]
        exact hb.map (Algebra.TensorProduct.includeRight (R := k) (A := C) (B := C))
      have h1 : a ⊗ₜ[k] b - algebraMap k (C ⊗[k] C) (φ (a ⊗ₜ[k] b)) =
          (a ⊗ₜ[k] (1 : C) - algebraMap k (C ⊗[k] C) (f a)) * ((1 : C) ⊗ₜ[k] b) +
            algebraMap k (C ⊗[k] C) (f a) * ((1 : C) ⊗ₜ[k] b - algebraMap k (C ⊗[k] C) (f b)) := by
        rw [hφ, map_mul, show a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : C)) * ((1 : C) ⊗ₜ[k] b) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
        ring
      rw [h1]
      exact Commute.isNilpotent_add (Commute.all _ _) (Commute.isNilpotent_mul_right (Commute.all _ _) hA)
        (Commute.isNilpotent_mul_left (Commute.all _ _) hB)
    | add x y hx hy =>
      have : x + y - algebraMap k (C ⊗[k] C) (φ (x + y)) =
          (x - algebraMap k (C ⊗[k] C) (φ x)) + (y - algebraMap k (C ⊗[k] C) (φ y)) := by
        rw [map_add, map_add]; abel
      rw [this]
      exact Commute.isNilpotent_add (Commute.all _ _) hx hy

  obtain ⟨u, hu⟩ := (IsUnit.mk0 _ hz).map (algebraMap k (C ⊗[k] C))
  have hzu : z = u * (1 + ↑u⁻¹ * (z - algebraMap k (C ⊗[k] C) (φ z))) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hu]
    abel
  rw [hzu]
  exact (Units.isUnit u).mul
    (IsNilpotent.isUnit_one_add (Commute.isNilpotent_mul_left (Commute.all _ _) (hdec z)))

end TensorLocal

section HopfIdeal

variable (k : Type u) [Field k] (B : Type u) [CommRing B] [HopfAlgebra k B]

p2m_open_scoped "HopfAlgebra" in

abbrev HopfAlgebra.unitComponentIdealHOMOG : Ideal B :=
  HopfAlgebra.pointKerIdealHOMOG (Bialgebra.counitAlgHom k B)

p2m_open_scoped "HopfAlgebra" in
theorem HopfAlgebra.counit_surjective_HOMOG : Function.Surjective (Bialgebra.counitAlgHom k B) :=
  fun c => ⟨algebraMap k B c, (Bialgebra.counitAlgHom k B).commutes c⟩

p2m_open_scoped "HopfAlgebra" in
scoped instance HopfAlgebra.isMaximal_ker_counit_HOMOG : (RingHom.ker (Bialgebra.counitAlgHom k B)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (HopfAlgebra.counit_surjective_HOMOG k B)

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed.HopfAlgebra"
p2m_open_scoped "HopfAlgebra" in
theorem HopfAlgebra.unitComponentIdealHOMOG_ne_top : HopfAlgebra.unitComponentIdealHOMOG k B ≠ ⊤ := fun h =>
  (HopfAlgebra.isMaximal_ker_counit_HOMOG k B).ne_top
    (top_le_iff.1 (h ▸ HopfAlgebra.pointKerIdealHOMOG_le_ker (Bialgebra.counitAlgHom k B)))

p2m_open_scoped "HopfAlgebra" in

scoped instance HopfAlgebra.isLocalRing_quotient_unitComponentIdealHOMOG [Module.Finite k B] :
    IsLocalRing (B ⧸ HopfAlgebra.unitComponentIdealHOMOG k B) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  haveI : Nontrivial (B ⧸ HopfAlgebra.unitComponentIdealHOMOG k B) :=
    Ideal.Quotient.nontrivial_iff.2 (HopfAlgebra.unitComponentIdealHOMOG_ne_top k B)
  have hsurj := IsArtinianRing.localization_surjective (RingHom.ker (Bialgebra.counitAlgHom k B)).primeCompl
    (Localization.AtPrime (RingHom.ker (Bialgebra.counitAlgHom k B)))
  have hK := HopfAlgebra.pointKerIdealHOMOG_eq_ker_algebraMap (Bialgebra.counitAlgHom k B)
    (RingHom.ker (Bialgebra.counitAlgHom k B)) rfl
  let e : Localization.AtPrime (RingHom.ker (Bialgebra.counitAlgHom k B)) →+*
      B ⧸ HopfAlgebra.unitComponentIdealHOMOG k B :=
    ((Ideal.quotEquivOfEq hK).symm.toRingHom).comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom
  refine IsLocalRing.of_surjective' e ?_
  exact (Ideal.quotEquivOfEq hK).symm.surjective.comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.surjective

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed.HopfAlgebra"
p2m_open_scoped "HopfAlgebra" in

def HopfAlgebra.counitQuotHOMOG : B ⧸ HopfAlgebra.unitComponentIdealHOMOG k B →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom k B) fun _ hx =>
    HopfAlgebra.pointKerIdealHOMOG_le_ker (Bialgebra.counitAlgHom k B) hx

p2m_open_scoped "HopfAlgebra" in
theorem HopfAlgebra.counitQuotHOMOG_mk (x : B) :
    HopfAlgebra.counitQuotHOMOG k B (Ideal.Quotient.mk _ x) = Coalgebra.counit (R := k) x := rfl

p2m_open_scoped "HopfAlgebra" in

theorem HopfAlgebra.lift_counit_counit_comul_HOMOG (x : B) :
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k B) (Bialgebra.counitAlgHom k B) (fun _ _ => Commute.all _ _)
      (Coalgebra.comul (R := k) x) = Coalgebra.counit (R := k) x := by
  have h1 : WithConv.toConv (Bialgebra.counitAlgHom k B) = (1 : WithConv (B →ₐ[k] k)) := by
    rw [AlgHom.convOne_def]
    congr 1
  have h2 := AlgHom.convMul_apply (WithConv.toConv (Bialgebra.counitAlgHom k B))
    (WithConv.toConv (Bialgebra.counitAlgHom k B)) x
  rw [WithConv.ofConv_toConv, h1, one_mul, AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] at h2
  exact h2.symm

p2m_open_scoped "HopfAlgebra" in

scoped instance HopfAlgebra.isHopfIdeal_unitComponentIdealHOMOG [Module.Finite k B] :
    (HopfAlgebra.unitComponentIdealHOMOG k B).IsHopfIdeal' k := by
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro x ⟨s, hs, hsx⟩
    let Φ : B →ₐ[k] (B ⧸ HopfAlgebra.unitComponentIdealHOMOG k B) ⊗[k] (B ⧸ HopfAlgebra.unitComponentIdealHOMOG k B) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ k _)).comp (Bialgebra.comulAlgHom k B)
    have hΦ : ∀ y, Φ y = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (HopfAlgebra.unitComponentIdealHOMOG k B))
        (Ideal.Quotient.mkₐ k (HopfAlgebra.unitComponentIdealHOMOG k B)) (Coalgebra.comul (R := k) y) := fun y => rfl
    rw [← hΦ]
    have hunit : IsUnit (Φ s) := by
      refine Algebra.isUnit_tensorProduct_of_lift_ne_zero_HOMOG (HopfAlgebra.counitQuotHOMOG k B) (Φ s) ?_
      have hcomp : (Algebra.TensorProduct.lift (HopfAlgebra.counitQuotHOMOG k B) (HopfAlgebra.counitQuotHOMOG k B)
          (fun _ _ => Commute.all _ _)).comp (Algebra.TensorProduct.map
            (Ideal.Quotient.mkₐ k (HopfAlgebra.unitComponentIdealHOMOG k B))
            (Ideal.Quotient.mkₐ k (HopfAlgebra.unitComponentIdealHOMOG k B))) =
          Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k B) (Bialgebra.counitAlgHom k B)
            (fun _ _ => Commute.all _ _) := by
        apply Algebra.TensorProduct.ext'
        intro a b
        rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
          Algebra.TensorProduct.lift_tmul]
        rfl
      rw [hΦ, ← AlgHom.comp_apply, hcomp, HopfAlgebra.lift_counit_counit_comul_HOMOG]
      exact hs
    have h0 : Φ s * Φ x = 0 := by rw [← map_mul, hsx, map_zero]
    exact (hunit.mul_right_eq_zero).1 h0
  ·
    intro x hx
    exact HopfAlgebra.pointKerIdealHOMOG_le_ker (Bialgebra.counitAlgHom k B) hx
  ·
    rintro x ⟨s, hs, hsx⟩
    refine ⟨HopfAlgebra.antipode k s, ?_, ?_⟩
    · rw [Bialgebra.counitAlgHom_apply, HopfAlgebra.counit_antipode]
      exact hs
    · rw [← HopfAlgebra.antipodeAlgHom_apply k B s, ← HopfAlgebra.antipodeAlgHom_apply k B x, ← map_mul, hsx, map_zero]

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed.HopfAlgebra"
end HopfIdeal
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed.HopfAlgebra"

p2m_open_scoped "Algebra" in
theorem Algebra.exists_algHom_ker_eq_of_isMaximal_HOMOG {k : Type u} [Field k] [IsAlgClosed k]
    {B : Type u} [CommRing B] [Algebra k B] [Module.Finite k B] (𝔪 : Ideal B) [𝔪.IsMaximal] :
    ∃ g : B →ₐ[k] k, RingHom.ker g = 𝔪 := by
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ 𝔪)
  let e : k ≃ₐ[k] B ⧸ 𝔪 := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ 𝔪)) hbij
  refine ⟨(e.symm : (B ⧸ 𝔪) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k 𝔪), ?_⟩
  ext x
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_algHom,
    map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [CommRing B] [HopfAlgebra k B] [Module.Finite k B] :
    ∃ (n : ℕ) (B₀ : Type u) (_ : CommRing B₀) (_ : HopfAlgebra k B₀) (_ : Module.Finite k B₀) (π : B →ₐc[k] B₀),
      0 < n ∧ IsLocalRing B₀ ∧ Function.Surjective π ∧ Nonempty (B ≃ₐ[k] (Fin n → B₀)) := by
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B

  let K₀ : Ideal B := HopfAlgebra.unitComponentIdealHOMOG k B

  have hpt : ∀ 𝔪 : MaximalSpectrum B, ∃ g : B →ₐ[k] k, RingHom.ker g = 𝔪.asIdeal := fun 𝔪 => by
    haveI := 𝔪.isMaximal
    exact Algebra.exists_algHom_ker_eq_of_isMaximal_HOMOG 𝔪.asIdeal
  choose g hg using hpt

  have e₂ : ∀ 𝔪 : MaximalSpectrum B, Localization.AtPrime 𝔪.asIdeal ≃ₐ[k] B ⧸ HopfAlgebra.pointKerIdealHOMOG (g 𝔪) := by
    intro 𝔪
    have hsurj : Function.Surjective (IsScalarTower.toAlgHom k B (Localization.AtPrime 𝔪.asIdeal)) :=
      IsArtinianRing.localization_surjective 𝔪.asIdeal.primeCompl _
    have hK : RingHom.ker (IsScalarTower.toAlgHom k B (Localization.AtPrime 𝔪.asIdeal)) =
        HopfAlgebra.pointKerIdealHOMOG (g 𝔪) :=
      (HopfAlgebra.pointKerIdealHOMOG_eq_ker_algebraMap (g 𝔪) 𝔪.asIdeal (hg 𝔪)).symm
    exact (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.trans (Ideal.quotientEquivAlgOfEq k hK)

  have e₃ : ∀ 𝔪 : MaximalSpectrum B, (B ⧸ HopfAlgebra.pointKerIdealHOMOG (g 𝔪)) ≃ₐ[k] B ⧸ K₀ := by
    intro 𝔪
    let τ : B ≃ₐ[k] B := HopfAlgebra.HopfTower.translateEquiv k B (g 𝔪)
    refine Ideal.quotientEquivAlg (HopfAlgebra.pointKerIdealHOMOG (g 𝔪)) K₀ τ (le_antisymm ?_ ?_)
    · intro y hy
      rw [show y = τ (τ.symm y) from (τ.apply_symm_apply y).symm]
      refine Ideal.mem_map_of_mem _ ?_
      obtain ⟨s, hs, hsy⟩ := hy
      refine ⟨τ.symm s, ?_, ?_⟩
      · have h1 := congrArg (fun φ : B →ₐ[k] k => φ s)
          (HopfAlgebra.HopfTower.comp_translate (g 𝔪) ((g 𝔪).comp (HopfAlgebra.HopfTower.antipodeAlgHom k B)))
        simp only [AlgHom.comp_apply] at h1
        rw [HopfAlgebra.HopfTower.convMul_comp_antipodeAlgHom, AlgHom.convOne_apply, Algebra.algebraMap_self,
          RingHom.id_apply] at h1
        change (g 𝔪) (HopfAlgebra.HopfTower.translate k B ((g 𝔪).comp (HopfAlgebra.HopfTower.antipodeAlgHom k B)) s) ≠ 0
        rw [h1, ← Bialgebra.counitAlgHom_apply]
        exact hs
      · rw [← map_mul, hsy, map_zero]
    · rw [Ideal.map_le_iff_le_comap]
      rintro x ⟨s, hs, hsx⟩
      refine ⟨τ s, ?_, ?_⟩
      · change Bialgebra.counitAlgHom k B (HopfAlgebra.HopfTower.translate k B (g 𝔪) s) ≠ 0
        rw [Bialgebra.counitAlgHom_apply, HopfAlgebra.HopfTower.counit_translate]
        exact hs
      · change τ s * τ x = 0
        rw [← map_mul, hsx, map_zero]

  let eB : B ≃ₐ[k] (MaximalSpectrum B → B ⧸ K₀) :=
    ((MaximalSpectrum.toPiLocalizationEquiv B).restrictScalars k).trans
      (AlgEquiv.piCongrRight fun 𝔪 => (e₂ 𝔪).trans (e₃ 𝔪))
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let eFin : (MaximalSpectrum B → B ⧸ K₀) ≃ₐ[k] (Fin (Fintype.card (MaximalSpectrum B)) → B ⧸ K₀) :=
    AlgEquiv.piCongrLeft' k (fun _ => B ⧸ K₀) (Fintype.equivFin (MaximalSpectrum B))
  have hn : 0 < Fintype.card (MaximalSpectrum B) :=
    Fintype.card_pos_iff.2 ⟨⟨RingHom.ker (Bialgebra.counitAlgHom k B), inferInstance⟩⟩
  exact ⟨Fintype.card (MaximalSpectrum B), B ⧸ K₀, inferInstance, inferInstance, inferInstance,
    HopfAlgebra.quotientBialgHom k K₀, hn, inferInstance, HopfAlgebra.quotientBialgHom_surjective k K₀,
    ⟨eB.trans eFin⟩⟩

end S_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed (solution)
