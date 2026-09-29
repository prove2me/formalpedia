-- Prove2me | solution 1 for HopfAlgebra.exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7c4a9cd2-d141-522f-9d4b-3091bb957b0e

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_FVectStructure
import Theorems.Thm_HopfAlgebra_exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step
import Theorems.Thm_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul"

set_option autoImplicit false

namespace EigfunGlueE72

open HopfAlgebra

noncomputable section

section SigmaP

variable (P : ValuationSubring (AlgebraicClosure ℚ))
  {R' : Type} [CommRing R'] [Algebra R' ↥P]
  (hfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ r : R',
    σ ((algebraMap R' ↥P r : ↥P) : AlgebraicClosure ℚ) = (algebraMap R' ↥P r : ↥P))

def sigmaP (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    ↥P →ₐ[R'] ↥P where
  toFun y := ⟨σ y, (P.valuation_sub_lt_one_of_mem_inertiaSubgroupIn hσ y.2).1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  commutes' r := Subtype.ext (hfix σ hσ r)

@[scoped simp] theorem sigmaP_apply_coe (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (y : ↥P) :
    ((sigmaP P hfix σ hσ y : ↥P) : AlgebraicClosure ℚ) = σ y := rfl

theorem sigmaP_sub_mem (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (y : ↥P) :
    sigmaP P hfix σ hσ y - y ∈ IsLocalRing.maximalIdeal ↥P := by
  rw [ValuationSubring.valuation_lt_one_iff]
  exact (P.valuation_sub_lt_one_of_mem_inertiaSubgroupIn hσ y.2).2

theorem sigmaP_injective (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : Function.Injective (sigmaP P hfix σ hσ) := by
  intro a b h
  have := congrArg (fun z : ↥P => (z : AlgebraicClosure ℚ)) h
  simp only [sigmaP_apply_coe, EmbeddingLike.apply_eq_iff_eq] at this
  exact Subtype.ext this

end SigmaP

section Points

variable (P : ValuationSubring (AlgebraicClosure ℚ))
  {R' : Type} [CommRing R'] [Algebra R' ↥P]
  {F : Type} [Field F]
  {B : Type} [CommRing B] [HopfAlgebra R' B]
  (fv : FVectStructure F R' B)

def eps : B →ₐ[R'] ↥P := (Algebra.ofId R' ↥P).comp (Bialgebra.counitAlgHom R' B)

theorem eps_apply (x : B) : eps (R' := R') P x = algebraMap R' ↥P (Coalgebra.counit x) := rfl

def lact (a : F) (b : B →ₐ[R'] ↥P) : B →ₐ[R'] ↥P := b.comp (fv.act a : B →ₐ[R'] B)

theorem lact_apply (a : F) (b : B →ₐ[R'] ↥P) (x : B) : lact P fv a b x = b (fv.act a x) := rfl

theorem lact_one (b : B →ₐ[R'] ↥P) : lact P fv 1 b = b := by
  ext x; rw [lact_apply, fv.act_one]; rfl

theorem lact_lact (a a' : F) (b : B →ₐ[R'] ↥P) :
    lact P fv a (lact P fv a' b) = lact P fv (a' * a) b := by
  ext x; simp only [lact_apply, fv.act_mul]; rfl

theorem act_zero_apply (x : B) : fv.act 0 x = algebraMap R' B (Coalgebra.counit x) := by
  have h' : (fv.act 0 : B →ₐ[R'] B) = (Algebra.ofId R' B).comp (Bialgebra.counitAlgHom R' B) :=
    WithConv.toConv_injective (by rw [fv.act_zero, AlgHom.convOne_def])
  have := DFunLike.congr_fun h' x
  simpa using this

theorem lact_zero (b : B →ₐ[R'] ↥P) : lact P fv 0 b = eps P := by
  apply AlgHom.ext
  intro x
  rw [lact_apply, act_zero_apply, eps_apply, AlgHom.commutes]

theorem toConv_lact_add (a a' : F) (b : B →ₐ[R'] ↥P) :
    WithConv.toConv (lact P fv (a + a') b) =
      WithConv.toConv (lact P fv a b) * WithConv.toConv (lact P fv a' b) := by
  have h := fv.act_add a a'
  apply WithConv.ofConv_injective
  rw [WithConv.ofConv_toConv]
  unfold lact
  have h2 : (fv.act (a + a') : B →ₐ[R'] B) =
      (WithConv.toConv (fv.act a : B →ₐ[R'] B) * WithConv.toConv (fv.act a' : B →ₐ[R'] B)).ofConv := by
    rw [← h, WithConv.ofConv_toConv]
  rw [h2, AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, WithConv.ofConv_toConv]

theorem lact_eps (a : F) : lact P fv a (eps P) = eps (R' := R') (B := B) P := by
  ext x
  simp [lact_apply, eps]

theorem eq_eps_of_forall_apply_eq_zero {s : ℕ} (X : Fin s → B)
    (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
    (hgen : Algebra.adjoin R' (Set.range X) = ⊤)
    (b : B →ₐ[R'] ↥P) (hb : ∀ i, b (X i) = 0) : b = eps P := by
  refine AlgHom.ext_of_adjoin_eq_top hgen ?_
  rintro _ ⟨i, rfl⟩
  rw [hb i, eps_apply, h5 i, map_zero]

theorem exists_apply_ne_zero_of_ne_eps {s : ℕ} (X : Fin s → B)
    (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
    (hgen : Algebra.adjoin R' (Set.range X) = ⊤)
    (b : B →ₐ[R'] ↥P) (hb : b ≠ eps P) : ∃ i, b (X i) ≠ 0 := by
  by_contra h
  push Not at h
  exact hb (eq_eps_of_forall_apply_eq_zero P X h5 hgen b h)

end Points

section Free

variable {p : ℕ} [hp : Fact p.Prime]
  (P : ValuationSubring (AlgebraicClosure ℚ))
  {R' : Type} [CommRing R'] [Algebra R' ↥P]
  {F : Type} [Field F] [CharP F p]
  {B : Type} [CommRing B] [HopfAlgebra R' B]
  (fv : FVectStructure F R' B)
  (χ : Fˣ →* R'ˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P)
  (hχ : ∀ l : Fˣ, IsLocalRing.residue ↥P (algebraMap R' ↥P ((χ l : R'ˣ) : R')) = ι₀ l)
  {s : ℕ} (X : Fin s → B)
  (h1 : ∀ (i : Fin s) (l : Fˣ), fv.act l (X i) = (((χ ^ (p ^ (i : ℕ))) l : R'ˣ) : R') • X i)
  (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
  (hgen : Algebra.adjoin R' (Set.range X) = ⊤)

omit hp [CharP F p] in
include h1 in
theorem lact_units_apply_X (u : Fˣ) (b : B →ₐ[R'] ↥P) (i : Fin s) :
    lact P fv (u : F) b (X i) = algebraMap R' ↥P (((χ u) ^ (p ^ (i : ℕ)) : R'ˣ) : R') * b (X i) := by
  rw [lact_apply, h1 i u, map_smul, Algebra.smul_def, MonoidHom.pow_apply]

theorem units_eq_one_of_pow_prime_pow {u : Fˣ} {m : ℕ} (h : (u : F) ^ (p ^ m) = 1) : u = 1 := by
  have : ((u : F) - 1) ^ (p ^ m) = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  have h2 : (u : F) - 1 = 0 := pow_eq_zero_iff (pow_ne_zero m hp.out.ne_zero) |>.mp this
  exact Units.ext (sub_eq_zero.mp h2)

include hχ h1 h5 hgen in

theorem eq_eps_of_lact_eq (u : Fˣ) (hu : u ≠ 1) (b : B →ₐ[R'] ↥P)
    (hb : lact P fv (u : F) b = b) : b = eps P := by
  refine eq_eps_of_forall_apply_eq_zero P X h5 hgen b fun i => ?_
  have key : (algebraMap R' ↥P (((χ u) ^ (p ^ (i : ℕ)) : R'ˣ) : R') - 1) * b (X i) = 0 := by
    rw [sub_mul, one_mul, ← lact_units_apply_X P fv χ X h1, hb, sub_self]
  rcases mul_eq_zero.mp key with h | h
  · exfalso
    apply hu
    have h2 : IsLocalRing.residue ↥P (algebraMap R' ↥P ((χ (u ^ (p ^ (i : ℕ))) : R'ˣ) : R')) = 1 := by
      rw [map_pow, sub_eq_zero.mp h, map_one]
    rw [hχ] at h2
    have h3 : ((u ^ (p ^ (i : ℕ)) : Fˣ) : F) = 1 := ι₀.injective (h2.trans (map_one ι₀).symm)
    exact units_eq_one_of_pow_prime_pow (m := (i : ℕ)) (by simpa [Units.val_pow_eq_pow_val] using h3)
  · exact h

end Free

section Orbit

variable {p : ℕ} [hp : Fact p.Prime]
  (P : ValuationSubring (AlgebraicClosure ℚ))
  {R' : Type} [CommRing R'] [Algebra R' ↥P]
  {F : Type} [Field F] [Fintype F] [CharP F p]
  {B : Type} [CommRing B] [HopfAlgebra R' B]
  (fv : FVectStructure F R' B)
  (χ : Fˣ →* R'ˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P)
  (hχ : ∀ l : Fˣ, IsLocalRing.residue ↥P (algebraMap R' ↥P ((χ l : R'ˣ) : R')) = ι₀ l)
  {s : ℕ} (X : Fin s → B)
  (h1 : ∀ (i : Fin s) (l : Fˣ), fv.act l (X i) = (((χ ^ (p ^ (i : ℕ))) l : R'ˣ) : R') • X i)
  (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
  (hgen : Algebra.adjoin R' (Set.range X) = ⊤)
  (hF : Fintype.card F = p ^ s) (hcardV : Nat.card (B →ₐ[R'] ↥P) = p ^ s)
  (b₀ : B →ₐ[R'] ↥P) (hb₀ : b₀ ≠ eps P)

include hχ h1 h5 hgen hb₀ in
theorem lact_ne_eps (u : Fˣ) : lact P fv (u : F) b₀ ≠ eps P := by
  intro h
  apply hb₀
  have h2 := congrArg (lact P fv ((u⁻¹ : Fˣ) : F)) h
  rwa [lact_lact, Units.mul_inv, lact_one, lact_eps] at h2

include hχ h1 h5 hgen hb₀ in
theorem lact_b0_injective : Function.Injective (fun a : F => lact P fv a b₀) := by
  intro a a' h
  simp only at h
  by_cases ha : a = 0
  · subst ha
    by_contra ha'
    rw [lact_zero] at h
    exact lact_ne_eps P fv χ ι₀ hχ X h1 h5 hgen b₀ hb₀ (Units.mk0 a' (Ne.symm ha')) (by simpa using h.symm)
  by_cases ha' : a' = 0
  · subst ha'
    rw [lact_zero] at h
    exact absurd (by simpa using h) (lact_ne_eps P fv χ ι₀ hχ X h1 h5 hgen b₀ hb₀ (Units.mk0 a ha))

  set u := Units.mk0 a ha
  set u' := Units.mk0 a' ha'
  have hu : (u : F) = a := rfl
  have hu' : (u' : F) = a' := rfl
  have key : lact P fv ((u * u'⁻¹ : Fˣ) : F) b₀ = b₀ := by
    have h2 := congrArg (lact P fv ((u'⁻¹ : Fˣ) : F)) h
    rw [← hu, ← hu', lact_lact, lact_lact, Units.mul_inv, lact_one] at h2
    rw [Units.val_mul]
    exact h2
  have : u * u'⁻¹ = 1 := by
    by_contra hne
    exact hb₀ (eq_eps_of_lact_eq P fv χ ι₀ hχ X h1 h5 hgen _ hne b₀ key)
  rw [← hu, ← hu', show u = u' from mul_inv_eq_one.mp this]

include hχ h1 h5 hgen hb₀ hF hcardV in
theorem lact_b0_bijective : Function.Bijective (fun a : F => lact P fv a b₀) := by
  haveI : Finite (B →ₐ[R'] ↥P) := Nat.finite_of_card_ne_zero (by rw [hcardV]; exact pow_ne_zero _ hp.out.ne_zero)
  refine (lact_b0_injective P fv χ ι₀ hχ X h1 h5 hgen b₀ hb₀).bijective_of_nat_card_le ?_
  rw [hcardV, Nat.card_eq_fintype_card, hF]

def coord (hbij : Function.Bijective (fun a : F => lact P fv a b₀)) (b : B →ₐ[R'] ↥P) : F :=
  (Equiv.ofBijective _ hbij).symm b

omit hp [Fintype F] [CharP F p] in
theorem lact_coord (hbij : Function.Bijective (fun a : F => lact P fv a b₀)) (b : B →ₐ[R'] ↥P) :
    lact P fv (coord P fv b₀ hbij b) b₀ = b :=
  (Equiv.ofBijective _ hbij).apply_symm_apply b

omit hp [Fintype F] [CharP F p] in
theorem coord_lact (hbij : Function.Bijective (fun a : F => lact P fv a b₀)) (a : F) :
    coord P fv b₀ hbij (lact P fv a b₀) = a :=
  (Equiv.ofBijective _ hbij).symm_apply_apply a

omit hp [Fintype F] [CharP F p] in
theorem coord_eps (hbij : Function.Bijective (fun a : F => lact P fv a b₀)) :
    coord P fv b₀ hbij (eps P) = 0 := by
  rw [← lact_zero P fv b₀, coord_lact]

omit hp [Fintype F] [CharP F p] in
theorem coord_b0 (hbij : Function.Bijective (fun a : F => lact P fv a b₀)) :
    coord P fv b₀ hbij b₀ = 1 := by
  have h := coord_lact P fv b₀ hbij 1
  rwa [lact_one] at h

omit hp [Fintype F] [CharP F p] in

theorem coord_convMul (hbij : Function.Bijective (fun a : F => lact P fv a b₀)) (b b' : B →ₐ[R'] ↥P) :
    coord P fv b₀ hbij (WithConv.toConv b * WithConv.toConv b').ofConv =
      coord P fv b₀ hbij b + coord P fv b₀ hbij b' := by
  have h : (WithConv.toConv b * WithConv.toConv b').ofConv =
      lact P fv (coord P fv b₀ hbij b + coord P fv b₀ hbij b') b₀ := by
    apply WithConv.toConv_injective
    rw [WithConv.toConv_ofConv, toConv_lact_add, lact_coord, lact_coord]
  rw [h, coord_lact]

end Orbit

section Sigma

variable {p : ℕ} [hp : Fact p.Prime]
  (P : ValuationSubring (AlgebraicClosure ℚ))
  {R' : Type} [CommRing R'] [Algebra R' ↥P]
  (hfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ r : R',
    σ ((algebraMap R' ↥P r : ↥P) : AlgebraicClosure ℚ) = (algebraMap R' ↥P r : ↥P))
  {F : Type} [Field F]
  {B : Type} [CommRing B] [HopfAlgebra R' B]
  (fv : FVectStructure F R' B)
  (b₀ : B →ₐ[R'] ↥P) (hb₀ : b₀ ≠ eps P)
  (hbij : Function.Bijective (fun a : F => lact P fv a b₀))

def spt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (b : B →ₐ[R'] ↥P) : B →ₐ[R'] ↥P :=
  (sigmaP P hfix σ hσ).comp b

theorem spt_apply_coe (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (b : B →ₐ[R'] ↥P) (x : B) :
    ((spt P hfix σ hσ b x : ↥P) : AlgebraicClosure ℚ) = σ (b x) := rfl

theorem spt_lact (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (a : F) (b : B →ₐ[R'] ↥P) :
    spt P hfix σ hσ (lact P fv a b) = lact P fv a (spt P hfix σ hσ b) := rfl

theorem spt_eps (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : spt P hfix σ hσ (eps P) = eps (R' := R') (B := B) P := by
  apply AlgHom.ext
  intro x
  rw [spt, AlgHom.comp_apply, eps_apply, AlgHom.commutes]

theorem spt_injective (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : Function.Injective (spt (B := B) P hfix σ hσ) := by
  intro b b' h
  apply AlgHom.ext
  intro x
  exact sigmaP_injective P hfix σ hσ (DFunLike.congr_fun h x)

def psi (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : F :=
  coord P fv b₀ hbij (spt P hfix σ hσ b₀)

theorem lact_psi (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    lact P fv (psi P hfix fv b₀ hbij σ hσ) b₀ = spt P hfix σ hσ b₀ :=
  lact_coord P fv b₀ hbij _

include hb₀ in
theorem psi_ne_zero (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    psi P hfix fv b₀ hbij σ hσ ≠ 0 := by
  intro h
  have h2 := lact_psi P hfix fv b₀ hbij σ hσ
  rw [h, lact_zero, ← spt_eps P hfix σ hσ] at h2
  exact hb₀ (spt_injective P hfix σ hσ h2.symm)

theorem coord_spt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (b : B →ₐ[R'] ↥P) :
    coord P fv b₀ hbij (spt P hfix σ hσ b) = psi P hfix fv b₀ hbij σ hσ * coord P fv b₀ hbij b := by
  conv_lhs => rw [← lact_coord P fv b₀ hbij b, spt_lact, ← lact_psi P hfix fv b₀ hbij σ hσ, lact_lact]
  rw [coord_lact]

end Sigma

section Digits

variable {p : ℕ} [hp : Fact p.Prime] {R' : Type} [CommRing R'] {s : ℕ}

open Classical in

def digit (δ : Fin s → R') (i : Fin s) : ℕ := if IsUnit (δ i) then 0 else 1

omit hp in
theorem digit_le_one (δ : Fin s → R') (i : Fin s) : digit δ i ≤ 1 := by
  unfold digit; split_ifs <;> simp

theorem digit_eq_of_associated (hunif : Irreducible (p : R')) (δ : Fin s → R')
    (n : Fin s → ℕ) (hn : ∀ i, n i ≤ 1) (hassoc : ∀ i, Associated (δ i) ((p : R') ^ n i)) :
    n = digit δ := by
  funext i
  have hi := hn i
  have ha := hassoc i
  unfold digit
  interval_cases h : n i
  · rw [pow_zero, associated_one_iff_isUnit] at ha
    rw [if_pos ha]
  · rw [pow_one] at ha
    have : ¬ IsUnit (δ i) := fun hu => hunif.not_isUnit (ha.isUnit hu)
    rw [if_neg this]

def digitSet (δ : Fin s → R') : Finset ℕ :=
  (Finset.univ.filter (fun m : Fin s => digit δ m = 1)).image (fun m : Fin s => s - 1 - m.val)

omit hp in
theorem digitSet_lt (δ : Fin s → R') : ∀ j ∈ digitSet δ, j < s := by
  intro j hj
  simp only [digitSet, Finset.mem_image] at hj
  obtain ⟨m, -, rfl⟩ := hj
  have := m.2
  omega

omit hp in
theorem sum_digitSet (δ : Fin s → R') :
    ∑ j ∈ digitSet δ, p ^ j = ∑ m : Fin s, digit δ m * p ^ (s - 1 - (m : ℕ)) := by
  rw [digitSet, Finset.sum_image]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    have := digit_le_one δ m
    interval_cases h : digit δ m <;> simp
  · intro m hm m' hm' h
    have := m.2; have := m'.2
    exact Fin.ext (by simp only at h; omega)

omit hp in
theorem rotate_modEq (M : ℕ) (hM : p ^ s = M + 1) (n : Fin s → ℕ) (i : Fin s) [NeZero s] :
    (∑ j : Fin s, n (i + j) * p ^ (s - 1 - (j : ℕ))) * p ^ (s - (i : ℕ)) ≡
      ∑ m : Fin s, n m * p ^ (s - 1 - (m : ℕ)) [MOD M] := by
  rw [← ZMod.natCast_eq_natCast_iff, Finset.sum_mul]
  have hps : ((p : ZMod M)) ^ s = 1 := by
    have : ((p ^ s : ℕ) : ZMod M) = ((M + 1 : ℕ) : ZMod M) := by rw [hM]
    push_cast at this
    simpa using this
  have hre : ∑ m : Fin s, n m * p ^ (s - 1 - (m : ℕ)) =
      ∑ j : Fin s, n (i + j) * p ^ (s - 1 - ((i + j : Fin s) : ℕ)) :=
    (Fintype.sum_equiv (Equiv.addLeft i) (fun j => n (i + j) * p ^ (s - 1 - ((i + j : Fin s) : ℕ)))
      (fun m => n m * p ^ (s - 1 - (m : ℕ))) (fun j => rfl)).symm
  rw [hre]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi := i.2; have hj := j.2
  rw [mul_assoc, ← pow_add]
  congr 1
  rcases lt_or_ge ((i : ℕ) + (j : ℕ)) s with h | h
  · have hv : ((i + j : Fin s) : ℕ) = (i : ℕ) + (j : ℕ) := by
      rw [Fin.val_add, Nat.mod_eq_of_lt h]
    rw [hv, show s - 1 - (j : ℕ) + (s - (i : ℕ)) = s + (s - 1 - ((i : ℕ) + (j : ℕ))) by omega,
      pow_add, hps, one_mul]
  · have hv : ((i + j : Fin s) : ℕ) = (i : ℕ) + (j : ℕ) - s := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hv, show s - 1 - (j : ℕ) + (s - (i : ℕ)) = s - 1 - ((i : ℕ) + (j : ℕ) - s) by omega]

omit hp in
theorem pow_eq_pow_of_modEq {M : Type*} [Monoid M] (θ : M) {N a b : ℕ} (hθ : θ ^ N = 1)
    (h : a ≡ b [MOD N]) : θ ^ a = θ ^ b := by
  rw [← Nat.div_add_mod a N, ← Nat.div_add_mod b N, pow_add, pow_add, pow_mul, pow_mul, hθ,
    one_pow, one_pow, one_mul, one_mul, h]

end Digits

section CharComp

variable {p : ℕ} [hp : Fact p.Prime]
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
  {R' : Type} [CommRing R'] [Algebra R' ↥P]
  (hunif : Irreducible (p : R'))
  (hfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ r : R',
    σ ((algebraMap R' ↥P r : ↥P) : AlgebraicClosure ℚ) = (algebraMap R' ↥P r : ↥P))
  {F : Type} [Field F] [Fintype F] [CharP F p]
  {B : Type} [CommRing B] [HopfAlgebra R' B]
  (fv : FVectStructure F R' B)
  (χ : Fˣ →* R'ˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P)
  (hχ : ∀ l : Fˣ, IsLocalRing.residue ↥P (algebraMap R' ↥P ((χ l : R'ˣ) : R')) = ι₀ l)
  {s : ℕ} [NeZero s] (X : Fin s → B) (δ : Fin s → R')
  (h1 : ∀ (i : Fin s) (l : Fˣ), fv.act l (X i) = (((χ ^ (p ^ (i : ℕ))) l : R'ˣ) : R') • X i)
  (h2 : ∀ i, X i ^ p = δ i • X (i + 1))
  (h4 : ∀ i, δ i ∣ (p : R'))
  (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
  (hgen : Algebra.adjoin R' (Set.range X) = ⊤)
  (hF : Fintype.card F = p ^ s)
  (b₀ : B →ₐ[R'] ↥P) (hb₀ : b₀ ≠ eps P)
  (hbij : Function.Bijective (fun a : F => lact P fv a b₀))

omit [NeZero s] in
theorem one_le_pow_sub_one : 1 ≤ p ^ s - 1 ∨ s = 0 := by
  rcases Nat.eq_zero_or_pos s with h | h
  · exact Or.inr h
  · left
    have : 2 ≤ p ^ s := le_trans hp.out.two_le (Nat.le_self_pow h.ne' p)
    omega

theorem mem_of_pow_eq (π' : AlgebraicClosure ℚ) (hπ' : π' ^ (p ^ s - 1) = p) : π' ∈ P := by
  have hps1 : p ^ s - 1 ≠ 0 := by
    have : 2 ≤ p ^ s := le_trans hp.out.two_le (Nat.le_self_pow (NeZero.ne s) p)
    omega
  rw [← ValuationSubring.valuation_le_one_iff]
  by_contra h
  push Not at h
  have h2 : 1 < P.valuation (π' ^ (p ^ s - 1)) := by
    rw [map_pow]
    exact one_lt_pow' h hps1
  rw [hπ'] at h2
  have h3 : P.valuation (p : AlgebraicClosure ℚ) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff P _).mpr (natCast_mem P p)
  exact absurd h2 (not_lt.mpr h3)

omit [CharP F p] in
include hP hunif hχ h1 h2 h4 h5 hgen hF hb₀ in

theorem iota_psi_eq (π' : AlgebraicClosure ℚ) (hπ' : π' ^ (p ^ s - 1) = p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    ι₀ (psi P hfix fv b₀ hbij σ hσ) = P.tameCharacter π' σ ^ (∑ j ∈ digitSet δ, p ^ j) := by
  classical
  set x : Fin s → ↥P := fun i => b₀ (X i) with hxdef
  have hx : ∀ i, x i ^ p = algebraMap R' ↥P (δ i) * x (i + 1) := by
    intro i
    have := congrArg b₀ (h2 i)
    rwa [map_pow, map_smul, Algebra.smul_def] at this
  obtain ⟨i₀, hi₀⟩ := exists_apply_ne_zero_of_ne_eps P X h5 hgen b₀ hb₀
  have hps1 : p ^ s - 1 ≠ 0 := by
    have : 2 ≤ p ^ s := le_trans hp.out.two_le (Nat.le_self_pow (NeZero.ne s) p)
    omega
  have hπ'0 : π' ≠ 0 := by
    rintro rfl
    rw [zero_pow hps1] at hπ'
    exact hp.out.ne_zero (by exact_mod_cast hπ'.symm)
  have hπ'P : π' ∈ P := mem_of_pow_eq P π' hπ'
  set πP : ↥P := ⟨π', hπ'P⟩ with hπPdef
  have hπP : πP ^ (p ^ s - 1) = algebraMap R' ↥P p := by
    apply Subtype.ext
    rw [map_natCast]
    push_cast
    exact hπ'
  have hpS : algebraMap R' ↥P p ∈ IsLocalRing.maximalIdeal ↥P := by
    rw [map_natCast, ValuationSubring.valuation_lt_one_iff]
    have := (ValuationSubring.mem_nonunits_iff (A := P)).mp hP
    simpa using this
  have hp0 : algebraMap R' ↥P p ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hp.out.ne_zero
  obtain ⟨n, hn, hassoc, t, ht1, hσπ, hσx⟩ :=
    ValuationRing.exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul hunif hpS hp0
      (sigmaP P hfix σ hσ) (sigmaP_sub_mem P hfix σ hσ) δ h4 x hx πP hπP
  have hnd : n = digit δ := digit_eq_of_associated hunif δ n hn hassoc

  have hψ0 := psi_ne_zero P hfix fv b₀ hb₀ hbij σ hσ
  set u : Fˣ := Units.mk0 _ hψ0 with hu
  have hlu : lact P fv (u : F) b₀ = spt P hfix σ hσ b₀ := by
    rw [hu, Units.val_mk0]; exact lact_psi P hfix fv b₀ hbij σ hσ
  have hcmp : algebraMap R' ↥P (((χ u) ^ (p ^ (i₀ : ℕ)) : R'ˣ) : R') * x i₀ =
      t ^ (∑ j : Fin s, n (i₀ + j) * p ^ (s - 1 - (j : ℕ))) * x i₀ := by
    rw [← lact_units_apply_X P fv χ X h1 u b₀ i₀, ← hσx i₀, hlu]
    rfl
  have hcmp' : algebraMap R' ↥P (((χ u) ^ (p ^ (i₀ : ℕ)) : R'ˣ) : R') =
      t ^ (∑ j : Fin s, n (i₀ + j) * p ^ (s - 1 - (j : ℕ))) :=
    mul_right_cancel₀ hi₀ hcmp

  have hres : (ι₀ (psi P hfix fv b₀ hbij σ hσ)) ^ (p ^ (i₀ : ℕ)) =
      (IsLocalRing.residue ↥P t) ^ (∑ j : Fin s, n (i₀ + j) * p ^ (s - 1 - (j : ℕ))) := by
    have h := congrArg (IsLocalRing.residue ↥P) hcmp'
    rw [map_pow (IsLocalRing.residue ↥P) t] at h
    rw [← h, ← map_pow χ, hχ, Units.val_pow_eq_pow_val, map_pow, hu, Units.val_mk0]

  have hσπ' : σ π' = (t : AlgebraicClosure ℚ) * π' := by
    have := congrArg (fun z : ↥P => (z : AlgebraicClosure ℚ)) hσπ
    simpa using this
  have hdiv : σ π' / π' = (t : AlgebraicClosure ℚ) := by
    rw [hσπ', mul_div_assoc, div_self hπ'0, mul_one]
  have hmem : σ π' / π' ∈ P := by rw [hdiv]; exact t.2
  have hθ : P.tameCharacter π' σ = IsLocalRing.residue ↥P t := by
    unfold ValuationSubring.tameCharacter
    rw [dif_pos hmem]
    congr 1
    exact Subtype.ext hdiv

  set θ := IsLocalRing.residue ↥P t with hθdef
  set y := ι₀ (psi P hfix fv b₀ hbij σ hσ) with hydef
  have hθ1 : θ ^ (p ^ s - 1) = 1 := by rw [hθdef, ← map_pow, ht1, map_one]
  have hy : y ^ (p ^ s) = y := by
    rw [hydef, ← map_pow, ← hF, FiniteField.pow_card]
  have hi₀s : (i₀ : ℕ) ≤ s := le_of_lt i₀.2
  have key : y = θ ^ ((∑ j : Fin s, n (i₀ + j) * p ^ (s - 1 - (j : ℕ))) * p ^ (s - (i₀ : ℕ))) := by
    rw [← hy, show p ^ s = p ^ (i₀ : ℕ) * p ^ (s - (i₀ : ℕ)) by
        rw [← pow_add, Nat.add_sub_cancel' hi₀s],
      pow_mul, hres, ← pow_mul]
  rw [hθ, key]
  subst hnd
  refine pow_eq_pow_of_modEq θ hθ1 ?_
  rw [sum_digitSet]
  exact rotate_modEq (p ^ s - 1) (by omega) (digit δ) i₀

end CharComp

section Assembly

variable {p : ℕ} [hp : Fact p.Prime]
  {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
  (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
  (hKK' : K ≤ K')
  {s : ℕ} [NeZero s]
  {R' : Type} [CommRing R'] [Algebra R' ↥P]
  (hunif : Irreducible (p : R'))
  (hfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ r : R',
    σ ((algebraMap R' ↥P r : ↥P) : AlgebraicClosure ℚ) = (algebraMap R' ↥P r : ↥P))
  {F : Type} [Field F] [Fintype F]
  {B : Type} [CommRing B] [HopfAlgebra R' B]
  (fv : FVectStructure F R' B)
  (χ : Fˣ →* R'ˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P)
  (hχ : ∀ l : Fˣ, IsLocalRing.residue ↥P (algebraMap R' ↥P ((χ l : R'ˣ) : R')) = ι₀ l)
  (X : Fin s → B) (δ : Fin s → R')
  (h1 : ∀ (i : Fin s) (l : Fˣ), fv.act l (X i) = (((χ ^ (p ^ (i : ℕ))) l : R'ˣ) : R') • X i)
  (h2 : ∀ i, X i ^ p = δ i • X (i + 1))
  (h4 : ∀ i, δ i ∣ (p : R'))
  (h5 : ∀ i, Coalgebra.counit (R := R') (X i) = 0)
  (hgen : Algebra.adjoin R' (Set.range X) = ⊤)
  (hF : Fintype.card F = p ^ s)
  (hcardV : Nat.card (B →ₐ[R'] ↥P) = p ^ s)
  (q : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → (B →ₐ[R'] ↥P))
  (hqmul : ∀ f ∈ K', ∀ g ∈ K',
    WithConv.toConv (q (f * g)) = WithConv.toConv (q f) * WithConv.toConv (q g))
  (hqker : ∀ f ∈ K', (WithConv.toConv (q f) = 1 ↔ f ∈ K))
  (hqsurj : ∀ b : B →ₐ[R'] ↥P, ∃ f ∈ K', q f = b)
  (hqequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
    ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      (∀ h : H, g h = σ (f h)) → ∀ x : B,
        ((q g x : ↥P) : AlgebraicClosure ℚ) = σ ((q f x : ↥P) : AlgebraicClosure ℚ))

omit [NeZero s] in
include hF in
theorem charP_of_card : CharP F p := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  ·
    exfalso
    rw [hs, pow_zero] at hF
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have h0 : ((p : F)) ^ s = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rw [hF] at this
    exact_mod_cast this
  have hp0 : (p : F) = 0 := (pow_eq_zero_iff hs.ne').mp h0
  have hdvd : ringChar F ∣ p := (ringChar.spec F p).mp hp0
  have hne : ringChar F ≠ 1 := CharP.ringChar_ne_one
  have : ringChar F = p := ((Nat.dvd_prime hp.out).mp hdvd).resolve_left hne
  exact ringChar.of_eq this

include hP hKK' hunif hfix hχ h1 h2 h4 h5 hgen hF hcardV hqmul hqker hqsurj hqequiv in
theorem eigfun_of_model :
    ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧
        ∃ L : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →
            IsLocalRing.ResidueField P,
        (∀ f ∈ K', ∀ g ∈ K', L (f * g) = L f + L g) ∧ (∀ f ∈ K, L f = 0) ∧ (∃ f ∈ K', L f ≠ 0) ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → L g = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) * L f := by
  intro π' hπ'
  classical
  haveI : CharP F p := charP_of_card hF
  haveI : Finite (B →ₐ[R'] ↥P) :=
    Nat.finite_of_card_ne_zero (by rw [hcardV]; exact pow_ne_zero _ hp.out.ne_zero)
  have hex : ∃ b₀ : B →ₐ[R'] ↥P, b₀ ≠ eps P := by
    have h1lt : 1 < Nat.card (B →ₐ[R'] ↥P) := by
      rw [hcardV]; exact Nat.one_lt_pow (NeZero.ne s) hp.out.one_lt
    haveI := (Finite.one_lt_card_iff_nontrivial).mp h1lt
    exact exists_ne _
  obtain ⟨b₀, hb₀⟩ := hex
  have hbij := lact_b0_bijective P fv χ ι₀ hχ X h1 h5 hgen hF hcardV b₀ hb₀
  refine ⟨digitSet δ, digitSet_lt δ, fun f => ι₀ (coord P fv b₀ hbij (q f)), ?_, ?_, ?_, ?_⟩
  · intro f hf g hg
    have hq : q (f * g) = (WithConv.toConv (q f) * WithConv.toConv (q g)).ofConv := by
      apply WithConv.toConv_injective
      rw [WithConv.toConv_ofConv]
      exact hqmul f hf g hg
    simp only []
    rw [hq, coord_convMul, map_add]
  · intro f hf
    have hq : q f = eps P := by
      have h := (hqker f (hKK' hf)).mpr hf
      apply WithConv.toConv_injective
      rw [h, eps, AlgHom.convOne_def]
    simp only []
    rw [hq, coord_eps, map_zero]
  · obtain ⟨f, hf, hqf⟩ := hqsurj b₀
    refine ⟨f, hf, ?_⟩
    simp only []
    rw [hqf, coord_b0, map_one]
    exact one_ne_zero
  · intro σ hσ f hf g hfg
    have hqg : q g = spt P hfix σ hσ (q f) := by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      rw [spt_apply_coe]
      exact hqequiv σ hσ f hf g hfg x
    simp only []
    rw [hqg, coord_spt, map_mul,
      iota_psi_eq P hP hunif hfix fv χ ι₀ hχ X δ h1 h2 h4 h5 hgen hF b₀ hb₀ hbij π' hπ' σ hσ]

end Assembly

end

end EigfunGlueE72
p2m_reactivate "P2MW.S_HopfAlgebra_exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step.EigfunGlueE72"

theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) (hs : 1 ≤ s) (hcard : Nat.card K' = p ^ s * Nat.card K) :
    ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧
        ∃ L : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P,
        (∀ f ∈ K', ∀ g ∈ K', L (f * g) = L f + L g) ∧ (∀ f ∈ K, L f = 0) ∧ (∃ f ∈ K', L f ≠ 0) ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → L g = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) * L f := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨R', _, _, F, _, _, B, _, _, fv, χ, ι₀, X, δ, q, hunif, hfix, hF, hχ, h1, h2, h4, h5, hgen,
    hcardV, hqmul, hqker, hqsurj, hqequiv⟩ :=
    HopfAlgebra.exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step hp hp2 hMp P hP K K' hKK' hK hK' hstep s hcard
  exact EigfunGlueE72.eigfun_of_model P hP K K' hKK' hunif hfix fv χ ι₀ hχ X δ h1 h2 h4 h5 hgen hF hcardV q
    hqmul hqker hqsurj hqequiv

end S_HopfAlgebra_exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step
end P2MW
export P2MW.S_HopfAlgebra_exists_additive_eigenfunctional_tameCharacter_pow_of_finite_flat_of_inertiaSimple_step (solution)
