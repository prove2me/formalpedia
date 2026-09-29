-- Prove2me | solution 1 for HopfAlgebra.FVect.exists_generators_normalForm_of_finrank_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d03db3a9-5423-558b-9dcc-aefccec0e47c

import Definitions.Def_HopfAlgebra_FVectStructure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.Ideal.GoingUp
import Theorems.Thm_CyclicPowerRelations_presentation
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_FVect_exists_generators_normalForm_of_finrank_eq_card

universe u v w

open TensorProduct

namespace W2RaynS3

section Interface

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
variable {F : Type*} [Field F]
variable (act : F → (B →ₐc[R] B))

private def ActAdd : Prop :=
  ∀ a b, ((act (a + b) : B →ₐ[R] B).toLinearMap) =
    LinearMap.mul' R B ∘ₗ TensorProduct.map (act a : B →ₐ[R] B).toLinearMap (act b : B →ₐ[R] B).toLinearMap
      ∘ₗ Coalgebra.comul

private def ActMul : Prop := ∀ a b, act (a * b) = (act a).comp (act b)

private def ActOne : Prop := act 1 = BialgHom.id R B

variable {act}

private theorem toConv_act_add (hadd : ActAdd act) (a b : F) :
    WithConv.toConv (act (a + b) : B →ₐ[R] B) =
      WithConv.toConv (act a : B →ₐ[R] B) * WithConv.toConv (act b : B →ₐ[R] B) := by
  rw [AlgHom.convMul_def]
  congr 1
  apply AlgHom.toLinearMap_injective
  rw [hadd a b]
  rfl

private theorem algHom_convMul_comp_antipode (f : B →ₐ[R] B) :
    WithConv.toConv f.toLinearMap * WithConv.toConv (f.toLinearMap ∘ₗ HopfAlgebra.antipode R) = 1 := by
  rw [LinearMap.convMul_def, LinearMap.convOne_def]
  congr 1
  apply LinearMap.ext
  intro x
  have h2 : LinearMap.mul' R B ∘ₗ TensorProduct.map f.toLinearMap f.toLinearMap = f.toLinearMap ∘ₗ LinearMap.mul' R B :=
    (AlgHom.comp_mul' f).symm
  simp only [LinearMap.comp_apply]
  rw [← LinearMap.map_comp_lTensor, LinearMap.comp_apply, ← LinearMap.comp_apply (f := LinearMap.mul' R B),
    h2, LinearMap.comp_apply, HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp

private theorem act_zero_eq (hadd : ActAdd act) (x : B) :
    act 0 x = algebraMap R B (Coalgebra.counit (R := R) x) := by
  have h00 := hadd 0 0
  rw [add_zero] at h00
  have hu : WithConv.toConv (act 0 : B →ₐ[R] B).toLinearMap * WithConv.toConv (act 0 : B →ₐ[R] B).toLinearMap =
      WithConv.toConv (act 0 : B →ₐ[R] B).toLinearMap := by
    rw [LinearMap.convMul_def]
    change WithConv.toConv (LinearMap.mul' R B ∘ₗ TensorProduct.map (act 0 : B →ₐ[R] B).toLinearMap
        (act 0 : B →ₐ[R] B).toLinearMap ∘ₗ Coalgebra.comul) = _
    rw [← h00]
  have hw := algHom_convMul_comp_antipode (R := R) (act 0 : B →ₐ[R] B)
  have h1 : WithConv.toConv (act 0 : B →ₐ[R] B).toLinearMap = 1 := by
    calc WithConv.toConv (act 0 : B →ₐ[R] B).toLinearMap
        = WithConv.toConv (act 0 : B →ₐ[R] B).toLinearMap * (WithConv.toConv (act 0 : B →ₐ[R] B).toLinearMap *
            WithConv.toConv ((act 0 : B →ₐ[R] B).toLinearMap ∘ₗ HopfAlgebra.antipode R)) := by rw [hw, mul_one]
      _ = 1 := by rw [← mul_assoc, hu, hw]
  have h2 := LinearMap.congr_fun (congrArg WithConv.ofConv h1) x
  simpa [LinearMap.convOne_def] using h2

omit [Field F] in

private theorem counit_act (a : F) (x : B) :
    Coalgebra.counit (R := R) (act a x) = Coalgebra.counit (R := R) x :=
  CoalgHomClass.counit_comp_apply (act a) x

variable {T : Type w} [CommRing T] [Algebra R T]

private def psmul (act : F → (B →ₐc[R] B)) (a : F) (f : B →ₐ[R] T) : B →ₐ[R] T :=
  f.comp (act a : B →ₐ[R] B)

omit [Field F] in
private theorem psmul_apply (a : F) (f : B →ₐ[R] T) (x : B) : psmul act a f x = f (act a x) := rfl

private theorem psmul_one (hone : ActOne act) (f : B →ₐ[R] T) : psmul act 1 f = f := by
  apply AlgHom.ext
  intro x
  change f (act 1 x) = f x
  rw [hone]
  rfl

private theorem psmul_mul (hmul : ActMul act) (a b : F) (f : B →ₐ[R] T) :
    psmul act (a * b) f = psmul act b (psmul act a f) := by
  apply AlgHom.ext
  intro x
  change f (act (a * b) x) = f (act a (act b x))
  rw [hmul a b]
  rfl

private def onePt (R B T : Type*) [CommRing R] [CommRing B] [HopfAlgebra R B] [CommRing T] [Algebra R T] :
    B →ₐ[R] T :=
  (Algebra.ofId R T).comp (Bialgebra.counitAlgHom R B)

private theorem onePt_eq_convOne :
    WithConv.toConv (onePt R B T) = (1 : WithConv (B →ₐ[R] T)) := rfl

omit [Field F] in
private theorem psmul_onePt (a : F) : psmul act a (onePt R B T) = onePt R B T := by
  apply AlgHom.ext
  intro x
  change algebraMap R T (Coalgebra.counit (R := R) (act a x)) = algebraMap R T (Coalgebra.counit (R := R) x)
  rw [counit_act]

private theorem toConv_psmul_add (hadd : ActAdd act) (a b : F) (f : B →ₐ[R] T) :
    WithConv.toConv (psmul act (a + b) f) = WithConv.toConv (psmul act a f) * WithConv.toConv (psmul act b f) := by
  have h := AlgHom.comp_convMul_distrib f (WithConv.toConv (act a : B →ₐ[R] B)) (WithConv.toConv (act b : B →ₐ[R] B))
  rw [← toConv_act_add hadd] at h
  calc WithConv.toConv (psmul act (a + b) f)
      = WithConv.toConv (f.comp (WithConv.toConv (act (a + b) : B →ₐ[R] B)).ofConv) := rfl
    _ = WithConv.toConv ((WithConv.toConv (psmul act a f) * WithConv.toConv (psmul act b f)).ofConv) := by rw [h]; rfl
    _ = WithConv.toConv (psmul act a f) * WithConv.toConv (psmul act b f) := WithConv.toConv_ofConv _

private theorem psmul_zero (hadd : ActAdd act) (f : B →ₐ[R] T) : psmul act 0 f = onePt R B T := by
  apply AlgHom.ext
  intro x
  change f (act 0 x) = algebraMap R T (Coalgebra.counit (R := R) x)
  rw [act_zero_eq hadd, AlgHom.commutes]

private theorem eq_onePt_of_psmul_eq (hone : ActOne act) (hmul : ActMul act) (hadd : ActAdd act)
    {a : F} (ha : a ≠ 1) {f : B →ₐ[R] T} (hf : psmul act a f = f) : f = onePt R B T := by
  have h1 : psmul act (a - 1) f = onePt R B T := by
    have e : WithConv.toConv (psmul act (a - 1) f) = WithConv.toConv (onePt R B T) := by
      calc WithConv.toConv (psmul act (a - 1) f)
          = WithConv.toConv (psmul act a f) * WithConv.toConv (psmul act (-1) f) := by
              rw [sub_eq_add_neg, toConv_psmul_add hadd]
        _ = WithConv.toConv (psmul act 1 f) * WithConv.toConv (psmul act (-1) f) := by rw [hf, psmul_one hone]
        _ = WithConv.toConv (psmul act (1 + -1) f) := by rw [← toConv_psmul_add hadd]
        _ = WithConv.toConv (psmul act 0 f) := by rw [add_neg_cancel]
        _ = WithConv.toConv (onePt R B T) := by rw [psmul_zero hadd]
    exact WithConv.toConv_injective e
  have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  calc f = psmul act 1 f := (psmul_one hone f).symm
    _ = psmul act ((a - 1) * (a - 1)⁻¹) f := by rw [mul_inv_cancel₀ ha1]
    _ = psmul act (a - 1)⁻¹ (psmul act (a - 1) f) := psmul_mul hmul _ _ f
    _ = psmul act (a - 1)⁻¹ (onePt R B T) := by rw [h1]
    _ = onePt R B T := psmul_onePt _

private theorem psmul_injective_of_ne (hone : ActOne act) (hmul : ActMul act) (hadd : ActAdd act)
    {f : B →ₐ[R] T} (hf : f ≠ onePt R B T) :
    Function.Injective (fun a : Fˣ => psmul act (a : F) f) ∧ ∀ a : Fˣ, psmul act (a : F) f ≠ onePt R B T := by
  refine ⟨fun a b hab => ?_, fun a h => ?_⟩
  · by_contra hne
    apply hf
    have hfix : psmul act ((a : F) * (b : F)⁻¹) f = f := by
      have h' : psmul act ((b : F)⁻¹) (psmul act (a : F) f) = psmul act ((b : F)⁻¹) (psmul act (b : F) f) := by
        simp only at hab
        rw [hab]
      rw [← psmul_mul hmul, ← psmul_mul hmul, mul_inv_cancel₀ b.ne_zero, psmul_one hone] at h'
      exact h'
    refine eq_onePt_of_psmul_eq hone hmul hadd ?_ hfix
    intro h1
    exact hne (Units.ext ((mul_inv_eq_one₀ b.ne_zero).mp h1))
  · apply hf
    calc f = psmul act 1 f := (psmul_one hone f).symm
      _ = psmul act ((a : F) * (a : F)⁻¹) f := by rw [mul_inv_cancel₀ a.ne_zero]
      _ = psmul act (a : F)⁻¹ (psmul act (a : F) f) := psmul_mul hmul _ _ f
      _ = psmul act (a : F)⁻¹ (onePt R B T) := by rw [h]
      _ = onePt R B T := psmul_onePt _

private theorem finite_and_card_algHom_le [Nontrivial R] [Module.Free R B] [Module.Finite R B]
    (K : Type*) [Field K] [Algebra R K] :
    Finite (B →ₐ[R] K) ∧ Nat.card (B →ₐ[R] K) ≤ Module.finrank R B := by
  have hli := linearIndependent_algHom_toLinearMap R B K
  let bB := Module.Free.chooseBasis R B
  let e : (Module.Free.ChooseBasisIndex R B → K) ≃ₗ[K] (B →ₗ[R] K) := bB.constr K
  haveI : Module.Finite K (B →ₗ[R] K) := Module.Finite.equiv e
  have hfin : Module.finrank K (B →ₗ[R] K) = Module.finrank R B := by
    rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_chooseBasisIndex]
  have hfinite : Finite (B →ₐ[R] K) := hli.finite_of_isNoetherian
  refine ⟨hfinite, ?_⟩
  haveI := Fintype.ofFinite (B →ₐ[R] K)
  rw [Nat.card_eq_fintype_card, ← hfin]
  exact hli.fintype_card_le_finrank

end Interface

section Grading

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {Λ : Type*} [CommGroup Λ] (ρ : Λ →* (B ≃ₐ[R] B))

private def eig (ψ : Λ →* Rˣ) : Submodule R B where
  carrier := {b | ∀ l : Λ, ρ l b = ((ψ l : Rˣ) : R) • b}
  add_mem' := by
    intro x y hx hy l
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, hx l, hy l, smul_add]
  zero_mem' := by
    intro l
    simp
  smul_mem' := by
    intro r x hx l
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smul, hx l, smul_comm]

private theorem mem_eig {ψ : Λ →* Rˣ} {b : B} : b ∈ eig ρ ψ ↔ ∀ l : Λ, ρ l b = ((ψ l : Rˣ) : R) • b :=
  Iff.rfl

private theorem mul_mem_eig {ψ φ : Λ →* Rˣ} {a b : B} (ha : a ∈ eig ρ ψ) (hb : b ∈ eig ρ φ) :
    a * b ∈ eig ρ (ψ * φ) := by
  intro l
  rw [map_mul, ha l, hb l, MonoidHom.mul_apply, Units.val_mul, mul_smul_mul_comm]

private theorem algebraMap_mem_eig_one (r : R) : algebraMap R B r ∈ eig ρ 1 := by
  intro l
  simp

variable [Fintype Λ] (c : R)

private def proj (ψ : Λ →* Rˣ) : B →ₗ[R] B :=
  c • ∑ l : Λ, (((ψ l)⁻¹ : Rˣ) : R) • (ρ l).toLinearMap

private theorem proj_apply (ψ : Λ →* Rˣ) (b : B) :
    proj ρ c ψ b = c • ∑ l : Λ, (((ψ l)⁻¹ : Rˣ) : R) • ρ l b := by
  simp only [proj, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, AlgEquiv.toLinearMap_apply]

private theorem proj_mem_eig (ψ : Λ →* Rˣ) (b : B) : proj ρ c ψ b ∈ eig ρ ψ := by
  intro m
  rw [proj_apply, map_smul, map_sum, smul_comm]
  congr 1
  have hre : ∀ l : Λ, ρ m ((((ψ l)⁻¹ : Rˣ) : R) • ρ l b) =
      ((ψ m : Rˣ) : R) • (((((ψ (m * l))⁻¹ : Rˣ) : R)) • ρ (m * l) b) := by
    intro l
    rw [map_smul, map_mul, map_mul, AlgEquiv.mul_apply, smul_smul]
    congr 1
    rw [mul_inv]
    push_cast
    rw [← mul_assoc, Units.mul_inv, one_mul]
  simp_rw [hre, ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft m) (fun l => ((((ψ l)⁻¹ : Rˣ) : R)) • ρ l b)

private theorem proj_eq_self (hc : c * (Fintype.card Λ : R) = 1) {ψ : Λ →* Rˣ} {b : B}
    (hb : b ∈ eig ρ ψ) : proj ρ c ψ b = b := by
  rw [proj_apply]
  have : ∀ l : Λ, (((ψ l)⁻¹ : Rˣ) : R) • ρ l b = b := fun l => by
    rw [(mem_eig ρ).mp hb l, smul_smul, Units.inv_mul, one_smul]
  simp_rw [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

private theorem proj_eq_zero_of_ne {ψ φ : Λ →* Rˣ} {b : B} (hb : b ∈ eig ρ φ)
    (hsep : ∃ l : Λ, IsUnit ((((ψ l)⁻¹ * φ l : Rˣ) : R) - 1)) : proj ρ c ψ b = 0 := by
  obtain ⟨l₀, hl₀⟩ := hsep
  rw [proj_apply]
  have hsum : ∀ l : Λ, (((ψ l)⁻¹ : Rˣ) : R) • ρ l b = ((((ψ l)⁻¹ * φ l : Rˣ) : R)) • b := fun l => by
    rw [(mem_eig ρ).mp hb l, smul_smul, Units.val_mul]
  simp_rw [hsum, ← Finset.sum_smul]
  set θ : Λ →* Rˣ := ψ⁻¹ * φ with hθ
  have hθl : ∀ l, (ψ l)⁻¹ * φ l = θ l := fun l => by simp [hθ]
  simp_rw [hθl]
  have hS : ((θ l₀ : R) - 1) * ∑ l, ((θ l : Rˣ) : R) = 0 := by
    rw [sub_mul, one_mul, Finset.mul_sum, sub_eq_zero]
    calc ∑ l, (θ l₀ : R) * (θ l : R) = ∑ l, ((θ (l₀ * l) : Rˣ) : R) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_mul, Units.val_mul]
      _ = ∑ l, ((θ l : Rˣ) : R) := by
          exact Equiv.sum_comp (Equiv.mulLeft l₀) (fun l => ((θ l : Rˣ) : R))
  have hu : IsUnit ((θ l₀ : R) - 1) := by simpa [hθl] using hl₀
  rw [(hu.mul_right_eq_zero).mp hS, zero_smul, smul_zero]

private theorem sum_proj_pow_eq_self (hc : c * (Fintype.card Λ : R) = 1) (χ : Λ →* Rˣ)
    (hunit : ∀ l : Λ, l ≠ 1 → IsUnit (((χ l : Rˣ) : R) - 1)) (b : B) :
    ∑ j ∈ Finset.range (Fintype.card Λ), proj ρ c (χ ^ j) b = b := by
  classical
  simp_rw [proj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have key : ∀ l : Λ, (∑ j ∈ Finset.range (Fintype.card Λ), ((((χ ^ j) l)⁻¹ : Rˣ) : R) • ρ l b)
      = if l = 1 then (Fintype.card Λ : R) • b else 0 := by
    intro l
    rw [← Finset.sum_smul]
    split_ifs with hl
    · subst hl
      simp
    · have hζ : ∀ j : ℕ, ((((χ ^ j) l)⁻¹ : Rˣ) : R) = (((χ l)⁻¹ : Rˣ) : R) ^ j := fun j => by
        rw [MonoidHom.pow_apply, ← inv_pow, Units.val_pow_eq_pow_val]
      simp_rw [hζ]
      have hu : IsUnit ((((χ l)⁻¹ : Rˣ) : R) - 1) := by
        have e1 : (((χ l)⁻¹ : Rˣ) : R) - 1 = -((((χ l)⁻¹ : Rˣ) : R) * (((χ l : Rˣ) : R) - 1)) := by
          rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
        rw [e1]
        exact ((Units.isUnit _).mul (hunit l hl)).neg
      have hpow : (((χ l)⁻¹ : Rˣ) : R) ^ Fintype.card Λ = 1 := by
        rw [← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, pow_card_eq_one, map_one, inv_one, Units.val_one]
      have hg := geom_sum_mul (((χ l)⁻¹ : Rˣ) : R) (Fintype.card Λ)
      rw [hpow, sub_self] at hg
      rw [(hu.mul_left_eq_zero).mp hg, zero_smul]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_ite_eq' Finset.univ (1 : Λ), if_pos (Finset.mem_univ _),
    smul_smul, hc, one_smul]

end Grading

section Rho

variable {R : Type u} [CommRing R] [IsLocalRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
variable {F : Type*} [Field F] [Fintype F]
variable {act : F → (B →ₐc[R] B)}

private noncomputable def rho (hone : ActOne act) (hmul : ActMul act) : Fˣ →* (B ≃ₐ[R] B) where
  toFun a := AlgEquiv.ofAlgHom (act (a : F) : B →ₐ[R] B) (act (a⁻¹ : Fˣ) : B →ₐ[R] B)
    (by
      apply AlgHom.ext
      intro x
      have h := DFunLike.congr_fun (hmul (a : F) ((a⁻¹ : Fˣ) : F)) x
      rw [Units.mul_inv, hone] at h
      exact h.symm)
    (by
      apply AlgHom.ext
      intro x
      have h := DFunLike.congr_fun (hmul ((a⁻¹ : Fˣ) : F) (a : F)) x
      rw [Units.inv_mul, hone] at h
      exact h.symm)
  map_one' := by
    apply AlgEquiv.ext
    intro x
    change act ((1 : Fˣ) : F) x = x
    rw [Units.val_one, hone]
    rfl
  map_mul' := by
    intro a b
    apply AlgEquiv.ext
    intro x
    change act ((a * b : Fˣ) : F) x = act (a : F) (act (b : F) x)
    rw [Units.val_mul, hmul]
    rfl

omit [IsLocalRing R] [Fintype F] in
private theorem rho_apply (hone : ActOne act) (hmul : ActMul act) (a : Fˣ) (x : B) :
    rho hone hmul a x = act (a : F) x := rfl

variable (p r : ℕ) [Fact p.Prime] [NeZero r] (hF : Fintype.card F = p ^ r)
variable (χ : Fˣ →* Rˣ) (ι : F →+* IsLocalRing.ResidueField R)
  (hχ : ∀ l : Fˣ, IsLocalRing.residue R (χ l : R) = ι l)

include hF in

private theorem charP_of_card : CharP F p := by
  obtain ⟨n, hp0, hn⟩ := FiniteField.card F (ringChar F)
  have hp : p.Prime := Fact.out
  have hdvd : p ∣ ringChar F ^ (n : ℕ) := by
    rw [← hn, hF]
    exact dvd_pow_self p (NeZero.ne r)
  have hpeq : p = ringChar F := (Nat.prime_dvd_prime_iff_eq hp hp0).mp (hp.dvd_of_dvd_pow hdvd)
  rw [hpeq]
  infer_instance

include hF ι in

private theorem natCast_p_mem_maximalIdeal : (p : R) ∈ IsLocalRing.maximalIdeal R := by
  haveI := charP_of_card p r hF
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, ← map_natCast ι p, CharP.cast_eq_zero F p, map_zero]

include hF ι in

private theorem isUnit_card_sub_one : IsUnit ((p ^ r : R) - 1) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hpm := natCast_p_mem_maximalIdeal p r hF ι
  have hpr := Ideal.pow_mem_of_mem (IsLocalRing.maximalIdeal R) hpm r (Nat.pos_of_ne_zero (NeZero.ne r))
  have h1 : (1 : R) = (p ^ r : R) - ((p ^ r : R) - 1) := by ring
  apply (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  rw [h1]
  refine Ideal.sub_mem _ ?_ hmem
  exact hpr

omit [Fintype F] in
include hχ in

private theorem isUnit_chi_sub_one {l : Fˣ} (hl : l ≠ 1) : IsUnit (((χ l : Rˣ) : R) - 1) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [map_sub, map_one, hχ l, sub_eq_zero, ← ι.map_one] at h0
  exact hl (Units.val_eq_one.mp (ι.injective h0))

omit [Fact (Nat.Prime p)] [NeZero r] in
include hF hχ in

private theorem exists_isUnit_pow_sub_pow {j j' : ℕ} (hj : j < p ^ r - 1) (hj' : j' < p ^ r - 1) (hne : j ≠ j') :
    ∃ l : Fˣ, IsUnit ((((χ ^ j) l : Rˣ) : R) - (((χ ^ j') l : Rˣ) : R)) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_zpow_surjective (G := Fˣ)
  have hord : orderOf g = p ^ r - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (fun x => ?_), Nat.card_eq_fintype_card, Fintype.card_units, hF]
    obtain ⟨n, hn⟩ := hg x
    exact ⟨n, hn⟩
  refine ⟨g, IsLocalRing.notMem_maximalIdeal.mp fun hmem => hne ?_⟩
  have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [map_sub, MonoidHom.pow_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    map_pow, map_pow, hχ g, ← map_pow, ← map_pow, ← map_sub, map_eq_zero_iff ι ι.injective, sub_eq_zero,
    ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at h0
  refine pow_injOn_Iio_orderOf ?_ ?_ (Units.ext h0)
  · show j < orderOf g
    rw [hord]
    exact hj
  · show j' < orderOf g
    rw [hord]
    exact hj'

omit [IsLocalRing R] [NeZero r] in
include hF in

private theorem chi_pow_card : χ ^ (p ^ r) = χ := by
  classical
  have hcard : Fintype.card Fˣ = p ^ r - 1 := by rw [Fintype.card_units, hF]
  refine MonoidHom.ext fun l => ?_
  rw [MonoidHom.pow_apply, ← map_pow]
  congr 1
  calc l ^ p ^ r = l ^ (p ^ r - 1 + 1) := by
        rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out))]
    _ = l := by rw [pow_succ, ← hcard, pow_card_eq_one, one_mul]

omit [IsLocalRing R] [Fact (Nat.Prime p)] [NeZero r] in
include hF in

private theorem chi_pow_card_sub_one : χ ^ (p ^ r - 1) = 1 := by
  classical
  have hcard : Fintype.card Fˣ = p ^ r - 1 := by rw [Fintype.card_units, hF]
  refine MonoidHom.ext fun l => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, ← hcard, pow_card_eq_one, map_one]

omit [IsLocalRing R] [Fact (Nat.Prime p)] [NeZero r] in
include hF in

private theorem chi_pow_mod (n : ℕ) : χ ^ (n % (p ^ r - 1)) = χ ^ n := by
  refine MonoidHom.ext fun l => ?_
  have hQ : χ l ^ (p ^ r - 1) = 1 := by
    have := DFunLike.congr_fun (chi_pow_card_sub_one p r hF χ) l
    rwa [MonoidHom.pow_apply, MonoidHom.one_apply] at this
  rw [MonoidHom.pow_apply, MonoidHom.pow_apply]
  conv_rhs => rw [← Nat.mod_add_div n (p ^ r - 1), pow_add, pow_mul, hQ, one_pow, mul_one]

private def powAlgHom (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Algebra (ZMod p) F] (j : ℕ) (hj : j ≠ 0)
    (key : ∀ a b : F, (a + b) ^ j = a ^ j + b ^ j) : F →ₐ[ZMod p] F where
  toFun a := a ^ j
  map_one' := one_pow j
  map_mul' a b := mul_pow a b j
  map_zero' := zero_pow hj
  map_add' := key
  commutes' c := by
    show (algebraMap (ZMod p) F c) ^ j = algebraMap (ZMod p) F c
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective c
    rw [map_natCast]
    induction n with
    | zero => simp [zero_pow hj]
    | succ n ih => rw [Nat.cast_succ, key, ih, one_pow]

private theorem powAlgHom_apply (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Algebra (ZMod p) F] (j : ℕ)
    (hj : j ≠ 0) (key : ∀ a b : F, (a + b) ^ j = a ^ j + b ^ j) (a : F) : powAlgHom p j hj key a = a ^ j := rfl

include hF in

private theorem exists_pow_eq_of_additive {j : ℕ} (hj : 1 ≤ j)
    (hadd : ∀ a b : F, ι (a + b) ^ j = ι a ^ j + ι b ^ j) :
    ∃ i : ℕ, i < r ∧ ∀ l : Fˣ, (χ ^ j) l = (χ ^ p ^ i) l := by
  have hp : p.Prime := Fact.out
  haveI := charP_of_card p r hF
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have key : ∀ a b : F, (a + b) ^ j = a ^ j + b ^ j := fun a b =>
    ι.injective (by simpa [map_pow, map_add] using hadd a b)
  obtain ⟨⟨n, hn⟩, hθ⟩ :=
    (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 (powAlgHom p j (by omega) key)
  have hfr : Module.finrank (ZMod p) F = r := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    rw [ZMod.card, hF] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  refine ⟨n, hfr ▸ hn, fun l => ?_⟩
  have hval : ∀ a : F, a ^ j = a ^ p ^ n := fun a => by
    have h1 := AlgHom.congr_fun hθ a
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card, powAlgHom_apply] at h1
    exact h1.symm
  rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ← map_pow, ← map_pow]
  congr 1
  ext
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval]

end Rho

section Aug

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]

private def augSub (R B : Type*) [CommRing R] [CommRing B] [HopfAlgebra R B] : Submodule R B :=
  LinearMap.ker (Coalgebra.counit (R := R) (A := B))

private def augIdeal (R B : Type*) [CommRing R] [CommRing B] [HopfAlgebra R B] : Ideal B :=
  RingHom.ker (Bialgebra.counitAlgHom R B)

private theorem mem_augSub {x : B} : x ∈ augSub R B ↔ Coalgebra.counit (R := R) x = 0 := LinearMap.mem_ker

private theorem augIdeal_restrictScalars : (augIdeal R B).restrictScalars R = augSub R B := by
  ext x
  rw [Submodule.restrictScalars_mem, mem_augSub]
  exact RingHom.mem_ker

private def piAug (R B : Type*) [CommRing R] [CommRing B] [HopfAlgebra R B] : B →ₗ[R] B :=
  LinearMap.id - Algebra.linearMap R B ∘ₗ Coalgebra.counit

private theorem piAug_apply (y : B) :
    piAug R B y = y - algebraMap R B (Coalgebra.counit (R := R) y) := rfl

private theorem piAug_mem (y : B) : piAug R B y ∈ augIdeal R B := by
  apply (RingHom.mem_ker).mpr
  simp [piAug_apply]

private theorem counit_piAug (y : B) : Coalgebra.counit (R := R) (piAug R B y) = 0 := by
  simpa using (RingHom.mem_ker).mp (piAug_mem (R := R) y)

private theorem piAug_algebraMap (r : R) : piAug R B (algebraMap R B r) = 0 := by
  rw [piAug_apply, Bialgebra.counit_algebraMap, sub_self]

private theorem free_and_finite_of_retract {S M : Type*} [CommRing S] [IsLocalRing S] [AddCommGroup M] [Module S M]
    [Module.Free S M] [Module.Finite S M] (N : Submodule S M) (rN : M →ₗ[S] N) (h : ∀ w : N, rN w = w) :
    Module.Free S N ∧ Module.Finite S N := by
  have hri : rN ∘ₗ N.subtype = LinearMap.id := LinearMap.ext h
  haveI : Module.Flat S N := Module.Flat.of_retract _ _ hri
  haveI : Module.Finite S N := Module.Finite.of_surjective rN fun w => ⟨N.subtype w, h w⟩
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

private theorem isCompl_one_aug :
    IsCompl (Submodule.span R {(1 : B)}) (augSub R B) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h1
    rw [mem_augSub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at h2
    rw [h2, zero_smul]
  · rw [Submodule.eq_top_iff']
    intro x
    have hx : x = Coalgebra.counit (R := R) x • (1 : B) + (x - Coalgebra.counit (R := R) x • (1 : B)) := by
      exact (add_sub_cancel _ _).symm
    rw [hx]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (1 : B))) ?_
    rw [mem_augSub, map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_self]

end Aug

section RankOne

variable {R : Type u} [CommRing R] [IsLocalRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
  [Module.Free R B] [Module.Finite R B]
variable {F : Type*} [Field F] [Fintype F]
variable {act : F → (B →ₐc[R] B)} (hone : ActOne act) (hmul : ActMul act) (hadd : ActAdd act)
variable (p r : ℕ) [Fact p.Prime] [NeZero r] (hF : Fintype.card F = p ^ r)
  (hq : IsUnit ((p ^ r : R) - 1))
  (χ : Fˣ →* Rˣ) (ι : F →+* IsLocalRing.ResidueField R) (hχ : ∀ l : Fˣ, IsLocalRing.residue R (χ l : R) = ι l)
  (hrank : Module.finrank R B = p ^ r)

private noncomputable def piece (j : ℕ) : Submodule R B := eig (rho hone hmul) (χ ^ j) ⊓ augSub R B

omit [IsLocalRing R] [NeZero r] in
include hF hq in

private theorem exists_cinv : ∃ c : R, c * (Nat.card Fˣ : R) = 1 := by
  classical
  refine ⟨((hq.unit⁻¹ : Rˣ) : R), ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_units, hF, Nat.cast_sub (Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)),
    Nat.cast_pow, Nat.cast_one]
  have h := hq.unit.inv_mul
  rwa [IsUnit.unit_spec] at h

private noncomputable def Qp [DecidableEq F] (c : R) (j : ℕ) : B →ₗ[R] B :=
  proj (rho hone hmul) c (χ ^ j) ∘ₗ piAug R B

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] in
private theorem Qp_apply [DecidableEq F] (c : R) (j : ℕ) (y : B) :
    Qp hone hmul χ c j y = proj (rho hone hmul) c (χ ^ j) (piAug R B y) := rfl

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] in
private theorem Qp_mem [DecidableEq F] (c : R) (j : ℕ) (y : B) : Qp hone hmul χ c j y ∈ piece hone hmul χ j := by
  refine Submodule.mem_inf.mpr ⟨proj_mem_eig _ _ _ _, ?_⟩
  rw [mem_augSub, Qp_apply, proj_apply, map_smul, map_sum]
  simp_rw [map_smul, rho_apply, counit_act, counit_piAug, smul_zero, Finset.sum_const_zero, smul_zero]

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] in
private theorem Qp_eq_self [DecidableEq F] {c : R} (hc : c * (Fintype.card Fˣ : R) = 1) {j : ℕ} {w : B}
    (hw : w ∈ piece hone hmul χ j) : Qp hone hmul χ c j w = w := by
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
  rw [Qp_apply, piAug_apply, (mem_augSub (R := R)).mp hw2, map_zero, sub_zero]
  exact proj_eq_self _ _ hc hw1

omit [Module.Free R B] [Module.Finite R B] [Fact (Nat.Prime p)] [NeZero r] in
include hF hχ in
private theorem Qp_eq_zero_of_ne [DecidableEq F] (c : R) {j j' : ℕ} (hj : j < p ^ r - 1) (hj' : j' < p ^ r - 1)
    (hne : j ≠ j') {w : B} (hw : w ∈ piece hone hmul χ j') : Qp hone hmul χ c j w = 0 := by
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
  rw [Qp_apply, piAug_apply, (mem_augSub (R := R)).mp hw2, map_zero, sub_zero]
  refine proj_eq_zero_of_ne _ _ hw1 ?_
  obtain ⟨l, hl⟩ := exists_isUnit_pow_sub_pow p r hF χ ι hχ hj hj' hne
  refine ⟨l, ?_⟩
  have e : ((((χ ^ j) l)⁻¹ * (χ ^ j') l : Rˣ) : R) - 1 =
      -(((((χ ^ j) l)⁻¹ : Rˣ) : R) * ((((χ ^ j) l : Rˣ) : R) - (((χ ^ j') l : Rˣ) : R))) := by
    rw [Units.val_mul, mul_sub, Units.inv_mul, neg_sub]
  rw [e]
  exact ((Units.isUnit _).mul hl).neg

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] in
private theorem Qp_algebraMap [DecidableEq F] (c : R) (j : ℕ) (r : R) : Qp hone hmul χ c j (algebraMap R B r) = 0 := by
  rw [Qp_apply, piAug_algebraMap, map_zero]

omit [Module.Free R B] [Module.Finite R B] [Fact (Nat.Prime p)] [NeZero r] in
include hF hχ in

private theorem sum_Qp [DecidableEq F] {c : R} (hc : c * (Fintype.card Fˣ : R) = 1) (b : B) :
    algebraMap R B (Coalgebra.counit (R := R) b) + ∑ j ∈ Finset.range (p ^ r - 1), Qp hone hmul χ c j b = b := by
  have hcard : Fintype.card Fˣ = p ^ r - 1 := by rw [Fintype.card_units, hF]
  have hsum := sum_proj_pow_eq_self (rho hone hmul) c hc χ (fun l hl => isUnit_chi_sub_one χ ι hχ hl) (piAug R B b)
  rw [hcard] at hsum
  simp_rw [Qp_apply]
  rw [hsum, piAug_apply]
  abel

omit [NeZero r] in
include hF hq in

private theorem piece_free (j : ℕ) : Module.Free R (piece hone hmul χ j) ∧ Module.Finite R (piece hone hmul χ j) := by
  classical
  obtain ⟨c, hc⟩ := exists_cinv p r hF hq
  rw [Nat.card_eq_fintype_card] at hc
  exact free_and_finite_of_retract (piece hone hmul χ j)
    (LinearMap.codRestrict _ (Qp hone hmul χ c j) (Qp_mem hone hmul χ c j))
    fun w => Subtype.ext (Qp_eq_self hone hmul χ hc w.2)

omit [NeZero r] in
include hq hχ hF in

private theorem finrank_eq_one_add_sum :
    Module.finrank R B = 1 + ∑ j ∈ Finset.range (p ^ r - 1), Module.finrank R (piece hone hmul χ j) := by
  classical
  obtain ⟨c, hc⟩ := exists_cinv p r hF hq
  rw [Nat.card_eq_fintype_card] at hc

  let N : Option (Fin (p ^ r - 1)) → Submodule R B := fun o =>
    o.elim (LinearMap.range (Algebra.linearMap R B)) (fun j => piece hone hmul χ j)
  let E : Option (Fin (p ^ r - 1)) → (B →ₗ[R] B) := fun o =>
    o.elim (Algebra.linearMap R B ∘ₗ Coalgebra.counit) (fun j => Qp hone hmul χ c j)
  have hEfix : ∀ o, ∀ x ∈ N o, E o x = x := by
    rintro (_ | j) x hx
    · obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hx
      simp [E, Algebra.linearMap_apply, Bialgebra.counit_algebraMap]
    · exact Qp_eq_self hone hmul χ hc hx
  have hEkill : ∀ o o', o ≠ o' → ∀ x ∈ N o', E o x = 0 := by
    rintro (_ | j) (_ | j') hne x hx
    · exact absurd rfl hne
    · obtain ⟨-, hx2⟩ := Submodule.mem_inf.mp hx
      simp [E, (mem_augSub (R := R)).mp hx2]
    · obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hx
      exact Qp_algebraMap hone hmul χ c j s
    · exact Qp_eq_zero_of_ne hone hmul p r hF χ ι hχ c j.isLt j'.isLt
        (fun h => hne (congrArg some (Fin.ext h))) hx
  have hind : iSupIndep N := by
    rw [iSupIndep_def]
    intro o
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 : E o x = x := hEfix o x hx
    have hle : (⨆ o', ⨆ (_ : o' ≠ o), N o') ≤ LinearMap.ker (E o) :=
      iSup_le fun o' => iSup_le fun hne' => fun y hy => LinearMap.mem_ker.mpr (hEkill o o' (Ne.symm hne') y hy)
    have h2 : E o x = 0 := LinearMap.mem_ker.mp (hle hx')
    rw [← h1, h2]
  have htop : iSup N = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro b
    rw [← sum_Qp hone hmul p r hF χ ι hχ hc b]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j hj => ?_)
    · exact Submodule.mem_iSup_of_mem none (LinearMap.mem_range_self (Algebra.linearMap R B) _)
    · exact Submodule.mem_iSup_of_mem (some ⟨j, Finset.mem_range.mp hj⟩) (Qp_mem hone hmul χ c j b)
  have hint : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N).mpr ⟨hind, htop⟩

  have hinj : Function.Injective (Algebra.linearMap R B) := fun s s' h => by
    simpa [Algebra.linearMap_apply, Bialgebra.counit_algebraMap] using congrArg (Coalgebra.counit (R := R) (A := B)) h
  let eN : R ≃ₗ[R] N none := LinearEquiv.ofInjective (Algebra.linearMap R B) hinj
  haveI : ∀ o, Module.Free R (N o) := by
    rintro (_ | j)
    · exact Module.Free.of_equiv eN
    · exact (piece_free hone hmul p r hF hq χ j).1
  haveI : ∀ o, Module.Finite R (N o) := by
    rintro (_ | j)
    · exact Module.Finite.equiv eN
    · exact (piece_free hone hmul p r hF hq χ j).2
  have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint
  rw [← e.finrank_eq, Module.finrank_directSum, Fintype.sum_option, ← eN.finrank_eq, Module.finrank_self]
  change 1 + ∑ i : Fin (p ^ r - 1), Module.finrank R (piece hone hmul χ (i : ℕ)) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => Module.finrank R (piece hone hmul χ j)) (p ^ r - 1)]

variable (L : Type w) [Field L] [Algebra R L] (hpts : Nat.card (B →ₐ[R] L) = p ^ r)

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] in

private theorem linearIndependent_eval (K : Type*) [Field K] [Algebra R K] {ι : Type*} [Fintype ι]
    (bB : Module.Basis ι R B) (hK : Nat.card (B →ₐ[R] K) = Fintype.card ι) :
    LinearIndependent K (fun i : ι => fun f : B →ₐ[R] K => f (bB i)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact linearIndependent_empty_type
  haveI : Finite (B →ₐ[R] K) := Nat.finite_of_card_ne_zero (by rw [hK]; exact Fintype.card_ne_zero)
  haveI := Fintype.ofFinite (B →ₐ[R] K)
  have hD := linearIndependent_algHom_toLinearMap R B K
  have hrows : LinearIndependent K (fun f : B →ₐ[R] K => fun i : ι => f (bB i)) := by
    have h := hD.map' ((bB.constr K).symm : (B →ₗ[R] K) ≃ₗ[K] (ι → K)).toLinearMap (LinearEquiv.ker _)
    convert h using 1
    rfl
    rfl
    rfl
  have hcard : Fintype.card (B →ₐ[R] K) = Fintype.card ι := by rw [← Nat.card_eq_fintype_card, hK]
  let σ : (B →ₐ[R] K) ≃ ι := Fintype.equivOfCardEq hcard
  let A : Matrix ι ι K := fun i' i => (σ.symm i') (bB i)
  have hArows : LinearIndependent K A.row := hrows.comp σ.symm σ.symm.injective
  have hAcols : LinearIndependent K A.col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr (Matrix.linearIndependent_rows_iff_isUnit.mp hArows)
  have h := hAcols.map' (LinearEquiv.funCongrLeft K K σ).toLinearMap (LinearEquiv.ker _)
  convert h using 1
  all_goals try rfl
  all_goals (funext i; funext f; simp [A, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Matrix.col_apply])

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] in
include hone hmul hadd hF in

private theorem exists_orbit_bijection (K : Type*) [Field K] [Algebra R K]
    (hK : Nat.card (B →ₐ[R] K) = p ^ r) :
    ∃ f₀ : B →ₐ[R] K, f₀ ≠ onePt R B K ∧ Function.Injective (fun a : Fˣ => psmul act (a : F) f₀) ∧
      ∀ f : B →ₐ[R] K, f ≠ onePt R B K → ∃ a : Fˣ, psmul act (a : F) f₀ = f := by
  classical
  have hp : p.Prime := Fact.out
  have hq0 : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  haveI : Finite (B →ₐ[R] K) := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  haveI := Fintype.ofFinite (B →ₐ[R] K)
  have hcard : Fintype.card (B →ₐ[R] K) = p ^ r := by rw [← Nat.card_eq_fintype_card, hK]
  have h2 : 1 < Fintype.card (B →ₐ[R] K) := by rw [hcard]; exact Nat.one_lt_pow (NeZero.ne r) hp.one_lt
  obtain ⟨f₀, hf₀⟩ := Fintype.exists_ne_of_one_lt_card h2 (onePt R B K)
  obtain ⟨hinj, hne⟩ := psmul_injective_of_ne hone hmul hadd hf₀
  refine ⟨f₀, hf₀, hinj, fun f hf => ?_⟩
  let g : Option Fˣ → (B →ₐ[R] K) := fun o => o.elim (onePt R B K) (fun a => psmul act (a : F) f₀)
  have hg : Function.Injective g := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exact absurd h.symm (hne b)
    · exact absurd h (hne a)
    · exact congrArg some (hinj h)
  have hcardO : Fintype.card (Option Fˣ) = Fintype.card (B →ₐ[R] K) := by
    rw [Fintype.card_option, Fintype.card_units, hF, hcard, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
  have hsurj : Function.Surjective g := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcardO⟩).2
  obtain ⟨(_ | a), ha⟩ := hsurj f
  · exact absurd ha.symm hf
  · exact ⟨a, ha⟩

include hadd hq hF hrank hpts in

private theorem finrank_piece_le_one (j : ℕ) : Module.finrank R (piece hone hmul χ j) ≤ 1 := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := exists_cinv p r hF hq
  rw [Nat.card_eq_fintype_card] at hc
  haveI := (piece_free hone hmul p r hF hq χ j).1
  haveI := (piece_free hone hmul p r hF hq χ j).2
  haveI : Finite (B →ₐ[R] L) := Nat.finite_of_card_ne_zero (by rw [hpts]; exact pow_ne_zero r hp.ne_zero)

  set N := piece hone hmul χ j with hN
  let rQ : B →ₗ[R] N := LinearMap.codRestrict _ (Qp hone hmul χ c j) (Qp_mem hone hmul χ c j)
  have hrQ : ∀ w : N, rQ w = w := fun w => Subtype.ext (Qp_eq_self hone hmul χ hc w.2)
  have hcompl : IsCompl N (LinearMap.ker rQ) := LinearMap.isCompl_of_proj hrQ
  have hCfree := free_and_finite_of_retract (LinearMap.ker rQ)
    (LinearMap.codRestrict _ (LinearMap.id - N.subtype ∘ₗ rQ) fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        map_sub, hrQ, sub_self])
    fun w => Subtype.ext (by simp [LinearMap.mem_ker.mp w.2])
  haveI := hCfree.1
  haveI := hCfree.2
  let bN := Module.Free.chooseBasis R N
  let bC := Module.Free.chooseBasis R (LinearMap.ker rQ)
  let bB := (bN.prod bC).map (Submodule.prodEquivOfIsCompl (p := N) (q := LinearMap.ker rQ) hcompl)
  have hbB : ∀ k, bB (Sum.inl k) = (bN k : B) := fun k => by
    simp [bB, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

  have hcardι : Nat.card (B →ₐ[R] L) =
      Fintype.card (Module.Free.ChooseBasisIndex R N ⊕ Module.Free.ChooseBasisIndex R (LinearMap.ker rQ)) := by
    rw [hpts, ← hrank, Module.finrank_eq_card_basis bB]
  have hliN : LinearIndependent L (fun k => fun f : B →ₐ[R] L => f (bN k : B)) := by
    have h := (linearIndependent_eval L bB hcardι).comp Sum.inl Sum.inl_injective
    refine (linearIndependent_equiv' (Equiv.refl _) ?_).mp h
    funext k
    simp [hbB]

  obtain ⟨f₀, hf₀, hinj, horb⟩ := exists_orbit_bijection hone hmul hadd p r hF L hpts
  let w : (B →ₐ[R] L) → L := fun f =>
    if h : ∃ a : Fˣ, psmul act (a : F) f₀ = f then algebraMap R L (((χ ^ j) h.choose : Rˣ) : R) else 0
  have hw : ∀ k, (fun f : B →ₐ[R] L => f (bN k : B)) = (f₀ (bN k : B)) • w := by
    intro k
    funext f
    simp only [Pi.smul_apply, smul_eq_mul, w]
    by_cases hf : f = onePt R B L
    · subst hf
      have hy : Coalgebra.counit (R := R) (bN k : B) = 0 :=
        (mem_augSub (R := R)).mp (Submodule.mem_inf.mp (bN k).2).2
      have hno : ¬ ∃ a : Fˣ, psmul act (a : F) f₀ = onePt R B L :=
        fun ⟨a, ha⟩ => (psmul_injective_of_ne hone hmul hadd hf₀).2 a ha
      rw [dif_neg hno, mul_zero]
      change algebraMap R L (Coalgebra.counit (R := R) (bN k : B)) = 0
      rw [hy, map_zero]
    · obtain ⟨a, rfl⟩ := horb f hf
      have hex : ∃ a' : Fˣ, psmul act (a' : F) f₀ = psmul act (a : F) f₀ := ⟨a, rfl⟩
      rw [dif_pos hex, hinj hex.choose_spec, psmul_apply]
      have hy1 := (Submodule.mem_inf.mp (bN k).2).1
      have e : act (a : F) (bN k : B) = (((χ ^ j) a : Rˣ) : R) • (bN k : B) := (mem_eig _).mp hy1 a
      rw [e, Algebra.smul_def, map_mul, AlgHom.commutes, mul_comm]

  have h1 := linearIndependent_iff_card_eq_finrank_span.mp hliN
  have h2 : Submodule.span L (Set.range fun k => fun f : B →ₐ[R] L => f (bN k : B)) ≤ Submodule.span L {w} := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    dsimp only
    rw [hw k]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have h3 : Module.finrank L (Submodule.span L ({w} : Set ((B →ₐ[R] L) → L))) ≤ 1 := by
    simpa using finrank_span_le_card ({w} : Set ((B →ₐ[R] L) → L))
  calc Module.finrank R N = Fintype.card (Module.Free.ChooseBasisIndex R N) := Module.finrank_eq_card_chooseBasisIndex R N
    _ = Module.finrank L (Submodule.span L (Set.range fun k => fun f : B →ₐ[R] L => f (bN k : B))) := h1
    _ ≤ Module.finrank L (Submodule.span L ({w} : Set ((B →ₐ[R] L) → L))) := Submodule.finrank_mono h2
    _ ≤ 1 := h3

include hadd hq ι hχ hF hrank hpts in

private theorem exists_gen_piece :
    ∃ Y : ℕ → B, ∀ j, j < p ^ r - 1 →
      Y j ∈ piece hone hmul χ j ∧ (∀ y ∈ piece hone hmul χ j, ∃ c : R, y = c • Y j) ∧ (∀ c : R, c • Y j = 0 → c = 0) := by
  classical
  have hp : p.Prime := Fact.out
  have hd1 : ∀ j, Module.finrank R (piece hone hmul χ j) ≤ 1 := fun j =>
    finrank_piece_le_one (hone := hone) (hmul := hmul) (hadd := hadd) (p := p) (r := r) (hF := hF) (hq := hq)
      (χ := χ) (hrank := hrank) (L := L) (hpts := hpts) j
  have hsum := finrank_eq_one_add_sum (hone := hone) (hmul := hmul) (p := p) (r := r) (hF := hF) (hq := hq)
    (χ := χ) (ι := ι) (hχ := hχ) (B := B)
  have hall : ∀ j ∈ Finset.range (p ^ r - 1), Module.finrank R (piece hone hmul χ j) = 1 := by
    have hle : ∀ j ∈ Finset.range (p ^ r - 1), Module.finrank R (piece hone hmul χ j) ≤ 1 := fun j _ => hd1 j
    refine (Finset.sum_eq_sum_iff_of_le hle).mp ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    have e : 1 + ∑ j ∈ Finset.range (p ^ r - 1), Module.finrank R (piece hone hmul χ j) = 1 + (p ^ r - 1) := by
      rw [← hsum, hrank, Nat.add_sub_cancel' (Nat.one_le_pow _ _ hp.pos)]
    omega
  have hY : ∀ j, j < p ^ r - 1 → ∃ y : B, y ∈ piece hone hmul χ j ∧
      (∀ y' ∈ piece hone hmul χ j, ∃ c : R, y' = c • y) ∧ (∀ c : R, c • y = 0 → c = 0) := by
    intro j hj
    haveI := (piece_free hone hmul p r hF hq χ j).1
    haveI := (piece_free hone hmul p r hF hq χ j).2
    let b := Module.Free.chooseBasis R (piece hone hmul χ j)
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex R (piece hone hmul χ j)) = 1 := by
      rw [← Module.finrank_eq_card_chooseBasisIndex]
      exact hall j (Finset.mem_range.mpr hj)
    obtain ⟨k, hk⟩ := Fintype.card_eq_one_iff.mp hcard
    have hsingle : ∀ g : Module.Free.ChooseBasisIndex R (piece hone hmul χ j) → R,
        ∑ i, g i • b i = g k • b k := fun g =>
      Fintype.sum_eq_single k (fun k' hk' => absurd (hk k') hk')
    refine ⟨(b k : B), (b k).2, fun y' hy' => ?_, fun c hc => ?_⟩
    · refine ⟨b.repr ⟨y', hy'⟩ k, ?_⟩
      have e := b.sum_repr ⟨y', hy'⟩
      rw [hsingle] at e
      have e' := congrArg Subtype.val e
      simpa using e'.symm
    · have h0 : c • b k = 0 := Subtype.ext (by simpa using hc)
      have h1 : ∑ i, (fun _ => c) i • b i = 0 := by rw [hsingle]; exact h0
      exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun _ => c) h1 k
  choose! Y hY' using hY
  exact ⟨Y, hY'⟩

end RankOne

section MulLaw

variable {R : Type u} [CommRing R] [IsLocalRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
variable {F : Type*} [Field F] [Fintype F]
variable {act : F → (B →ₐc[R] B)} (hone : ActOne act) (hmul : ActMul act)
variable (p r : ℕ) [Fact p.Prime] [NeZero r] (χ : Fˣ →* Rˣ)

omit [IsLocalRing R] [Fintype F] in

private theorem mul_mem_piece {j j' : ℕ} {a b : B} (ha : a ∈ piece hone hmul χ j) (hb : b ∈ piece hone hmul χ j') :
    a * b ∈ piece hone hmul χ (j + j') := by
  have ha' := Submodule.mem_inf.mp (show a ∈ eig (rho hone hmul) (χ ^ j) ⊓ augSub R B from ha)
  have hb' := Submodule.mem_inf.mp (show b ∈ eig (rho hone hmul) (χ ^ j') ⊓ augSub R B from hb)
  show a * b ∈ eig (rho hone hmul) (χ ^ (j + j')) ⊓ augSub R B
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    convert mul_mem_eig (rho hone hmul) ha'.1 hb'.1 using 2
    exact pow_add χ j j'
  · rw [mem_augSub] at *
    rw [← Bialgebra.counitAlgHom_apply (R := R), map_mul, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      ha'.2, zero_mul]

omit [IsLocalRing R] [Fintype F] [NeZero r] in

private theorem pow_p_mem_piece_succ {i : ℕ} {x : B}
    (hx : x ∈ piece hone hmul χ (p ^ i)) : x ^ p ∈ piece hone hmul χ (p ^ (i + 1)) := by
  have key : ∀ n : ℕ, x ^ (n + 1) ∈ piece hone hmul χ (p ^ i * (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ, show p ^ i * (n + 1 + 1) = p ^ i * (n + 1) + p ^ i by ring]
      exact mul_mem_piece hone hmul χ ih hx
  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel (Nat.Prime.one_le Fact.out)).symm
  have := key (p - 1)
  rw [← hp1, ← pow_succ] at this
  exact this

omit [IsLocalRing R] [Fintype F] [Fact (Nat.Prime p)] in

private theorem chi_pow_fin_succ (hχr : χ ^ (p ^ r) = χ) (i : Fin r) :
    χ ^ p ^ ((i + 1 : Fin r) : ℕ) = χ ^ p ^ ((i : ℕ) + 1) := by
  have hv : ((i + 1 : Fin r) : ℕ) = ((i : ℕ) + 1) % r := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hv]
  rcases Nat.lt_or_ge ((i : ℕ) + 1) r with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have hi : (i : ℕ) + 1 = r := le_antisymm (Nat.succ_le_of_lt i.isLt) h
    rw [hi, Nat.mod_self, pow_zero]
    exact (pow_one χ).trans hχr.symm

end MulLaw

section Gen

variable {R : Type u} [CommRing R] [IsLocalRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
  [Module.Free R B] [Module.Finite R B]
variable {F : Type*} [Field F] [Fintype F]
variable {act : F → (B →ₐc[R] B)} (hone : ActOne act) (hmul : ActMul act) (hadd : ActAdd act)
variable (p r : ℕ) [Fact p.Prime] [NeZero r] (hF : Fintype.card F = p ^ r)
  (χ : Fˣ →* Rˣ) (ι : F →+* IsLocalRing.ResidueField R) (hχ : ∀ l : Fˣ, IsLocalRing.residue R (χ l : R) = ι l)

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] [Fintype F] in
include hadd in

private theorem act_add_sub_mem_sq {x : B} (hx : x ∈ augIdeal R B) (a b : F) :
    act (a + b) x - act a x - act b x ∈ (augIdeal R B) ^ 2 := by

  have hεx : Coalgebra.counit (R := R) x = 0 := by simpa using (RingHom.mem_ker).mp hx
  have hfour : ∀ t : B ⊗[R] B, TensorProduct.map (piAug R B) (piAug R B) t =
      t - TensorProduct.map (Algebra.linearMap R B ∘ₗ Coalgebra.counit) LinearMap.id t
        - TensorProduct.map LinearMap.id (Algebra.linearMap R B ∘ₗ Coalgebra.counit) t
        + TensorProduct.map (Algebra.linearMap R B ∘ₗ Coalgebra.counit)
            (Algebra.linearMap R B ∘ₗ Coalgebra.counit) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul y z =>
      simp only [TensorProduct.map_tmul, piAug_apply, LinearMap.id_apply, LinearMap.comp_apply,
        Algebra.linearMap_apply, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
    | add y z hy hz => simp only [map_add, hy, hz]; abel
  have e1 : TensorProduct.map (Algebra.linearMap R B ∘ₗ Coalgebra.counit) LinearMap.id (Coalgebra.comul (R := R) x)
      = (1 : B) ⊗ₜ[R] x := by
    show LinearMap.rTensor B (Algebra.linearMap R B ∘ₗ Coalgebra.counit) (Coalgebra.comul (R := R) x) = _
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, LinearMap.rTensor_tmul]
    simp
  have e2 : TensorProduct.map LinearMap.id (Algebra.linearMap R B ∘ₗ Coalgebra.counit) (Coalgebra.comul (R := R) x)
      = x ⊗ₜ[R] (1 : B) := by
    show LinearMap.lTensor B (Algebra.linearMap R B ∘ₗ Coalgebra.counit) (Coalgebra.comul (R := R) x) = _
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul, LinearMap.lTensor_tmul]
    simp
  have e3 : TensorProduct.map (Algebra.linearMap R B ∘ₗ Coalgebra.counit) (Algebra.linearMap R B ∘ₗ Coalgebra.counit)
      (Coalgebra.comul (R := R) x) = 0 := by
    have e0 : TensorProduct.map Coalgebra.counit Coalgebra.counit (Coalgebra.comul (R := R) x) = (0 : R ⊗[R] R) := by
      rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul,
        LinearMap.rTensor_tmul, hεx, TensorProduct.zero_tmul]
    rw [TensorProduct.map_comp, LinearMap.comp_apply, e0, map_zero]
  have hcomul : Coalgebra.comul (R := R) x = TensorProduct.map (piAug R B) (piAug R B) (Coalgebra.comul (R := R) x)
      + (1 : B) ⊗ₜ[R] x + x ⊗ₜ[R] (1 : B) := by
    rw [hfour, e1, e2, e3]
    abel

  have h1 : act (a + b) x = LinearMap.mul' R B (TensorProduct.map (act a : B →ₐ[R] B).toLinearMap
      (act b : B →ₐ[R] B).toLinearMap (Coalgebra.comul (R := R) x)) := by
    have := LinearMap.congr_fun (hadd a b) x
    simpa using this

  have hrem : ∀ t : B ⊗[R] B, LinearMap.mul' R B (TensorProduct.map (act a : B →ₐ[R] B).toLinearMap
      (act b : B →ₐ[R] B).toLinearMap (TensorProduct.map (piAug R B) (piAug R B) t)) ∈ (augIdeal R B) ^ 2 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul y z =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply]
      rw [pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · apply (RingHom.mem_ker).mpr
        rw [Bialgebra.counitAlgHom_apply, BialgHom.coe_toAlgHom, counit_act]
        simpa using (RingHom.mem_ker).mp (piAug_mem (R := R) y)
      · apply (RingHom.mem_ker).mpr
        rw [Bialgebra.counitAlgHom_apply, BialgHom.coe_toAlgHom, counit_act]
        simpa using (RingHom.mem_ker).mp (piAug_mem (R := R) z)
    | add y z hy hz =>
      simp only [map_add]
      exact Ideal.add_mem _ hy hz
  have hfin : act (a + b) x - act a x - act b x = LinearMap.mul' R B (TensorProduct.map
      (act a : B →ₐ[R] B).toLinearMap (act b : B →ₐ[R] B).toLinearMap
        (TensorProduct.map (piAug R B) (piAug R B) (Coalgebra.comul (R := R) x))) := by
    rw [h1]
    conv_lhs => rw [hcomul]
    simp only [map_add, TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, BialgHom.coe_toAlgHom,
      map_one, one_mul, mul_one]
    abel
  rw [hfin]
  exact hrem _

omit [IsLocalRing R] [Module.Free R B] [Module.Finite R B] in
include hone hadd hF in

private theorem p_smul_mem_sq {x : B} (hx : x ∈ augIdeal R B) : (p : B) * x ∈ (augIdeal R B) ^ 2 := by
  haveI := charP_of_card p r hF
  have hcx : Coalgebra.counit (R := R) x = 0 := by
    simpa using (RingHom.mem_ker).mp hx
  have hx0 : act 0 x = 0 := by
    rw [act_zero_eq hadd, hcx, map_zero]
  have key : ∀ n : ℕ, act (n : F) x - (n : B) * x ∈ (augIdeal R B) ^ 2 := by
    intro n
    induction n with
    | zero => simp [hx0]
    | succ n ih =>
      have h1 := act_add_sub_mem_sq hadd hx (n : F) 1
      have hone1 : act 1 x = x := by
        rw [hone]
        rfl
      rw [hone1] at h1
      have e : act ((n + 1 : ℕ) : F) x - ((n + 1 : ℕ) : B) * x
          = (act ((n : F) + 1) x - act (n : F) x - x) + (act (n : F) x - (n : B) * x) := by
        push_cast
        ring
      rw [e]
      exact Ideal.add_mem _ h1 ih
  have hp := key p
  rw [CharP.cast_eq_zero F p, hx0, zero_sub] at hp
  exact (Ideal.neg_mem_iff _).mp hp

omit [Module.Free R B] [Module.Finite R B] in
include hadd hF ι hχ in

private theorem piece_le_sq_sup_of_not_fundamental {j : ℕ} (hj1 : 1 ≤ j)
    (hnf : ∀ i : ℕ, i < r → χ ^ j ≠ χ ^ (p ^ i)) :
    piece hone hmul χ j ≤ ((augIdeal R B) ^ 2).restrictScalars R ⊔
      (IsLocalRing.maximalIdeal R) • (augIdeal R B).restrictScalars R := by
  classical
  intro x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hεx : Coalgebra.counit (R := R) x = 0 := (mem_augSub (R := R)).mp hx2
  have hxI : x ∈ augIdeal R B := (RingHom.mem_ker).mpr (by simpa using hεx)

  have hna : ¬ ∀ a b : F, ι (a + b) ^ j = ι a ^ j + ι b ^ j := fun H => by
    obtain ⟨i, hi, h⟩ := exists_pow_eq_of_additive (p := p) (r := r) (hF := hF) (χ := χ) (ι := ι) hj1 H
    exact hnf i hi (MonoidHom.ext h)
  push Not at hna
  obtain ⟨a, b, hab⟩ := hna

  let ch : F → R := fun c => if hc : c = 0 then 0 else (((χ (Units.mk0 c hc)) : Rˣ) : R) ^ j
  have hch_act : ∀ c : F, act c x = ch c • x := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp only [ch, dif_pos rfl, zero_smul]
      rw [act_zero_eq hadd, hεx, map_zero]
    · simp only [ch, dif_neg hc]
      have e := (mem_eig _).mp hx1 (Units.mk0 c hc)
      rw [rho_apply, Units.val_mk0, MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at e
      exact e
  have hch_res : ∀ c : F, IsLocalRing.residue R (ch c) = ι c ^ j := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp only [ch, dif_pos rfl, map_zero]
      rw [zero_pow (Nat.one_le_iff_ne_zero.mp hj1)]
    · simp only [ch, dif_neg hc, map_pow, hχ, Units.val_mk0]
  have hs : IsUnit (ch (a + b) - ch a - ch b) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    apply hab
    have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub, map_sub, hch_res, hch_res, hch_res, sub_sub, sub_eq_zero] at h0
    exact h0
  have hsx : (ch (a + b) - ch a - ch b) • x = act (a + b) x - act a x - act b x := by
    rw [hch_act, hch_act, hch_act, sub_smul, sub_smul]
  have hmem2 : (ch (a + b) - ch a - ch b) • x ∈ (augIdeal R B) ^ 2 := by
    rw [hsx]
    exact act_add_sub_mem_sq hadd hxI a b
  have hx' : x = ((hs.unit⁻¹ : Rˣ) : R) • ((ch (a + b) - ch a - ch b) • x) := by
    rw [smul_smul, IsUnit.val_inv_mul, one_smul]
  rw [hx']
  exact Submodule.mem_sup_left (Submodule.smul_mem _ _ hmem2)

omit [Module.Free R B] [Module.Finite R B] in
include hadd hF hχ in

private theorem aug_le_span_sup (hq : IsUnit ((p ^ r : R) - 1)) (X : Fin r → B)
    (hXgen : ∀ i : Fin r, ∀ y ∈ piece hone hmul χ (p ^ (i : ℕ)), ∃ c : R, y = c • X i) :
    augSub R B ≤ Submodule.span R (Set.range X) ⊔ ((augIdeal R B) ^ 2).restrictScalars R ⊔
      (IsLocalRing.maximalIdeal R) • (augIdeal R B).restrictScalars R := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := exists_cinv p r hF hq
  rw [Nat.card_eq_fintype_card] at hc
  intro x hx
  have hdec := sum_Qp hone hmul p r hF χ ι hχ hc x
  rw [(mem_augSub (R := R)).mp hx, map_zero, zero_add] at hdec
  rw [← hdec]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hjlt := Finset.mem_range.mp hj

  obtain ⟨j', hj'1, -, hpiece⟩ : ∃ j', 1 ≤ j' ∧ j' ≤ p ^ r - 1 ∧ piece hone hmul χ j = piece hone hmul χ j' := by
    by_cases hj0 : j = 0
    · have h2 : 1 < p ^ r := Nat.one_lt_pow (NeZero.ne r) hp.one_lt
      refine ⟨p ^ r - 1, by omega, le_rfl, ?_⟩
      subst hj0
      show eig _ (χ ^ 0) ⊓ _ = eig _ (χ ^ (p ^ r - 1)) ⊓ _
      rw [show χ ^ 0 = 1 from MonoidHom.ext fun l => by rw [MonoidHom.pow_apply, pow_zero, MonoidHom.one_apply],
        chi_pow_card_sub_one p r hF χ]
    · exact ⟨j, Nat.one_le_iff_ne_zero.mpr hj0, by omega, rfl⟩
  have hmem : Qp hone hmul χ c j x ∈ piece hone hmul χ j' := hpiece ▸ Qp_mem hone hmul χ c j x
  by_cases hfund : ∃ i : ℕ, i < r ∧ χ ^ j' = χ ^ (p ^ i)
  · obtain ⟨i, hi, hχeq⟩ := hfund
    have hmem' : Qp hone hmul χ c j x ∈ piece hone hmul χ (p ^ ((⟨i, hi⟩ : Fin r) : ℕ)) := by
      show _ ∈ eig _ (χ ^ (p ^ i)) ⊓ _
      rw [← hχeq]
      exact hmem
    obtain ⟨c', hc'⟩ := hXgen ⟨i, hi⟩ _ hmem'
    rw [hc']
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)))
  · push Not at hfund
    have hle3 : ((augIdeal R B) ^ 2).restrictScalars R ⊔ (IsLocalRing.maximalIdeal R) • (augIdeal R B).restrictScalars R ≤
        Submodule.span R (Set.range X) ⊔ ((augIdeal R B) ^ 2).restrictScalars R ⊔
          (IsLocalRing.maximalIdeal R) • (augIdeal R B).restrictScalars R :=
      sup_le_sup_right le_sup_right _
    exact hle3 (piece_le_sq_sup_of_not_fundamental (hone := hone) (hmul := hmul) (hadd := hadd) (p := p) (r := r)
      (hF := hF) (χ := χ) (ι := ι) (hχ := hχ) hj'1 hfund hmem)

omit [Module.Free R B] [NeZero r] in

private theorem adjoin_eq_top_of_aug_pow_le (X : Fin r → B) (hXI : ∀ i, X i ∈ augIdeal R B)
    (hle : augSub R B ≤ Submodule.span R (Set.range X) ⊔ ((augIdeal R B) ^ 2).restrictScalars R ⊔
      (IsLocalRing.maximalIdeal R) • (augIdeal R B).restrictScalars R)
    {N : ℕ} (hN : ((augIdeal R B) ^ N).restrictScalars R ≤ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R B)) :
    Algebra.adjoin R (Set.range X) = ⊤ := by
  classical

  let I : Ideal B := augIdeal R B
  let C : Submodule R B := Subalgebra.toSubmodule (Algebra.adjoin R (Set.range X))
  let M : Submodule R B := (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R B)
  have hXC : Submodule.span R (Set.range X) ≤ C := Submodule.span_le.mpr Algebra.subset_adjoin
  have hXI' : Submodule.span R (Set.range X) ≤ (I ^ 1).restrictScalars R := by
    rw [Submodule.span_le, pow_one]
    rintro _ ⟨i, rfl⟩
    exact hXI i
  have hmI : (IsLocalRing.maximalIdeal R) • (augIdeal R B).restrictScalars R ≤ M := Submodule.smul_mono le_rfl le_top
  have hMmul : ∀ (y : B), ∀ z ∈ M, y * z ∈ M := by
    intro y z hz
    have hz' : z ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R B)).restrictScalars R := by
      rw [← Ideal.smul_top_eq_map]; exact hz
    show y * z ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R B)
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_left _ y hz'
  have hCC : ∀ y ∈ C, ∀ z ∈ C, y * z ∈ C := fun y hy z hz => Subalgebra.mul_mem _ hy hz
  have hI2I : ∀ {z : B}, z ∈ I ^ 2 → z ∈ I := fun hz => Ideal.pow_le_self two_ne_zero hz

  have hbase : (I ^ 1).restrictScalars R ≤ (C ⊓ (I ^ 1).restrictScalars R) ⊔ (I ^ 2).restrictScalars R ⊔ M := by
    intro y hy
    have hy' : y ∈ augSub R B := by
      rw [← augIdeal_restrictScalars]
      simpa [pow_one] using hy
    exact (sup_le_sup (sup_le_sup (le_inf hXC hXI') le_rfl) hmI) (hle hy')

  have step : ∀ m : ℕ, 1 ≤ m →
      (I ^ m).restrictScalars R ≤ (C ⊓ (I ^ m).restrictScalars R) ⊔ (I ^ (m + 1)).restrictScalars R ⊔ M := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      intro y hy
      have hy' : y ∈ I ^ m * I := by rw [← pow_succ]; exact hy
      refine Submodule.mul_induction_on hy' (fun u hu v hv => ?_) (fun u v hu' hv' => Submodule.add_mem _ hu' hv')

      obtain ⟨w, hw, mu, hmu, rfl⟩ := Submodule.mem_sup.mp (ih hu)
      obtain ⟨cu, hcu, iu, hiu, rfl⟩ := Submodule.mem_sup.mp hw
      have hv1 : v ∈ (I ^ 1).restrictScalars R := by simpa [pow_one] using hv
      obtain ⟨w', hw', mv, hmv, rfl⟩ := Submodule.mem_sup.mp (hbase hv1)
      obtain ⟨cv, hcv, iv, hiv, rfl⟩ := Submodule.mem_sup.mp hw'
      obtain ⟨hcuC, hcuI⟩ := Submodule.mem_inf.mp hcu
      obtain ⟨hcvC, hcvI⟩ := Submodule.mem_inf.mp hcv
      have hcuI' : cu ∈ I ^ m := hcuI
      have hcvI' : cv ∈ I := by simpa [pow_one] using (hcvI : cv ∈ I ^ 1)
      have hiuI : iu ∈ I ^ (m + 1) := hiu
      have hivI : iv ∈ I ^ 2 := hiv

      have h1 : cu * cv ∈ C ⊓ (I ^ (m + 1)).restrictScalars R :=
        Submodule.mem_inf.mpr ⟨hCC _ hcuC _ hcvC, by
          show cu * cv ∈ I ^ (m + 1)
          rw [pow_succ]
          exact Ideal.mul_mem_mul hcuI' hcvI'⟩
      have h2 : cu * iv + iu * (cv + iv) ∈ (I ^ (m + 1 + 1)).restrictScalars R := by
        show cu * iv + iu * (cv + iv) ∈ I ^ (m + 1 + 1)
        refine Ideal.add_mem _ ?_ ?_
        · rw [show m + 1 + 1 = m + 2 by ring, pow_add]
          exact Ideal.mul_mem_mul hcuI' hivI
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hiuI (Ideal.add_mem _ hcvI' (hI2I hivI))
      have h3 : (cu + iu) * mv + mu * (cv + iv + mv) ∈ M :=
        Submodule.add_mem _ (hMmul _ _ hmv) (by rw [mul_comm]; exact hMmul _ _ hmu)
      have e : (cu + iu + mu) * (cv + iv + mv) = cu * cv + (cu * iv + iu * (cv + iv)) + ((cu + iu) * mv + mu * (cv + iv + mv)) := by
        ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left h1))
        (Submodule.mem_sup_left (Submodule.mem_sup_right h2))) (Submodule.mem_sup_right h3)

  have tele : ∀ n : ℕ, 2 ≤ n → (I ^ 1).restrictScalars R ≤ C ⊔ (I ^ n).restrictScalars R ⊔ M := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hbase.trans (sup_le_sup (sup_le_sup inf_le_left le_rfl) le_rfl)
    | succ n hn ih =>
      refine ih.trans (sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) le_sup_right)
      exact (step n (by omega)).trans (sup_le_sup (sup_le_sup inf_le_left le_rfl) le_rfl)

  have hIN : (I ^ (N + 2)).restrictScalars R ≤ M := by
    intro y hy
    exact hN (Ideal.pow_le_pow_right (by omega) hy)
  have hICM : (I ^ 1).restrictScalars R ≤ C ⊔ M :=
    (tele (N + 2) (by omega)).trans (sup_le (sup_le le_sup_left (hIN.trans le_sup_right)) le_sup_right)

  have htop : (⊤ : Submodule R B) ≤ C ⊔ M := by
    intro b _
    have hb : b = algebraMap R B (Coalgebra.counit (R := R) b) + piAug R B b := by
      rw [piAug_apply]; abel
    rw [hb]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (hICM ?_)
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Subalgebra.one_mem _)
    · show piAug R B b ∈ I ^ 1
      rw [pow_one]
      exact piAug_mem (R := R) b

  have hjac : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hfg : (⊤ : Submodule R B).FG := Module.Finite.fg_top
  have := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac htop
  exact Algebra.toSubmodule_eq_top.mp (eq_top_iff.mpr this)

omit [NeZero r] in
include hone hmul hadd hF in

private theorem one_or_card_points (hrank : Module.finrank R B = p ^ r) (K : Type*) [Field K] [IsAlgClosed K]
    [Algebra R K] [Algebra (IsLocalRing.ResidueField R) K] [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    (Nat.card (B →ₐ[R] K) = 1 ∧ ∃ N : ℕ, ((augIdeal R B) ^ N).restrictScalars R ≤
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R B)) ∨ Nat.card (B →ₐ[R] K) = p ^ r := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hfin, hle⟩ := finite_and_card_algHom_le (R := R) (B := B) K
  rw [hrank] at hle
  by_cases hex : ∃ f₀ : B →ₐ[R] K, f₀ ≠ onePt R B K
  ·
    right
    obtain ⟨f₀, hf₀⟩ := hex
    obtain ⟨hinj, hne⟩ := psmul_injective_of_ne hone hmul hadd hf₀
    haveI := Fintype.ofFinite (B →ₐ[R] K)
    let g : Option Fˣ → (B →ₐ[R] K) := fun o => o.elim (onePt R B K) (fun a => psmul act (a : F) f₀)
    have hg : Function.Injective g := by
      rintro (_ | a) (_ | b) h
      · rfl
      · exact absurd h.symm (hne b)
      · exact absurd h (hne a)
      · exact congrArg some (hinj h)
    have h1 := Fintype.card_le_of_injective g hg
    rw [Fintype.card_option, Fintype.card_units, hF, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)] at h1
    rw [Nat.card_eq_fintype_card] at hle ⊢
    exact le_antisymm hle h1
  ·
    left
    push Not at hex
    refine ⟨?_, ?_⟩
    · rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun f g => by rw [hex f, hex g]⟩, ⟨onePt R B K⟩⟩
    let I : Ideal B := augIdeal R B
    let J : Ideal B := (IsLocalRing.maximalIdeal R).map (algebraMap R B)

    have hIP : ∀ P : Ideal B, P.IsPrime → J ≤ P → I ≤ P := by
      intro P hP hJP
      haveI := hP
      have hcomap : P.comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
        ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
          (Ideal.map_le_iff_le_comap.mp hJP)).symm
      haveI hPmax : P.IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (by rw [hcomap]; infer_instance)
      letI : Field (B ⧸ P) := Ideal.Quotient.field P
      let φk : IsLocalRing.ResidueField R →+* B ⧸ P :=
        Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ((Ideal.Quotient.mk P).comp (algebraMap R B))
          (fun a ha => by
            rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
            exact hJP (Ideal.mem_map_of_mem _ ha))
      letI : Algebra (IsLocalRing.ResidueField R) (B ⧸ P) := φk.toAlgebra
      haveI : IsScalarTower R (IsLocalRing.ResidueField R) (B ⧸ P) :=
        IsScalarTower.of_algebraMap_eq (fun a => rfl)
      haveI : Module.Finite (IsLocalRing.ResidueField R) (B ⧸ P) :=
        Module.Finite.of_restrictScalars_finite R _ _
      haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (B ⧸ P) := Algebra.IsAlgebraic.of_finite _ _
      haveI : FaithfulSMul (IsLocalRing.ResidueField R) (B ⧸ P) :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (IsLocalRing.ResidueField R) (B ⧸ P)).injective
      haveI : FaithfulSMul (IsLocalRing.ResidueField R) K :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (IsLocalRing.ResidueField R) K).injective
      let ψ : (B ⧸ P) →ₐ[IsLocalRing.ResidueField R] K := IsAlgClosed.lift
      let f : B →ₐ[R] K := (ψ.restrictScalars R).comp (Ideal.Quotient.mkₐ R P)
      have hf : f = onePt R B K := hex f
      intro x hx
      have hεx : Coalgebra.counit (R := R) x = 0 := by simpa using (RingHom.mem_ker).mp hx
      have hx0 : f x = 0 := by
        rw [hf]
        change algebraMap R K (Coalgebra.counit (R := R) x) = 0
        rw [hεx, map_zero]
      have hψx : ψ (Ideal.Quotient.mk P x) = 0 := hx0
      have h0 : Ideal.Quotient.mk P x = 0 := by
        apply ψ.toRingHom.injective
        rw [map_zero]
        exact hψx
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0

    have hIrad : I ≤ J.radical := by
      rw [Ideal.radical_eq_sInf]
      exact le_sInf fun P ⟨hJP, hP⟩ => hIP P hP hJP
    have hIfg : I.FG := by
      obtain ⟨-, hfinI⟩ := free_and_finite_of_retract (augSub R B)
        (LinearMap.codRestrict _ (piAug R B) fun y => (mem_augSub (R := R)).mpr (counit_piAug (R := R) y))
        fun w => Subtype.ext (by
          show piAug R B w = w
          rw [piAug_apply, (mem_augSub (R := R)).mp w.2, map_zero, sub_zero])
      haveI := hfinI
      obtain ⟨S, hS⟩ := (Submodule.fg_top _).mp (Module.Finite.fg_top (R := R) (M := augSub R B))
      refine ⟨S, le_antisymm ?_ ?_⟩
      · rw [Ideal.span_le]
        intro y hy
        have hy' : y ∈ augSub R B := hS ▸ Submodule.subset_span hy
        exact (RingHom.mem_ker).mpr (by simpa using (mem_augSub (R := R)).mp hy')
      · intro y hy
        have hy' : y ∈ augSub R B := (mem_augSub (R := R)).mpr (by simpa using (RingHom.mem_ker).mp hy)
        rw [← hS] at hy'
        exact Submodule.span_le_restrictScalars R B (S : Set B) hy'
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIrad hIfg
    refine ⟨n, fun y hy => ?_⟩
    rw [Ideal.smul_top_eq_map]
    exact hn hy

omit [Module.Free R B] [Module.Finite R B] in
include hone hmul hadd hF hχ in

private theorem adjoin_singleton_eq_top_of_card_points (hrank : Module.finrank R B = p ^ r) (K : Type*) [Field K]
    [Algebra R K] [Algebra (IsLocalRing.ResidueField R) K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (hK : Nat.card (B →ₐ[R] K) = p ^ r) {κ : Type*} [Fintype κ] (bB : Module.Basis κ R B) (i₀ : κ)
    (hx0 : bB i₀ ∈ piece hone hmul χ 1) :
    Algebra.adjoin R {bB i₀} = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite (B →ₐ[R] K) := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero r hp.ne_zero)
  haveI := Fintype.ofFinite (B →ₐ[R] K)
  have hcardκ : Fintype.card κ = p ^ r := by rw [← hrank, Module.finrank_eq_card_basis bB]
  have hcardpt : Fintype.card (B →ₐ[R] K) = Fintype.card κ := by rw [← Nat.card_eq_fintype_card, hK, hcardκ]
  let σ : (B →ₐ[R] K) ≃ κ := Fintype.equivOfCardEq hcardpt
  let τ : κ ≃ Fin (p ^ r) := Fintype.equivFinOfCardEq hcardκ

  let E : Matrix κ κ K := fun i' i => (σ.symm i') (bB i)
  have hE : IsUnit E := by
    have hD := linearIndependent_algHom_toLinearMap R B K
    have hrows : LinearIndependent K (fun f : B →ₐ[R] K => fun i : κ => f (bB i)) := by
      have h := hD.map' ((bB.constr K).symm : (B →ₗ[R] K) ≃ₗ[K] (κ → K)).toLinearMap (LinearEquiv.ker _)
      convert h using 1
      rfl
      rfl
      rfl
    exact Matrix.linearIndependent_rows_iff_isUnit.mp (hrows.comp σ.symm σ.symm.injective)

  obtain ⟨f₀, hf₀, hinj, horb⟩ := exists_orbit_bijection hone hmul hadd p r hF K hK
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx0
  have hεx : Coalgebra.counit (R := R) (bB i₀) = 0 := (mem_augSub (R := R)).mp hx2
  have hact : ∀ a : Fˣ, act (a : F) (bB i₀) = ((χ a : Rˣ) : R) • bB i₀ := fun a => by
    have e := (mem_eig _).mp hx1 a
    rw [rho_apply, MonoidHom.pow_apply, pow_one] at e
    exact e
  have hval1 : onePt R B K (bB i₀) = 0 := by
    change algebraMap R K (Coalgebra.counit (R := R) (bB i₀)) = 0
    rw [hεx, map_zero]
  have hvala : ∀ a : Fˣ, psmul act (a : F) f₀ (bB i₀) = algebraMap R K ((χ a : Rˣ) : R) * f₀ (bB i₀) := fun a => by
    rw [psmul_apply, hact, Algebra.smul_def, map_mul, AlgHom.commutes]
  have hχK : ∀ a : Fˣ, algebraMap R K ((χ a : Rˣ) : R) = algebraMap (IsLocalRing.ResidueField R) K (ι a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) K, ← hχ a]
    rfl
  have hχK0 : ∀ a : Fˣ, algebraMap R K ((χ a : Rˣ) : R) ≠ 0 := fun a => by
    rw [hχK]
    exact (map_ne_zero _).mpr ((map_ne_zero ι).mpr a.ne_zero)

  have hf0x : f₀ (bB i₀) ≠ 0 := by
    intro h0
    have hall : ∀ f : B →ₐ[R] K, f (bB i₀) = 0 := by
      intro f
      by_cases hf : f = onePt R B K
      · rw [hf]; exact hval1
      · obtain ⟨a, rfl⟩ := horb f hf
        rw [hvala, h0, mul_zero]
    exact ((Matrix.isUnit_iff_isUnit_det E).mp hE).ne_zero
      (Matrix.det_eq_zero_of_column_eq_zero i₀ fun i' => hall _)

  have hvinj : Function.Injective (fun f : B →ₐ[R] K => f (bB i₀)) := by
    intro f g hfg
    simp only at hfg
    by_cases hf : f = onePt R B K <;> by_cases hg : g = onePt R B K
    · rw [hf, hg]
    · exfalso
      obtain ⟨a, rfl⟩ := horb g hg
      rw [hf, hval1, hvala] at hfg
      exact (mul_ne_zero (hχK0 a) hf0x) hfg.symm
    · exfalso
      obtain ⟨a, rfl⟩ := horb f hf
      rw [hg, hval1, hvala] at hfg
      exact (mul_ne_zero (hχK0 a) hf0x) hfg
    · obtain ⟨a, rfl⟩ := horb f hf
      obtain ⟨b, rfl⟩ := horb g hg
      rw [hvala, hvala] at hfg
      have h1 := mul_right_cancel₀ hf0x hfg
      rw [hχK, hχK] at h1
      have hab : (a : F) = b := ι.injective ((algebraMap (IsLocalRing.ResidueField R) K).injective h1)
      rw [Units.ext hab]

  let v : κ → B := fun i => bB i₀ ^ (τ i : ℕ)
  have hW : E * (bB.toMatrix v).map (algebraMap R K) = Matrix.of (fun i' i => ((σ.symm i') (bB i₀)) ^ (τ i : ℕ)) := by
    ext i' i
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, E]
    calc ∑ j, (σ.symm i') (bB j) * algebraMap R K (bB.toMatrix v j i)
        = (σ.symm i') (∑ j, bB.toMatrix v j i • bB j) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, map_mul, AlgHom.commutes, mul_comm]
      _ = (σ.symm i') (v i) := by rw [bB.sum_toMatrix_smul_self v i]
      _ = ((σ.symm i') (bB i₀)) ^ (τ i : ℕ) := by simp only [v, map_pow]
  have hV : (Matrix.of fun i' i => ((σ.symm i') (bB i₀)) ^ (τ i : ℕ)).det ≠ 0 := by
    have e : (Matrix.of fun i' i => ((σ.symm i') (bB i₀)) ^ (τ i : ℕ)) =
        (Matrix.vandermonde fun m => (σ.symm (τ.symm m)) (bB i₀)).submatrix τ τ := by
      ext i' i
      simp [Matrix.vandermonde_apply, Matrix.submatrix_apply]
    rw [e, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde_ne_zero_iff]
    exact hvinj.comp (σ.symm.injective.comp τ.symm.injective)

  have hdet : IsUnit (bB.toMatrix v).det := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    apply hV
    have e1 : ((bB.toMatrix v).map (algebraMap R K)).det = algebraMap R K (bB.toMatrix v).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have e2 : algebraMap R (IsLocalRing.ResidueField R) (bB.toMatrix v).det = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [← hW, Matrix.det_mul, e1, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) K, e2, map_zero,
      mul_zero]
  have hspan : Submodule.span R (Set.range v) = ⊤ :=
    ((Module.Basis.is_basis_iff_det (e := bB)).mpr (by rw [Module.Basis.det_apply]; exact hdet)).2

  refine Algebra.eq_top_iff.mpr fun y => ?_
  have hy : y ∈ Submodule.span R (Set.range v) := hspan ▸ Submodule.mem_top
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin R {bB i₀}))).mpr ?_ hy
  rintro _ ⟨i, rfl⟩
  exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton R (bB i₀)) _

include hone hmul hadd hF hχ in

private theorem adjoin_singleton_eq_top_of_card_points' (hq : IsUnit ((p ^ r : R) - 1))
    (hrank : Module.finrank R B = p ^ r) (K : Type*) [Field K]
    [Algebra R K] [Algebra (IsLocalRing.ResidueField R) K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (hK : Nat.card (B →ₐ[R] K) = p ^ r) {x₀ : B} (hx0 : x₀ ∈ piece hone hmul χ 1)
    (hgen1 : ∀ y ∈ piece hone hmul χ 1, ∃ c : R, y = c • x₀) (htor : ∀ c : R, c • x₀ = 0 → c = 0) :
    Algebra.adjoin R {x₀} = ⊤ := by
  classical
  obtain ⟨c, hc⟩ := exists_cinv p r hF hq
  rw [Nat.card_eq_fintype_card] at hc
  set N := piece hone hmul χ 1 with hN

  have hli : LinearIndependent R (fun _ : Unit => (⟨x₀, hx0⟩ : N)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg u
    have h0 : g () • x₀ = 0 := by
      have := congrArg Subtype.val hg
      simpa using this
    cases u
    exact htor _ h0
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun _ : Unit => (⟨x₀, hx0⟩ : N)) := by
    rintro ⟨y, hy⟩ -
    obtain ⟨c', hc'⟩ := hgen1 y hy
    rw [Set.range_const, Submodule.mem_span_singleton]
    exact ⟨c', Subtype.ext (by simp [hc'])⟩
  let bN : Module.Basis Unit R N := Module.Basis.mk hli hsp
  have hbN : (bN () : B) = x₀ := by
    simp [bN, Module.Basis.mk_apply]

  let rQ : B →ₗ[R] N := LinearMap.codRestrict _ (Qp hone hmul χ c 1) (Qp_mem hone hmul χ c 1)
  have hrQ : ∀ w : N, rQ w = w := fun w => Subtype.ext (Qp_eq_self hone hmul χ hc w.2)
  have hcompl : IsCompl N (LinearMap.ker rQ) := LinearMap.isCompl_of_proj hrQ
  have hCfree := free_and_finite_of_retract (LinearMap.ker rQ)
    (LinearMap.codRestrict _ (LinearMap.id - N.subtype ∘ₗ rQ) fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        map_sub, hrQ, sub_self])
    fun w => Subtype.ext (by simp [LinearMap.mem_ker.mp w.2])
  haveI := hCfree.1
  haveI := hCfree.2
  let bC := Module.Free.chooseBasis R (LinearMap.ker rQ)
  let bB := (bN.prod bC).map (Submodule.prodEquivOfIsCompl (p := N) (q := LinearMap.ker rQ) hcompl)
  have hbB : bB (Sum.inl ()) = x₀ := by
    rw [← hbN]
    simp [bB, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  rw [← hbB]
  exact adjoin_singleton_eq_top_of_card_points (hone := hone) (hmul := hmul) (hadd := hadd) (p := p) (r := r)
    (hF := hF) (χ := χ) (ι := ι) (hχ := hχ) hrank K hK bB (Sum.inl ()) (by rw [hbB]; exact hx0)

end Gen

section Dock

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

open MvPolynomial in

private theorem exists_algHom_of_solution (p r : ℕ) [NeZero r] (Xv : Fin r → A) (δ : Fin r → R)
    (hsurj : Function.Surjective (aeval (R := R) Xv))
    (hker : RingHom.ker (aeval (R := R) Xv).toRingHom
      = Ideal.span (Set.range fun i : Fin r => (X i ^ p - C (δ i) * X (i + 1) : MvPolynomial (Fin r) R)))
    (T : Type*) [CommRing T] [Algebra R T] (x : Fin r → T) (hx : ∀ i, x i ^ p = δ i • x (i + 1)) :
    ∃ f : A →ₐ[R] T, ∀ i, f (Xv i) = x i := by
  classical
  have hle : Ideal.span (Set.range fun i : Fin r => (X i ^ p - C (δ i) * X (i + 1) : MvPolynomial (Fin r) R))
      ≤ RingHom.ker (aeval (R := R) x).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker, hx i, Algebra.smul_def]
  have hI : ∀ P ∈ RingHom.ker (aeval (R := R) Xv), aeval x P = 0 := by
    intro P hP
    have hP' : P ∈ RingHom.ker (aeval (R := R) Xv).toRingHom := by simpa [RingHom.mem_ker] using hP
    have hPk := hle (hker ▸ hP')
    simpa [RingHom.mem_ker] using hPk
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let φ := Ideal.Quotient.liftₐ (RingHom.ker (aeval (R := R) Xv)) (aeval x) hI
  refine ⟨φ.comp e.symm.toAlgHom, fun i => ?_⟩
  have h1 : e (Ideal.Quotient.mk (RingHom.ker (aeval (R := R) Xv)) (X i)) = Xv i := by
    simp [e]
  show φ (e.symm (Xv i)) = x i
  rw [← h1, AlgEquiv.symm_apply_apply]
  simp [φ]

end Dock

section Div

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

private theorem dvd_of_sq (p r : ℕ) [NeZero r] (hp : 2 ≤ p) (Xv : Fin r → B) (δ : Fin r → R)
    (hsurj : Function.Surjective (MvPolynomial.aeval (R := R) Xv))
    (hker : RingHom.ker (MvPolynomial.aeval (R := R) Xv).toRingHom
      = Ideal.span (Set.range fun i : Fin r =>
          (MvPolynomial.X i ^ p - MvPolynomial.C (δ i) * MvPolynomial.X (i + 1) : MvPolynomial (Fin r) R)))
    (εB : B →ₐ[R] R) (hε : ∀ k, εB (Xv k) = 0)
    (i : Fin r) (hpI : (p : B) * Xv i ∈ (RingHom.ker εB) ^ 2) :
    δ (i - 1) ∣ (p : R) := by
  classical
  let J : Ideal R := Ideal.span {δ (i - 1)}
  let T := DualNumber (R ⧸ J)
  let x : Fin r → T := fun k => if k = i then DualNumber.eps else 0
  have hεε : (DualNumber.eps : T) * DualNumber.eps = 0 := DualNumber.eps_mul_eps
  have hδε : δ (i - 1) • (DualNumber.eps : T) = 0 := by
    rw [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl', Ideal.Quotient.algebraMap_eq,
      show (DualNumber.eps : T) = TrivSqZeroExt.inr 1 from rfl, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), TrivSqZeroExt.inr_zero]
  have hx : ∀ k, x k ^ p = δ k • x (k + 1) := by
    intro k
    have hl : x k ^ p = 0 := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
      by_cases hk : k = i
      · simp only [x, if_pos hk]
        rw [hn, pow_add, pow_two, hεε, mul_zero]
      · simp only [x, if_neg hk]
        exact zero_pow (by omega)
    rw [hl]
    by_cases hk1 : k + 1 = i
    · have hk' : k = i - 1 := by rw [← hk1, add_sub_cancel_right]
      simp only [x, if_pos hk1]
      rw [hk']
      exact hδε.symm
    · simp only [x, if_neg hk1, smul_zero]
  obtain ⟨φ, hφ⟩ := exists_algHom_of_solution p r Xv δ hsurj hker T x hx
  have hxfst : ∀ k, (x k).fst = 0 := by
    intro k
    by_cases hk : k = i
    · simp only [x, if_pos hk, DualNumber.fst_eps]
    · simp only [x, if_neg hk, TrivSqZeroExt.fst_zero]

  have hfst : ∀ b : B, (φ b).fst = Ideal.Quotient.mk J (εB b) := by
    intro b
    obtain ⟨P, rfl⟩ := hsurj b
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.aeval_C, AlgHom.commutes, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl',
        TrivSqZeroExt.fst_inl, Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_self_apply]
    | add P Q hP hQ => rw [map_add, map_add, TrivSqZeroExt.fst_add, hP, hQ, map_add, map_add]
    | mul_X P k hP =>
      rw [map_mul, map_mul, TrivSqZeroExt.fst_mul, hP, MvPolynomial.aeval_X, hφ, hxfst, mul_zero, map_mul, map_mul,
        hε, map_zero, mul_zero]

  have hzero : ∀ u ∈ RingHom.ker εB, (φ u).fst = 0 := fun u hu => by
    rw [hfst, RingHom.mem_ker.mp hu, map_zero]
  have hsq : ∀ y ∈ (RingHom.ker εB) ^ 2, φ y = 0 := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) (fun u v hu' hv' => by rw [map_add, hu', hv', add_zero])
    rw [map_mul]
    have eu : φ u = TrivSqZeroExt.inr (φ u).snd :=
      TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_inr]; exact hzero u hu) (by rw [TrivSqZeroExt.snd_inr])
    have ev : φ v = TrivSqZeroExt.inr (φ v).snd :=
      TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_inr]; exact hzero v hv) (by rw [TrivSqZeroExt.snd_inr])
    rw [eu, ev, TrivSqZeroExt.inr_mul_inr]

  have h0 := hsq _ hpI
  rw [map_mul, map_natCast, hφ i] at h0
  simp only [x, if_pos rfl] at h0
  have h1 : TrivSqZeroExt.snd ((p : T) * DualNumber.eps) = (p : R ⧸ J) := by
    rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast, DualNumber.snd_eps,
      DualNumber.fst_eps]
    simp
  rw [h0, TrivSqZeroExt.snd_zero] at h1
  have h2 : Ideal.Quotient.mk J (p : R) = 0 := by rw [map_natCast]; exact h1.symm
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)

end Div

end W2RaynS3

open W2RaynS3

theorem solution
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [CharZero R']
    (p r : ℕ) [Fact p.Prime] [NeZero r]
    (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
    (hq : IsUnit ((p ^ r : R') - 1))
    (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R')
    (hχ : ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l)
    (B : Type v) [CommRing B] [HopfAlgebra R' B] [Module.Finite R' B] [Module.Free R' B]
    (hrank : Module.finrank R' B = p ^ r)
    (fv : HopfAlgebra.FVectStructure F R' B) :
    ∃ (X : Fin r → B) (δ : Fin r → R'),
      (∀ i (l : Fˣ), (fv.act l) (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i) ∧
      (∀ i, X i ^ p = δ i • X (i + 1)) ∧
      (∀ i, δ i ∣ (p : R')) ∧
      (∀ i, Coalgebra.counit (R := R') (X i) = 0) ∧
      Algebra.adjoin R' (Set.range X) = ⊤ := by
  classical
  have hone : ActOne fv.act := fv.act_one
  have hmul : ActMul fv.act := fv.act_mul
  have hadd : ActAdd fv.act := fv.act_add_linearMap
  let L := AlgebraicClosure (FractionRing R')
  haveI : CharZero (FractionRing R') :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R' (FractionRing R'))
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap (FractionRing R') L).injective
  have hpts : Nat.card (B →ₐ[R'] L) = p ^ r := by
    rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R' B L, hrank]
  have hp : p.Prime := Fact.out
  have hq2 : 2 ≤ p ^ r := Nat.one_lt_pow (NeZero.ne r) hp.one_lt

  obtain ⟨Y, hY⟩ := exists_gen_piece (hone := hone) (hmul := hmul) (hadd := hadd) (p := p) (r := r) (hF := hF)
    (hq := hq) (χ := χ) (ι := ι) (hχ := hχ) (hrank := hrank) (L := L) (hpts := hpts)

  let e : Fin r → ℕ := fun i => p ^ (i : ℕ) % (p ^ r - 1)
  have he : ∀ i : Fin r, e i < p ^ r - 1 := fun i => Nat.mod_lt _ (by omega)
  have hpiece_e : ∀ i : Fin r, piece hone hmul χ (e i) = piece hone hmul χ (p ^ (i : ℕ)) := by
    intro i
    show eig _ (χ ^ (p ^ (i : ℕ) % (p ^ r - 1))) ⊓ _ = eig _ (χ ^ (p ^ (i : ℕ))) ⊓ _
    rw [chi_pow_mod p r hF χ]
  let X : Fin r → B := fun i => Y (e i)
  have hXpiece : ∀ i : Fin r, X i ∈ piece hone hmul χ (p ^ (i : ℕ)) := fun i => hpiece_e i ▸ (hY (e i) (he i)).1
  have hXgen : ∀ i : Fin r, ∀ y ∈ piece hone hmul χ (p ^ (i : ℕ)), ∃ c : R', y = c • X i := by
    intro i y hy
    rw [← hpiece_e i] at hy
    exact (hY (e i) (he i)).2.1 y hy
  have hXtor : ∀ (i : Fin r) (c : R'), c • X i = 0 → c = 0 := fun i => (hY (e i) (he i)).2.2

  have h1 : ∀ (i : Fin r) (l : Fˣ), (fv.act l) (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i :=
    fun i l => (mem_eig _).mp (Submodule.mem_inf.mp (hXpiece i)).1 l
  have h5 : ∀ i : Fin r, Coalgebra.counit (R := R') (X i) = 0 :=
    fun i => (mem_augSub (R := R')).mp (Submodule.mem_inf.mp (hXpiece i)).2
  have hXI : ∀ i : Fin r, X i ∈ augIdeal R' B := fun i => (RingHom.mem_ker).mpr (by simpa using h5 i)

  have hpow : ∀ i : Fin r, X i ^ p ∈ piece hone hmul χ (p ^ ((i + 1 : Fin r) : ℕ)) := by
    intro i
    have h := pow_p_mem_piece_succ (hone := hone) (hmul := hmul) (p := p) (χ := χ) (hXpiece i)
    show X i ^ p ∈ eig _ (χ ^ p ^ ((i + 1 : Fin r) : ℕ)) ⊓ _
    rw [chi_pow_fin_succ (p := p) (r := r) (χ := χ) (chi_pow_card p r hF χ) i]
    exact h
  choose δ hδ using fun i : Fin r => hXgen (i + 1) (X i ^ p) (hpow i)

  have hgen : Algebra.adjoin R' (Set.range X) = ⊤ := by
    let k := IsLocalRing.ResidueField R'
    let K := AlgebraicClosure k
    rcases one_or_card_points (hone := hone) (hmul := hmul) (hadd := hadd) (p := p) (r := r) (hF := hF) (B := B)
        hrank K with ⟨-, N, hN⟩ | hcard
    · exact adjoin_eq_top_of_aug_pow_le (R := R') (B := B) (r := r) X hXI
        (aug_le_span_sup (hone := hone) (hmul := hmul) (hadd := hadd) (p := p) (r := r) (hF := hF)
          (χ := χ) (ι := ι) (hχ := hχ) hq X hXgen) hN
    · have hx0 : X 0 ∈ piece hone hmul χ 1 := by
        have := hXpiece 0
        simpa using this
      have hgen1 : ∀ y ∈ piece hone hmul χ 1, ∃ c : R', y = c • X 0 := by
        intro y hy
        refine hXgen 0 y ?_
        simpa using hy
      have htop := adjoin_singleton_eq_top_of_card_points' (hone := hone) (hmul := hmul) (hadd := hadd) (p := p)
        (r := r) (hF := hF) (χ := χ) (ι := ι) (hχ := hχ) hq hrank K hcard hx0 hgen1 (hXtor 0)
      refine eq_top_iff.mpr (htop ▸ Algebra.adjoin_mono ?_)
      rintro _ rfl
      exact ⟨0, rfl⟩

  obtain ⟨-, hsurj, hker⟩ := CyclicPowerRelations.presentation p r hp.two_le hrank X δ hδ hgen

  have h4 : ∀ i : Fin r, δ i ∣ (p : R') := by
    intro i
    have h := dvd_of_sq p r hp.two_le X δ hsurj hker (Bialgebra.counitAlgHom R' B)
      (fun j => by simpa using h5 j) (i + 1)
      (p_smul_mem_sq (hone := hone) (hadd := hadd) (p := p) (r := r) (hF := hF) (hXI (i + 1)))
    simpa using h
  exact ⟨X, δ, h1, hδ, h4, h5, hgen⟩

end S_HopfAlgebra_FVect_exists_generators_normalForm_of_finrank_eq_card
end P2MW
export P2MW.S_HopfAlgebra_FVect_exists_generators_normalForm_of_finrank_eq_card (solution)
