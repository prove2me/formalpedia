-- Prove2me | solution 1 for IsLocalRing.exists_adicCompletion_ringHom_finite_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c197ad27-72bd-5f19-af0b-02e056f9fb3e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace CompFin

section Cofinal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (M : Ideal S)

theorem pow_smul_top_eq_restrictScalars (n : ℕ) :
    (I ^ n • ⊤ : Submodule R S) = ((I.map (algebraMap R S)) ^ n).restrictScalars R := by
  rw [← Ideal.map_pow, Ideal.smul_top_eq_map]

theorem mem_pow_smul_top_iff (n : ℕ) (s : S) : s ∈ (M ^ n • ⊤ : Submodule S S) ↔ s ∈ M ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

variable {I M}

theorem pow_smul_top_le (hIM : I.map (algebraMap R S) ≤ M) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R S) ≤ (M ^ n • ⊤ : Submodule S S).restrictScalars R := by
  intro s hs
  rw [pow_smul_top_eq_restrictScalars] at hs
  rw [Submodule.restrictScalars_mem, mem_pow_smul_top_iff]
  exact Ideal.pow_right_mono hIM n hs

theorem pow_smul_top_ge {k : ℕ} (hk : M ^ k ≤ I.map (algebraMap R S)) (n : ℕ) :
    (M ^ (k * n) • ⊤ : Submodule S S).restrictScalars R ≤ (I ^ n • ⊤ : Submodule R S) := by
  intro s hs
  rw [Submodule.restrictScalars_mem, mem_pow_smul_top_iff, pow_mul] at hs
  rw [pow_smul_top_eq_restrictScalars]
  exact Ideal.pow_right_mono hk n hs

def θ (hIM : I.map (algebraMap R S) ≤ M) (n : ℕ) :
    S ⧸ (I ^ n • ⊤ : Submodule R S) →ₗ[R] S ⧸ (M ^ n • ⊤ : Submodule S S) :=
  (I ^ n • ⊤ : Submodule R S).liftQ (((M ^ n • ⊤ : Submodule S S).mkQ).restrictScalars R) (by
    rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
    exact pow_smul_top_le hIM n)

theorem θ_mk (hIM : I.map (algebraMap R S) ≤ M) (n : ℕ) (s : S) :
    θ hIM n (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := rfl

def η {k : ℕ} (hk : M ^ k ≤ I.map (algebraMap R S)) (n : ℕ) :
    S ⧸ (M ^ (k * n) • ⊤ : Submodule S S) →ₗ[R] S ⧸ (I ^ n • ⊤ : Submodule R S) :=
  (((M ^ (k * n) • ⊤ : Submodule S S).restrictScalars R).liftQ (I ^ n • ⊤ : Submodule R S).mkQ (by
    rw [Submodule.ker_mkQ]; exact pow_smul_top_ge hk n)).comp
    (Submodule.Quotient.restrictScalarsEquiv R (M ^ (k * n) • ⊤ : Submodule S S)).symm.toLinearMap

theorem η_mk {k : ℕ} (hk : M ^ k ≤ I.map (algebraMap R S)) (n : ℕ) (s : S) :
    η hk n (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := rfl

def χ (hIM : I.map (algebraMap R S) ≤ M) (f : AdicCompletion I S) : AdicCompletion M S :=
  ⟨fun n => θ hIM n (f.val n), by
    intro m n hmn
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (f.val n)
    have hm : f.val m = Submodule.Quotient.mk s := by
      rw [← f.property hmn, ← hs]; rfl
    simp only [← hs, hm, θ_mk]
    rfl⟩

theorem χ_val (hIM : I.map (algebraMap R S) ≤ M) (f : AdicCompletion I S) (n : ℕ) :
    (χ hIM f).val n = θ hIM n (f.val n) := rfl

def χinv {k : ℕ} (hk : M ^ k ≤ I.map (algebraMap R S)) (g : AdicCompletion M S) :
    AdicCompletion I S :=
  ⟨fun n => η hk n (g.val (k * n)), by
    intro m n hmn
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (g.val (k * n))
    have hm : g.val (k * m) = Submodule.Quotient.mk s := by
      rw [← g.property (Nat.mul_le_mul_left k hmn), ← hs]; rfl
    simp only [← hs, hm, η_mk]
    rfl⟩

theorem χinv_χ (hIM : I.map (algebraMap R S) ≤ M) {k : ℕ} (hk : M ^ k ≤ I.map (algebraMap R S)) (hk1 : 1 ≤ k)
    (f : AdicCompletion I S) : χinv hk (χ hIM f) = f := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (f.val (k * n))
  have hn : f.val n = Submodule.Quotient.mk s := by
    rw [← f.property (Nat.le_mul_of_pos_left n hk1), ← hs]; rfl
  show η hk n (θ hIM (k * n) (f.val (k * n))) = f.val n
  rw [← hs, θ_mk, η_mk, hn]

theorem χ_χinv (hIM : I.map (algebraMap R S) ≤ M) {k : ℕ} (hk : M ^ k ≤ I.map (algebraMap R S)) (hk1 : 1 ≤ k)
    (g : AdicCompletion M S) : χ hIM (χinv hk g) = g := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (g.val (k * n))
  have hn : g.val n = Submodule.Quotient.mk s := by
    rw [← g.property (Nat.le_mul_of_pos_left n hk1), ← hs]; rfl
  show θ hIM n (η hk n (g.val (k * n))) = g.val n
  rw [← hs, η_mk, θ_mk, hn]

theorem χ_bijective (hIM : I.map (algebraMap R S) ≤ M) {k : ℕ} (hk : M ^ k ≤ I.map (algebraMap R S))
    (hk1 : 1 ≤ k) : Function.Bijective (χ hIM) :=
  ⟨Function.LeftInverse.injective (χinv_χ hIM hk hk1), Function.RightInverse.surjective (χ_χinv hIM hk hk1)⟩

theorem χ_add (hIM : I.map (algebraMap R S) ≤ M) (f g : AdicCompletion I S) :
    χ hIM (f + g) = χ hIM f + χ hIM g := by
  apply AdicCompletion.ext
  intro n
  rw [AdicCompletion.val_add_apply]
  show θ hIM n ((f + g).val n) = θ hIM n (f.val n) + θ hIM n (g.val n)
  rw [← map_add]
  rfl

theorem χ_zero (hIM : I.map (algebraMap R S) ≤ M) : χ hIM (0 : AdicCompletion I S) = 0 := by
  have h := χ_add hIM 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

end Cofinal

section Ideals

open IsLocalRing

variable (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S] [Module.Finite R S]

theorem map_maximalIdeal_ne_top : (maximalIdeal R).map (algebraMap R S) ≠ ⊤ := by
  intro h
  have htop : (⊤ : Submodule R S) ≤ maximalIdeal R • ⊤ := by
    rw [Ideal.smul_top_eq_map, h]
    intro s _
    trivial
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (⊤ : Submodule R S)
    Module.Finite.fg_top htop (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  have h1 : (1 : S) ∈ (⊥ : Submodule R S) := hbot ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  exact one_ne_zero h1

theorem map_maximalIdeal_le : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
  IsLocalRing.le_maximalIdeal (map_maximalIdeal_ne_top R S)

theorem exists_maximalIdeal_pow_le [IsNoetherianRing S] :
    ∃ k : ℕ, 1 ≤ k ∧ maximalIdeal S ^ k ≤ (maximalIdeal R).map (algebraMap R S) := by
  set J := (maximalIdeal R).map (algebraMap R S) with hJ
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have hc : maximalIdeal R ≤ P.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.1 hJP
    have hne : P.comap (algebraMap R S) ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
    have heq : maximalIdeal R = P.comap (algebraMap R S) := (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hc
    have hcm : (P.comap (algebraMap R S)).IsMaximal := heq ▸ IsLocalRing.maximalIdeal.isMaximal R
    haveI := hP
    have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hcm
    exact le_of_eq (IsLocalRing.eq_maximalIdeal hPm).symm
  obtain ⟨k, hk⟩ := Ideal.exists_radical_pow_le_of_fg J (IsNoetherian.noetherian _)
  exact ⟨k + 1, Nat.succ_pos k,
    (Ideal.pow_le_pow_right (Nat.le_succ k)).trans ((Ideal.pow_right_mono hrad k).trans hk)⟩

end Ideals

section Eval

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem smul_top_le_pow (n : ℕ) : (I ^ n • ⊤ : Submodule R R) ≤ I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem pow_le_smul_top (n : ℕ) : I ^ n ≤ (I ^ n • ⊤ : Submodule R R) := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem evalₐ_eq_mk_of_val_eq {n : ℕ} (x : AdicCompletion I R) (r : R)
    (h : x.val n = Submodule.Quotient.mk r) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (smul_top_le_pow I n), AdicCompletion.eval_apply]
  show Submodule.factor _ (x.val n) = _
  rw [h]
  rfl

theorem val_eq_zero_of_evalₐ_eq_zero {n : ℕ} (x : AdicCompletion I R) (h : AdicCompletion.evalₐ I n x = 0) :
    x.val n = 0 := by
  have h2 := AdicCompletion.factor_evalₐ_eq_eval I x (pow_le_smul_top I n)
  rw [h, map_zero, AdicCompletion.eval_apply] at h2
  exact h2.symm

theorem evalₐ_eq_zero_of_le {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R)
    (h : AdicCompletion.evalₐ I n x = 0) : AdicCompletion.evalₐ I m x = 0 := by
  have hn := val_eq_zero_of_evalₐ_eq_zero I x h
  have hm : x.val m = Submodule.Quotient.mk 0 := by
    rw [← x.property hle, hn, map_zero]
    rfl
  rw [evalₐ_eq_mk_of_val_eq I x 0 hm, map_zero]

theorem exists_evalₐ_sub_of_eq_zero (n : ℕ) (x : AdicCompletion I R) :
    ∃ a : R, AdicCompletion.evalₐ I n (x - AdicCompletion.of I R a) = 0 := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  exact ⟨a, by rw [map_sub, AdicCompletion.evalₐ_of, ha, sub_self]⟩

theorem of_eq_algebraMap (r : R) : AdicCompletion.of I R r = algebraMap R (AdicCompletion I R) r := by
  rw [AdicCompletion.algebraMap_apply]
  rfl

end Eval

end CompFin

open CompFin IsLocalRing in
theorem solution
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    ∃ φ : AdicCompletion (IsLocalRing.maximalIdeal R) R →+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (∀ r : R, φ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap R S r)) ∧
      φ.Finite ∧
      (Function.Injective (algebraMap R S) → Function.Injective φ) ∧

      ∃ e : TensorProduct R (AdicCompletion (IsLocalRing.maximalIdeal R) R) S ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal S) S,
        (∀ x : AdicCompletion (IsLocalRing.maximalIdeal R) R, e (x ⊗ₜ[R] (1 : S)) = φ x) ∧
        (∀ s : S, e ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] s) =
          algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s) := by
  classical

  set I : Ideal R := maximalIdeal R with hI
  set M : Ideal S := maximalIdeal S with hM
  have hIM : I.map (algebraMap R S) ≤ M := map_maximalIdeal_le R S
  obtain ⟨k, hk1, hk⟩ := exists_maximalIdeal_pow_le R S
  have hpow : ∀ n : ℕ, I ^ n ≤ (M ^ n).comap (algebraMap R S) := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hIM n

  let f : ∀ n : ℕ, AdicCompletion I R →+* S ⧸ M ^ n := fun n =>
    (Ideal.quotientMap (M ^ n) (algebraMap R S) (hpow n)).comp (AdicCompletion.evalₐ I n).toRingHom
  have hfapp : ∀ (n : ℕ) (x : AdicCompletion I R),
      f n x = Ideal.quotientMap (M ^ n) (algebraMap R S) (hpow n) (AdicCompletion.evalₐ I n x) := fun n x => rfl
  have hfof : ∀ (n : ℕ) (a : R), f n (AdicCompletion.of I R a) = Ideal.Quotient.mk (M ^ n) (algebraMap R S a) := by
    intro n a
    rw [hfapp, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  have hfzero : ∀ (n : ℕ) (y : AdicCompletion I R), AdicCompletion.evalₐ I n y = 0 → f n y = 0 := by
    intro n y hy
    rw [hfapp, hy, map_zero]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow M hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨a, ha⟩ := exists_evalₐ_sub_of_eq_zero I n x
    have hx : x = (x - AdicCompletion.of I R a) + AdicCompletion.of I R a := (sub_add_cancel x _).symm
    rw [RingHom.comp_apply, hx, map_add, map_add, map_add, hfzero n _ ha, hfzero m _ (evalₐ_eq_zero_of_le I hle _ ha),
      hfof, hfof, map_zero, zero_add, zero_add]
    exact Ideal.Quotient.factor_mk _ _
  let φ : AdicCompletion I R →+* AdicCompletion M S := AdicCompletion.liftRingHom M f hf
  have hφev : ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ M n (φ x) = f n x :=
    fun n x => AdicCompletion.evalₐ_liftRingHom M f hf n x

  have hφR : ∀ r : R, φ (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion M S) (algebraMap R S r) := by
    intro r
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [hφev, ← of_eq_algebraMap, hfof, ← of_eq_algebraMap, AdicCompletion.evalₐ_of]

  let φₐ : AdicCompletion I R →ₐ[R] AdicCompletion M S :=
    { φ with
      commutes' := fun r => by
        show φ (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion M S) r
        rw [hφR, IsScalarTower.algebraMap_apply R S (AdicCompletion M S)] }
  let σ : S →ₐ[R] AdicCompletion M S := IsScalarTower.toAlgHom R S (AdicCompletion M S)
  let ψ : AdicCompletion I R ⊗[R] S →ₐ[R] AdicCompletion M S :=
    Algebra.TensorProduct.lift φₐ σ (fun _ _ => Commute.all _ _)
  have hψ : ∀ (x : AdicCompletion I R) (s : S), ψ (x ⊗ₜ[R] s) = φ x * algebraMap S (AdicCompletion M S) s :=
    fun x s => Algebra.TensorProduct.lift_tmul _ _ _ x s

  let ω := AdicCompletion.ofTensorProduct I S
  have hω : Function.Bijective ω := by
    obtain ⟨n, N, ⟨e⟩⟩ := Module.Finite.exists_fin_quot_equiv R S
    have hP := AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I ((Fin n → R) ⧸ N)
    let τ : AdicCompletion I R ⊗[R] ((Fin n → R) ⧸ N) ≃ₗ[R] AdicCompletion I R ⊗[R] S :=
      LinearEquiv.lTensor (AdicCompletion I R) e
    have hme : Function.Bijective (AdicCompletion.map I e.toLinearMap) := by
      have h1 : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := LinearMap.ext fun p => e.symm_apply_apply p
      have h2 : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := LinearMap.ext fun p => e.apply_symm_apply p
      refine Function.bijective_iff_has_inverse.2 ⟨AdicCompletion.map I e.symm.toLinearMap, fun z => ?_, fun z => ?_⟩
      · rw [AdicCompletion.map_comp_apply, h1, AdicCompletion.map_id, LinearMap.id_apply]
      · rw [AdicCompletion.map_comp_apply, h2, AdicCompletion.map_id, LinearMap.id_apply]
    have hcomp : ∀ z : AdicCompletion I R ⊗[R] ((Fin n → R) ⧸ N), ω (τ z) = AdicCompletion.map I e.toLinearMap
        (AdicCompletion.ofTensorProduct I ((Fin n → R) ⧸ N) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul x p =>
        simp only [τ, ω, LinearEquiv.lTensor_tmul, AdicCompletion.ofTensorProduct_tmul, map_smul]
        rw [AdicCompletion.map_of]
        rfl
    have hfun : (ω : _ → AdicCompletion I S) = fun z => AdicCompletion.map I e.toLinearMap
        (AdicCompletion.ofTensorProduct I ((Fin n → R) ⧸ N) (τ.symm z)) := by
      funext z
      rw [← hcomp, LinearEquiv.apply_symm_apply]
    rw [hfun]
    exact hme.comp (hP.comp τ.symm.bijective)

  have hχb : Function.Bijective (CompFin.χ (I := I) (M := M) hIM) := χ_bijective hIM hk hk1
  have hlev0 : ∀ (n : ℕ) (y : AdicCompletion I R) (s : S), AdicCompletion.evalₐ I n y = 0 →
      AdicCompletion.evalₐ M n (CompFin.χ hIM (ω (y ⊗ₜ[R] s))) = 0 := by
    intro n y s hy
    have hv : (CompFin.χ hIM (ω (y ⊗ₜ[R] s))).val n = Submodule.Quotient.mk 0 := by
      rw [χ_val]
      show CompFin.θ hIM n ((AdicCompletion.ofTensorProduct I S (y ⊗ₜ[R] s)).val n) = _
      rw [AdicCompletion.ofTensorProduct_tmul, AdicCompletion.smul_eval, val_eq_zero_of_evalₐ_eq_zero I y hy,
        zero_smul, map_zero]
      rfl
    rw [evalₐ_eq_mk_of_val_eq M _ 0 hv, map_zero]
  have hlev1 : ∀ (n : ℕ) (a : R) (s : S),
      AdicCompletion.evalₐ M n (CompFin.χ hIM (ω (AdicCompletion.of I R a ⊗ₜ[R] s))) =
        Ideal.Quotient.mk (M ^ n) (algebraMap R S a * s) := by
    intro n a s
    have hv : (CompFin.χ hIM (ω (AdicCompletion.of I R a ⊗ₜ[R] s))).val n = Submodule.Quotient.mk (a • s) := by
      rw [χ_val]
      show CompFin.θ hIM n ((AdicCompletion.ofTensorProduct I S (AdicCompletion.of I R a ⊗ₜ[R] s)).val n) = _
      rw [AdicCompletion.ofTensorProduct_tmul, of_eq_algebraMap, algebraMap_smul, ← map_smul,
        AdicCompletion.of_apply]
      rfl
    rw [evalₐ_eq_mk_of_val_eq M _ (a • s) hv, Algebra.smul_def]
  have hid : ∀ z : AdicCompletion I R ⊗[R] S, ψ z = CompFin.χ hIM (ω z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, χ_zero]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, χ_add, h₁, h₂]
    | tmul x s =>
      refine AdicCompletion.ext_evalₐ fun n => ?_
      obtain ⟨a, ha⟩ := exists_evalₐ_sub_of_eq_zero I n x
      have hx : x = (x - AdicCompletion.of I R a) + AdicCompletion.of I R a := (sub_add_cancel x _).symm
      rw [hx, TensorProduct.add_tmul, map_add, map_add, map_add, χ_add, map_add, hψ, hψ, map_mul, map_mul, hφev, hφev,
        hfzero n _ ha, zero_mul, zero_add, hfof, hlev0 n _ s ha, zero_add, hlev1, ← of_eq_algebraMap,
        AdicCompletion.evalₐ_of, ← map_mul]
  have hψfun : (ψ : AdicCompletion I R ⊗[R] S → AdicCompletion M S) = CompFin.χ hIM ∘ ω := funext hid
  have hψbij : Function.Bijective ψ := by
    rw [hψfun]
    exact hχb.comp hω

  refine ⟨φ, hφR, ?_, ?_, ⟨RingEquiv.ofBijective ψ.toRingHom hψbij, fun x => ?_, fun s => ?_⟩⟩
  ·
    letI alg : Algebra (AdicCompletion I R) (AdicCompletion M S) := φ.toAlgebra
    let ψl : AdicCompletion I R ⊗[R] S →ₗ[AdicCompletion I R] AdicCompletion M S :=
      { toFun := ψ
        map_add' := fun a b => map_add ψ a b
        map_smul' := fun x z => by
          rw [RingHom.id_apply, Algebra.smul_def x z, Algebra.TensorProduct.algebraMap_apply,
            Algebra.smul_def x (ψ z), map_mul, hψ, map_one, mul_one]
          rfl }
    exact Module.Finite.of_surjective ψl hψbij.2
  ·
    intro hinj x y hxy
    have h1 : ψ (x ⊗ₜ[R] (1 : S)) = ψ (y ⊗ₜ[R] (1 : S)) := by
      rw [hψ, hψ, map_one, mul_one, mul_one]; exact hxy
    have h2 := hψbij.1 h1
    have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := AdicCompletion I R)
      (Algebra.linearMap R S) hinj
    have h3 : LinearMap.lTensor (AdicCompletion I R) (Algebra.linearMap R S) (x ⊗ₜ[R] (1 : R)) =
        LinearMap.lTensor (AdicCompletion I R) (Algebra.linearMap R S) (y ⊗ₜ[R] (1 : R)) := by
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
      exact h2
    have h4 := congrArg (TensorProduct.rid R (AdicCompletion I R)) (hl h3)
    rwa [TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, one_smul] at h4
  · show ψ (x ⊗ₜ[R] (1 : S)) = φ x
    rw [hψ, map_one, mul_one]
  · show ψ ((1 : AdicCompletion I R) ⊗ₜ[R] s) = algebraMap S (AdicCompletion M S) s
    rw [hψ, map_one, one_mul]

end S_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite
end P2MW
export P2MW.S_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite (solution)
