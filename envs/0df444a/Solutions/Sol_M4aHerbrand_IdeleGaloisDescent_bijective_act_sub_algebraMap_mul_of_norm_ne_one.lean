-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.bijective_act_sub_algebraMap_mul_of_norm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d4a6b4e2-a85d-5131-a9db-a433c5e25520

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one

set_option autoImplicit false

noncomputable section

namespace R1HypL45

open NumberField Finset

section Galois

variable {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
  {σ : F ≃ₐ[E] F}

theorem orderOf_eq_finrank (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) :
    orderOf σ = Module.finrank E F := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

theorem pow_finrank_eq_one (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) :
    σ ^ Module.finrank E F = 1 := by
  rw [← orderOf_eq_finrank hgen, pow_orderOf_eq_one]

theorem prod_algEquiv_eq_prod_range (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ)
    {M : Type*} [CommMonoid M] (f : (F ≃ₐ[E] F) → M) :
    ∏ τ : F ≃ₐ[E] F, f τ = ∏ i ∈ Finset.range (Module.finrank E F), f (σ ^ i) := by
  classical
  have horder := orderOf_eq_finrank hgen
  have hinj : Function.Injective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  have hbij : Function.Bijective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [Fintype.card_fin, horder, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]⟩
  rw [← Fintype.prod_bijective _ hbij (fun i => f (σ ^ (i : ℕ))) f (fun _ => rfl),
    ← horder, ← Fin.prod_univ_eq_prod_range]

theorem prod_range_iterate_eq_algebraMap_norm (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ)
    (a : F) :
    ∏ i ∈ Finset.range (Module.finrank E F), (⇑σ)^[i] a = algebraMap E F (Algebra.norm E a) := by
  rw [Algebra.norm_eq_prod_automorphisms, prod_algEquiv_eq_prod_range hgen]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [AlgEquiv.coe_pow]

theorem forall_mem_zpowers_symm (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) :
    ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ.symm := by
  intro τ
  have h : σ.symm = σ⁻¹ := (AlgEquiv.aut_inv σ).symm
  rw [h, Subgroup.zpowers_inv]
  exact hgen τ

end Galois

section Descent

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]
  (D : M4aHerbrand.IdeleGaloisDescent R E F) (σ : F ≃ₐ[E] F)

local notation "𝔸" => AdeleRing R F

def θ : 𝔸 → 𝔸 := fun s => (D.act σ : RingAut 𝔸) s

def ι : F →+* 𝔸 := algebraMap F 𝔸

theorem θ_apply (s : 𝔸) : θ D σ s = (D.act σ : RingAut 𝔸) s := rfl

theorem θ_add (s t : 𝔸) : θ D σ (s + t) = θ D σ s + θ D σ t := map_add _ s t

theorem θ_sub (s t : 𝔸) : θ D σ (s - t) = θ D σ s - θ D σ t := map_sub _ s t

theorem θ_mul (s t : 𝔸) : θ D σ (s * t) = θ D σ s * θ D σ t := map_mul _ s t

theorem θ_zero : θ D σ 0 = 0 := map_zero _

theorem θ_sum {ι' : Type*} (s : Finset ι') (f : ι' → 𝔸) :
    θ D σ (∑ i ∈ s, f i) = ∑ i ∈ s, θ D σ (f i) := map_sum _ f s

theorem θ_ι (x : F) : θ D σ (ι x) = ι (σ x) := D.compat σ x

theorem θ_ι_mul (x : F) (s : 𝔸) : θ D σ (ι x * s) = ι (σ x) * θ D σ s := by
  rw [θ_mul, θ_ι]

theorem act_pow_apply (k : ℕ) (s : 𝔸) : (D.act (σ ^ k) : RingAut 𝔸) s = (θ D σ)^[k] s := by
  induction k generalizing s with
  | zero =>
      rw [pow_zero, map_one, Function.iterate_zero, id_eq]
      rfl
  | succ k ih =>
      rw [pow_succ, map_mul, Function.iterate_succ_apply']
      change (D.act (σ ^ k) : RingAut 𝔸) ((D.act σ : RingAut 𝔸) s) = _
      rw [ih]

      exact (Function.iterate_succ_apply' (θ D σ) k s ▸ Function.iterate_succ_apply (θ D σ) k s ▸ rfl)

theorem iterate_θ_ι_mul (x : F) (s : 𝔸) (k : ℕ) :
    (θ D σ)^[k] (ι x * s) = ι ((⇑σ)^[k] x) * (θ D σ)^[k] s := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, θ_ι_mul, Function.iterate_succ_apply',
        Function.iterate_succ_apply']

variable [FiniteDimensional E F] [IsGalois E F]

theorem iterate_θ_finrank {σ : F ≃ₐ[E] F} (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) (s : 𝔸) :
    (θ D σ)^[Module.finrank E F] s = s := by
  rw [← act_pow_apply, pow_finrank_eq_one hgen, map_one]
  rfl

end Descent

section Main

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
  (D : M4aHerbrand.IdeleGaloisDescent R E F) {σ : F ≃ₐ[E] F}

local notation "𝔸" => AdeleRing R F

def T (σ : F ≃ₐ[E] F) (c : F) (s : 𝔸) : 𝔸 := θ D σ s - ι c * s

theorem T_apply (σ : F ≃ₐ[E] F) (c : F) (s : 𝔸) : T D σ c s = θ D σ s - ι c * s := rfl

theorem T_add (σ : F ≃ₐ[E] F) (c : F) (s t : 𝔸) : T D σ c (s + t) = T D σ c s + T D σ c t := by
  simp only [T_apply, θ_add, mul_add]; abel

theorem T_sub (σ : F ≃ₐ[E] F) (c : F) (s t : 𝔸) : T D σ c (s - t) = T D σ c s - T D σ c t := by
  simp only [T_apply, θ_sub, mul_sub]; abel

theorem T_ι_mul_of_fixed (σ : F ≃ₐ[E] F) (c : F) {y : F} (hy : σ y = y) (s : 𝔸) :
    T D σ c (ι y * s) = ι y * T D σ c s := by
  rw [T_apply, T_apply, θ_ι_mul, hy, mul_sub, ← mul_assoc, ← mul_assoc, mul_comm (ι c) (ι y)]

theorem iterate_θ_eq_of_θ_eq (σ : F ≃ₐ[E] F) {c : F} {s : 𝔸} (h : θ D σ s = ι c * s) (k : ℕ) :
    (θ D σ)^[k] s = ι (∏ i ∈ Finset.range k, (⇑σ)^[i] c) * s := by
  induction k with
  | zero => simp [ι]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, θ_ι_mul, h, ← mul_assoc, ← map_mul]
      congr 2
      rw [prod_range_succ', map_prod]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      rw [Function.iterate_succ_apply']

theorem T_injective (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) {c : F}
    (hc : Algebra.norm E c ≠ 1) : Function.Injective (T D σ c) := by
  intro s t hst
  have h0 : T D σ c (s - t) = 0 := by rw [T_sub, hst, sub_self]
  set r := s - t with hr
  have hθ : θ D σ r = ι c * r := sub_eq_zero.mp h0
  have hn := iterate_θ_eq_of_θ_eq D σ hθ (Module.finrank E F)
  rw [iterate_θ_finrank D hgen, prod_range_iterate_eq_algebraMap_norm hgen] at hn

  have h1 : ι (F := F) (R := R) (algebraMap E F (Algebra.norm E c - 1)) * r = 0 := by
    rw [map_sub, map_one, map_sub, map_one, sub_mul, one_mul, ← hn, sub_self]
  have hunit : IsUnit (ι (F := F) (R := R) (algebraMap E F (Algebra.norm E c - 1))) :=
    (IsUnit.mk0 _ (sub_ne_zero.mpr hc)).map _ |>.map _
  have hr0 : r = 0 := by
    have := congrArg (fun a => hunit.unit⁻¹.val * a) h1
    simpa only [mul_zero, ← mul_assoc, IsUnit.val_inv_mul, one_mul] using this
  exact sub_eq_zero.mp hr0

def g (σ : F ≃ₐ[E] F) (c : F) : ℕ → F
  | 0 => 1
  | k + 1 => σ.symm (c * g σ c k)

theorem g_zero (σ : F ≃ₐ[E] F) (c : F) : g σ c 0 = 1 := rfl

theorem g_succ (σ : F ≃ₐ[E] F) (c : F) (k : ℕ) : g σ c (k + 1) = σ.symm (c * g σ c k) := rfl

theorem σ_g_succ (σ : F ≃ₐ[E] F) (c : F) (k : ℕ) : σ (g σ c (k + 1)) = c * g σ c k := by
  rw [g_succ, AlgEquiv.apply_symm_apply]

theorem g_eq_prod (σ : F ≃ₐ[E] F) (c : F) (k : ℕ) :
    g σ c k = ∏ i ∈ Finset.range k, (⇑σ.symm)^[i + 1] c := by
  induction k with
  | zero => simp [g_zero]
  | succ k ih =>
      rw [g_succ, ih, map_mul, map_prod, prod_range_succ', mul_comm]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem c_mul_g_eq_norm (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) (c : F) {m : ℕ}
    (hm : m + 1 = Module.finrank E F) :
    c * g σ c m = algebraMap E F (Algebra.norm E c) := by
  rw [g_eq_prod, ← prod_range_iterate_eq_algebraMap_norm (forall_mem_zpowers_symm hgen) c, ← hm,
    prod_range_succ']
  simp only [Function.iterate_zero, id_eq]
  rw [mul_comm]

def S (σ : F ≃ₐ[E] F) (c : F) (m : ℕ) (t : 𝔸) : 𝔸 :=
  ∑ k ∈ Finset.range (m + 1), ι (g σ c k) * (θ D σ)^[m - k] t

theorem T_S (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) (c : F) {m : ℕ}
    (hm : m + 1 = Module.finrank E F) (t : 𝔸) :
    T D σ c (S D σ c m t) = ι (1 - algebraMap E F (Algebra.norm E c)) * t := by

  set a : ℕ → 𝔸 := fun k => ι (σ (g σ c k)) * (θ D σ)^[m + 1 - k] t with ha
  set b : ℕ → 𝔸 := fun k => ι (c * g σ c k) * (θ D σ)^[m - k] t with hb
  have hθS : θ D σ (S D σ c m t) = ∑ k ∈ Finset.range (m + 1), a k := by
    rw [S, θ_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [θ_ι_mul, ha]
    simp only
    congr 1
    rw [← Function.iterate_succ_apply' (θ D σ)]
    congr 1
    have hk' : k < m + 1 := mem_range.mp hk
    omega
  have hcS : ι c * S D σ c m t = ∑ k ∈ Finset.range (m + 1), b k := by
    rw [S, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [hb]
    simp only
    rw [map_mul, mul_assoc]

  have hshift : ∀ k ∈ Finset.range m, a (k + 1) = b k := by
    intro k hk
    rw [ha, hb]
    simp only
    rw [σ_g_succ]
    congr 2
    have hk' : k < m := mem_range.mp hk
    omega
  rw [T_apply, hθS, hcS, sum_range_succ' a m, sum_range_succ b m]
  rw [sum_congr rfl hshift]

  have e1 : (∑ k ∈ Finset.range m, b k + a 0) - (∑ k ∈ Finset.range m, b k + b m) = a 0 - b m := by abel
  rw [e1, ha, hb]
  simp only
  rw [g_zero, map_one, map_one, one_mul, Nat.sub_zero, hm, iterate_θ_finrank D hgen, Nat.sub_self,
    Function.iterate_zero, id_eq, c_mul_g_eq_norm hgen c hm, map_sub, map_one, sub_mul, one_mul]

theorem T_surjective (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) {c : F}
    (hc : Algebra.norm E c ≠ 1) : Function.Surjective (T D σ c) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = Module.finrank E F :=
    ⟨Module.finrank E F - 1, Nat.sub_add_cancel Module.finrank_pos⟩
  intro t
  set e : E := 1 - Algebra.norm E c with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  refine ⟨ι (algebraMap E F e⁻¹) * S D σ c m t, ?_⟩
  rw [T_ι_mul_of_fixed D σ c (σ.commutes _), T_S D hgen c hm, ← mul_assoc, ← map_mul]
  have : algebraMap E F e⁻¹ * (1 - algebraMap E F (Algebra.norm E c)) = 1 := by
    rw [← map_one (algebraMap E F), ← map_sub, ← he, ← map_mul, inv_mul_cancel₀ he0]
  rw [this, map_one, one_mul]

theorem main (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) (c : F) (hc : Algebra.norm E c ≠ 1) :
    Function.Bijective fun s : 𝔸 => (D.act σ : RingAut 𝔸) s - algebraMap F 𝔸 c * s :=
  ⟨T_injective D hgen hc, T_surjective D hgen hc⟩

end Main

end R1HypL45

end

open NumberField in
theorem solution
    {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
    (D : M4aHerbrand.IdeleGaloisDescent R E F)
    {σ : F ≃ₐ[E] F} (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ)
    (c : F) (hc : Algebra.norm E c ≠ 1) :
    Function.Bijective fun s : AdeleRing R F =>
      (D.act σ : RingAut (AdeleRing R F)) s - algebraMap F (AdeleRing R F) c * s :=
  R1HypL45.main D hgen c hc

end S_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one (solution)
