-- Prove2me | solution 1 for LT.TwistedNorm.exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5198e599-f436-56f0-aa58-9f3e84e31c82

import Definitions.Def_TwistedNormClasses
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers

set_option autoImplicit false

attribute [local simp] LT.TwistedNorm.sigmaPartialNorm_one

namespace LT
p2m_export "LT" "TwistedNorm.sigmaPartialNorm_one TwistedNorm.sigmaNormPow TwistedNorm.iterate_generalLinearGroup_map_eq_self TwistedNorm.iterate_finrank_apply_of_generator"
namespace TwistedNorm
p2m_export "LT.TwistedNorm" "sigmaPartialNorm sigmaPartialNorm_succ' sigmaPartialNorm_one sigmaNormPow sigmaNormPow_def iterate_map_sigmaNormPow iterate_generalLinearGroup_map_eq_self map_sigmaNormPow_generalLinearGroup coe_generalLinearGroup_map iterate_finrank_apply_of_generator"
namespace NormCentralizerDescent
p2m_open "LT.TwistedNorm LT"

section Cocycle

variable {G : Type*} [Group G]

private def lemma42Cocycle (σ : G →* G) (x y : G) (r : ℕ) : G :=
  sigmaPartialNorm σ y r * (sigmaPartialNorm σ x r)⁻¹

@[scoped simp] private theorem lemma42Cocycle_zero (σ : G →* G) (x y : G) :
    lemma42Cocycle σ x y 0 = 1 := by
  simp [lemma42Cocycle]

@[scoped simp] private theorem lemma42Cocycle_one (σ : G →* G) (x y : G) :
    lemma42Cocycle σ x y 1 = y * x⁻¹ := by
  simp [lemma42Cocycle]

private theorem lemma42Cocycle_succ (σ : G →* G) (x y : G) (r : ℕ) :
    lemma42Cocycle σ x y (r + 1)
      = lemma42Cocycle σ x y 1 * (x * σ (lemma42Cocycle σ x y r) * x⁻¹) := by
  rw [lemma42Cocycle_one]
  unfold lemma42Cocycle
  rw [sigmaPartialNorm_succ' σ y r, sigmaPartialNorm_succ' σ x r]
  simp only [map_mul, map_inv, mul_inv_rev]
  group

private theorem lemma42Cocycle_ell (σ : G →* G) (ℓ : ℕ) {x y : G}
    (hN : sigmaNormPow σ ℓ x = sigmaNormPow σ ℓ y) :
    lemma42Cocycle σ x y ℓ = 1 := by
  unfold lemma42Cocycle
  rw [← sigmaNormPow_def, ← sigmaNormPow_def, ← hN]
  group

private theorem lemma42Cocycle_normPow_conj (σ : G →* G) (ℓ : ℕ) {x y : G}
    (hσx : (⇑σ)^[ℓ] x = x) (hσy : (⇑σ)^[ℓ] y = y)
    (hN : sigmaNormPow σ ℓ x = sigmaNormPow σ ℓ y) (r : ℕ) :
    lemma42Cocycle σ x y r * sigmaNormPow σ ℓ x * (lemma42Cocycle σ x y r)⁻¹
      = sigmaNormPow σ ℓ x := by
  calc lemma42Cocycle σ x y r * sigmaNormPow σ ℓ x * (lemma42Cocycle σ x y r)⁻¹
      = sigmaPartialNorm σ y r
          * ((sigmaPartialNorm σ x r)⁻¹ * sigmaNormPow σ ℓ x * sigmaPartialNorm σ x r)
          * (sigmaPartialNorm σ y r)⁻¹ := by
        unfold lemma42Cocycle; group
    _ = sigmaPartialNorm σ y r * ((⇑σ)^[r] (sigmaNormPow σ ℓ x))
          * (sigmaPartialNorm σ y r)⁻¹ := by rw [← iterate_map_sigmaNormPow σ ℓ hσx r]
    _ = sigmaPartialNorm σ y r * ((⇑σ)^[r] (sigmaNormPow σ ℓ y))
          * (sigmaPartialNorm σ y r)⁻¹ := by rw [hN]
    _ = sigmaPartialNorm σ y r
          * ((sigmaPartialNorm σ y r)⁻¹ * sigmaNormPow σ ℓ y * sigmaPartialNorm σ y r)
          * (sigmaPartialNorm σ y r)⁻¹ := by rw [iterate_map_sigmaNormPow σ ℓ hσy r]
    _ = sigmaNormPow σ ℓ y := by group
    _ = sigmaNormPow σ ℓ x := hN.symm

private theorem lemma42Cocycle_mul_normPow (σ : G →* G) (ℓ : ℕ) {x y : G}
    (hσx : (⇑σ)^[ℓ] x = x) (hσy : (⇑σ)^[ℓ] y = y)
    (hN : sigmaNormPow σ ℓ x = sigmaNormPow σ ℓ y) (r : ℕ) :
    lemma42Cocycle σ x y r * sigmaNormPow σ ℓ x
      = sigmaNormPow σ ℓ x * lemma42Cocycle σ x y r := by
  have h := lemma42Cocycle_normPow_conj σ ℓ hσx hσy hN r
  calc lemma42Cocycle σ x y r * sigmaNormPow σ ℓ x
      = (lemma42Cocycle σ x y r * sigmaNormPow σ ℓ x * (lemma42Cocycle σ x y r)⁻¹)
          * lemma42Cocycle σ x y r := by group
    _ = sigmaNormPow σ ℓ x * lemma42Cocycle σ x y r := by rw [h]

private def sigmaTwistedPartialNorm (σ : G →* G) (x c : G) : ℕ → G
  | 0 => 1
  | r + 1 => c * (x * σ (sigmaTwistedPartialNorm σ x c r) * x⁻¹)

@[scoped simp] private theorem sigmaTwistedPartialNorm_zero (σ : G →* G) (x c : G) :
    sigmaTwistedPartialNorm σ x c 0 = 1 := rfl

private theorem sigmaTwistedPartialNorm_succ (σ : G →* G) (x c : G) (r : ℕ) :
    sigmaTwistedPartialNorm σ x c (r + 1)
      = c * (x * σ (sigmaTwistedPartialNorm σ x c r) * x⁻¹) := rfl

private theorem sigmaTwistedPartialNorm_lemma42Cocycle (σ : G →* G) (x y : G) (r : ℕ) :
    sigmaTwistedPartialNorm σ x (y * x⁻¹) r = lemma42Cocycle σ x y r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaTwistedPartialNorm_succ, ih, lemma42Cocycle_succ, lemma42Cocycle_one]

private def SigmaTwistedCentralizerH1Trivial (σ : G →* G) (ℓ : ℕ) (x : G) : Prop :=
  ∀ c : G, c * sigmaNormPow σ ℓ x = sigmaNormPow σ ℓ x * c →
    sigmaTwistedPartialNorm σ x c ℓ = 1 →
      ∃ h : G, h * sigmaNormPow σ ℓ x = sigmaNormPow σ ℓ x * h
        ∧ c = h⁻¹ * (x * σ h * x⁻¹)

private theorem lemma42_sigmaConj_of_sigmaNormPow_eq (σ : G →* G) (ℓ : ℕ)
    (hσℓ : ∀ g : G, (⇑σ)^[ℓ] g = g) {x y : G}
    (hN : sigmaNormPow σ ℓ x = sigmaNormPow σ ℓ y)
    (hH1 : SigmaTwistedCentralizerH1Trivial σ ℓ x) :
    ∃ h : G, y = h⁻¹ * x * σ h := by
  have hcomm : (y * x⁻¹) * sigmaNormPow σ ℓ x = sigmaNormPow σ ℓ x * (y * x⁻¹) := by
    have h1 := lemma42Cocycle_mul_normPow σ ℓ (hσℓ x) (hσℓ y) hN 1
    rwa [lemma42Cocycle_one] at h1
  have htw : sigmaTwistedPartialNorm σ x (y * x⁻¹) ℓ = 1 := by
    rw [sigmaTwistedPartialNorm_lemma42Cocycle, lemma42Cocycle_ell σ ℓ hN]
  obtain ⟨h, -, hch⟩ := hH1 (y * x⁻¹) hcomm htw
  refine ⟨h, ?_⟩
  calc y = (y * x⁻¹) * x := by group
    _ = (h⁻¹ * (x * σ h * x⁻¹)) * x := by rw [hch]
    _ = h⁻¹ * x * σ h := by group

end Cocycle

section Matrices

open Matrix

variable {L : Type*} [Field L]

local notation "A" => Matrix (Fin 2) (Fin 2) L

private def polar (P Q : A) : L := (P + Q).det - P.det - Q.det

private theorem polar_eq (P Q : A) : polar P Q = P 0 0 * Q 1 1 + Q 0 0 * P 1 1 - P 0 1 * Q 1 0 - Q 0 1 * P 1 0 := by
  simp only [polar, Matrix.det_fin_two, Matrix.add_apply]
  ring

private theorem det_add_eq (P Q : A) : (P + Q).det = P.det + Q.det + polar P Q := by
  simp only [polar]; ring

private theorem det_smul_two (a : L) (P : A) : (a • P).det = a ^ 2 * P.det := by
  simp only [Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem polar_smul_left (a : L) (P Q : A) : polar (a • P) Q = a * polar P Q := by
  simp only [polar_eq, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem polar_add_right (P Q R : A) : polar P (Q + R) = polar P Q + polar P R := by
  simp only [polar_eq, Matrix.add_apply]
  ring

private theorem polar_comm (P Q : A) : polar P Q = polar Q P := by
  simp only [polar_eq]
  ring

private theorem polar_sum_right {ι : Type*} (s : Finset ι) (P : A) (Q : ι → A) :
    polar P (∑ i ∈ s, Q i) = ∑ i ∈ s, polar P (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polar_eq]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, polar_add_right, ih]

private theorem det_sum_smul_eq_zero {ι : Type*} (s : Finset ι) (a : ι → L) (w : ι → A)
    (hdet : ∀ i ∈ s, (w i).det = 0) (hpol : ∀ i ∈ s, ∀ j ∈ s, polar (w i) (w j) = 0) :
    (∑ i ∈ s, a i • w i).det = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.det_fin_two]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, det_add_eq, det_smul_two, hdet i (Finset.mem_insert_self i s),
        ih (fun j hj => hdet j (Finset.mem_insert_of_mem hj))
          (fun j hj k hk => hpol j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)),
        polar_smul_left, polar_sum_right]
      have : ∑ j ∈ s, polar (w i) (a j • w j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [polar_comm, polar_smul_left, polar_comm,
          hpol i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj), mul_zero]
      rw [this]; ring

end Matrices

section Core

open Matrix

variable {L : Type*} [Field L]

local notation "A" => Matrix (Fin 2) (Fin 2) L
local notation "GL₂" => GL (Fin 2) L

private theorem conj_mul_conj (δ : GL₂) (X Y : A) :
    ((δ : A) * X * ((δ⁻¹ : GL₂) : A)) * ((δ : A) * Y * ((δ⁻¹ : GL₂) : A))
      = (δ : A) * (X * Y) * ((δ⁻¹ : GL₂) : A) := by
  simp only [mul_assoc]
  rw [← mul_assoc ((δ⁻¹ : GL₂) : A) (δ : A), Units.inv_mul, one_mul]

private def tauM (σ : L →+* L) (δ : GL₂) (m : A) : A := (δ : A) * m.map σ * ((δ⁻¹ : GL₂) : A)

private def theta (σ : L →+* L) (δ c : GL₂) (m : A) : A := tauM σ δ m * ((c⁻¹ : GL₂) : A)

private theorem tauM_coe (σ : L →+* L) (δ g : GL₂) :
    tauM σ δ (g : A) = ((δ * Matrix.GeneralLinearGroup.map σ g * δ⁻¹ : GL₂) : A) := by
  simp only [tauM, Units.val_mul, coe_generalLinearGroup_map]

private theorem theta_add (σ : L →+* L) (δ c : GL₂) (m m' : A) :
    theta σ δ c (m + m') = theta σ δ c m + theta σ δ c m' := by
  have hadd : (m + m').map σ = m.map σ + m'.map σ := by ext i j; simp
  simp only [theta, tauM, hadd, mul_add, add_mul]

private theorem map_smul_eq (σ : L →+* L) (a : L) (m : A) : (a • m).map σ = σ a • m.map σ := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]

private theorem theta_smul (σ : L →+* L) (δ c : GL₂) (a : L) (m : A) :
    theta σ δ c (a • m) = σ a • theta σ δ c m := by
  simp only [theta, tauM, map_smul_eq, Matrix.mul_smul, Matrix.smul_mul]

private theorem theta_sum (σ : L →+* L) (δ c : GL₂) {ι : Type*} (s : Finset ι) (f : ι → A) :
    theta σ δ c (∑ i ∈ s, f i) = ∑ i ∈ s, theta σ δ c (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [theta, tauM]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, theta_add, ih]

private theorem iterate_tauM (σ : L →+* L) (δ : GL₂) (k : ℕ) (m : A) :
    (tauM σ δ)^[k] m
      = ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ k : GL₂) : A) * m.map ((⇑σ)^[k])
        * (((sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ k)⁻¹ : GL₂) : A) := by
  induction k generalizing m with
  | zero => simp [Matrix.map_id]
  | succ k ih =>
      have hmm : (m.map ((⇑σ)^[k])).map σ = m.map ((⇑σ)^[k + 1]) := by
        rw [Matrix.map_map, Function.iterate_succ']
      have hinv : (sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ (k + 1))⁻¹
          = Matrix.GeneralLinearGroup.map σ (sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) δ k)⁻¹ * δ⁻¹ := by
        rw [sigmaPartialNorm_succ', _root_.mul_inv_rev, map_inv]
      rw [Function.iterate_succ_apply', ih, hinv, sigmaPartialNorm_succ']
      simp only [tauM, Matrix.map_mul, ← coe_generalLinearGroup_map, hmm, Units.val_mul]
      simp only [mul_assoc]

private theorem iterate_theta (σ : L →+* L) (δ c : GL₂) (k : ℕ) (m : A) :
    (theta σ δ c)^[k] m
      = (tauM σ δ)^[k] m * (((sigmaTwistedPartialNorm (Matrix.GeneralLinearGroup.map σ) δ c k)⁻¹ : GL₂) : A) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      have hinv : (sigmaTwistedPartialNorm (Matrix.GeneralLinearGroup.map σ) δ c (k + 1))⁻¹
          = δ * Matrix.GeneralLinearGroup.map σ
              (sigmaTwistedPartialNorm (Matrix.GeneralLinearGroup.map σ) δ c k)⁻¹ * δ⁻¹ * c⁻¹ := by
        rw [sigmaTwistedPartialNorm_succ, map_inv]; group
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hinv]
      simp only [theta, tauM, Matrix.map_mul, ← coe_generalLinearGroup_map, Units.val_mul]
      simp only [mul_assoc]
      congr 2
      rw [← mul_assoc ((δ⁻¹ : GL₂) : A) (δ : A), Units.inv_mul, one_mul]

private theorem iterate_tauM_eq_self {σ : L →+* L} {δ N : GL₂} {n : ℕ} (hσn : ∀ a : L, (⇑σ)^[n] a = a)
    {m : A} (hm : m * (N : A) = (N : A) * m) (hN : sigmaNormPow (Matrix.GeneralLinearGroup.map σ) n δ = N) :
    (tauM σ δ)^[n] m = m := by
  rw [iterate_tauM, ← sigmaNormPow_def, hN]
  have hmap : m.map ((⇑σ)^[n]) = m := by ext i j; simp [Matrix.map_apply, hσn]
  rw [hmap, ← hm, mul_assoc, Units.mul_inv, mul_one]

private theorem tauM_comm {σ : L →+* L} {δ N : GL₂} (hδN : Matrix.GeneralLinearGroup.map σ N = δ⁻¹ * N * δ)
    {m : A} (hm : m * (N : A) = (N : A) * m) :
    tauM σ δ m * (N : A) = (N : A) * tauM σ δ m := by
  have hNconj : (N : A) = (δ : A) * (N : A).map σ * ((δ⁻¹ : GL₂) : A) := by
    have hu : δ * Matrix.GeneralLinearGroup.map σ N * δ⁻¹ = N := by rw [hδN]; group
    have h := congrArg (fun u : GL₂ => (u : A)) hu
    simp only [Units.val_mul, coe_generalLinearGroup_map] at h
    exact h.symm
  have hmul : (m.map σ) * (N : A).map σ = (N : A).map σ * m.map σ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hm]
  conv_lhs => rw [hNconj]
  conv_rhs => rw [hNconj]
  rw [tauM, conj_mul_conj, conj_mul_conj, hmul]

private theorem theta_comm {σ : L →+* L} {δ c N : GL₂} (hδN : Matrix.GeneralLinearGroup.map σ N = δ⁻¹ * N * δ)
    (hcN : c * N = N * c) {m : A} (hm : m * (N : A) = (N : A) * m) :
    theta σ δ c m * (N : A) = (N : A) * theta σ δ c m := by
  have hc' : c⁻¹ * N = N * c⁻¹ := by
    calc c⁻¹ * N = c⁻¹ * (N * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * N) * c⁻¹ := by rw [hcN]
      _ = N * c⁻¹ := by group
  have hc'' : ((c⁻¹ : GL₂) : A) * (N : A) = (N : A) * ((c⁻¹ : GL₂) : A) := by
    rw [← Units.val_mul, ← Units.val_mul, hc']
  rw [theta, mul_assoc, hc'', ← mul_assoc, tauM_comm hδN hm, mul_assoc]

end Core

section Descent

open Matrix

variable {L : Type*} [Field L]

local notation "A" => Matrix (Fin 2) (Fin 2) L
local notation "GL₂" => GL (Fin 2) L

private def dvec (σ : L →+* L) (δ c : GL₂) (n : ℕ) (θ : L) (m : A) : A :=
  ∑ k ∈ Finset.range n, ((⇑σ)^[k] θ) • (theta σ δ c)^[k] m

private theorem theta_dvec {σ : L →+* L} {δ c : GL₂} {n : ℕ} (hσn : ∀ a : L, (⇑σ)^[n] a = a) {θ : L} {m : A}
    (hm : (theta σ δ c)^[n] m = m) : theta σ δ c (dvec σ δ c n θ m) = dvec σ δ c n θ m := by
  unfold dvec
  rw [theta_sum]
  simp only [theta_smul]
  have step : ∀ k : ℕ, σ ((⇑σ)^[k] θ) • theta σ δ c ((theta σ δ c)^[k] m)
      = ((⇑σ)^[k + 1] θ) • (theta σ δ c)^[k + 1] m := by
    intro k
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  simp only [step]

  set g : ℕ → A := fun k => ((⇑σ)^[k] θ) • (theta σ δ c)^[k] m with hg
  have h1 := Finset.sum_range_succ' g n
  have h2 := Finset.sum_range_succ g n
  have hend : g n = g 0 := by simp only [hg, hσn, hm, Function.iterate_zero, id]
  have : ∑ k ∈ Finset.range n, g (k + 1) = ∑ k ∈ Finset.range n, g k := by
    have := h1.symm.trans h2
    rw [hend] at this
    exact add_right_cancel this
  simpa only [hg] using this

private theorem dvec_comm {σ : L →+* L} {δ c N : GL₂} {n : ℕ} (hδN : Matrix.GeneralLinearGroup.map σ N = δ⁻¹ * N * δ)
    (hcN : c * N = N * c) {θ : L} {m : A} (hm : m * (N : A) = (N : A) * m) :
    dvec σ δ c n θ m * (N : A) = (N : A) * dvec σ δ c n θ m := by
  have hk : ∀ k : ℕ, (theta σ δ c)^[k] m * (N : A) = (N : A) * (theta σ δ c)^[k] m := by
    intro k
    induction k with
    | zero => simpa using hm
    | succ k ih => rw [Function.iterate_succ_apply']; exact theta_comm hδN hcN ih
  unfold dvec
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, hk]

end Descent

section Main

open Matrix

variable {L : Type*} [Field L]

local notation "A" => Matrix (Fin 2) (Fin 2) L
local notation "GL₂" => GL (Fin 2) L

private theorem exists_eq_inv_mul_conj_map {σ : L →+* L} {n : ℕ} (hn : 0 < n) (hσn : ∀ a : L, (⇑σ)^[n] a = a)
    {ι : Type*} [Fintype ι] (θ μ : ι → L)
    (horth0 : ∑ i, μ i * θ i = 1)
    (horth : ∀ k : ℕ, 0 < k → k < n → ∑ i, μ i * (⇑σ)^[k] (θ i) = 0)
    (δ : GL₂) {N : GL₂} (hN : sigmaNormPow (Matrix.GeneralLinearGroup.map σ) n δ = N)
    (c : GL₂) (hcN : c * N = N * c) (htw : sigmaTwistedPartialNorm (Matrix.GeneralLinearGroup.map σ) δ c n = 1) :
    ∃ h : GL₂, h * N = N * h ∧ c = h⁻¹ * (δ * Matrix.GeneralLinearGroup.map σ h * δ⁻¹) := by
  classical

  have hδN : Matrix.GeneralLinearGroup.map σ N = δ⁻¹ * N * δ := by
    rw [← hN]
    exact map_sigmaNormPow_generalLinearGroup hσn δ

  have hper : ∀ m : A, m * (N : A) = (N : A) * m → (theta σ δ c)^[n] m = m := by
    intro m hm
    rw [iterate_theta, iterate_tauM_eq_self hσn hm hN, htw, inv_one, Units.val_one, mul_one]
  by_contra hne

  have hsing : ∀ m : A, m * (N : A) = (N : A) * m → theta σ δ c m = m → m.det = 0 := by
    intro m hm hfix
    by_contra hdet
    let h : GL₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero m hdet
    have hh : (h : A) = m := rfl
    refine hne ⟨h, Units.ext (by rw [Units.val_mul, Units.val_mul, hh, hm]), ?_⟩

    have hfix' : tauM σ δ m = m * (c : A) := by
      have := congrArg (· * (c : A)) hfix
      simpa only [theta, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one] using this
    have hGL : δ * Matrix.GeneralLinearGroup.map σ h * δ⁻¹ = h * c := by
      apply Units.ext
      rw [← tauM_coe, hh, hfix', Units.val_mul, hh]
    rw [hGL, ← mul_assoc, inv_mul_cancel, one_mul]

  have hpol : ∀ m m' : A, m * (N : A) = (N : A) * m → theta σ δ c m = m →
      m' * (N : A) = (N : A) * m' → theta σ δ c m' = m' → polar m m' = 0 := by
    intro m m' hm hfm hm' hfm'
    have hs : (m + m') * (N : A) = (N : A) * (m + m') := by rw [add_mul, mul_add, hm, hm']
    have hf : theta σ δ c (m + m') = m + m' := by rw [theta_add, hfm, hfm']
    rw [polar, hsing _ hs hf, hsing _ hm hfm, hsing _ hm' hfm', sub_zero, sub_zero]

  have h1c : (1 : A) * (N : A) = (N : A) * 1 := by rw [one_mul, mul_one]
  have hWc : ∀ i, dvec σ δ c n (θ i) 1 * (N : A) = (N : A) * dvec σ δ c n (θ i) 1 :=
    fun i => dvec_comm hδN hcN h1c
  have hWf : ∀ i, theta σ δ c (dvec σ δ c n (θ i) 1) = dvec σ δ c n (θ i) 1 :=
    fun i => theta_dvec hσn (hper 1 h1c)

  have hsum : ∑ i, μ i • dvec σ δ c n (θ i) 1 = 1 := by
    have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
    calc ∑ i, μ i • dvec σ δ c n (θ i) 1
        = ∑ i, ∑ k ∈ Finset.range n, (μ i * (⇑σ)^[k] (θ i)) • (theta σ δ c)^[k] (1 : A) := by
          simp only [dvec, Finset.smul_sum, smul_smul]
      _ = ∑ k ∈ Finset.range n, ∑ i, (μ i * (⇑σ)^[k] (θ i)) • (theta σ δ c)^[k] (1 : A) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.range n, (∑ i, μ i * (⇑σ)^[k] (θ i)) • (theta σ δ c)^[k] (1 : A) := by
          simp only [Finset.sum_smul]
      _ = (∑ i, μ i * (⇑σ)^[0] (θ i)) • (theta σ δ c)^[0] (1 : A) := by
          refine Finset.sum_eq_single 0 (fun k hk hk0 => ?_) (fun h => absurd h0 h)
          rw [horth k (Nat.pos_of_ne_zero hk0) (Finset.mem_range.mp hk), zero_smul]
      _ = 1 := by simp [horth0]
  have : (1 : A).det = 0 := by
    rw [← hsum]
    exact det_sum_smul_eq_zero _ _ _ (fun i _ => hsing _ (hWc i) (hWf i))
      (fun i _ j _ => hpol _ _ (hWc i) (hWf i) (hWc j) (hWf j))
  simp at this

end Main

section

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private theorem orderOf_eq_finrank_of_generator {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) : orderOf σ = Module.finrank F L := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

private theorem pow_ne_one_of_generator_of_lt {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {i : ℕ} (hi : i ≠ 0) (hlt : i < Module.finrank F L) :
    σ ^ i ≠ 1 :=
  pow_ne_one_of_lt_orderOf hi (by rwa [orderOf_eq_finrank_of_generator hgen])

private theorem sum_traceDual_mul_apply_eq_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : Module.Basis ι F L) (g : L ≃ₐ[F] L) :
    ∃ e : ι ≃ (L ≃ₐ[F] L),
      ∑ i, θ.traceDual i * g (θ i) = if e.symm 1 = e.symm g then (1 : L) else 0 := by
  have hcol : ∀ i j : ι, ∑ τ : L ≃ₐ[F] L, τ (θ i) * τ (θ.traceDual j) = if i = j then (1 : L) else 0 := by
    intro i j
    have h := trace_eq_sum_automorphisms (K := F) (θ i * θ.traceDual j)
    rw [Module.Basis.trace_mul_traceDual] at h
    simp only [map_mul] at h
    rw [← h]
    split_ifs <;> simp
  have hcard : Fintype.card ι = Fintype.card (L ≃ₐ[F] L) := by
    rw [← Module.finrank_eq_card_basis θ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let e : ι ≃ (L ≃ₐ[F] L) := Fintype.equivOfCardEq hcard
  refine ⟨e, ?_⟩
  let A : Matrix ι ι L := Matrix.of fun i j => e j (θ i)
  let B : Matrix ι ι L := Matrix.of fun j k => e j (θ.traceDual k)
  have hAB : A * B = 1 := by
    ext i k
    simp only [A, B, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← hcol i k]
    exact e.sum_comp fun τ => τ (θ i) * τ (θ.traceDual k)
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hentry := congrFun (congrFun hBA (e.symm 1)) (e.symm g)
  simpa only [A, B, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Equiv.apply_symm_apply,
    AlgEquiv.one_apply] using hentry

private theorem sum_traceDual_mul_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : Module.Basis ι F L) :
    ∑ i, θ.traceDual i * θ i = 1 := by
  classical
  obtain ⟨e, he⟩ := sum_traceDual_mul_apply_eq_core θ (1 : L ≃ₐ[F] L)
  simpa [AlgEquiv.one_apply] using he

private theorem sum_traceDual_mul_apply_eq_zero_of_ne_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : Module.Basis ι F L) {g : L ≃ₐ[F] L} (hg : g ≠ 1) :
    ∑ i, θ.traceDual i * g (θ i) = 0 := by
  classical
  obtain ⟨e, he⟩ := sum_traceDual_mul_apply_eq_core θ g
  rw [he, if_neg]
  exact fun h => hg (e.symm.injective h).symm

end

section Assembly

private theorem sigmaTwistedCentralizerH1Trivial_generalLinearGroup
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ : GL (Fin 2) L) :
    SigmaTwistedCentralizerH1Trivial (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ := by
  classical
  intro c hcN htw
  have hn : 0 < Module.finrank F L := Module.finrank_pos
  have hσn : ∀ a : L, (⇑(σ : L →+* L))^[Module.finrank F L] a = a := fun a => by
    rw [RingHom.coe_coe]
    exact iterate_finrank_apply_of_generator hgen a
  let θ := Module.finBasis F L
  refine exists_eq_inv_mul_conj_map hn hσn (⇑θ) (⇑θ.traceDual) (sum_traceDual_mul_eq_one θ) ?_ δ rfl c hcN htw
  intro k hk0 hkn
  have h := sum_traceDual_mul_apply_eq_zero_of_ne_one θ (pow_ne_one_of_generator_of_lt hgen hk0.ne' hkn)
  simpa only [AlgEquiv.coe_pow, RingHom.coe_coe] using h

end Assembly

end LT.TwistedNorm.NormCentralizerDescent
p2m_reactivate "P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers.LT P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers.LT.TwistedNorm P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers.LT.TwistedNorm.NormCentralizerDescent"
p2m_reactivate "P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers.LT P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers.LT.TwistedNorm"
p2m_reactivate "P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers.LT"

theorem solution
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) L}
    (hN : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ₁
      = LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ₂) :
    ∃ h : Matrix.GeneralLinearGroup (Fin 2) L, δ₂ = h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h
 := by
  exact LT.TwistedNorm.NormCentralizerDescent.lemma42_sigmaConj_of_sigmaNormPow_eq _ _
    (LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self
      (fun a => by
        rw [RingHom.coe_coe]
        exact LT.TwistedNorm.iterate_finrank_apply_of_generator hgen a))
    hN (LT.TwistedNorm.NormCentralizerDescent.sigmaTwistedCentralizerH1Trivial_generalLinearGroup hgen δ₁)

example {δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) ℚ}
    (hN : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map ((AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) : ℚ →+* ℚ))
        (Module.finrank ℚ ℚ) δ₁
      = LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map ((AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) : ℚ →+* ℚ))
        (Module.finrank ℚ ℚ) δ₂) :
    ∃ h : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      δ₂ = h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map ((AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) : ℚ →+* ℚ) h :=
  solution (σ := AlgEquiv.refl) (fun τ => by rw [Subsingleton.elim τ AlgEquiv.refl]; exact Subgroup.mem_zpowers _) hN

end S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers
end P2MW
export P2MW.S_LT_TwistedNorm_exists_eq_sigmaConj_of_sigmaNormPow_eq_of_forall_mem_zpowers (solution)
