-- Prove2me | solution 1 for Matrix.exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d4394592-cb49-59d6-8a1e-efd7d2662006

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Topology Filter Metric Set
open scoped Matrix

noncomputable section

namespace HolIntertwiner

section holomorphy

variable {p q s : Type*} [Fintype p] [Fintype q] [Fintype s]

def HolM (A : ℂ → Matrix p q ℂ) (U : Set ℂ) : Prop := ∀ i j, DifferentiableOn ℂ (fun z => A z i j) U

theorem holM_const (A : Matrix p q ℂ) (U : Set ℂ) : HolM (fun _ => A) U := fun _ _ => differentiableOn_const _

theorem HolM.add {A B : ℂ → Matrix p q ℂ} {U : Set ℂ} (hA : HolM A U) (hB : HolM B U) :
    HolM (fun z => A z + B z) U := fun i j => (hA i j).add (hB i j)

theorem HolM.sub {A B : ℂ → Matrix p q ℂ} {U : Set ℂ} (hA : HolM A U) (hB : HolM B U) :
    HolM (fun z => A z - B z) U := fun i j => (hA i j).sub (hB i j)

theorem HolM.mul {A : ℂ → Matrix p q ℂ} {B : ℂ → Matrix q s ℂ} {U : Set ℂ} (hA : HolM A U) (hB : HolM B U) :
    HolM (fun z => A z * B z) U := by
  intro i j
  have : (fun z => (A z * B z) i j) = fun z => ∑ k, A z i k * B z k j := by
    funext z; simp [Matrix.mul_apply]
  rw [this]
  exact DifferentiableOn.fun_sum (fun k _ => (hA i k).mul (hB k j))

theorem HolM.smul {A : ℂ → Matrix p q ℂ} {c : ℂ → ℂ} {U : Set ℂ} (hc : DifferentiableOn ℂ c U) (hA : HolM A U) :
    HolM (fun z => c z • A z) U := fun i j => by
  show DifferentiableOn ℂ (fun z => c z * A z i j) U
  exact hc.mul (hA i j)

theorem HolM.sum {ι : Type*} {t : Finset ι} {A : ι → ℂ → Matrix p q ℂ} {U : Set ℂ} (hA : ∀ x ∈ t, HolM (A x) U) :
    HolM (fun z => ∑ x ∈ t, A x z) U := by
  intro i j
  have : (fun z => (∑ x ∈ t, A x z) i j) = fun z => ∑ x ∈ t, A x z i j := by
    funext z; simp [Matrix.sum_apply]
  rw [this]
  exact DifferentiableOn.fun_sum (fun x hx => hA x hx i j)

theorem HolM.det [DecidableEq p] {A : ℂ → Matrix p p ℂ} {U : Set ℂ} (hA : HolM A U) :
    DifferentiableOn ℂ (fun z => (A z).det) U := by
  have : (fun z => (A z).det) = fun z => ∑ σ : Equiv.Perm p, (Equiv.Perm.sign σ : ℂ) * ∏ i, A z (σ i) i := by
    funext z; rw [Matrix.det_apply']
  rw [this]
  refine DifferentiableOn.fun_sum (fun σ _ => ?_)
  refine (differentiableOn_const _).mul ?_
  exact DifferentiableOn.fun_finsetProd (fun i _ => hA (σ i) i)

theorem HolM.updateCol [DecidableEq q] {A : ℂ → Matrix p q ℂ} {U : Set ℂ} (hA : HolM A U) (j : q) (b : p → ℂ) :
    HolM (fun z => (A z).updateCol j b) U := by
  intro i k
  by_cases hk : k = j
  · subst hk
    have : (fun z => (A z).updateCol k b i k) = fun _ => b i := by funext z; simp
    rw [this]; exact differentiableOn_const _
  · have : (fun z => (A z).updateCol j b i k) = fun z => A z i k := by funext z; simp [hk]
    rw [this]; exact hA i k

theorem HolM.cramer [DecidableEq p] {A : ℂ → Matrix p p ℂ} {U : Set ℂ} (hA : HolM A U) (b : p → ℂ) (i : p) :
    DifferentiableOn ℂ (fun z => Matrix.cramer (A z) b i) U := by
  have : (fun z => Matrix.cramer (A z) b i) = fun z => ((A z).updateCol i b).det := by
    funext z; rw [Matrix.cramer_apply]
  rw [this]
  exact (hA.updateCol i b).det

end holomorphy

section linalg

variable {n : ℕ}

def ip (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ := Matrix.trace (Aᴴ * B)

theorem ip_eq_sum (A B : Matrix (Fin n) (Fin n) ℂ) : ip A B = ∑ i, ∑ j, star (A i j) * B i j := by
  simp only [ip, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

def nsq (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem ip_self (A : Matrix (Fin n) (Fin n) ℂ) : ip A A = (nsq A : ℂ) := by
  simp only [ip_eq_sum, nsq, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem nsq_nonneg (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ nsq A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

theorem nsq_eq_zero {A : Matrix (Fin n) (Fin n) ℂ} (h : nsq A = 0) : A = 0 := by
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by positivity)).mp h i
    (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h1 j (Finset.mem_univ j)
  simpa using h2

theorem ip_self_eq_zero {A : Matrix (Fin n) (Fin n) ℂ} (h : ip A A = 0) : A = 0 := by
  rw [ip_self] at h
  exact nsq_eq_zero (by exact_mod_cast h)

theorem ip_self_ne_zero {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ≠ 0) : ip A A ≠ 0 :=
  fun h => hA (ip_self_eq_zero h)

theorem ip_add_right (A B C : Matrix (Fin n) (Fin n) ℂ) : ip A (B + C) = ip A B + ip A C := by
  simp only [ip, Matrix.mul_add, Matrix.trace_add]

theorem ip_sub_right (A B C : Matrix (Fin n) (Fin n) ℂ) : ip A (B - C) = ip A B - ip A C := by
  simp only [ip, Matrix.mul_sub, Matrix.trace_sub]

theorem ip_smul_right (A B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) : ip A (c • B) = c * ip A B := by
  simp only [ip, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem ip_zero_right (A : Matrix (Fin n) (Fin n) ℂ) : ip A 0 = 0 := by simp [ip]

theorem ip_zero_left (A : Matrix (Fin n) (Fin n) ℂ) : ip 0 A = 0 := by simp [ip]

theorem ip_sum_right {ι : Type*} (t : Finset ι) (A : Matrix (Fin n) (Fin n) ℂ) (B : ι → Matrix (Fin n) (Fin n) ℂ) :
    ip A (∑ x ∈ t, B x) = ∑ x ∈ t, ip A (B x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [ip_zero_right]
  | insert x t hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ip_add_right, ih]

theorem ip_sub_left (A B C : Matrix (Fin n) (Fin n) ℂ) : ip (A - B) C = ip A C - ip B C := by
  simp only [ip, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub]

theorem ip_mul_right_adj (M a N : Matrix (Fin n) (Fin n) ℂ) : ip (M * a) N = ip M (N * aᴴ) := by
  simp only [ip, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

theorem ip_mul_left_adj (b M N : Matrix (Fin n) (Fin n) ℂ) : ip (b * M) N = ip M (bᴴ * N) := by
  simp only [ip, Matrix.conjTranspose_mul, Matrix.mul_assoc]

def τ (a b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.mulRight ℂ a - LinearMap.mulLeft ℂ b

@[scoped simp] theorem τ_apply (a b M : Matrix (Fin n) (Fin n) ℂ) : τ a b M = M * a - b * M := by
  simp [τ]

def τd (a b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.mulRight ℂ aᴴ - LinearMap.mulLeft ℂ bᴴ

@[scoped simp] theorem τd_apply (a b N : Matrix (Fin n) (Fin n) ℂ) : τd a b N = N * aᴴ - bᴴ * N := by
  simp [τd]

theorem ip_τ_adj (a b M N : Matrix (Fin n) (Fin n) ℂ) : ip (τ a b M) N = ip M (τd a b N) := by
  rw [τ_apply, τd_apply, ip_sub_left, ip_mul_right_adj, ip_mul_left_adj, ip_sub_right]

def φ (v₀ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun := ip v₀
  map_add' := ip_add_right v₀
  map_smul' := fun c B => by rw [ip_smul_right]; rfl

@[scoped simp] theorem φ_apply (v₀ M : Matrix (Fin n) (Fin n) ℂ) : φ v₀ M = ip v₀ M := rfl

theorem schur {X : Type} (ι' : X → Matrix (Fin n) (Fin n) ℂ) (S : Set X)
    (hspan : Submodule.span ℂ (ι' '' S) = ⊤) (r : X → Matrix (Fin n) (Fin n) ℂ)
    (w : Matrix (Fin n) (Fin n) ℂ) (hw : w.det ≠ 0) (hwI : ∀ x ∈ S, w * ι' x = r x * w)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ x ∈ S, M * ι' x = r x * M) : ∃ c : ℂ, M = c • w := by
  have hwu : IsUnit w.det := isUnit_iff_ne_zero.mpr hw
  set Q : Matrix (Fin n) (Fin n) ℂ := w⁻¹ * M with hQ
  have hwQ : w * Q = M := by rw [hQ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv w hwu, Matrix.one_mul]

  have hcomm : ∀ x ∈ S, Q * ι' x = ι' x * Q := by
    intro x hx
    have h1 : w * (Q * ι' x) = w * (ι' x * Q) := by
      rw [← Matrix.mul_assoc, hwQ, hM x hx, ← hwQ, ← Matrix.mul_assoc, ← hwI x hx, Matrix.mul_assoc]
    have h2 := congrArg (fun T => w⁻¹ * T) h1
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul w hwu, Matrix.one_mul] at h2
    exact h2

  have hall : ∀ a : Matrix (Fin n) (Fin n) ℂ, Q * a = a * Q := by
    intro a
    have ha : a ∈ Submodule.span ℂ (ι' '' S) := by rw [hspan]; exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact hcomm x hx
    | zero => simp
    | add y y' _ _ hy hy' => rw [Matrix.mul_add, Matrix.add_mul, hy, hy']
    | smul c y _ hy => rw [Matrix.mul_smul, Matrix.smul_mul, hy]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := Q)
    (fun i j _ => (hall (Matrix.single i j 1)).symm)
  refine ⟨c, ?_⟩
  rw [← hwQ, ← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

end linalg

section operator

variable {n : ℕ} {X : Type}

def Sop (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (∑ x ∈ T, (τd (ι' x) (ρ z₀ x)).comp (τ (ι' x) (ρ z x))) + (LinearMap.toSpanSingleton ℂ _ v₀).comp (φ v₀)

theorem Sop_apply (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Sop ι' ρ z₀ T v₀ z M = (∑ x ∈ T, τd (ι' x) (ρ z₀ x) (τ (ι' x) (ρ z x) M)) + ip v₀ M • v₀ := by
  simp [Sop, LinearMap.sum_apply]

theorem holM_Sop (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) {U : Set ℂ} (hρ : ∀ x : X, HolM (fun z => ρ z x) U)
    (E : Matrix (Fin n) (Fin n) ℂ) : HolM (fun z => Sop ι' ρ z₀ T v₀ z E) U := by
  have h : HolM (fun z => (∑ x ∈ T, ((E * ι' x - ρ z x * E) * (ι' x)ᴴ - (ρ z₀ x)ᴴ * (E * ι' x - ρ z x * E)))
      + ip v₀ E • v₀) U := by
    refine HolM.add (HolM.sum fun x _ => ?_) (holM_const _ _)
    have h1 : HolM (fun z => E * ι' x - ρ z x * E) U :=
      (holM_const _ _).sub ((hρ x).mul (holM_const _ _))
    exact (h1.mul (holM_const _ _)).sub ((holM_const _ _).mul h1)
  intro i j
  refine (h i j).congr (fun z hz => ?_)
  simp [Sop_apply]

def vecE : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (Fin n × Fin n → ℂ) where
  toFun := fun M pq => M pq.1 pq.2
  invFun := fun v => Matrix.of fun i j => v (i, j)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := fun M => by ext i j; rfl
  right_inv := fun v => by funext pq; rfl

@[scoped simp] theorem vecE_apply (M : Matrix (Fin n) (Fin n) ℂ) (pq : Fin n × Fin n) : vecE M pq = M pq.1 pq.2 := rfl

def Smat (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  LinearMap.toMatrix' ((vecE.toLinearMap.comp (Sop ι' ρ z₀ T v₀ z)).comp vecE.symm.toLinearMap)

theorem Smat_mulVec (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Smat ι' ρ z₀ T v₀ z *ᵥ (vecE M) = vecE (Sop ι' ρ z₀ T v₀ z M) := by
  rw [Smat, LinearMap.toMatrix'_mulVec]
  simp

theorem Smat_entry (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (pq rs : Fin n × Fin n) :
    Smat ι' ρ z₀ T v₀ z pq rs = (Sop ι' ρ z₀ T v₀ z (vecE.symm (Pi.single rs 1))) pq.1 pq.2 := by
  rw [Smat, LinearMap.toMatrix'_apply]
  simp

theorem holM_Smat (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) {U : Set ℂ} (hρ : ∀ x : X, HolM (fun z => ρ z x) U) :
    HolM (Smat ι' ρ z₀ T v₀) U := by
  intro pq rs
  have : (fun z => Smat ι' ρ z₀ T v₀ z pq rs) =
      fun z => (Sop ι' ρ z₀ T v₀ z (vecE.symm (Pi.single rs 1))) pq.1 pq.2 := by
    funext z; exact Smat_entry ι' ρ z₀ T v₀ z pq rs
  rw [this]
  exact holM_Sop ι' ρ z₀ T v₀ hρ _ pq.1 pq.2

theorem Sop_injective_of_det (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ) (z₀ : ℂ)
    (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (hdet : (Smat ι' ρ z₀ T v₀ z).det ≠ 0)
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : Sop ι' ρ z₀ T v₀ z M = 0) : M = 0 := by
  by_contra hne
  have hv : vecE M ≠ 0 := fun h => hne (by simpa using congrArg vecE.symm h)
  have : ∃ v ≠ 0, Smat ι' ρ z₀ T v₀ z *ᵥ v = 0 := ⟨vecE M, hv, by rw [Smat_mulVec, hM, map_zero]⟩
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp this)

theorem det_ne_zero_of_Sop_injective (ι' : X → Matrix (Fin n) (Fin n) ℂ) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ)
    (z₀ : ℂ) (T : Finset X) (v₀ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hinj : ∀ M : Matrix (Fin n) (Fin n) ℂ, Sop ι' ρ z₀ T v₀ z M = 0 → M = 0) :
    (Smat ι' ρ z₀ T v₀ z).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : Smat ι' ρ z₀ T v₀ z *ᵥ vecE (vecE.symm v) = 0 := by simpa using hv0
  rw [Smat_mulVec] at h1
  have h2 : Sop ι' ρ z₀ T v₀ z (vecE.symm v) = 0 := vecE.injective (by simpa using h1)
  have h3 := hinj _ h2
  exact hv (by simpa using congrArg vecE h3)

end operator

section main

variable {n : ℕ} {X : Type}

theorem core (ι' : X → Matrix (Fin n) (Fin n) ℂ)
    (hspan : Submodule.span ℂ (Set.range ι') = ⊤)
    (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ (x : X) (i j : Fin n), DifferentiableOn ℂ (fun z : ℂ => ρ z x i j) (Metric.ball z₀ ε))
    (hM : ∀ z ∈ Metric.ball z₀ ε, ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det ≠ 0 ∧ ∀ x : X, M * ι' x = ρ z x * M)
    (hn : 0 < n) :
    ∃ (ε' : ℝ) (N : ℂ → Matrix (Fin n) (Fin n) ℂ), 0 < ε' ∧ ε' ≤ ε ∧
      (∀ i j : Fin n, DifferentiableOn ℂ (fun z : ℂ => N z i j) (Metric.ball z₀ ε')) ∧
      ∀ z ∈ Metric.ball z₀ ε',
        (N z).det ≠ 0 ∧ (∀ x : X, N z * ι' x = ρ z x * N z) ∧
        ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ x : X, M * ι' x = ρ z x * M) → ∃ c : ℂ, M = c • N z := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hρ' : ∀ x : X, HolM (fun z => ρ z x) (ball z₀ ε) := fun x i j => hρ x i j

  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range ι')
  have hbfin : b.Finite := hbli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hX : ∀ y : b, ∃ x : X, ι' x = y := fun y => hbsub y.2
  choose pre hpre using hX
  set T : Finset X := Finset.univ.image pre with hT
  have hspanT : Submodule.span ℂ (ι' '' (↑T : Set X)) = ⊤ := by
    have hbT : b ⊆ ι' '' (↑T : Set X) := fun y hy => ⟨pre ⟨y, hy⟩, by simp [hT], hpre ⟨y, hy⟩⟩
    have htop : Submodule.span ℂ b = ⊤ := hbspan.trans hspan
    rw [eq_top_iff, ← htop]
    exact Submodule.span_mono hbT

  obtain ⟨v₀, hv₀det, hv₀I⟩ := hM z₀ (mem_ball_self hε)
  have hv₀ne : v₀ ≠ 0 := fun h => hv₀det (by rw [h]; exact Matrix.det_zero)
  have hipv₀ : ip v₀ v₀ ≠ 0 := ip_self_ne_zero hv₀ne

  have hinj0 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Sop ι' ρ z₀ T v₀ z₀ M = 0 → M = 0 := by
    intro M hSM
    have hτv₀ : ∀ x ∈ T, τ (ι' x) (ρ z₀ x) v₀ = 0 := fun x _ => by rw [τ_apply, hv₀I x, sub_self]

    have h1 : ip v₀ M = 0 := by
      have h := congrArg (ip v₀) hSM
      rw [ip_zero_right, Sop_apply, ip_add_right, ip_sum_right, ip_smul_right] at h
      have hsum : ∑ x ∈ T, ip v₀ (τd (ι' x) (ρ z₀ x) (τ (ι' x) (ρ z₀ x) M)) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [← ip_τ_adj, hτv₀ x hx, ip_zero_left]
      rw [hsum, zero_add] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hipv₀

    have h2 : ∀ x ∈ T, τ (ι' x) (ρ z₀ x) M = 0 := by
      have h := congrArg (ip M) hSM
      rw [ip_zero_right, Sop_apply, h1, zero_smul, add_zero, ip_sum_right] at h
      have h' : ∑ x ∈ T, (nsq (τ (ι' x) (ρ z₀ x) M) : ℂ) = 0 := by
        rw [← h]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← ip_τ_adj, ip_self]
      have h'' : ∑ x ∈ T, nsq (τ (ι' x) (ρ z₀ x) M) = 0 := by exact_mod_cast h'
      intro x hx
      exact nsq_eq_zero ((Finset.sum_eq_zero_iff_of_nonneg (fun x _ => nsq_nonneg _)).mp h'' x hx)

    obtain ⟨c, hc⟩ := schur ι' (↑T) hspanT (ρ z₀) v₀ hv₀det (fun x _ => hv₀I x) M
      (fun x hx => by have := h2 x hx; rw [τ_apply] at this; exact sub_eq_zero.mp this)
    rw [hc, ip_smul_right] at h1
    rcases mul_eq_zero.mp h1 with h' | h'
    · rw [hc, h', zero_smul]
    · exact absurd h' hipv₀
  have hdet0 : (Smat ι' ρ z₀ T v₀ z₀).det ≠ 0 := det_ne_zero_of_Sop_injective ι' ρ z₀ T v₀ z₀ hinj0

  have hdetHol : DifferentiableOn ℂ (fun z => (Smat ι' ρ z₀ T v₀ z).det) (ball z₀ ε) :=
    (holM_Smat ι' ρ z₀ T v₀ hρ').det
  have hev : ∀ᶠ z in 𝓝 z₀, (Smat ι' ρ z₀ T v₀ z).det ≠ 0 :=
    (hdetHol.continuousOn.continuousAt (ball_mem_nhds z₀ hε)).eventually_ne hdet0
  obtain ⟨ε₁, hε₁, hdetne⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set ε' : ℝ := min ε₁ ε with hε'
  have hε'p : 0 < ε' := lt_min hε₁ hε

  set N : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z => vecE.symm (Matrix.cramer (Smat ι' ρ z₀ T v₀ z) (vecE v₀)) with hN
  refine ⟨ε', N, hε'p, min_le_right _ _, ?_, ?_⟩
  · intro i j
    have : (fun z => N z i j) = fun z => Matrix.cramer (Smat ι' ρ z₀ T v₀ z) (vecE v₀) (i, j) := by
      funext z; rfl
    rw [this]
    exact ((holM_Smat ι' ρ z₀ T v₀ hρ').cramer (vecE v₀) (i, j)).mono (ball_subset_ball (min_le_right _ _))
  intro z hz
  have hzε : z ∈ ball z₀ ε := ball_subset_ball (min_le_right _ _) hz
  have hdetz : (Smat ι' ρ z₀ T v₀ z).det ≠ 0 := hdetne z (ball_subset_ball (min_le_left _ _) hz)

  have E1 : Sop ι' ρ z₀ T v₀ z (N z) = (Smat ι' ρ z₀ T v₀ z).det • v₀ := by
    apply vecE.injective
    rw [← Smat_mulVec, map_smul]
    show Smat ι' ρ z₀ T v₀ z *ᵥ vecE (vecE.symm (Matrix.cramer (Smat ι' ρ z₀ T v₀ z) (vecE v₀))) = _
    rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_cramer]

  obtain ⟨w, hwdet, hwI⟩ := hM z hzε
  have hwne : w ≠ 0 := fun h => hwdet (by rw [h]; exact Matrix.det_zero)

  have E2 : Sop ι' ρ z₀ T v₀ z w = ip v₀ w • v₀ := by
    rw [Sop_apply]
    have : ∑ x ∈ T, τd (ι' x) (ρ z₀ x) (τ (ι' x) (ρ z x) w) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [τ_apply, hwI x, sub_self, map_zero]
    rw [this, zero_add]

  have E3 : ip v₀ w • N z = (Smat ι' ρ z₀ T v₀ z).det • w := by
    have h : Sop ι' ρ z₀ T v₀ z (ip v₀ w • N z - (Smat ι' ρ z₀ T v₀ z).det • w) = 0 := by
      rw [map_sub, map_smul, map_smul, E1, E2, smul_smul, smul_smul, mul_comm, sub_self]
    exact sub_eq_zero.mp (Sop_injective_of_det ι' ρ z₀ T v₀ z hdetz h)
  have hcne : ip v₀ w ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at E3
    exact hwne ((smul_eq_zero.mp E3.symm).resolve_left hdetz)
  set d : ℂ := (ip v₀ w)⁻¹ * (Smat ι' ρ z₀ T v₀ z).det with hd
  have hdne : d ≠ 0 := mul_ne_zero (inv_ne_zero hcne) hdetz
  have hNd : N z = d • w := by
    have := congrArg (fun A => (ip v₀ w)⁻¹ • A) E3
    simp only [smul_smul, inv_mul_cancel₀ hcne, one_smul] at this
    rw [this, hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [hNd, Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ hdne) hwdet
  · intro x
    rw [hNd, Matrix.smul_mul, Matrix.mul_smul, hwI x]
  · intro M hMI
    obtain ⟨c, hc⟩ := schur ι' Set.univ (by rwa [Set.image_univ]) (ρ z) w hwdet (fun x _ => hwI x) M
      (fun x _ => hMI x)
    refine ⟨c * d⁻¹, ?_⟩
    rw [hc, hNd, smul_smul, mul_assoc, inv_mul_cancel₀ hdne, mul_one]

end main

end HolIntertwiner
p2m_reactivate "P2MW.S_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul.HolIntertwiner"

end
p2m_reactivate "P2MW.S_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul.HolIntertwiner"

open HolIntertwiner in
theorem solution
    {X : Type} {n : ℕ} (ι' : X → Matrix (Fin n) (Fin n) ℂ)
    (hspan : Submodule.span ℂ (Set.range ι') = ⊤)
    (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) (ρ : ℂ → X → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ (x : X) (i j : Fin n), DifferentiableOn ℂ (fun z : ℂ => ρ z x i j) (Metric.ball z₀ ε))
    (hM : ∀ z ∈ Metric.ball z₀ ε, ∃ M : Matrix (Fin n) (Fin n) ℂ, M.det ≠ 0 ∧ ∀ x : X, M * ι' x = ρ z x * M) :
    ∃ (ε' : ℝ) (N : ℂ → Matrix (Fin n) (Fin n) ℂ), 0 < ε' ∧ ε' ≤ ε ∧
      (∀ i j : Fin n, DifferentiableOn ℂ (fun z : ℂ => N z i j) (Metric.ball z₀ ε')) ∧
      ∀ z ∈ Metric.ball z₀ ε',
        (N z).det ≠ 0 ∧ (∀ x : X, N z * ι' x = ρ z x * N z) ∧
        ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ x : X, M * ι' x = ρ z x * M) → ∃ c : ℂ, M = c • N z := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨ε, fun _ => 0, hε, le_rfl, fun i j => i.elim0, fun z hz => ⟨?_, fun x => Subsingleton.elim _ _,
      fun M _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩
    rw [Matrix.det_fin_zero]; exact one_ne_zero
  · exact core ι' hspan z₀ hε ρ hρ hM hn

end S_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul
end P2MW
export P2MW.S_Matrix_exists_differentiableOn_det_ne_zero_forall_intertwiner_eq_smul (solution)
