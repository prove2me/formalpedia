-- Prove2me | solution 1 for MvPowerSeries.isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/429b5a51-c7c6-5747-83ef-16eaa81ca781

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient

set_option autoImplicit false

open IsLocalRing

namespace C0
namespace W2MV
open MvPowerSeries

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

section IndexBijection

variable {α β : Type*}

theorem Finsupp.sumElim_injective2 :
    Function.Injective2 (Finsupp.sumElim : (α →₀ ℕ) → (β →₀ ℕ) → (α ⊕ β →₀ ℕ)) := by
  intro a a' b b' h
  constructor
  · simpa [Finsupp.comapDomain_inl_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn) h
  · simpa [Finsupp.comapDomain_inr_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn) h

theorem Finsupp.sumElim_eq_zero_iff {a : α →₀ ℕ} {b : β →₀ ℕ} :
    a.sumElim b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact Finsupp.sumElim_zero_zero.symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_zero_zero

theorem Finsupp.sumElim_eq_single_inl_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {s : α} {c : ℕ} :
    a.sumElim b = Finsupp.single (Sum.inl s) c ↔ a = Finsupp.single s c ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact (Finsupp.sumElim_single_zero s c).symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_single_zero s c

theorem Finsupp.sumElim_eq_single_inr_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {t : β} {c : ℕ} :
    a.sumElim b = Finsupp.single (Sum.inr t) c ↔ a = 0 ∧ b = Finsupp.single t c := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact (Finsupp.sumElim_zero_single t c).symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_zero_single t c

end IndexBijection

section SumRingEquiv

variable (α β : Type*) {R : Type*} [CommSemiring R]

def sumToFun (f : MvPowerSeries (α ⊕ β) R) : MvPowerSeries α (MvPowerSeries β R) :=
  fun a => fun b => f (a.sumElim b)

def sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) : MvPowerSeries (α ⊕ β) R :=
  fun d => g (d.comapDomain Sum.inl Sum.inl_injective.injOn)
    (d.comapDomain Sum.inr Sum.inr_injective.injOn)

variable {α β}

@[scoped simp]
theorem coeff_sumToFun (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumToFun α β f)) = coeff (a.sumElim b) f :=
  rfl

@[scoped simp]
theorem coeff_sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) (d : α ⊕ β →₀ ℕ) :
    coeff d (sumInvFun α β g) =
      coeff (d.comapDomain Sum.inr Sum.inr_injective.injOn)
        (coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn) g) :=
  rfl

theorem coeff_mul_sumElim [DecidableEq α] [DecidableEq β]
    (f g : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff (a.sumElim b) (f * g) =
      ∑ q ∈ antidiagonal a, ∑ r ∈ antidiagonal b,
        coeff (q.1.sumElim r.1) f * coeff (q.2.sumElim r.2) g := by
  classical
  rw [coeff_mul, ← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image,
    Finset.sum_product]

  rintro ⟨⟨q₁, q₂⟩, ⟨r₁, r₂⟩⟩ - ⟨⟨q₁', q₂'⟩, ⟨r₁', r₂'⟩⟩ - h
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨hq₁, hr₁⟩ := Finsupp.sumElim_injective2 h₁
  obtain ⟨hq₂, hr₂⟩ := Finsupp.sumElim_injective2 h₂
  exact ⟨⟨hq₁, hq₂⟩, ⟨hr₁, hr₂⟩⟩

variable (α β) (R) in

def sumRingEquiv : MvPowerSeries (α ⊕ β) R ≃+* MvPowerSeries α (MvPowerSeries β R) where
  toFun := sumToFun α β
  invFun := sumInvFun α β
  left_inv f := by
    ext d
    rw [show coeff d (sumInvFun α β (sumToFun α β f)) =
        coeff ((d.comapDomain Sum.inl Sum.inl_injective.injOn).sumElim
          (d.comapDomain Sum.inr Sum.inr_injective.injOn)) f from rfl,
      Finsupp.comapDomain_sumElim_comapDomain]
  right_inv g := by
    ext a b
    rw [show coeff b (coeff a (sumToFun α β (sumInvFun α β g))) =
        coeff ((a.sumElim b).comapDomain Sum.inr Sum.inr_injective.injOn)
          (coeff ((a.sumElim b).comapDomain Sum.inl Sum.inl_injective.injOn) g) from rfl,
      Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  map_add' f g := by
    ext a b
    simp only [map_add, coeff_sumToFun]
  map_mul' f g := by
    classical
    ext a b
    rw [coeff_sumToFun, coeff_mul_sumElim]
    rw [show coeff a (sumToFun α β f * sumToFun α β g) =
        ∑ q ∈ antidiagonal a, coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g) from
      coeff_mul (φ := sumToFun α β f) (ψ := sumToFun α β g) (n := a), map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show coeff b (coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g)) =
        ∑ r ∈ antidiagonal b, coeff r.1 (coeff q.1 (sumToFun α β f)) *
          coeff r.2 (coeff q.2 (sumToFun α β g)) from coeff_mul ..]
    exact Finset.sum_congr rfl fun r _ => by rw [coeff_sumToFun, coeff_sumToFun]

@[scoped simp]
theorem coeff_sumRingEquiv (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumRingEquiv α β R f)) = coeff (a.sumElim b) f :=
  rfl

@[scoped simp]
theorem sumRingEquiv_X_inl (s : α) :
    sumRingEquiv α β R (X (Sum.inl s)) = X s := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, X_def (R := MvPowerSeries β R), coeff_monomial,
    apply_ite (coeff b), coeff_one, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inl_iff]
  by_cases ha : a = Finsupp.single s 1 <;> by_cases hb : b = (0 : β →₀ ℕ) <;>
    simp [ha, hb]

@[scoped simp]
theorem sumRingEquiv_X_inr (t : β) :
    sumRingEquiv α β R (X (Sum.inr t)) = C (X t) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, coeff_C, apply_ite (coeff b), coeff_X, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inr_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = Finsupp.single t 1 <;>
    simp [ha, hb]

@[scoped simp]
theorem sumRingEquiv_C (r : R) :
    sumRingEquiv α β R (C r) = C (C r) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_C, coeff_C, apply_ite (coeff b), coeff_C, coeff_zero]
  simp only [Finsupp.sumElim_eq_zero_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = (0 : β →₀ ℕ) <;> simp [ha, hb]

end SumRingEquiv

section FinSucc

variable {R : Type*} [CommSemiring R]

def finSuccSumEquiv (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := Fin.cases (Sum.inl ()) (fun i => Sum.inr i)
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    induction i using Fin.cases <;> simp
  right_inv x := by
    rcases x with ⟨⟩ | i <;> simp

@[scoped simp] theorem finSuccSumEquiv_zero (n : ℕ) : finSuccSumEquiv n 0 = Sum.inl () := rfl

@[scoped simp] theorem finSuccSumEquiv_succ (n : ℕ) (i : Fin n) :
    finSuccSumEquiv n i.succ = Sum.inr i := by
  simp [finSuccSumEquiv]

variable (R) in

def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
  ((renameEquiv R (finSuccSumEquiv n)).toRingEquiv).trans (sumRingEquiv Unit (Fin n) R)

theorem finSuccRingEquiv_apply (n : ℕ) (f : MvPowerSeries (Fin (n + 1)) R) :
    finSuccRingEquiv R n f =
      sumRingEquiv Unit (Fin n) R (rename (finSuccSumEquiv n) f) :=
  rfl

@[scoped simp]
theorem finSuccRingEquiv_X_zero (n : ℕ) :
    finSuccRingEquiv R n (X 0) = PowerSeries.X := by
  rw [finSuccRingEquiv_apply, rename_X]
  exact sumRingEquiv_X_inl ()

@[scoped simp]
theorem finSuccRingEquiv_X_succ (n : ℕ) (i : Fin n) :
    finSuccRingEquiv R n (X i.succ) = PowerSeries.C (X i) := by
  rw [finSuccRingEquiv_apply, rename_X, finSuccSumEquiv_succ]
  exact sumRingEquiv_X_inr i

@[scoped simp]
theorem finSuccRingEquiv_C (n : ℕ) (r : R) :
    finSuccRingEquiv R n (C r) = PowerSeries.C (C r) := by
  rw [finSuccRingEquiv_apply, rename_C]
  exact sumRingEquiv_C r

end FinSucc

section IsEmpty

variable (σ : Type*) [IsEmpty σ] (R : Type*) [CommSemiring R]

def isEmptyRingEquiv : MvPowerSeries σ R ≃+* R :=
  RingEquiv.ofRingHom (constantCoeff (σ := σ) (R := R)) (C (σ := σ) (R := R))
    (by ext r; simp)
    (by classical
        ext f d
        obtain rfl : d = 0 := Subsingleton.eq_zero d
        simp [coeff_C, coeff_zero_eq_constantCoeff])

@[scoped simp]
theorem isEmptyRingEquiv_apply (f : MvPowerSeries σ R) :
    isEmptyRingEquiv σ R f = constantCoeff f := rfl

@[scoped simp]
theorem isEmptyRingEquiv_symm_apply (r : R) :
    (isEmptyRingEquiv σ R).symm r = C r := rfl

end IsEmpty

section Noetherian

theorem isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (isEmptyRingEquiv (Fin 0) R).symm
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _ (finSuccRingEquiv R n).symm

end Noetherian

end MvPowerSeries
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries"

end
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries"

end C0.W2MV
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0 P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV"
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0"

universe u v w

namespace C0
namespace M4cP4PS

open MvPowerSeries IsLocalRing Finsupp

variable {σ : Type u} {R : Type v} [CommRing R]

theorem smodEq_pow_smul_top_iff (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem maximalIdeal_eq_comap [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) = (maximalIdeal R).comap (constantCoeff (σ := σ) (R := R)) := by
  ext φ
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

def dropVar (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

theorem coeff_dropVar (i : σ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (dropVar i φ) = if m i = 0 then coeff m φ else 0 := rfl

theorem mem_pow_span_X_of_coeff_eq_zero [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R)
    (hφ : ∀ m : σ →₀ ℕ, m.degree < k → coeff m φ = 0) :
    φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  classical
  haveI := Fintype.ofFinite σ
  set J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) with hJ
  induction k generalizing φ with
  | zero => simp
  | succ k ihk =>
    suffices h : ∀ (s : Finset σ) (ψ : MvPowerSeries σ R), (∀ m : σ →₀ ℕ, m.degree < k + 1 → coeff m ψ = 0) →
        (∀ m : σ →₀ ℕ, ¬ (m.support ⊆ s) → coeff m ψ = 0) → ψ ∈ J ^ (k + 1) by
      exact h Finset.univ φ hφ fun m hm => (hm (Finset.subset_univ _)).elim
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro ψ h0 hs
      have : ψ = 0 := by
        ext m
        by_cases hm : m = 0
        · subst hm; rw [map_zero]; exact h0 0 (by simp)
        · rw [map_zero]
          refine hs m fun hsub => hm ?_
          ext j
          have : j ∉ m.support := fun hj => by simpa using hsub hj
          simpa [Finsupp.mem_support_iff] using this
      rw [this]; exact Ideal.zero_mem _
    | insert i s hi ih =>
      intro ψ h0 hs
      have hdiv : (X i : MvPowerSeries σ R) ∣ ψ - dropVar i ψ := by
        rw [X_dvd_iff]
        intro m hm
        rw [map_sub, coeff_dropVar, if_pos hm, sub_self]
      obtain ⟨q, hq⟩ := hdiv
      have hqk : ∀ m : σ →₀ ℕ, m.degree < k → coeff m q = 0 := by
        intro m hm
        have h1 : coeff (Finsupp.single i 1 + m) (X i * q) = coeff m q := by
          rw [X, coeff_add_monomial_mul, one_mul]
        have h2 : coeff (Finsupp.single i 1 + m) (ψ - dropVar i ψ) = 0 := by
          rw [map_sub, coeff_dropVar, if_neg (by simp), sub_zero]
          exact h0 _ (by rw [map_add, Finsupp.degree_single]; omega)
        rw [← h1, ← hq, h2]
      have hrest : dropVar i ψ ∈ J ^ (k + 1) := by
        refine ih _ ?_ ?_
        · intro m hm
          rw [coeff_dropVar]
          split_ifs
          · exact h0 m hm
          · rfl
        · intro m hm
          rw [coeff_dropVar]
          split_ifs with hmi
          · refine hs m fun hsub => hm fun j hj => ?_
            rcases Finset.mem_insert.mp (hsub hj) with rfl | h
            · exact absurd hmi (by simpa [Finsupp.mem_support_iff] using hj)
            · exact h
          · rfl
      have : ψ = dropVar i ψ + X i * q := by rw [← hq]; ring
      rw [this, pow_succ']
      exact Ideal.add_mem _ (pow_succ' J k ▸ hrest)
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ihk q hqk))

theorem sub_truncTotal_mem_pow_span_X [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R) :
    φ - (truncTotal k φ : MvPolynomial σ R) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  refine mem_pow_span_X_of_coeff_eq_zero k _ fun m hm => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hm, sub_self]

section LocalCoeff

variable [IsLocalRing R]

local notation "𝔐" => maximalIdeal (MvPowerSeries σ R)
local notation "𝔪" => maximalIdeal R

theorem coeff_mem_pow_of_mem_pow (n : ℕ) (x : MvPowerSeries σ R) (hx : x ∈ 𝔐 ^ n) (m : σ →₀ ℕ) :
    coeff m x ∈ 𝔪 ^ (n - m.degree) := by
  classical
  induction n generalizing x m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add, hp]
      by_cases hp2 : p.2 = 0
      ·
        have hp1 : p.1 = m := by simpa [hp2] using hp
        have hz0 : coeff p.2 z ∈ 𝔪 := by
          rw [hp2, coeff_zero_eq_constantCoeff_apply]
          rw [maximalIdeal_eq_comap, Ideal.mem_comap] at hz
          exact hz
        have hmem := Ideal.mul_mem_mul (ih y hy p.1) hz0
        rw [← pow_succ] at hmem
        rw [hp1] at hmem ⊢
        have hle : n + 1 - m.degree ≤ n - m.degree + 1 := by omega
        exact Ideal.pow_le_pow_right hle hmem
      ·
        have hp2' : 0 < p.2.degree := by
          rw [Nat.pos_iff_ne_zero, Ne, Finsupp.degree_eq_zero_iff]
          exact hp2
        have hmem := Ideal.mul_mem_right (coeff p.2 z) _ (ih y hy p.1)
        have hle : n + 1 - m.degree ≤ n - p.1.degree := by omega
        exact Ideal.pow_le_pow_right hle hmem
    · intro y z hy hz
      rw [map_add]
      exact Ideal.add_mem _ hy hz

theorem C_mem_pow (k : ℕ) (c : R) (hc : c ∈ 𝔪 ^ k) : (C c : MvPowerSeries σ R) ∈ 𝔐 ^ k := by
  have h : (𝔪).map (C (σ := σ) (R := R)) ≤ 𝔐 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_C]
    exact ha
  have := Ideal.pow_right_mono h k
  rw [← Ideal.map_pow] at this
  exact this (Ideal.mem_map_of_mem _ hc)

theorem span_X_le : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ 𝔐 := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_X]
  exact Ideal.zero_mem _

variable [Finite σ]

theorem monomial_one_mem_pow (m : σ →₀ ℕ) : (monomial m (1 : R) : MvPowerSeries σ R) ∈ 𝔐 ^ m.degree := by
  classical
  refine Ideal.pow_right_mono span_X_le m.degree (mem_pow_span_X_of_coeff_eq_zero _ _ fun m' hm' => ?_)
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact lt_irrefl _ hm'

theorem monomial_mem_pow (n : ℕ) (m : σ →₀ ℕ) (c : R) (hc : c ∈ 𝔪 ^ (n - m.degree)) :
    (monomial m c : MvPowerSeries σ R) ∈ 𝔐 ^ n := by
  have : (monomial m c : MvPowerSeries σ R) = C c * monomial m 1 := by
    rw [← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
  rw [this]
  have hmem := Ideal.mul_mem_mul (C_mem_pow _ c hc) (monomial_one_mem_pow (R := R) m)
  rw [← pow_add] at hmem
  have hle : n ≤ n - m.degree + m.degree := by omega
  exact Ideal.pow_le_pow_right hle hmem

theorem mem_pow_of_coeff_mem_pow (n : ℕ) (x : MvPowerSeries σ R)
    (hx : ∀ m : σ →₀ ℕ, m.degree < n → coeff m x ∈ 𝔪 ^ (n - m.degree)) : x ∈ 𝔐 ^ n := by
  classical
  have hsplit : x = (truncTotal n x : MvPolynomial σ R) + (x - (truncTotal n x : MvPolynomial σ R)) := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ (Ideal.pow_right_mono span_X_le n (sub_truncTotal_mem_pow_span_X n x))
  have hcoe : ((truncTotal n x : MvPolynomial σ R) : MvPowerSeries σ R) =
      ∑ m ∈ (finite_of_degree_lt (σ := σ) n).toFinset, monomial m (coeff m x) := by
    rw [truncTotal, truncFinset_apply, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
  rw [hcoe]
  refine Ideal.sum_mem _ fun m hm => monomial_mem_pow n m _ (hx m ?_)
  simpa using hm

theorem isAdicComplete_maximalIdeal [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete 𝔐 (MvPowerSeries σ R) := by
  haveI : IsHausdorff 𝔐 (MvPowerSeries σ R) := ⟨fun x hx => by
    ext m
    rw [map_zero]
    refine IsHausdorff.haus (inferInstance : IsHausdorff 𝔪 R) (coeff m x) fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hk := hx (k + m.degree)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at hk
    have := coeff_mem_pow_of_mem_pow (k + m.degree) x hk m
    rwa [show k + m.degree - m.degree = k by omega] at this⟩
  have hP : IsPrecomplete 𝔐 (MvPowerSeries σ R) := ⟨fun g hg => by
    have hgd : ∀ {k l : ℕ}, k ≤ l → g l - g k ∈ 𝔐 ^ k := fun h => by
      have := (smodEq_pow_smul_top_iff _ _ _ _).mp (hg h)
      rwa [← neg_sub, Ideal.neg_mem_iff] at this

    have hc : ∀ m : σ →₀ ℕ, ∃ c : R, ∀ k, coeff m (g (k + m.degree)) - c ∈ 𝔪 ^ k := by
      intro m
      obtain ⟨c, hc⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete 𝔪 R)
        (f := fun k => coeff m (g (k + m.degree))) (fun {k l} hkl => by
          rw [smodEq_pow_smul_top_iff, ← map_sub]
          have := coeff_mem_pow_of_mem_pow (k + m.degree) _
            (hgd (show k + m.degree ≤ l + m.degree by omega)) m
          rw [show k + m.degree - m.degree = k by omega] at this
          rwa [← neg_sub, map_neg, Ideal.neg_mem_iff])
      exact ⟨c, fun k => (smodEq_pow_smul_top_iff _ _ _ _).mp (hc k)⟩
    choose c hc using hc
    refine ⟨fun m => c m, fun n => ?_⟩
    rw [smodEq_pow_smul_top_iff]
    refine mem_pow_of_coeff_mem_pow n _ fun m hm => ?_
    rw [map_sub]
    have h := hc m (n - m.degree)
    rw [show n - m.degree + m.degree = n by omega] at h
    exact h⟩
  exact ⟨⟩

end LocalCoeff
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0 P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV"

end C0.M4cP4PS
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0 P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV"
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0 P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV"

namespace C0
namespace Glue

open AdicCompletion

universe u' v' w'

variable {R : Type u'} [CommRing R] (I : Ideal R)

theorem isPrecomplete_of_surjective {M : Type v'} {N : Type w'} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsPrecomplete I M] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : IsPrecomplete I N := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hf y
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M z
  exact ⟨f x, (AdicCompletion.map_of I f x).symm⟩

theorem isAdicComplete_quotient [IsNoetherianRing R] [IsAdicComplete I R] (J : Ideal R) :
    IsAdicComplete I (R ⧸ J) := by
  haveI : IsHausdorff I (R ⧸ J) :=
    IsHausdorff.of_le_jacobson I (R ⧸ J) (IsAdicComplete.le_jacobson_bot I)
  haveI : IsPrecomplete I (R ⧸ J) :=
    isPrecomplete_of_surjective I (Submodule.mkQ J) (Submodule.mkQ_surjective J)
  exact ⟨⟩

theorem isAdicComplete_map_quotient_mk [IsNoetherianRing R] [IsAdicComplete I R] (J : Ideal R) :
    IsAdicComplete (I.map (Ideal.Quotient.mk J)) (R ⧸ J) := by
  rw [← Ideal.Quotient.algebraMap_eq J]
  exact (IsAdicComplete.map_algebraMap_iff I (S := R ⧸ J) (M := R ⧸ J)).mpr
    (isAdicComplete_quotient I J)

end C0.Glue
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0 P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV"
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0 P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient.C0.W2MV"

theorem solution
    (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    (n : ℕ) (J : Ideal (MvPowerSeries (Fin n) W)) :
    IsNoetherianRing (MvPowerSeries (Fin n) W ⧸ J) ∧
      IsAdicComplete ((maximalIdeal (MvPowerSeries (Fin n) W)).map (Ideal.Quotient.mk J))
        (MvPowerSeries (Fin n) W ⧸ J) := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin n) W) :=
    C0.W2MV.MvPowerSeries.isNoetherianRing_fin W n
  haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) W)) (MvPowerSeries (Fin n) W) :=
    C0.M4cP4PS.isAdicComplete_maximalIdeal
  exact ⟨inferInstance, C0.Glue.isAdicComplete_map_quotient_mk _ J⟩

end S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient
end P2MW
export P2MW.S_MvPowerSeries_isNoetherianRing_and_isAdicComplete_map_maximalIdeal_quotient (solution)
