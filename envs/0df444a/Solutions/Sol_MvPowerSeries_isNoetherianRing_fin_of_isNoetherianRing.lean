-- Prove2me | solution 1 for MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/cbb9df24-4ee2-5a24-adea-1f615066eea7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing

set_option autoImplicit false

universe u

namespace W2MV
open MvPowerSeries

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

section IndexBijection

variable {α β : Type*}

private theorem Finsupp.sumElim_injective2 :
    Function.Injective2 (Finsupp.sumElim : (α →₀ ℕ) → (β →₀ ℕ) → (α ⊕ β →₀ ℕ)) := by
  intro a a' b b' h
  constructor
  · simpa [Finsupp.comapDomain_inl_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn) h
  · simpa [Finsupp.comapDomain_inr_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn) h

private theorem Finsupp.sumElim_eq_zero_iff {a : α →₀ ℕ} {b : β →₀ ℕ} :
    a.sumElim b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact Finsupp.sumElim_zero_zero.symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_zero_zero

private theorem Finsupp.sumElim_eq_single_inl_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {s : α} {c : ℕ} :
    a.sumElim b = Finsupp.single (Sum.inl s) c ↔ a = Finsupp.single s c ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact (Finsupp.sumElim_single_zero s c).symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_single_zero s c

private theorem Finsupp.sumElim_eq_single_inr_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {t : β} {c : ℕ} :
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

private def sumToFun (f : MvPowerSeries (α ⊕ β) R) : MvPowerSeries α (MvPowerSeries β R) :=
  fun a => fun b => f (a.sumElim b)

private def sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) : MvPowerSeries (α ⊕ β) R :=
  fun d => g (d.comapDomain Sum.inl Sum.inl_injective.injOn)
    (d.comapDomain Sum.inr Sum.inr_injective.injOn)

variable {α β}

@[scoped simp]
private theorem coeff_sumToFun (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumToFun α β f)) = coeff (a.sumElim b) f :=
  rfl

@[scoped simp]
private theorem coeff_sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) (d : α ⊕ β →₀ ℕ) :
    coeff d (sumInvFun α β g) =
      coeff (d.comapDomain Sum.inr Sum.inr_injective.injOn)
        (coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn) g) :=
  rfl

private theorem coeff_mul_sumElim [DecidableEq α] [DecidableEq β]
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

private def sumRingEquiv : MvPowerSeries (α ⊕ β) R ≃+* MvPowerSeries α (MvPowerSeries β R) where
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
private theorem coeff_sumRingEquiv (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumRingEquiv α β R f)) = coeff (a.sumElim b) f :=
  rfl

@[scoped simp]
private theorem sumRingEquiv_X_inl (s : α) :
    sumRingEquiv α β R (X (Sum.inl s)) = X s := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, X_def (R := MvPowerSeries β R), coeff_monomial,
    apply_ite (coeff b), coeff_one, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inl_iff]
  by_cases ha : a = Finsupp.single s 1 <;> by_cases hb : b = (0 : β →₀ ℕ) <;>
    simp [ha, hb]

@[scoped simp]
private theorem sumRingEquiv_X_inr (t : β) :
    sumRingEquiv α β R (X (Sum.inr t)) = C (X t) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, coeff_C, apply_ite (coeff b), coeff_X, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inr_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = Finsupp.single t 1 <;>
    simp [ha, hb]

@[scoped simp]
private theorem sumRingEquiv_C (r : R) :
    sumRingEquiv α β R (C r) = C (C r) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_C, coeff_C, apply_ite (coeff b), coeff_C, coeff_zero]
  simp only [Finsupp.sumElim_eq_zero_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = (0 : β →₀ ℕ) <;> simp [ha, hb]

end SumRingEquiv

section FinSucc

variable {R : Type*} [CommSemiring R]

private def finSuccSumEquiv (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := Fin.cases (Sum.inl ()) (fun i => Sum.inr i)
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    induction i using Fin.cases <;> simp
  right_inv x := by
    rcases x with ⟨⟩ | i <;> simp

@[scoped simp] private theorem finSuccSumEquiv_zero (n : ℕ) : finSuccSumEquiv n 0 = Sum.inl () := rfl

@[scoped simp] private theorem finSuccSumEquiv_succ (n : ℕ) (i : Fin n) :
    finSuccSumEquiv n i.succ = Sum.inr i := by
  simp [finSuccSumEquiv]

variable (R) in

private def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
  ((renameEquiv R (finSuccSumEquiv n)).toRingEquiv).trans (sumRingEquiv Unit (Fin n) R)

private theorem finSuccRingEquiv_apply (n : ℕ) (f : MvPowerSeries (Fin (n + 1)) R) :
    finSuccRingEquiv R n f =
      sumRingEquiv Unit (Fin n) R (rename (finSuccSumEquiv n) f) :=
  rfl

@[scoped simp]
private theorem finSuccRingEquiv_X_zero (n : ℕ) :
    finSuccRingEquiv R n (X 0) = PowerSeries.X := by
  rw [finSuccRingEquiv_apply, rename_X]
  exact sumRingEquiv_X_inl ()

@[scoped simp]
private theorem finSuccRingEquiv_X_succ (n : ℕ) (i : Fin n) :
    finSuccRingEquiv R n (X i.succ) = PowerSeries.C (X i) := by
  rw [finSuccRingEquiv_apply, rename_X, finSuccSumEquiv_succ]
  exact sumRingEquiv_X_inr i

@[scoped simp]
private theorem finSuccRingEquiv_C (n : ℕ) (r : R) :
    finSuccRingEquiv R n (C r) = PowerSeries.C (C r) := by
  rw [finSuccRingEquiv_apply, rename_C]
  exact sumRingEquiv_C r

end FinSucc

section IsEmpty

variable (σ : Type*) [IsEmpty σ] (R : Type*) [CommSemiring R]

private def isEmptyRingEquiv : MvPowerSeries σ R ≃+* R :=
  RingEquiv.ofRingHom (constantCoeff (σ := σ) (R := R)) (C (σ := σ) (R := R))
    (by ext r; simp)
    (by classical
        ext f d
        obtain rfl : d = 0 := Subsingleton.eq_zero d
        simp [coeff_C, coeff_zero_eq_constantCoeff])

@[scoped simp]
private theorem isEmptyRingEquiv_apply (f : MvPowerSeries σ R) :
    isEmptyRingEquiv σ R f = constantCoeff f := rfl

@[scoped simp]
private theorem isEmptyRingEquiv_symm_apply (r : R) :
    (isEmptyRingEquiv σ R).symm r = C r := rfl

end IsEmpty

section Noetherian

private theorem isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (isEmptyRingEquiv (Fin 0) R).symm
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _ (finSuccRingEquiv R n).symm

end Noetherian

end MvPowerSeries
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing.W2MV.MvPowerSeries"

end
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing.W2MV.MvPowerSeries"

end W2MV
p2m_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing.W2MV"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) :=
  W2MV.MvPowerSeries.isNoetherianRing_fin R n

end S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing
end P2MW
export P2MW.S_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing (solution)
