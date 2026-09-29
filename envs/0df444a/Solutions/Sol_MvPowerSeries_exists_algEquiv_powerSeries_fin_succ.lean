-- Prove2me | solution 1 for MvPowerSeries.exists_algEquiv_powerSeries_fin_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6a224d75-fa1b-5696-8561-ee87e79ae81b

import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finsupp.Option
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ

universe u v w

noncomputable section

namespace M4cP1PS

open Finsupp Finset

section Equiv

variable {σ : Type*} {R : Type*} [CommSemiring R]

def optFun (φ : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  PowerSeries.mk fun n => fun d => MvPowerSeries.coeff (d.optionElim n) φ

def optInv (ψ : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  fun m => MvPowerSeries.coeff m.some (PowerSeries.coeff (m none) ψ)

@[scoped simp]
theorem coeff_coeff_optFun (φ : MvPowerSeries (Option σ) R) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optFun φ)) = MvPowerSeries.coeff (d.optionElim n) φ := by
  rw [optFun, PowerSeries.coeff_mk]; rfl

@[scoped simp]
theorem coeff_optInv (ψ : PowerSeries (MvPowerSeries σ R)) (m : Option σ →₀ ℕ) :
    MvPowerSeries.coeff m (optInv ψ) = MvPowerSeries.coeff m.some (PowerSeries.coeff (m none) ψ) :=
  rfl

theorem optInv_optFun (φ : MvPowerSeries (Option σ) R) : optInv (optFun φ) = φ := by
  ext m
  rw [coeff_optInv, coeff_coeff_optFun, optionElim_some]

theorem optFun_optInv (ψ : PowerSeries (MvPowerSeries σ R)) : optFun (optInv ψ) = ψ := by
  ext n d
  rw [coeff_coeff_optFun, coeff_optInv, some_optionElim, optionElim_apply_none]

theorem optFun_add (φ ψ : MvPowerSeries (Option σ) R) : optFun (φ + ψ) = optFun φ + optFun ψ := by
  ext n d
  simp only [map_add, coeff_coeff_optFun]

theorem optFun_mul (φ ψ : MvPowerSeries (Option σ) R) : optFun (φ * ψ) = optFun φ * optFun ψ := by
  classical
  ext n d
  rw [coeff_coeff_optFun, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp_rw [MvPowerSeries.coeff_mul, coeff_coeff_optFun]
  rw [← sum_product']
  refine sum_nbij' (fun p => ((p.1 none, p.2 none), (p.1.some, p.2.some)))
    (fun q => (q.2.1.optionElim q.1.1, q.2.2.optionElim q.1.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_antidiagonal] at hp
    rw [mem_product, mem_antidiagonal, mem_antidiagonal, ← Finsupp.add_apply, hp, ← some_add, hp,
      optionElim_apply_none, some_optionElim]
    exact ⟨rfl, rfl⟩
  · intro q hq
    rw [mem_product, mem_antidiagonal, mem_antidiagonal] at hq
    rw [mem_antidiagonal, ← optionElim_add, hq.1, hq.2]
  · intro p _
    simp only [optionElim_some]
  · intro q _
    simp only [some_optionElim, optionElim_apply_none, Prod.mk.eta]
  · intro p _
    simp only [optionElim_some]

def optRingEquiv : MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := optFun
  invFun := optInv
  left_inv := optInv_optFun
  right_inv := optFun_optInv
  map_mul' := optFun_mul
  map_add' := optFun_add

end Equiv

section Transport

variable {σ : Type*} {R : Type*} [CommSemiring R]

theorem optionElim_eq_iff {n : ℕ} {d : σ →₀ ℕ} {m : Option σ →₀ ℕ} :
    d.optionElim n = m ↔ n = m none ∧ d = m.some := by
  constructor
  · rintro rfl
    exact ⟨(optionElim_apply_none n d).symm, (some_optionElim n d).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact optionElim_some m

theorem optFun_monomial (m : Option σ →₀ ℕ) (r : R) :
    optFun (MvPowerSeries.monomial m r) =
      PowerSeries.monomial (m none) (MvPowerSeries.monomial m.some r) := by
  classical
  ext n d
  rw [coeff_coeff_optFun, MvPowerSeries.coeff_monomial, PowerSeries.coeff_monomial]
  by_cases hn : n = m none
  · rw [if_pos hn, MvPowerSeries.coeff_monomial]
    by_cases hd : d = m.some
    · rw [if_pos hd, if_pos (optionElim_eq_iff.mpr ⟨hn, hd⟩)]
    · rw [if_neg hd, if_neg fun h => hd (optionElim_eq_iff.mp h).2]
  · rw [if_neg hn, map_zero, if_neg fun h => hn (optionElim_eq_iff.mp h).1]

theorem optFun_C (r : R) :
    optFun (MvPowerSeries.C r : MvPowerSeries (Option σ) R) = PowerSeries.C (MvPowerSeries.C r) := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, optFun_monomial, Finsupp.zero_apply, some_zero,
    MvPowerSeries.monomial_zero_eq_C_apply, PowerSeries.monomial_zero_eq_C_apply]

theorem optFun_X_none : optFun (MvPowerSeries.X none : MvPowerSeries (Option σ) R) = PowerSeries.X := by
  rw [MvPowerSeries.X, optFun_monomial, single_eq_same, some_single_none,
    MvPowerSeries.monomial_zero_eq_C_apply, map_one, ← PowerSeries.X_eq]

theorem optFun_X_some (i : σ) :
    optFun (MvPowerSeries.X (some i) : MvPowerSeries (Option σ) R) =
      PowerSeries.C (MvPowerSeries.X i) := by
  classical
  rw [MvPowerSeries.X, optFun_monomial, single_apply, if_neg (Option.some_ne_none i),
    some_single_some, PowerSeries.monomial_zero_eq_C_apply]
  rfl

theorem constantCoeff_optFun (φ : MvPowerSeries (Option σ) R) :
    PowerSeries.constantCoeff (optFun φ) =
      MvPowerSeries.killCompl (Function.Embedding.some) φ := by
  ext d
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_optFun]
  change _ = MvPowerSeries.coeff (embDomain Function.Embedding.some d) φ
  have h : d.optionElim 0 = embDomain Function.Embedding.some d := by
    ext x
    cases x with
    | none => rw [optionElim_apply_none]; exact (embDomain_notin_range _ _ _ (by simp)).symm
    | some i => rw [optionElim_apply_some]; exact (embDomain_apply_self Function.Embedding.some d i).symm
  rw [h]

theorem constantCoeff_constantCoeff_optFun (φ : MvPowerSeries (Option σ) R) :
    MvPowerSeries.constantCoeff (PowerSeries.constantCoeff (optFun φ)) =
      MvPowerSeries.constantCoeff φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_optFun, optionElim_zero,
    single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

def optAlgEquiv : MvPowerSeries (Option σ) R ≃ₐ[R] PowerSeries (MvPowerSeries σ R) :=
  AlgEquiv.ofRingEquiv (f := optRingEquiv) fun r => by
    change optFun (algebraMap R (MvPowerSeries (Option σ) R) r) = _
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply, optFun_C,
      PowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]

@[scoped simp] theorem optAlgEquiv_apply (φ : MvPowerSeries (Option σ) R) : optAlgEquiv φ = optFun φ := rfl
@[scoped simp] theorem optAlgEquiv_symm_apply (ψ : PowerSeries (MvPowerSeries σ R)) :
    (optAlgEquiv (σ := σ) (R := R)).symm ψ = optInv ψ := rfl

def finSuccAlgEquiv (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R) :=
  (MvPowerSeries.renameEquiv R (_root_.finSuccEquiv n)).trans optAlgEquiv

theorem finSuccAlgEquiv_apply (R : Type*) [CommSemiring R] (n : ℕ)
    (φ : MvPowerSeries (Fin (n + 1)) R) :
    finSuccAlgEquiv R n φ = optFun (MvPowerSeries.rename (_root_.finSuccEquiv n) φ) := rfl

theorem finSuccAlgEquiv_X_zero (R : Type*) [CommSemiring R] (n : ℕ) :
    finSuccAlgEquiv R n (MvPowerSeries.X 0) = PowerSeries.X := by
  rw [finSuccAlgEquiv_apply, MvPowerSeries.rename_X, finSuccEquiv_zero, optFun_X_none]

theorem finSuccAlgEquiv_X_succ (R : Type*) [CommSemiring R] (n : ℕ) (i : Fin n) :
    finSuccAlgEquiv R n (MvPowerSeries.X i.succ) = PowerSeries.C (MvPowerSeries.X i) := by
  rw [finSuccAlgEquiv_apply, MvPowerSeries.rename_X, finSuccEquiv_succ, optFun_X_some]

theorem finSuccAlgEquiv_C (R : Type*) [CommSemiring R] (n : ℕ) (r : R) :
    finSuccAlgEquiv R n (MvPowerSeries.C r) = PowerSeries.C (MvPowerSeries.C r) := by
  rw [finSuccAlgEquiv_apply, MvPowerSeries.rename_C, optFun_C]

end Transport

section SumSplit

variable {σ τ : Type*} {R : Type*} [CommSemiring R]

abbrev expE : (σ ⊕ τ →₀ ℕ) ≃+ (σ →₀ ℕ) × (τ →₀ ℕ) := sumFinsuppAddEquivProdFinsupp

def sumFun (φ : MvPowerSeries (σ ⊕ τ) R) : MvPowerSeries τ (MvPowerSeries σ R) :=
  fun e => fun d => MvPowerSeries.coeff (expE.symm (d, e)) φ

def sumInv (ψ : MvPowerSeries τ (MvPowerSeries σ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun m => MvPowerSeries.coeff (expE m).1 (MvPowerSeries.coeff (expE m).2 ψ)

@[scoped simp]
theorem coeff_coeff_sumFun (φ : MvPowerSeries (σ ⊕ τ) R) (e : τ →₀ ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (MvPowerSeries.coeff e (sumFun φ)) =
      MvPowerSeries.coeff (expE.symm (d, e)) φ :=
  rfl

@[scoped simp]
theorem coeff_sumInv (ψ : MvPowerSeries τ (MvPowerSeries σ R)) (m : σ ⊕ τ →₀ ℕ) :
    MvPowerSeries.coeff m (sumInv ψ) =
      MvPowerSeries.coeff (expE m).1 (MvPowerSeries.coeff (expE m).2 ψ) :=
  rfl

theorem sumInv_sumFun (φ : MvPowerSeries (σ ⊕ τ) R) : sumInv (sumFun φ) = φ := by
  ext m
  rw [coeff_sumInv, coeff_coeff_sumFun, Prod.mk.eta, AddEquiv.symm_apply_apply]

theorem sumFun_sumInv (ψ : MvPowerSeries τ (MvPowerSeries σ R)) : sumFun (sumInv ψ) = ψ := by
  ext e d
  rw [coeff_coeff_sumFun, coeff_sumInv, AddEquiv.apply_symm_apply]

theorem sumFun_add (φ ψ : MvPowerSeries (σ ⊕ τ) R) : sumFun (φ + ψ) = sumFun φ + sumFun ψ := by
  ext e d
  simp only [map_add, coeff_coeff_sumFun]

theorem sumFun_mul (φ ψ : MvPowerSeries (σ ⊕ τ) R) : sumFun (φ * ψ) = sumFun φ * sumFun ψ := by
  classical
  ext e d
  rw [coeff_coeff_sumFun, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
  simp_rw [MvPowerSeries.coeff_mul, coeff_coeff_sumFun]
  rw [← sum_product']
  refine sum_nbij' (fun p => (((expE p.1).2, (expE p.2).2), ((expE p.1).1, (expE p.2).1)))
    (fun q => (expE.symm (q.2.1, q.1.1), expE.symm (q.2.2, q.1.2))) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_antidiagonal] at hp
    have h := congrArg expE hp
    rw [map_add, AddEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h
    rw [mem_product, mem_antidiagonal, mem_antidiagonal]
    exact ⟨h.2, h.1⟩
  · intro q hq
    rw [mem_product, mem_antidiagonal, mem_antidiagonal] at hq
    rw [mem_antidiagonal, ← map_add, Prod.mk_add_mk, hq.1, hq.2]
  · intro p _
    simp only [Prod.mk.eta, AddEquiv.symm_apply_apply]
  · intro q _
    simp only [AddEquiv.apply_symm_apply, Prod.mk.eta]
  · intro p _
    simp only [Prod.mk.eta, AddEquiv.symm_apply_apply]

def sumRingEquiv : MvPowerSeries (σ ⊕ τ) R ≃+* MvPowerSeries τ (MvPowerSeries σ R) where
  toFun := sumFun
  invFun := sumInv
  left_inv := sumInv_sumFun
  right_inv := sumFun_sumInv
  map_mul' := sumFun_mul
  map_add' := sumFun_add

theorem expE_symm_eq_iff {d : σ →₀ ℕ} {e : τ →₀ ℕ} {m : σ ⊕ τ →₀ ℕ} :
    expE.symm (d, e) = m ↔ d = (expE m).1 ∧ e = (expE m).2 := by
  rw [AddEquiv.symm_apply_eq, Prod.ext_iff]

theorem sumFun_monomial (m : σ ⊕ τ →₀ ℕ) (r : R) :
    sumFun (MvPowerSeries.monomial m r) =
      MvPowerSeries.monomial (expE m).2 (MvPowerSeries.monomial (expE m).1 r) := by
  classical
  ext e d
  rw [coeff_coeff_sumFun, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
  by_cases he : e = (expE m).2
  · rw [if_pos he, MvPowerSeries.coeff_monomial]
    by_cases hd : d = (expE m).1
    · rw [if_pos hd, if_pos (expE_symm_eq_iff.mpr ⟨hd, he⟩)]
    · rw [if_neg hd, if_neg fun h => hd (expE_symm_eq_iff.mp h).1]
  · rw [if_neg he, map_zero, if_neg fun h => he (expE_symm_eq_iff.mp h).2]

theorem expE_single_inl (s : σ) (k : ℕ) :
    expE (single (Sum.inl s) k : σ ⊕ τ →₀ ℕ) = (single s k, 0) := by
  classical
  ext x
  · rw [fst_sumFinsuppAddEquivProdFinsupp, single_apply, single_apply]
    simp only [Sum.inl.injEq]
  · rw [snd_sumFinsuppAddEquivProdFinsupp, single_apply, if_neg Sum.inl_ne_inr]
    rfl

theorem expE_single_inr (t : τ) (k : ℕ) :
    expE (single (Sum.inr t) k : σ ⊕ τ →₀ ℕ) = (0, single t k) := by
  classical
  ext x
  · rw [fst_sumFinsuppAddEquivProdFinsupp, single_apply, if_neg Sum.inr_ne_inl]
    rfl
  · rw [snd_sumFinsuppAddEquivProdFinsupp, single_apply, single_apply]
    simp only [Sum.inr.injEq]

theorem sumFun_C (r : R) :
    sumFun (MvPowerSeries.C r : MvPowerSeries (σ ⊕ τ) R) =
      MvPowerSeries.C (MvPowerSeries.C r) := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, sumFun_monomial, map_zero, Prod.fst_zero,
    Prod.snd_zero, MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_zero_eq_C_apply]

theorem sumFun_X_inl (s : σ) :
    sumFun (MvPowerSeries.X (Sum.inl s) : MvPowerSeries (σ ⊕ τ) R) =
      MvPowerSeries.C (MvPowerSeries.X s) := by
  rw [MvPowerSeries.X, sumFun_monomial, expE_single_inl, MvPowerSeries.monomial_zero_eq_C_apply]
  rfl

theorem sumFun_X_inr (t : τ) :
    sumFun (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (σ ⊕ τ) R) = MvPowerSeries.X t := by
  rw [MvPowerSeries.X, sumFun_monomial, expE_single_inr, MvPowerSeries.monomial_zero_eq_C_apply,
    map_one]
  rfl

def sumAlgEquiv : MvPowerSeries (σ ⊕ τ) R ≃ₐ[R] MvPowerSeries τ (MvPowerSeries σ R) :=
  AlgEquiv.ofRingEquiv (f := sumRingEquiv) fun r => by
    change sumFun (algebraMap R (MvPowerSeries (σ ⊕ τ) R) r) = _
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply, sumFun_C,
      MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]

@[scoped simp] theorem sumAlgEquiv_apply (φ : MvPowerSeries (σ ⊕ τ) R) : sumAlgEquiv φ = sumFun φ := rfl

theorem sumAlgEquiv_X_inl (s : σ) :
    sumAlgEquiv (MvPowerSeries.X (Sum.inl s) : MvPowerSeries (σ ⊕ τ) R) =
      MvPowerSeries.C (MvPowerSeries.X s) :=
  sumFun_X_inl s

theorem sumAlgEquiv_X_inr (t : τ) :
    sumAlgEquiv (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (σ ⊕ τ) R) = MvPowerSeries.X t :=
  sumFun_X_inr t

theorem sumAlgEquiv_C (r : R) :
    sumAlgEquiv (MvPowerSeries.C r : MvPowerSeries (σ ⊕ τ) R) =
      MvPowerSeries.C (MvPowerSeries.C r) :=
  sumFun_C r

end SumSplit

section FinAdd

def finAddAlgEquiv (R : Type*) [CommSemiring R] (m n : ℕ) :
    MvPowerSeries (Fin (m + n)) R ≃ₐ[R] MvPowerSeries (Fin n) (MvPowerSeries (Fin m) R) :=
  (MvPowerSeries.renameEquiv R finSumFinEquiv.symm).trans sumAlgEquiv

theorem finAddAlgEquiv_apply (R : Type*) [CommSemiring R] (m n : ℕ)
    (φ : MvPowerSeries (Fin (m + n)) R) :
    finAddAlgEquiv R m n φ = sumFun (MvPowerSeries.rename finSumFinEquiv.symm φ) := rfl

theorem finAddAlgEquiv_X_castAdd (R : Type*) [CommSemiring R] (m n : ℕ) (i : Fin m) :
    finAddAlgEquiv R m n (MvPowerSeries.X (Fin.castAdd n i)) =
      MvPowerSeries.C (MvPowerSeries.X i) := by
  rw [finAddAlgEquiv_apply, MvPowerSeries.rename_X, finSumFinEquiv_symm_apply_castAdd, sumFun_X_inl]

theorem finAddAlgEquiv_X_natAdd (R : Type*) [CommSemiring R] (m n : ℕ) (j : Fin n) :
    finAddAlgEquiv R m n (MvPowerSeries.X (Fin.natAdd m j)) = MvPowerSeries.X j := by
  rw [finAddAlgEquiv_apply, MvPowerSeries.rename_X, finSumFinEquiv_symm_apply_natAdd, sumFun_X_inr]

theorem finAddAlgEquiv_C (R : Type*) [CommSemiring R] (m n : ℕ) (r : R) :
    finAddAlgEquiv R m n (MvPowerSeries.C r) = MvPowerSeries.C (MvPowerSeries.C r) := by
  rw [finAddAlgEquiv_apply, MvPowerSeries.rename_C, sumFun_C]

end FinAdd

end M4cP1PS
p2m_reactivate "P2MW.S_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ.M4cP1PS"

end
p2m_reactivate "P2MW.S_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ.M4cP1PS"

theorem solution (R : Type u) [CommSemiring R] (n : ℕ) :
    ∃ e : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R),
      e (MvPowerSeries.X 0) = PowerSeries.X ∧
        ∀ i : Fin n, e (MvPowerSeries.X i.succ) = PowerSeries.C (MvPowerSeries.X i) :=
  ⟨M4cP1PS.finSuccAlgEquiv R n, M4cP1PS.finSuccAlgEquiv_X_zero R n,
    M4cP1PS.finSuccAlgEquiv_X_succ R n⟩

end S_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ
end P2MW
export P2MW.S_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ (solution)
