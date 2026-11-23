-- Prove2me | solution 1 for KernelRank.linearIndependent_hasseDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:32:26.78535+00:00
-- url     : https://prove2.me/submissions/70cad4b2-8ee0-4e91-908b-f2f347fc8822

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {P : ℂ[X]} (hP : P ≠ 0) :
    LinearIndependent ℂ (fun k : Fin (P.natDegree + 1) => hasseDeriv k P) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c h
  simp only [smul_eq_C_mul] at h
  by_contra hne
  obtain ⟨k₀, hk₀, hmin'⟩ :=
    wellFounded_lt.has_min {k | c k ≠ 0} (by simpa [Set.Nonempty] using not_forall.mp hne)
  have hmin : ∀ k, k < k₀ → c k = 0 := fun k hk => by
    by_contra hck
    exact hmin' k hck hk
  have hcoeff := congrArg (fun Q => Q.coeff (P.natDegree - k₀)) h
  simp only [finsetSum_coeff, coeff_C_mul, hasseDeriv_coeff, coeff_zero] at hcoeff
  have hk : P.natDegree - (k₀ : ℕ) + k₀ = P.natDegree :=
    Nat.sub_add_cancel (Nat.lt_succ_iff.mp k₀.2)
  rw [Finset.sum_eq_single k₀] at hcoeff
  · rw [hk, ← leadingCoeff] at hcoeff
    have hchoose : ((P.natDegree.choose k₀ : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.lt_succ_iff.mp k₀.2)).ne'
    exact mul_ne_zero hk₀ (mul_ne_zero hchoose (leadingCoeff_ne_zero.mpr hP)) hcoeff
  · intro k _ hk'
    rcases lt_or_gt_of_ne hk' with hlt | hgt
    · simp [hmin k hlt]
    · have hk₀k : (k₀ : ℕ) < k := hgt
      have hdeg : P.natDegree < P.natDegree - k₀ + k := by have := k₀.2; omega
      rw [coeff_eq_zero_of_natDegree_lt hdeg]
      simp
  · simp
end KernelRank
