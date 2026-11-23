-- Prove2me | solution 1 for KernelRank.span_realExpEval_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:38:54.191633+00:00
-- url     : https://prove2.me/submissions/a33f51e5-7c56-4ee3-a1b1-31b54f99ad84

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_singleRealCoeff_of_ne_idx
import Theorems.Thm_KernelRank_singleRealCoeff_of_ne_deg
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_injective_rates_with_conjugates
import Theorems.Thm_KernelRank_singleCoeff_of_ne_deg
import Theorems.Thm_KernelRank_singleCoeff_of_ne_idx
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_span_range_eq_top_of_dual
import Theorems.Thm_P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
open scoped Classical
namespace KernelRank
theorem _root_.solution {ι : Type*} [Finite ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) (m : ι → ℕ) :
    Submodule.span ℝ
      (Set.range fun s : ℝ≥0 =>
        ((fun (i : {i : ι // (rate i).im = 0}) (q : Fin (m i.1)) =>
            ((s : ℝ) ^ (q : ℕ) / ((q : ℕ).factorial : ℝ)) *
              Real.exp ((rate i.1).re * (s : ℝ))),
         (fun (k : {i : ι // 0 < (rate i).im}) (q : Fin (m k.1)) =>
            ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
              exp (rate k.1 * (s : ℂ))))) = ⊤ := by
  cases nonempty_fintype ι
  let ι_R := {i : ι // (rate i).im = 0}
  let ι_C := {i : ι // 0 < (rate i).im}
  let m_R (i : ι_R) : ℕ := m i.1
  let m_C (k : ι_C) : ℕ := m k.1
  refine span_range_eq_top_of_dual fun L hL => ?_
  let a (i : ι_R) (q : Fin (m_R i)) : ℝ := L (embRealCoeff i q 1)
  let b (k : ι_C) (q : Fin (m_C k)) : ℂ :=
    L (0, singleCoeff k q 1) - I * L (0, singleCoeff k q I)
  have hL_expand (x : RealExpSpace m_R m_C) :
      L x = (∑ i : ι_R, ∑ q : Fin (m_R i), a i q * x.1 i q) +
        ∑ k : ι_C, ∑ q : Fin (m_C k), (b k q * x.2 k q).re := by
    have hx1 : x.1 = ∑ i : ι_R, ∑ q : Fin (m_R i), x.1 i q • singleRealCoeff i q (1 : ℝ) := by
      ext i₀ q₀
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single q₀]
        · simp
        · intro q _ hq
          simp [singleRealCoeff_of_ne_deg i₀ q q₀ 1 hq.symm]
        · simp
      · intro i _ hi
        exact Finset.sum_eq_zero fun q _ => by
          simp [singleRealCoeff_of_ne_idx i q 1 hi.symm]
      · simp
    have hx2 : x.2 = ∑ k : ι_C, ∑ q : Fin (m_C k),
        ((x.2 k q).re • singleCoeff k q (1 : ℂ) +
          (x.2 k q).im • singleCoeff k q I) := by
      ext k₀ q₀
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      rw [Finset.sum_eq_single k₀]
      · rw [Finset.sum_eq_single q₀]
        · simp [Complex.re_add_im]
        · intro q _ hq
          simp [singleCoeff_of_ne_deg k₀ q q₀ _ hq.symm]
        · simp
      · intro k _ hk
        exact Finset.sum_eq_zero fun q _ => by
          simp [singleCoeff_of_ne_idx k q _ hk.symm]
      · simp
    have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
    conv_lhs => rw [hx, hx1, hx2]
    rw [map_add]
    congr 1
    · have hp : (∑ i : ι_R, ∑ q : Fin (m_R i), x.1 i q • singleRealCoeff i q (1 : ℝ),
          (0 : CplxExpSpace m_C)) =
          ∑ i : ι_R, ∑ q : Fin (m_R i),
            x.1 i q • embRealCoeff (m_C := m_C) i q (1 : ℝ) := by
        ext <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum, embRealCoeff]
      rw [hp, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [map_smul, smul_eq_mul, mul_comm]
    · have hp : ((0 : ∀ i, Fin (m_R i) → ℝ), ∑ k : ι_C, ∑ q : Fin (m_C k),
          ((x.2 k q).re • singleCoeff k q (1 : ℂ) +
            (x.2 k q).im • singleCoeff k q I)) =
          ∑ k : ι_C, ∑ q : Fin (m_C k),
            ((x.2 k q).re • ((0 : ∀ i, Fin (m_R i) → ℝ), singleCoeff k q (1 : ℂ)) +
              (x.2 k q).im • ((0 : ∀ i, Fin (m_R i) → ℝ), singleCoeff k q I)) := by
        ext <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum, Complex.real_smul]
      rw [hp, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp [b, Complex.mul_re]
      ring
  let ν : ι ⊕ ι_C → ℂ := Sum.elim rate (fun k => starRingEnd ℂ (rate k.1))
  have hν : Function.Injective ν := injective_rates_with_conjugates hinj hup
  let polyR (i : ι_R) : ℂ[X] :=
    ∑ q : Fin (m_R i), C ((a i q : ℂ) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  let polyC (k : ι_C) : ℂ[X] :=
    ∑ q : Fin (m_C k), C ((b k q / 2) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  let polyConj (k : ι_C) : ℂ[X] :=
    ∑ q : Fin (m_C k), C ((starRingEnd ℂ (b k q) / 2) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ)
  let P : ι ⊕ ι_C → ℂ[X] := Sum.elim
    (fun i => if h : (rate i).im = 0 then polyR ⟨i, h⟩
      else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩)
    polyConj
  have hP0 : ∀ p, P p = 0 := by
    refine eq_zero_of_sum_expPoly_eq_zero' hν P fun u hu => ?_
    have hs := (hL_expand
      ((fun (i : ι_R) (q : Fin (m_R i)) =>
          (u ^ (q : ℕ) / ((q : ℕ).factorial : ℝ)) * Real.exp ((rate i.1).re * u)),
       (fun (k : ι_C) (q : Fin (m_C k)) =>
          ((u : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * exp (rate k.1 * (u : ℂ))))).symm.trans
      (hL ⟨u, hu.le⟩)
    dsimp only at hs
    have hsC : ((((∑ i : ι_R, ∑ q : Fin (m_R i),
        a i q * (u ^ (q : ℕ) / ((q : ℕ).factorial : ℝ) * Real.exp ((rate i.1).re * u))) +
      ∑ k : ι_C, ∑ q : Fin (m_C k),
        (b k q * ((u : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ) *
          exp (rate k.1 * (u : ℂ)))).re) : ℝ) : ℂ) = 0 := by
      rw [hs]; simp
    push_cast at hsC
    rw [← hsC]
    simp only [Fintype.sum_sum_type, P, ν, Sum.elim_inl, Sum.elim_inr]
    have hsplit_ι :
        (∑ i : ι, expPoly
          (if h : (rate i).im = 0 then polyR ⟨i, h⟩
           else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩) (rate i) u) =
        (∑ i : ι_R, expPoly (polyR i) (rate i.1) u) +
          ∑ k : ι_C, expPoly (polyC k) (rate k.1) u := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : ι => (rate i).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : ι => (rate i).im = 0)
          (Finset.univ.filter fun i : ι => (rate i).im = 0) (fun _ => by simp)
          (fun i => expPoly (if h : (rate i).im = 0 then polyR ⟨i, h⟩
            else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩) (rate i) u)]
        exact Finset.sum_congr rfl fun i _ => by simp [i.2]
      · have hiff (i : ι) : i ∈ Finset.univ.filter (fun i : ι => ¬ (rate i).im = 0) ↔
            0 < (rate i).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hup i) (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : ι => 0 < (rate i).im)
          (Finset.univ.filter fun i : ι => ¬ (rate i).im = 0) hiff
          (fun i => expPoly (if h : (rate i).im = 0 then polyR ⟨i, h⟩
            else polyC ⟨i, lt_of_le_of_ne (hup i) (Ne.symm h)⟩) (rate i) u)]
        exact Finset.sum_congr rfl fun k _ => by simp [k.2.ne']
    rw [hsplit_ι, add_assoc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hrate_re : rate i.1 = ((rate i.1).re : ℂ) :=
        Complex.ext rfl (by simpa using i.2)
      rw [hrate_re]
      simp only [expPoly, polyR, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
        Finset.sum_mul, Complex.ofReal_re]
      exact Finset.sum_congr rfl fun q _ => by ring
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [expPoly, polyC, polyConj, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
        Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.re_eq_add_conj]
      simp only [map_mul, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_natCast,
        ← Complex.exp_conj]
      ring
  have ha0 (i : ι_R) (q : Fin (m_R i)) : a i q = 0 := by
    have hc := congrArg (fun r => r.coeff (q : ℕ)) (hP0 (Sum.inl i.1))
    simp only [P, Sum.elim_inl, i.2, ↓reduceDIte, polyR, finsetSum_coeff, coeff_C_mul,
      coeff_X_pow, mul_ite, mul_one, mul_zero, coeff_zero] at hc
    have hmem : ∃ q' : Fin (m_R i), (q' : ℕ) = (q : ℕ) := ⟨q, rfl⟩
    rw [Finset.sum_eq_single q] at hc
    · simp only [↓reduceIte] at hc
      have hfq : ((q : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℕ).factorial_ne_zero
      have haC : (a i q : ℂ) = 0 := (div_eq_zero_iff.mp hc).resolve_right hfq
      exact Complex.ofReal_eq_zero.mp haC
    · intro q' _ hne
      have hne_val : (q : ℕ) ≠ (q' : ℕ) := fun he => hne (Fin.ext he.symm)
      simp [hne_val]
    · simp
  have hb0 (k : ι_C) (q : Fin (m_C k)) : b k q = 0 := by
    have hc := congrArg (fun r => r.coeff (q : ℕ)) (hP0 (Sum.inl k.1))
    simp only [P, Sum.elim_inl, k.2.ne', ↓reduceDIte, polyC, finsetSum_coeff, coeff_C_mul,
      coeff_X_pow, mul_ite, mul_one, mul_zero, coeff_zero] at hc
    rw [Finset.sum_eq_single q] at hc
    · simp only [↓reduceIte] at hc
      have hfq : ((q : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℕ).factorial_ne_zero
      have hb2 : b k q / 2 = 0 := (div_eq_zero_iff.mp hc).resolve_right hfq
      exact (div_eq_zero_iff.mp hb2).resolve_right two_ne_zero
    · intro q' _ hne
      have hne_val : (q : ℕ) ≠ (q' : ℕ) := fun he => hne (Fin.ext he.symm)
      simp [hne_val]
    · simp
  exact LinearMap.ext fun x => by simp [hL_expand, ha0, hb0]
end KernelRank
