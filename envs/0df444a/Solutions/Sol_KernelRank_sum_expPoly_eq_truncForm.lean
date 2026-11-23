-- Prove2me | solution 1 for KernelRank.sum_expPoly_eq_truncForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:16:51.911451+00:00
-- url     : https://prove2.me/submissions/0287ba84-ab36-4cf1-802b-2dcbd758dc4f

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_coeff_prod_truncExpPoly
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero


attribute [local simp] KernelRank.singleCoeff_same

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι] (d : ℕ) (rate : ι → ℂ)
    (P : ι → ℂ[X]) (s : Fin d → ℝ≥0) :
    (∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
      truncForm d (fun i => (P i).natDegree + 1) (fun i => (P i).natDegree + 1)
        (fun i k => (k.factorial : ℂ) * (P i).coeff k)
        (fun j i q => ((s j : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
          exp (rate i * (s j : ℂ))) := by
  simp only [truncForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  let m := (P i).natDegree + 1
  have hprod_eq : ∀ q : Fin d → Fin m,
      (∏ j : Fin d, ((s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
        exp (rate i * (s j : ℂ))) =
      (∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
        exp (rate i * ∑ j : Fin d, (s j : ℂ)) := fun q => by
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum]
  simp_rw [hprod_eq, ← mul_assoc, ← Finset.sum_mul]
  simp only [expPoly, Complex.ofReal_sum]
  congr 1
  -- Evaluate `P i` via `∏ j, truncExpPoly (P i).natDegree (s j)`!
  let k := (P i).natDegree
  have hP : (P i).eval (∑ j : Fin d, (s j : ℂ)) =
      ∑ n ∈ Finset.range m, (P i).coeff n * (∑ j : Fin d, (s j : ℂ)) ^ n :=
    eval_eq_sum_range _
  rw [hP]
  -- Partition `{q : Fin d → Fin m | ∑ j, q j < m}` by `n = ∑ j, q j < m`
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun q : Fin d → Fin m => ∑ j, (q j : ℕ))
    (t := Finset.range m)
    (fun _ hq => Finset.mem_range.mpr (Finset.mem_filter.mp hq).2)]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hcongr_n :
      ∑ q ∈ (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
          (fun q => (∑ j, (q j : ℕ)) = n),
        (((∑ j, (q j : ℕ)).factorial : ℂ) * (P i).coeff (∑ j, (q j : ℕ))) *
          ∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ) =
      ∑ q ∈ (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
          (fun q => (∑ j, (q j : ℕ)) = n),
        ((n.factorial : ℂ) * (P i).coeff n) *
          ∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ) :=
    Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2]
  rw [← hcongr_n |> Eq.symm]
  have hmultinom :
      ∑ q ∈ (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
          (fun q => (∑ j, (q j : ℕ)) = n),
        ((n.factorial : ℂ) * (P i).coeff n) *
          ∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ) =
      (P i).coeff n * (∑ j : Fin d, (s j : ℂ)) ^ n := by
    have hcoeff := coeff_prod_truncExpPoly (Finset.univ : Finset (Fin d)) k
      (fun j => (s j : ℂ)) hnk
    have hexpand : (∏ j : Fin d, truncExpPoly k (s j : ℂ)) =
        ∑ q : Fin d → Fin m,
          C (∏ j : Fin d, (s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
            X ^ (∑ j : Fin d, (q j : ℕ)) := by
      have htrunc (j : Fin d) : truncExpPoly k (s j : ℂ) =
          ∑ q : Fin m, C ((s j : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) * X ^ (q : ℕ) := by
        simpa [truncExpPoly, m, k] using (Fin.sum_univ_eq_sum_range
          (fun q : ℕ => C ((s j : ℂ) ^ q / (q.factorial : ℂ)) * X ^ q) m).symm
      simp_rw [htrunc]
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_prod C]
    rw [hexpand, finsetSum_coeff] at hcoeff
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      ← Finset.sum_filter] at hcoeff
    have hfilt : (Finset.univ.filter (fun q : Fin d → Fin m => ∑ j, (q j : ℕ) < m)).filter
        (fun q => (∑ j, (q j : ℕ)) = n) =
        Finset.univ.filter (fun q : Fin d → Fin m => n = ∑ j, (q j : ℕ)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hnm : n < m := Finset.mem_range.mp hn
      omega
    rw [hfilt, ← Finset.mul_sum, hcoeff]
    have hfn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  exact hmultinom.symm
end KernelRank
