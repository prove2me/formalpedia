-- Prove2me | solution 1 for KernelRank.separableRank_radial_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:47:46.136552+00:00
-- url     : https://prove2.me/submissions/7907f405-ea16-4d11-9a32-50306eb3fe91

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_isSumOfProducts_radial_multiComponent
import Theorems.Thm_KernelRank_realExpForm_rank_ge
import Theorems.Thm_KernelRank_realExpMultilinearMap_apply
import Theorems.Thm_KernelRank_span_realExpEval_eq_top
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum
import Theorems.Thm_KernelRank_exists_linear_factors_of_span_eq_top
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_separableRank_radial_eq_hankel
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_sum_expPoly_eq_truncForm
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
open scoped Classical
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) {cs : List Component}
    (hcs : IsRepresentation cs) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      multiTotalCost d cs := by
  let comp : Fin cs.length → Component := fun i => cs[i]
  have hinj : Function.Injective fun i => (comp i).rate := by
    intro i j hij
    have h : (cs.map Component.rate)[(i : ℕ)]'(by simp) =
        (cs.map Component.rate)[(j : ℕ)]'(by simp) := by simpa [comp] using hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hcs.2).mp h)
  have hwf : ∀ i, (comp i).WellFormed := fun i => hcs.1 _ (List.getElem_mem _)
  have hprof : (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      fun x => ∑ i : Fin cs.length, (comp i).eval (∑ j, x j ^ 2) := by
    funext x
    exact (Fin.sum_univ_fun_getElem cs fun c => c.eval (∑ j, x j ^ 2)).symm
  have hcost : multiTotalCost d cs = ∑ i : Fin cs.length, (comp i).multiCost d :=
    (Fin.sum_univ_fun_getElem cs (Component.multiCost d)).symm
  rw [hprof, hcost]
  refine le_antisymm ?_ ?_
  · exact iInf₂_le _ (IsSumOfProducts.finsetSum fun i =>
      isSumOfProducts_radial_multiComponent hd (hwf i))
  · rw [separableRank_radial_eq_hankel d
      (fun t => ∑ i : Fin cs.length, (comp i).eval t)]
    refine le_iInf₂ fun R hR => ?_
    let m (i : Fin cs.length) : ℕ := (comp i).poly.natDegree + 1
    let ι_R := {i : Fin cs.length // ((comp i).rate).im = 0}
    let ι_C := {i : Fin cs.length // 0 < ((comp i).rate).im}
    let m_R (i : ι_R) : ℕ := m i.1
    let m_C (k : ι_C) : ℕ := m k.1
    let w_R (i : ι_R) (n : ℕ) : ℝ := (n.factorial : ℝ) * ((comp i.1).poly.coeff n).re
    let w_C (k : ι_C) (n : ℕ) : ℂ := (n.factorial : ℂ) * (comp k.1).poly.coeff n
    let v (s : ℝ≥0) : RealExpSpace m_R m_C :=
      ((fun i q => ((s : ℝ) ^ (q : ℕ) / ((q : ℕ).factorial : ℝ)) *
          Real.exp (((comp i.1).rate).re * (s : ℝ))),
       (fun k q => ((s : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
          exp ((comp k.1).rate * (s : ℂ))))
    have hexp_unit (P : ℂ[X]) (μ : ℂ) (s : Fin d → ℝ≥0) :
        expPoly P μ (∑ j, (s j : ℝ)) =
          ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (P.natDegree + 1) =>
            ∑ j, (q j : ℕ) < P.natDegree + 1),
            (((∑ j, (q j : ℕ)).factorial : ℂ) * P.coeff (∑ j, (q j : ℕ))) *
              ∏ j : Fin d, ((s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
                exp (μ * (s j : ℂ)) := by
      simpa [truncForm] using sum_expPoly_eq_truncForm d (fun _ : Unit => μ) (fun _ : Unit => P) s
    have hK_eq : (fun s : Fin d → ℝ≥0 => ∑ i : Fin cs.length, (comp i).eval (∑ j, (s j : ℝ))) =
        fun s => realExpMultilinearMap d m_R m_C m_R m_C w_R w_C (fun j => v (s j)) := by
      funext s
      rw [realExpMultilinearMap_apply]
      simp only [realExpForm, realTruncForm, cplxTruncForm]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin cs.length => ((comp i).rate).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : Fin cs.length => ((comp i).rate).im = 0)
          (Finset.univ.filter fun i : Fin cs.length => ((comp i).rate).im = 0)
          (fun _ => by simp) (fun i => (comp i).eval (∑ j, (s j : ℝ)))]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hev : (comp i.1).eval (∑ j, (s j : ℝ)) =
            (expPoly (comp i.1).poly (comp i.1).rate (∑ j, (s j : ℝ))).re := rfl
        rw [hev, hexp_unit (comp i.1).poly (comp i.1).rate s, Complex.re_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        have hrate : (comp i.1).rate = (((comp i.1).rate).re : ℂ) :=
          Complex.ext rfl (by simpa using i.2)
        have hcoeff : (comp i.1).poly.coeff (∑ j, (q j : ℕ)) =
            (((comp i.1).poly.coeff (∑ j, (q j : ℕ))).re : ℂ) :=
          Complex.ext rfl (by simpa using (hwf i.1).2.2 i.2 (∑ j, (q j : ℕ)))
        have hcast_term :
            (((∑ j, (q j : ℕ)).factorial : ℂ) * (comp i.1).poly.coeff (∑ j, (q j : ℕ))) *
              (∏ j : Fin d, ((s j : ℂ) ^ (q j : ℕ) / ((q j : ℕ).factorial : ℂ)) *
                exp ((comp i.1).rate * (s j : ℂ))) =
            ((w_R i (∑ j, (q j : ℕ)) * ∏ j : Fin d, (v (s j)).1 i (q j) : ℝ) : ℂ) := by
          rw [hcoeff, hrate]
          dsimp [w_R, v]
          push_cast
          congr 1
        rw [hcast_term, Complex.ofReal_re]
      · have hiff (i : Fin cs.length) :
            i ∈ Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0) ↔
              0 < ((comp i).rate).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hwf i).2.1 (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : Fin cs.length => 0 < ((comp i).rate).im)
          (Finset.univ.filter fun i : Fin cs.length => ¬ ((comp i).rate).im = 0)
          hiff (fun i => (comp i).eval (∑ j, (s j : ℝ)))]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hev : (comp k.1).eval (∑ j, (s j : ℝ)) =
            (expPoly (comp k.1).poly (comp k.1).rate (∑ j, (s j : ℝ))).re := rfl
        rw [hev, hexp_unit (comp k.1).poly (comp k.1).rate s, Complex.re_sum]
    rw [hK_eq] at hR
    have hspan := span_realExpEval_eq_top hinj (fun i => (hwf i).2.1) m
    obtain ⟨ℓ, hℓ⟩ := exists_linear_factors_of_span_eq_top hspan
      (realExpMultilinearMap d m_R m_C m_R m_C w_R w_C) hR
    simp_rw [realExpMultilinearMap_apply] at hℓ
    have hwR : ∀ i : ι_R, 0 < m_R i → w_R i (m_R i - 1) ≠ 0 := fun i _ => by
      dsimp [w_R, m_R, m]
      have hlead : (comp i.1).poly.coeff (comp i.1).poly.natDegree ≠ 0 :=
        leadingCoeff_ne_zero.mpr (hwf i.1).1
      have him0 : ((comp i.1).poly.coeff (comp i.1).poly.natDegree).im = 0 :=
        (hwf i.1).2.2 i.2 _
      have hre_ne : ((comp i.1).poly.coeff (comp i.1).poly.natDegree).re ≠ 0 := fun h0 =>
        hlead (Complex.ext h0 him0)
      exact mul_ne_zero (Nat.cast_ne_zero.mpr ( Nat.factorial_ne_zero _ )) hre_ne
    have hwC : ∀ k : ι_C, 0 < m_C k → w_C k (m_C k - 1) ≠ 0 := fun k _ => by
      dsimp [w_C, m_C, m]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (leadingCoeff_ne_zero.mpr (hwf k.1).1)
    have hge := realExpForm_rank_ge hd m_R m_C m_C (fun _ => le_rfl) w_C hwC
      (∑ i, m_R i) m_R rfl (fun _ => le_rfl) w_R hwR R ℓ hℓ
    have hsum_cost : (∑ i : Fin cs.length, (comp i).multiCost d) =
        (∑ i : ι_R, if m_R i = 0 then 0 else (d - 1) * (m_R i - 1) + 1) +
        (∑ k : ι_C, if m_C k = 0 then 0 else 2 * (d - 1) * (m_C k - 1) + d) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin cs.length => ((comp i).rate).im = 0)]
      congr 1
      · rw [Finset.sum_subtype (p := fun i : Fin cs.length => ((comp i).rate).im = 0)
          (Finset.univ.filter fun i : Fin cs.length => ((comp i).rate).im = 0)
          (fun _ => by simp) (fun i => (comp i).multiCost d)]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Component.multiCost, i.2, m_R, m]
      · have hiff (i : Fin cs.length) :
            i ∈ Finset.univ.filter (fun i : Fin cs.length => ¬ ((comp i).rate).im = 0) ↔
              0 < ((comp i).rate).im := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne (hwf i).2.1 (Ne.symm h), fun h => h.ne'⟩
        rw [Finset.sum_subtype (p := fun i : Fin cs.length => 0 < ((comp i).rate).im)
          (Finset.univ.filter fun i : Fin cs.length => ¬ ((comp i).rate).im = 0)
          hiff (fun i => (comp i).multiCost d)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Component.multiCost, k.2.ne', m_C, m]
    rw [hsum_cost]
    exact_mod_cast hge
end KernelRank
