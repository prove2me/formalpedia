-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:08:49.419025+00:00
-- url     : https://prove2.me/submissions/93bafbe7-ba20-4523-b6ae-20d5502d4b73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model
import Theorems.Thm_InventoryAnomaly_EW_lemma_18
import Theorems.Thm_InventoryAnomaly_EW_lemma_19

open MeasureTheory ProbabilityTheory
open scoped NNReal
open InventoryAnomaly.EW

/-- The real Poisson weights are at most `1`. -/
lemma IA3_poisPmf_le_one (M : ℝ) (k : ℕ) : poisPmf M k ≤ 1 := by
  unfold poisPmf
  have h := hasSum_one_poissonMeasure M.toNNReal
  have := le_hasSum h k (fun j _ => by positivity)
  simpa [poissonPMFReal] using this

lemma IA3_poisPmf_nonneg (M : ℝ) (k : ℕ) : 0 ≤ poisPmf M k := by
  unfold poisPmf poissonPMFReal; positivity

lemma IA3_pmf_bounds {d : ℕ} (A : AnomModel d) (α : EuclideanSpace ℝ (Fin d)) (M : ℝ) (k : ℕ) :
    0 ≤ A.pmf α M k ∧ A.pmf α M k ≤ 1 := by
  unfold AnomModel.pmf
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (A.anom α M.toNNReal).coe_le_one k)

lemma IA3_clamp01 (z : ℝ) : 0 ≤ clamp01 z ∧ clamp01 z ≤ 1 := by
  unfold clamp01
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) zero_le_one⟩

theorem solution (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ ij ∈ I.omega (I.obs ω),
          |I.fstar (I.obs ω) ij.1 ij.2 - I.fhat svdr θhat (I.obs ω) ij.1 ij.2| ≤
            min (C * ((K + L) ^ 3 * L * I.δ' hI.r_pos μ L) /
              (I.xstar (I.obs ω) ij.1 ij.2 + I.ystar (I.obs ω) ij.1 ij.2)) 1} := by
  obtain ⟨Csp, C, C', hCsp, hC, hC', H⟩ := lemma_18 d cM cA CRC hcM hcA hcA1 hCRC
  refine ⟨Csp, C, C', hCsp, hC, hC', ?_⟩
  intro I K L μ hI hReg svdr θhat hsvd hsel
  have h18 := H I K L μ hI hReg svdr θhat hsvd hsel
  set δ := C * (L + K) ^ 2 * L * ((K + L) * I.δ' hI.r_pos μ L) with hδ
  have hpA1 : (I.pAstar : ℝ) < 1 := by have := hI.pA_le; linarith
  have hpA0 : (0 : ℝ) ≤ I.pAstar := I.pAstar.2
  -- the null set of observed values of probability zero
  let q : Fin I.n × Fin I.m → ℕ → ℝ := fun ij k =>
    (I.pAstar : ℝ) * I.model.pmf I.αstar (I.Mstar ij.1 ij.2) k +
      (1 - (I.pAstar : ℝ)) * poisPmf (I.Mstar ij.1 ij.2) k
  let S : Fin I.n × Fin I.m → Set Entry := fun ij => {e | e.1 = true ∧ q ij e.2.2 = 0}
  let N : Set I.Sample := ⋃ ij, (fun ω : I.Sample => ω ij) ⁻¹' S ij
  have hSnull : ∀ ij, (I.entryPMF ij).toMeasure (S ij) = 0 := by
    intro ij
    rw [PMF.toMeasure_apply_eq_zero_iff _ (Set.to_countable _).measurableSet]
    refine Set.disjoint_left.2 fun e he hS => ?_
    obtain ⟨o, b, k⟩ := e
    simp only [Instance.entryPMF, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at he
    obtain ⟨a, -, b', hb', x, hx, hEq⟩ := he
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl, rfl⟩ := hEq
    obtain ⟨-, hq⟩ := hS
    change (I.pAstar : ℝ) * I.model.pmf I.αstar (I.Mstar ij.1 ij.2) x +
      (1 - (I.pAstar : ℝ)) * poisPmf (I.Mstar ij.1 ij.2) x = 0 at hq
    have hx1 := mul_nonneg hpA0 (IA3_pmf_bounds I.model I.αstar (I.Mstar ij.1 ij.2) x).1
    have hx2 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - I.pAstar) (IA3_poisPmf_nonneg (I.Mstar ij.1 ij.2) x)
    cases b'
    · simp only [Bool.false_eq_true, if_false, PMF.mem_support_iff] at hx
      rw [← poissonPMFReal_ofReal_eq_poissonPMF, Ne, ENNReal.ofReal_eq_zero, not_le] at hx
      have : 0 < (1 - (I.pAstar : ℝ)) * poisPmf (I.Mstar ij.1 ij.2) x :=
        mul_pos (by linarith) hx
      linarith
    · simp only [if_true, PMF.mem_support_iff] at hx
      rw [PMF.mem_support_bernoulli_iff] at hb'
      simp only [cond_true, ne_eq] at hb'
      have hp : (0 : ℝ) < I.pAstar := by
        rcases eq_or_lt_of_le hpA0 with h | h
        · exfalso; apply hb'; rw [show I.pAstar = 0 from NNReal.coe_eq_zero.mp h.symm]; simp
        · exact h
      have hpm : 0 < I.model.pmf I.αstar (I.Mstar ij.1 ij.2) x :=
        ENNReal.toReal_pos hx (PMF.apply_ne_top _ _)
      have : 0 < (I.pAstar : ℝ) * I.model.pmf I.αstar (I.Mstar ij.1 ij.2) x := mul_pos hp hpm
      linarith
  have hNnull : I.law N = 0 := by
    apply measure_iUnion_null
    intro ij
    exact Measure.pi_eval_preimage_null _ (hSnull ij)
  have hsub : {ω | ∀ ij ∈ I.omega (I.obs ω),
      max |I.xhat svdr θhat (I.obs ω) ij.1 ij.2 - I.xstar (I.obs ω) ij.1 ij.2|
          |I.yhat svdr θhat (I.obs ω) ij.1 ij.2 - I.ystar (I.obs ω) ij.1 ij.2| ≤ δ} \ N ⊆
      {ω | ∀ ij ∈ I.omega (I.obs ω),
          |I.fstar (I.obs ω) ij.1 ij.2 - I.fhat svdr θhat (I.obs ω) ij.1 ij.2| ≤
            min (C * ((K + L) ^ 3 * L * I.δ' hI.r_pos μ L) /
              (I.xstar (I.obs ω) ij.1 ij.2 + I.ystar (I.obs ω) ij.1 ij.2)) 1} := by
    rintro ω ⟨hg, hN⟩ ij hij
    have hgij := hg ij hij
    have h1 : (ω ij).1 = true := by
      simpa [Instance.omega, Instance.obs] using hij
    have hnS : ω ij ∉ S ij := fun h => hN (Set.mem_iUnion.2 ⟨ij, h⟩)
    have hqne : q ij (ω ij).2.2 ≠ 0 := fun h => hnS ⟨h1, h⟩
    have hobs : I.obs ω (ij.1, ij.2) = some (ω ij).2.2 := by
      simp [Instance.obs, h1]
    have hxs : I.xstar (I.obs ω) ij.1 ij.2 =
        (I.pAstar : ℝ) * I.model.pmf I.αstar (I.Mstar ij.1 ij.2) (ω ij).2.2 := by
      simp only [Instance.xstar, hobs, Option.getD_some]
    have hys : I.ystar (I.obs ω) ij.1 ij.2 =
        (1 - (I.pAstar : ℝ)) * poisPmf (I.Mstar ij.1 ij.2) (ω ij).2.2 := by
      simp only [Instance.ystar, hobs, Option.getD_some]
    have hpm := IA3_pmf_bounds I.model I.αstar (I.Mstar ij.1 ij.2) (ω ij).2.2
    have hpp0 := IA3_poisPmf_nonneg (I.Mstar ij.1 ij.2) (ω ij).2.2
    have hpp1 := IA3_poisPmf_le_one (I.Mstar ij.1 ij.2) (ω ij).2.2
    have hxsb : 0 ≤ I.xstar (I.obs ω) ij.1 ij.2 ∧ I.xstar (I.obs ω) ij.1 ij.2 ≤ 1 := by
      rw [hxs]; constructor
      · exact mul_nonneg hpA0 hpm.1
      · calc (I.pAstar : ℝ) * _ ≤ 1 * 1 :=
            mul_le_mul hpA1.le hpm.2 hpm.1 zero_le_one
          _ = 1 := by norm_num
    have hysb : 0 ≤ I.ystar (I.obs ω) ij.1 ij.2 ∧ I.ystar (I.obs ω) ij.1 ij.2 ≤ 1 := by
      rw [hys]; constructor
      · exact mul_nonneg (by linarith) hpp0
      · calc (1 - (I.pAstar : ℝ)) * _ ≤ 1 * 1 :=
            mul_le_mul (by linarith) hpp1 hpp0 zero_le_one
          _ = 1 := by norm_num
    have hpos : 0 < I.ystar (I.obs ω) ij.1 ij.2 + I.xstar (I.obs ω) ij.1 ij.2 := by
      have hq0 : q ij (ω ij).2.2 = I.xstar (I.obs ω) ij.1 ij.2 + I.ystar (I.obs ω) ij.1 ij.2 := by
        rw [hxs, hys]
      rcases eq_or_lt_of_le (add_nonneg hysb.1 hxsb.1) with h | h
      · exact absurd (by rw [hq0]; linarith) hqne
      · exact h
    have hxh := IA3_clamp01 (pAOf (θhat (I.obs ω)) * I.model.pmf (alphaOf (θhat (I.obs ω)))
      (I.Mhat svdr (I.obs ω) ij.1 ij.2 / I.model.e (θhat (I.obs ω))) (((I.obs ω) (ij.1, ij.2)).getD 0))
    have hyh := IA3_clamp01 ((1 - pAOf (θhat (I.obs ω))) * poisPmf
      (I.Mhat svdr (I.obs ω) ij.1 ij.2 / I.model.e (θhat (I.obs ω))) (((I.obs ω) (ij.1, ij.2)).getD 0))
    have hxhat : 0 ≤ I.xhat svdr θhat (I.obs ω) ij.1 ij.2 ∧ I.xhat svdr θhat (I.obs ω) ij.1 ij.2 ≤ 1 :=
      hxh
    have hyhat : 0 ≤ I.yhat svdr θhat (I.obs ω) ij.1 ij.2 ∧ I.yhat svdr θhat (I.obs ω) ij.1 ij.2 ≤ 1 :=
      hyh
    have hfs : I.fstar (I.obs ω) ij.1 ij.2 =
        I.ystar (I.obs ω) ij.1 ij.2 / (I.ystar (I.obs ω) ij.1 ij.2 + I.xstar (I.obs ω) ij.1 ij.2) := by
      rw [Instance.fstar, add_comm]
    have hfh : I.fhat svdr θhat (I.obs ω) ij.1 ij.2 = I.yhat svdr θhat (I.obs ω) ij.1 ij.2 /
        (I.xhat svdr θhat (I.obs ω) ij.1 ij.2 + I.yhat svdr θhat (I.obs ω) ij.1 ij.2) := rfl
    have hδeq : C * ((K + L) ^ 3 * L * I.δ' hI.r_pos μ L) = δ := by rw [hδ]; ring
    rw [hδeq, hfs, hfh, add_comm (I.xstar _ _ _)]
    generalize I.xstar (I.obs ω) ij.1 ij.2 = xs at *
    generalize I.ystar (I.obs ω) ij.1 ij.2 = ys at *
    generalize I.xhat svdr θhat (I.obs ω) ij.1 ij.2 = xh at *
    generalize I.yhat svdr θhat (I.obs ω) ij.1 ij.2 = yh at *
    have h19 := (lemma_19 ys xs yh xh δ hysb hxsb hyhat hxhat hpos
      (le_trans (le_max_right _ _) hgij) (le_trans (le_max_left _ _) hgij)).1
    have hsh : (if 0 < yh + xh then yh / (yh + xh) else 0) = yh / (xh + yh) := by
      split_ifs with h
      · rw [add_comm]
      · have : xh + yh = 0 := by linarith
        rw [this, div_zero]
    try simp only at h19
    rw [hsh] at h19
    rwa [abs_sub_comm]
  have : IsProbabilityMeasure I.law := by unfold Instance.law; infer_instance
  calc 1 - C' / (I.n * I.m) ≤ _ := h18
    _ = I.law.real ({ω | ∀ ij ∈ I.omega (I.obs ω),
      max |I.xhat svdr θhat (I.obs ω) ij.1 ij.2 - I.xstar (I.obs ω) ij.1 ij.2|
          |I.yhat svdr θhat (I.obs ω) ij.1 ij.2 - I.ystar (I.obs ω) ij.1 ij.2| ≤ δ} \ N) := by
        rw [measureReal_def, measureReal_def, measure_diff_null hNnull]
    _ ≤ _ := measureReal_mono hsub
