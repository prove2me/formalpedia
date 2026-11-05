-- Prove2me | solution 1 for GreedWorks.OnlineList.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:52:40.100699+00:00
-- url     : https://prove2.me/submissions/ed2d970a-062c-4cb3-bc2a-dde6c0375120

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy
import Definitions.Def_GreedWorks_OnlineList_LP
import Theorems.Thm_GreedWorks_OnlineList_corollary_1
import Theorems.Thm_GreedWorks_OnlineList_lemma_4
import Theorems.Thm_GreedWorks_OnlineList_lemma_5

open MeasureTheory ProbabilityTheory

namespace GreedOLAux
open GreedWorks.OnlineList

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
set_option linter.unusedSectionVars false

/-! ### Scaling an instance by an integer factor `K` -/

noncomputable def scaleInst (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) :
    StochasticInstance M n Ω where
  Pr := I.Pr
  probability := I.probability
  P := fun i j ω => K * I.P i j ω
  measurable := fun i j =>
    (measurable_from_top (f := fun x : ℕ => K * x)).comp (I.measurable i j)
  eligible := I.eligible
  memLp := fun i j h => by
    have := (I.memLp i j h).const_mul (K : ℝ)
    convert this using 1
    funext ω; push_cast; ring
  hasMachine := I.hasMachine
  meanAtLeastOne := fun i j h => by
    have h1 := I.meanAtLeastOne i j h
    have : (∫ ω, ((K * I.P i j ω : ℕ) : ℝ) ∂I.Pr) = (K : ℝ) * ∫ ω, (I.P i j ω : ℝ) ∂I.Pr := by
      rw [← integral_const_mul]; congr 1; funext ω; push_cast; ring
    rw [this]
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  independentJobs := by
    have h := I.independentJobs.comp (fun _ (v : M → ℝ) => fun i => (K : ℝ) * v i)
      (fun _ => measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_mul _))
    convert h using 1
    funext j ω i
    simp [Function.comp]
  weight := I.weight
  weight_nonneg := I.weight_nonneg
  Delta := I.Delta
  Delta_nonneg := I.Delta_nonneg
  cvBound := fun i j h => by
    have h1 := I.cvBound i j h
    have hv : variance (fun ω => ((K * I.P i j ω : ℕ) : ℝ)) I.Pr =
        (K : ℝ) ^ 2 * variance (fun ω => (I.P i j ω : ℝ)) I.Pr := by
      rw [← variance_const_mul]; congr 1; funext ω; push_cast; ring
    have hm : (∫ ω, ((K * I.P i j ω : ℕ) : ℝ) ∂I.Pr) = (K : ℝ) * ∫ ω, (I.P i j ω : ℝ) ∂I.Pr := by
      rw [← integral_const_mul]; congr 1; funext ω; push_cast; ring
    rw [hv, hm]
    have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
    calc (K : ℝ) ^ 2 * variance (fun ω => (I.P i j ω : ℝ)) I.Pr
        ≤ (K : ℝ) ^ 2 * (I.Delta * (∫ ω, (I.P i j ω : ℝ) ∂I.Pr) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hK2
      _ = I.Delta * ((K : ℝ) * ∫ ω, (I.P i j ω : ℝ) ∂I.Pr) ^ 2 := by ring

lemma mean_scale (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) (i : M) (j : Fin n) :
    mean (scaleInst I K hK) i j = (K : ℝ) * mean I i j := by
  unfold mean
  rw [← integral_const_mul]
  show ∫ ω, ((K * I.P i j ω : ℕ) : ℝ) ∂I.Pr = _
  congr 1; funext ω; push_cast; ring

@[simp] lemma scale_weight (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) :
    (scaleInst I K hK).weight = I.weight := rfl

@[simp] lemma scale_Delta (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) :
    (scaleInst I K hK).Delta = I.Delta := rfl

lemma ratio_lt_iff {c : ℝ} (hc : 0 < c) (a b p q : ℝ) :
    a / (c * p) < b / (c * q) ↔ a / p < b / q := by
  rw [mul_comm c p, mul_comm c q, ← div_div, ← div_div]
  exact div_lt_div_iff_of_pos_right hc

lemma ratio_eq_iff {c : ℝ} (hc : 0 < c) (a b p q : ℝ) :
    a / (c * p) = b / (c * q) ↔ a / p = b / q := by
  rw [mul_comm c p, mul_comm c q, ← div_div, ← div_div]
  exact div_left_inj' hc.ne'

section Greedy
variable [DecidableEq M]
set_option linter.unusedSectionVars false

lemma high_scale (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) (j : Fin n) (i : M) :
    high (scaleInst I K hK) j i = high I j i := by
  have hc : (0 : ℝ) < K := by exact_mod_cast hK
  ext k
  simp only [high, Finset.mem_filter, Finset.mem_univ, true_and, mean_scale]
  show (I.weight j / (K * mean I i j) < I.weight k / (K * mean I i k) ∨
      (k ≤ j ∧ I.weight k / (K * mean I i k) = I.weight j / (K * mean I i j))) ↔ _
  rw [ratio_lt_iff hc, ratio_eq_iff hc]

lemma low_scale (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) (j : Fin n) (i : M) :
    low (scaleInst I K hK) j i = low I j i := by
  simp only [low, high_scale]

lemma incrementalCost_scale (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K)
    (m : Fin n → M) (j : Fin n) (i : M) :
    incrementalCost (scaleInst I K hK) m j i = (K : ℝ) * incrementalCost I m j i := by
  simp only [incrementalCost, high_scale, low_scale, mean_scale, scale_weight]
  rw [← Finset.mul_sum]
  show I.weight j * _ + _ = _
  ring

lemma isGreedy_scale (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K)
    (m : Fin n → M) (hm : IsGreedy I m) : IsGreedy (scaleInst I K hK) m := by
  have hc : (0 : ℝ) < K := by exact_mod_cast hK
  intro j
  refine ⟨(hm j).1, fun i hi => ?_⟩
  rw [incrementalCost_scale, incrementalCost_scale]
  exact mul_le_mul_of_nonneg_left ((hm j).2 i hi) hc.le

lemma fastMean_scale2 (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) (i : M) (j : Fin n) :
    fastMean (scaleInst I K hK) 2 i j = ((K : ℝ) / 2) * mean I i j := by
  simp only [fastMean, mean_scale]; push_cast; ring

lemma highFast_scale2 (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) (j : Fin n) (i : M) :
    highFast (scaleInst I K hK) 2 j i = high I j i := by
  have hc : (0 : ℝ) < (K : ℝ) / 2 := by
    have : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  ext k
  simp only [highFast, high, Finset.mem_filter, Finset.mem_univ, true_and, fastMean_scale2,
    scale_weight]
  rw [ratio_lt_iff hc, ratio_eq_iff hc]

lemma lowFast_scale2 (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K) (j : Fin n) (i : M) :
    lowFast (scaleInst I K hK) 2 j i = low I j i := by
  simp only [lowFast, low, highFast_scale2]

lemma alphaFast_scale2 (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K)
    (m : Fin n → M) (j : Fin n) :
    alphaFast (scaleInst I K hK) m 2 j = ((K : ℝ) / 2) * alpha I m j := by
  simp only [alphaFast, alpha, incrementalCostFast, incrementalCost, highFast_scale2,
    lowFast_scale2, fastMean_scale2, scale_weight]
  rw [← Finset.mul_sum]
  show I.weight j * _ + _ = _
  ring

lemma nominalCompletionFast_scale2 (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K)
    (m : Fin n → M) (j : Fin n) :
    nominalCompletionFast (scaleInst I K hK) m 2 j = ((K : ℝ) / 2) * nominalCompletion I m j := by
  simp only [nominalCompletionFast, nominalCompletion, highFast_scale2, fastMean_scale2]
  rw [← Finset.mul_sum]

end Greedy

/-! ### Counting integer slots below a threshold -/

lemma ind_zero_outside (c w : ℝ) :
    ∀ s ∉ Finset.range ⌈c⌉₊, (if (s : ℝ) < c then w else 0) = 0 := by
  intro s hs
  rw [Finset.mem_range, Nat.lt_ceil] at hs
  simp [hs]

lemma summable_ind (c w : ℝ) : Summable (fun s : ℕ => if (s : ℝ) < c then w else 0) :=
  (hasSum_sum_of_ne_finset_zero (ind_zero_outside c w)).summable

lemma tsum_ind (c w : ℝ) :
    ∑' s : ℕ, (if (s : ℝ) < c then w else 0) = (⌈c⌉₊ : ℝ) * w := by
  rw [tsum_eq_sum (ind_zero_outside c w)]
  rw [Finset.sum_congr rfl (g := fun _ => w) (fun s hs => by
    rw [Finset.mem_range, Nat.lt_ceil] at hs; simp [hs])]
  simp

section Beta
variable [DecidableEq M]
set_option linter.unusedSectionVars false

lemma sum_tsum_betaFast (I : StochasticInstance M n Ω) (m : Fin n → M) (f : ℕ) :
    ∑ i, ∑' s, betaFast I m f i s =
      ∑ k, (⌈nominalCompletionFast I m f k⌉₊ : ℝ) * I.weight k := by
  have h1 : ∀ i s, betaFast I m f i s = ∑ k, (if m k = i then
      (if (s : ℝ) < nominalCompletionFast I m f k then I.weight k else 0) else 0) := by
    intro i s
    simp only [betaFast]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : m k = i <;> simp [h]
  have h2 : ∀ i, ∑' s, betaFast I m f i s = ∑ k, (if m k = i then
      (⌈nominalCompletionFast I m f k⌉₊ : ℝ) * I.weight k else 0) := by
    intro i
    simp_rw [h1 i]
    rw [Summable.tsum_finsetSum (fun k _ => ?_)]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases h : m k = i <;> simp [h, tsum_ind]
    · by_cases h : m k = i
      · simp only [h, if_true]; exact summable_ind _ _
      · simp only [h, if_false]; exact summable_zero
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_comm]
  simp

end Beta

/-! ### Weak duality for (P) and (D) -/

open Classical in
lemma weak_duality (I : StochasticInstance M n Ω) (y : ProcessingPoint M n)
    (hy : IsPrimalFeasible I y) (a : Fin n → ℝ) (b : M → ℕ → ℝ)
    (hd : IsDualFeasible I a b) :
    ∑ j, a j - ∑ i, ∑' s, b i s ≤ primalValue I y := by
  obtain ⟨hy0, -, hys, hys2, hcap, hassign⟩ := hy
  obtain ⟨hb0, hbs, hdc⟩ := hd
  have hy1 : ∀ i j s, y i j s ≤ 1 := fun i j s =>
    le_trans (Finset.single_le_sum (f := fun j => y i j s) (fun j _ => hy0 i j s)
      (Finset.mem_univ j)) (hcap i s)
  have hyb : ∀ i j, Summable (fun s => y i j s * b i s) := fun i j =>
    Summable.of_nonneg_of_le (fun s => mul_nonneg (hy0 i j s) (hb0 i s))
      (fun s => by nlinarith [hy0 i j s, hb0 i s, hy1 i j s]) (hbs i)
  have key : ∀ j, ∀ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
      a j * ((∑' s, y i j s) / mean I i j) ≤
        (∑' s, y i j s * b i s) + I.weight j *
          ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2) := by
    intro j i hi
    have hel : I.eligible i j := (Finset.mem_filter.1 hi).2
    have hs1 : Summable (fun s : ℕ => y i j s / mean I i j * ((s : ℝ) + 1 / 2)) :=
      ((hys2 i j).mul_right (1 / mean I i j)).congr (fun s => by ring)
    have hs2 : Summable (fun s : ℕ => y i j s / 2) := (hys i j).div_const 2
    have hs3 := hs1.add hs2
    calc a j * ((∑' s, y i j s) / mean I i j) = ∑' s, y i j s * (a j / mean I i j) := by
          rw [tsum_mul_right]; ring
      _ ≤ ∑' s, (y i j s * b i s + I.weight j *
            (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2)) := by
          refine Summable.tsum_le_tsum (fun s => ?_) ((hys i j).mul_right _)
            ((hyb i j).add (hs3.mul_left _))
          have h2 : y i j s * (a j / mean I i j) ≤ y i j s * (b i s + I.weight j *
              (((s : ℝ) + 1 / 2) / mean I i j + 1 / 2)) :=
            mul_le_mul_of_nonneg_left (hdc i j s hel) (hy0 i j s)
          calc _ ≤ _ := h2
            _ = _ := by ring
      _ = _ := by rw [Summable.tsum_add (hyb i j) (hs3.mul_left _), tsum_mul_left]
  have hA : ∀ j, a j ≤ ∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
      ((∑' s, y i j s * b i s) + I.weight j *
          ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2)) := by
    intro j
    calc a j = a j * 1 := (mul_one _).symm
      _ = ∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
            a j * ((∑' s, y i j s) / mean I i j) := by rw [← hassign j, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (key j)
  have hT : ∑ j, ∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
      (∑' s, y i j s * b i s) ≤ ∑ i, ∑' s, b i s := by
    calc _ ≤ ∑ j, ∑ i, (∑' s, y i j s * b i s) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_univ_sum_of_nonneg
            (fun i => tsum_nonneg (fun s => mul_nonneg (hy0 i j s) (hb0 i s))))
      _ = ∑ i, ∑ j, (∑' s, y i j s * b i s) := Finset.sum_comm
      _ = ∑ i, ∑' s, ∑ j, y i j s * b i s := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Summable.tsum_finsetSum (fun j _ => hyb i j)]
      _ ≤ ∑ i, ∑' s, b i s := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine Summable.tsum_le_tsum (fun s => ?_) ?_ (hbs i)
          · rw [← Finset.sum_mul]; nlinarith [hcap i s, hb0 i s]
          · exact summable_sum (fun j _ => hyb i j)
  have hP : primalValue I y = ∑ j, I.weight j *
      ∑ i ∈ (Finset.univ.filter fun i : M => I.eligible i j),
        ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2) := rfl
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hA j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith

/-! ### Scaling a policy -/

noncomputable def cd (K : ℕ) (p : Realization M n) : Realization M n :=
  fun i j => ⌈(p i j : ℝ) / K⌉₊

noncomputable def scalePol (K : ℕ) (pol : Policy M n) : Policy M n :=
  fun p => ((pol (cd K p)).1, fun j => (K : ℝ) * (pol (cd K p)).2 j)

lemma le_K_cd (K : ℕ) (hK : 1 ≤ K) (x : ℕ) : (x : ℝ) ≤ K * (⌈(x : ℝ) / K⌉₊ : ℝ) := by
  have hc : (0 : ℝ) < K := by exact_mod_cast hK
  have := Nat.le_ceil ((x : ℝ) / K)
  calc (x : ℝ) = K * ((x : ℝ) / K) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left this hc.le

lemma cd_scale (K : ℕ) (hK : 1 ≤ K) (q : Realization M n) :
    cd K (fun i j => K * q i j) = q := by
  have hc : (K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < K := by exact_mod_cast hK
    exact this.ne'
  funext i j
  simp only [cd]
  push_cast
  rw [mul_div_cancel_left₀ _ hc, Nat.ceil_natCast]

lemma completion_scalePol_le (K : ℕ) (hK : 1 ≤ K) (pol : Policy M n) (p : Realization M n)
    (j : Fin n) : completion (scalePol K pol) p j ≤ K * completion pol (cd K p) j := by
  have h := le_K_cd K hK (p (machine pol (cd K p) j) j)
  show (K : ℝ) * start pol (cd K p) j + (p (machine pol (cd K p) j) j : ℝ) ≤
    K * (start pol (cd K p) j + (cd K p (machine pol (cd K p) j) j : ℝ))
  simp only [cd] at *
  nlinarith

lemma completion_scalePol_scale (K : ℕ) (hK : 1 ≤ K) (pol : Policy M n) (q : Realization M n)
    (j : Fin n) :
    completion (scalePol K pol) (fun i k => K * q i k) j = K * completion pol q j := by
  simp only [completion, start, machine, scalePol]
  rw [cd_scale K hK q]
  push_cast; ring

lemma scalePol_admissible (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K)
    (pol : Policy M n) (hpol : IsAdmissible I pol) :
    IsAdmissible (scaleInst I K hK) (scalePol K pol) := by
  have hc : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨hfeas, hna, hint⟩ := hpol
  refine ⟨?_, ?_, ?_⟩
  · intro p
    obtain ⟨h1, h2, h3⟩ := hfeas (cd K p)
    refine ⟨fun j => h1 j, fun j => ?_, fun j k hjk hmk => ?_⟩
    · show 0 ≤ (K : ℝ) * start pol (cd K p) j
      exact mul_nonneg hc.le (h2 j)
    · have zero_of : ∀ l, cd K p (machine pol (cd K p) l) l = 0 →
          p (machine pol (cd K p) l) l = 0 := by
        intro l hl
        have h := le_K_cd K hK (p (machine pol (cd K p) l) l)
        have hl' : ((⌈(p (machine pol (cd K p) l) l : ℝ) / K⌉₊ : ℕ) : ℝ) = 0 := by
          exact_mod_cast hl
        rw [hl', mul_zero] at h
        exact_mod_cast le_antisymm h (Nat.cast_nonneg _)
      have cj := completion_scalePol_le K hK pol p j
      have ck := completion_scalePol_le K hK pol p k
      rcases h3 j k hjk hmk with h | h | h | h
      · exact Or.inl (zero_of j h)
      · exact Or.inr (Or.inl (zero_of k h))
      · right; right; left
        show completion (scalePol K pol) p j ≤ (K : ℝ) * start pol (cd K p) k
        nlinarith
      · right; right; right
        show completion (scalePol K pol) p k ≤ (K : ℝ) * start pol (cd K p) j
        nlinarith
  · intro t p p' H j
    have e : ∀ (r : Realization M n) (l : Fin n),
        (start (scalePol K pol) r l ≤ t ↔ start pol (cd K r) l ≤ t / K) := by
      intro r l
      show (K : ℝ) * start pol (cd K r) l ≤ t ↔ _
      rw [le_div_iff₀ hc, mul_comm]
    have H' : ∀ l, start pol (cd K p) l ≤ t / K →
        (completion pol (cd K p) l ≤ t / K →
          cd K p' (machine pol (cd K p) l) l = cd K p (machine pol (cd K p) l) l) ∧
        (t / K < completion pol (cd K p) l →
          t / K < start pol (cd K p) l + (cd K p' (machine pol (cd K p) l) l : ℝ)) := by
      intro l hl
      obtain ⟨Ha, Hb⟩ := H l ((e p l).2 hl)
      have hle := completion_scalePol_le K hK pol p l
      constructor
      · intro hc1
        have : completion (scalePol K pol) p l ≤ t := by
          rw [le_div_iff₀ hc] at hc1; linarith
        have he : p' (machine pol (cd K p) l) l = p (machine pol (cd K p) l) l := Ha this
        simp only [cd]; rw [he]
      · intro hc2
        by_cases hcase : completion (scalePol K pol) p l ≤ t
        · have he : p' (machine pol (cd K p) l) l = p (machine pol (cd K p) l) l := Ha hcase
          have : cd K p' (machine pol (cd K p) l) l = cd K p (machine pol (cd K p) l) l := by
            simp only [cd]; rw [he]
          rw [this]; exact hc2
        · push Not at hcase
          have h3 : t < (K : ℝ) * start pol (cd K p) l + (p' (machine pol (cd K p) l) l : ℝ) :=
            Hb hcase
          have h4 := le_K_cd K hK (p' (machine pol (cd K p) l) l)
          rw [div_lt_iff₀ hc]
          show t < (start pol (cd K p) l + (⌈(p' (machine pol (cd K p) l) l : ℝ) / K⌉₊ : ℝ)) * K
          nlinarith
    have := hna (t / K) (cd K p) (cd K p') H' j
    refine ⟨by rw [e p j, e p' j]; exact this.1, fun hs => ?_⟩
    obtain ⟨hs1, hs2⟩ := this.2 ((e p j).1 hs)
    refine ⟨?_, hs2⟩
    show (K : ℝ) * start pol (cd K p') j = K * start pol (cd K p) j
    rw [hs1]
  · intro j
    have : (fun ω => completion (scalePol K pol) (fun i k => (scaleInst I K hK).P i k ω) j) =
        fun ω => (K : ℝ) * completion pol (fun i k => I.P i k ω) j := by
      funext ω
      exact completion_scalePol_scale K hK pol (fun i k => I.P i k ω) j
    rw [this]
    exact (hint j).const_mul _

lemma comparatorCost_scale (I : StochasticInstance M n Ω) (K : ℕ) (hK : 1 ≤ K)
    (pol : Policy M n) :
    comparatorCost (scaleInst I K hK) (scalePol K pol) = K * comparatorCost I pol := by
  unfold comparatorCost
  rw [← integral_const_mul]
  show ∫ ω, _ ∂I.Pr = _
  congr 1
  funext ω
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (fun i k => (scaleInst I K hK).P i k ω) = fun i k => K * I.P i k ω from rfl,
    completion_scalePol_scale K hK pol]
  simp only [scale_weight]; ring

/-! ### Linearity of expectation for the greedy schedule -/

section Alg
variable [DecidableEq M]

lemma mean_nonneg (I : StochasticInstance M n Ω) (i : M) (j : Fin n) : 0 ≤ mean I i j :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

lemma nominalCompletion_nonneg (I : StochasticInstance M n Ω) (m : Fin n → M) (j : Fin n) :
    0 ≤ nominalCompletion I m j := by
  simp only [nominalCompletion]
  exact Finset.sum_nonneg (fun k _ => mean_nonneg I _ _)

lemma algorithmCost_eq (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m) :
    algorithmCost I m = ∑ j, I.weight j * nominalCompletion I m j := by
  haveI := I.probability
  have hint : ∀ i k, I.eligible i k → Integrable (fun ω => (I.P i k ω : ℝ)) I.Pr :=
    fun i k h => (I.memLp i k h).integrable (by norm_num)
  have hmem : ∀ j, ∀ k ∈ (Finset.univ.filter fun k : Fin n =>
      m k = m j ∧ k ∈ high I j (m j)), Integrable (fun ω => (I.P (m j) k ω : ℝ)) I.Pr := by
    intro j k hk
    have h := (Finset.mem_filter.1 hk).2.1
    apply hint
    rw [← h]; exact (hm k).1
  have hac : ∀ j, Integrable (fun ω => algorithmCompletion I m j ω) I.Pr := by
    intro j
    simp only [algorithmCompletion]
    exact integrable_finsetSum _ (hmem j)
  unfold algorithmCost
  rw [integral_finsetSum _ (fun j _ => (hac j).const_mul _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul]
  congr 1
  simp only [algorithmCompletion, nominalCompletion]
  rw [integral_finsetSum _ (hmem j)]
  rfl

end Alg

end GreedOLAux

open GreedWorks.OnlineList GreedOLAux in
theorem solution {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (pol : Policy M n) (hpol : IsAdmissible I pol) :
    algorithmCost I m ≤ (4 + 2 * I.Delta) * comparatorCost I pol := by
  have hA1 : algorithmCost I m = ∑ j, alpha I m j := (lemma_4 n I m hm).1
  have hA2 := algorithmCost_eq I m hm
  have hW : 0 ≤ ∑ k, I.weight k := Finset.sum_nonneg (fun k _ => I.weight_nonneg k)
  have main : ∀ K : ℕ, ∀ hK : 1 ≤ K,
      (K : ℝ) * algorithmCost I m ≤
        (4 + 2 * I.Delta) * ((K : ℝ) * comparatorCost I pol) + 2 * ∑ k, I.weight k := by
    intro K hK
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    obtain ⟨y, hy, hyv⟩ := corollary_1 n (scaleInst I K hK) (scalePol K pol)
      (scalePol_admissible I K hK pol hpol)
    have hd := lemma_5 n (scaleInst I K hK) m (isGreedy_scale I K hK m hm) 2 le_rfl
    have hwd := weak_duality (scaleInst I K hK) y hy _ _ hd
    rw [comparatorCost_scale, scale_Delta] at hyv
    have e1 : ∑ j, alphaFast (scaleInst I K hK) m 2 j = ((K : ℝ) / 2) * algorithmCost I m := by
      simp_rw [alphaFast_scale2]; rw [← Finset.mul_sum, hA1]
    have e2 : ∑ i, ∑' s, betaFast (scaleInst I K hK) m 2 i s / ((2 : ℕ) : ℝ) ≤
        (((K : ℝ) / 2) * algorithmCost I m + ∑ k, I.weight k) / 2 := by
      simp_rw [tsum_div_const]
      rw [← Finset.sum_div, sum_tsum_betaFast]
      push_cast
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [hA2, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [scale_weight, nominalCompletionFast_scale2]
      have hc0 : 0 ≤ (K : ℝ) / 2 * nominalCompletion I m k :=
        mul_nonneg (by positivity) (nominalCompletion_nonneg I m k)
      have hceil := (Nat.ceil_lt_add_one hc0).le
      have hw := I.weight_nonneg k
      nlinarith
    try simp only at hwd
    rw [e1] at hwd
    nlinarith
  by_contra hcon
  push Not at hcon
  set ε := algorithmCost I m - (4 + 2 * I.Delta) * comparatorCost I pol with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (∑ k, I.weight k) / ε)
  have h := main (N + 1) (by omega)
  have hN' : 2 * (∑ k, I.weight k) < ((N + 1 : ℕ) : ℝ) * ε := by
    rw [div_lt_iff₀ hεpos] at hN
    push_cast; nlinarith
  have : ((N + 1 : ℕ) : ℝ) * ε ≤ 2 * ∑ k, I.weight k := by
    rw [hε]; nlinarith
  linarith
