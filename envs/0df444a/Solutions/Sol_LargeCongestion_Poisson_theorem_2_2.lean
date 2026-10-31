-- Prove2me | solution 2 for LargeCongestion.Poisson.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:11:14.061744+00:00
-- url     : https://prove2.me/submissions/20d5c67e-52f0-44e5-8c90-6973f8c9cd41

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game
import Theorems.Thm_LargeCongestion_Poisson_proposition_1
import Theorems.Thm_LargeCongestion_Poisson_lemma_1_smooth

namespace LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-! ### Total variation basics -/

section TV
variable {X : Type*} [MeasurableSpace X]

lemma tv_le {μ ν : Measure X} {c : ℝ}
    (h : ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ c) :
    MarkovChainCLT.tvDist μ ν ≤ c := by
  unfold MarkovChainCLT.tvDist
  refine csSup_le ?_ ?_
  · exact ⟨_, ∅, MeasurableSet.empty, rfl⟩
  · rintro r ⟨A, hA, rfl⟩
    exact h A hA

lemma le_tv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X}
    (hA : MeasurableSet A) : |μ.real A - ν.real A| ≤ MarkovChainCLT.tvDist μ ν := by
  unfold MarkovChainCLT.tvDist
  refine le_csSup ?_ ?_
  swap
  · exact ⟨A, hA, rfl⟩
  refine ⟨μ.real Set.univ + ν.real Set.univ, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  have h1 := measureReal_mono (μ := μ) (Set.subset_univ B)
  have h2 := measureReal_mono (μ := ν) (Set.subset_univ B)
  have h3 := measureReal_nonneg (μ := μ) (s := B)
  have h4 := measureReal_nonneg (μ := ν) (s := B)
  change |μ.real B - ν.real B| ≤ _
  rw [abs_le]; constructor <;> linarith

lemma tv_nonneg (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ MarkovChainCLT.tvDist μ ν :=
  le_trans (abs_nonneg _) (le_tv μ ν MeasurableSet.empty)

lemma tv_triangle (μ ν ρ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] :
    MarkovChainCLT.tvDist μ ρ ≤ MarkovChainCLT.tvDist μ ν + MarkovChainCLT.tvDist ν ρ :=
  tv_le fun A hA => by
    have h1 := le_tv μ ν hA
    have h2 := le_tv ν ρ hA
    calc |μ.real A - ρ.real A| ≤ |μ.real A - ν.real A| + |ν.real A - ρ.real A| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2

lemma tv_symm (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    MarkovChainCLT.tvDist μ ν ≤ MarkovChainCLT.tvDist ν μ :=
  tv_le fun A hA => by rw [abs_sub_comm]; exact le_tv ν μ hA

lemma tv_self (μ : Measure X) : MarkovChainCLT.tvDist μ μ ≤ 0 :=
  tv_le fun A _ => by simp

lemma tv_map {Y : Type*} [MeasurableSpace Y] {f : X → Y} (hf : Measurable f)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    MarkovChainCLT.tvDist (μ.map f) (ν.map f) ≤ MarkovChainCLT.tvDist μ ν :=
  tv_le fun A hA => by
    rw [map_measureReal_apply hf hA, map_measureReal_apply hf hA]
    exact le_tv μ ν (hf hA)

end TV

/-! ### Convolution contracts total variation -/

section Conv
variable {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]

lemma ms (A : Set M) : MeasurableSet A := (Set.to_countable A).measurableSet

lemma conv_apply_countable [AddCommMonoid M] [MeasurableAdd₂ M] (ρ μ : Measure M) [SFinite μ] (A : Set M) :
    (ρ ∗ μ) A = ∑' x, μ {y | x + y ∈ A} * ρ {x} := by
  rw [Measure.conv, Measure.map_apply measurable_add (ms A),
    Measure.prod_apply ((Set.to_countable _).measurableSet), lintegral_countable']
  rfl

lemma tsum_singleton_real (ρ : Measure M) [IsFiniteMeasure ρ] :
    HasSum (fun x => ρ.real {x}) (ρ.real Set.univ) := by
  have h1 : ∑' x, ρ {x} = ρ Set.univ := by
    have := lintegral_countable' (μ := ρ) (fun _ => (1 : ℝ≥0∞))
    simp only [lintegral_const, one_mul] at this
    exact this.symm
  have hfin : ∑' x, ρ {x} ≠ ∞ := by rw [h1]; exact measure_ne_top _ _
  have := (ENNReal.summable_toReal hfin).hasSum
  rw [← ENNReal.tsum_toReal_eq (fun x => measure_ne_top _ _), h1] at this
  exact this

lemma conv_real [AddCommMonoid M] [MeasurableAdd₂ M] (ρ μ : Measure M) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] (A : Set M) :
    (ρ ∗ μ).real A = ∑' x, μ.real {y | x + y ∈ A} * ρ.real {x} := by
  rw [Measure.real, conv_apply_countable, ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul]; rfl
  · intro x; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

lemma tv_conv_left [AddCommMonoid M] [MeasurableAdd₂ M] (ρ μ ν : Measure M) [IsProbabilityMeasure ρ] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    MarkovChainCLT.tvDist (ρ ∗ μ) (ρ ∗ ν) ≤ MarkovChainCLT.tvDist μ ν := by
  apply tv_le
  intro A _
  have hρ := tsum_singleton_real ρ
  rw [probReal_univ] at hρ
  have hs : ∀ (m : Measure M) [IsFiniteMeasure m],
      Summable (fun x => m.real {y | x + y ∈ A} * ρ.real {x}) := by
    intro m _
    refine Summable.of_nonneg_of_le (fun x => mul_nonneg measureReal_nonneg measureReal_nonneg)
      (fun x => mul_le_mul_of_nonneg_right (measureReal_mono (Set.subset_univ _))
        measureReal_nonneg) (hρ.summable.mul_left (m.real Set.univ))
  rw [conv_real, conv_real, ← (hs μ).tsum_sub (hs ν)]
  have hb : ∀ x, |μ.real {y | x + y ∈ A} * ρ.real {x} - ν.real {y | x + y ∈ A} * ρ.real {x}| ≤
      MarkovChainCLT.tvDist μ ν * ρ.real {x} := by
    intro x
    rw [← sub_mul, abs_mul, abs_of_nonneg measureReal_nonneg]
    exact mul_le_mul_of_nonneg_right (le_tv μ ν (ms _)) measureReal_nonneg
  have hsn : Summable (fun x => ‖μ.real {y | x + y ∈ A} * ρ.real {x} -
      ν.real {y | x + y ∈ A} * ρ.real {x}‖) :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => hb x)
      (hρ.summable.mul_left _)
  calc |∑' x, (μ.real {y | x + y ∈ A} * ρ.real {x} - ν.real {y | x + y ∈ A} * ρ.real {x})|
      ≤ ∑' x, ‖μ.real {y | x + y ∈ A} * ρ.real {x} - ν.real {y | x + y ∈ A} * ρ.real {x}‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' x, MarkovChainCLT.tvDist μ ν * ρ.real {x} :=
        hsn.tsum_le_tsum (fun x => hb x) (hρ.summable.mul_left _)
    _ = MarkovChainCLT.tvDist μ ν := by rw [tsum_mul_left, hρ.tsum_eq, mul_one]

lemma tv_conv_right [AddCommMonoid M] [MeasurableAdd₂ M] (ρ μ ν : Measure M) [IsProbabilityMeasure ρ] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    MarkovChainCLT.tvDist (μ ∗ ρ) (ν ∗ ρ) ≤ MarkovChainCLT.tvDist μ ν := by
  rw [Measure.conv_comm μ ρ, Measure.conv_comm ν ρ]
  exact tv_conv_left ρ μ ν

lemma tv_conv [AddCommMonoid M] [MeasurableAdd₂ M] (μ₁ μ₂ ν₁ ν₂ : Measure M) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    MarkovChainCLT.tvDist (μ₁ ∗ μ₂) (ν₁ ∗ ν₂) ≤
      MarkovChainCLT.tvDist μ₁ ν₁ + MarkovChainCLT.tvDist μ₂ ν₂ :=
  (tv_triangle _ (ν₁ ∗ μ₂) _).trans (add_le_add (tv_conv_right _ _ _) (tv_conv_left _ _ _))

end Conv

end LCPProp1Aux

namespace LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-! ### Finite weighted laws -/

section Law
variable {X : Type*} [MeasurableSpace X]

lemma law_real {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (f : α → X)
    {A : Set X} (hA : MeasurableSet A) :
    (∑ a, ENNReal.ofReal (w a) • Measure.dirac (f a)).real A =
      ∑ a, w a * A.indicator (fun _ => (1 : ℝ)) (f a) := by
  rw [Measure.real, Measure.coe_finsetSum, Finset.sum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hw a)]
    by_cases h : f a ∈ A <;> simp [h]
  · intro a _
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      by_cases h : f a ∈ A <;> simp [h])

lemma law_univ {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (f : α → X) : IsProbabilityMeasure (∑ a, ENNReal.ofReal (w a) • Measure.dirac (f a)) := by
  constructor
  have := law_real w hw f MeasurableSet.univ
  simp only [Set.indicator_univ, mul_one, hw1] at this
  rw [Measure.real] at this
  have hne : (∑ a, ENNReal.ofReal (w a) • Measure.dirac (f a)) Set.univ ≠ ∞ := by
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_ne_top.2 (fun a _ => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
  exact (ENNReal.toReal_eq_one_iff _).1 this

end Law

/-! ### Products of Poisson laws -/

section Poi
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `⊗_k Poisson(a_k)` on `K → ℕ`. -/
noncomputable def piPo (a : K → ℝ) : Measure (K → ℕ) :=
  Measure.pi (fun k => poissonMeasure (a k).toNNReal)

instance (a : K → ℝ) : IsProbabilityMeasure (piPo a) := by unfold piPo; infer_instance

lemma piPo_singleton_real (a : K → ℝ) (ha : ∀ k, 0 ≤ a k) (x : K → ℕ) :
    (piPo a).real {x} = ∏ k, (Real.exp (-a k) * a k ^ (x k) / ((x k).factorial : ℝ)) := by
  rw [← Set.univ_pi_singleton, piPo, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [← Measure.real, poissonMeasure_real_singleton, Real.coe_toNNReal _ (ha k)]

lemma piPo_zero_real (a : K → ℝ) (ha : ∀ k, 0 ≤ a k) :
    (piPo a).real {0} = Real.exp (-∑ k, a k) := by
  rw [piPo_singleton_real a ha, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp

lemma piPo_single_real (a : K → ℝ) (ha : ∀ k, 0 ≤ a k) (k : K) :
    (piPo a).real {Pi.single k 1} = a k * Real.exp (-∑ k, a k) := by
  rw [piPo_singleton_real a ha, ← Finset.sum_neg_distrib, Real.exp_sum,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [Finset.prod_congr rfl (fun j hj => by
    rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)])]
  simp only [Pi.single_eq_same, pow_one, Nat.factorial_one, Nat.cast_one, div_one, pow_zero,
    Nat.factorial_zero, mul_one]
  ring

lemma piPo_conv (a b : K → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) :
    piPo a ∗ piPo b = piPo (a + b) := by
  unfold piPo
  rw [Measure.conv, ← (measurePreserving_arrowProdEquivProdArrow ℕ ℕ K
    (fun k => poissonMeasure (a k).toNNReal) (fun k => poissonMeasure (b k).toNNReal)).map_eq,
    Measure.map_map measurable_add (MeasurableEquiv.measurable _)]
  have : (fun x : (K → ℕ) × (K → ℕ) => x.1 + x.2) ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ K) =
      fun w k => (fun p : ℕ × ℕ => p.1 + p.2) (w k) := by
    funext w k; rfl
  rw [this, Measure.pi_map_pi (fun k => measurable_add.aemeasurable)]
  congr 1; funext k
  rw [← Measure.conv, poissonMeasure_conv_poissonMeasure, Pi.add_apply,
    Real.toNNReal_add (ha k) (hb k)]

lemma ms' (A : Set (K → ℕ)) : MeasurableSet A := (Set.to_countable A).measurableSet

lemma tv_dirac_zero (μ : Measure (K → ℕ)) [IsProbabilityMeasure μ] :
    MarkovChainCLT.tvDist μ (Measure.dirac 0) ≤ 1 - μ.real {0} := by
  apply tv_le
  intro A hA
  have hd : (Measure.dirac (0 : K → ℕ)).real A = A.indicator (fun _ => (1 : ℝ)) 0 := by
    rw [Measure.real, Measure.dirac_apply' _ hA]
    by_cases h : (0 : K → ℕ) ∈ A <;> simp [h]
  rw [hd]
  by_cases h : (0 : K → ℕ) ∈ A
  · rw [Set.indicator_of_mem h]
    have h1 : μ.real {0} ≤ μ.real A := measureReal_mono (Set.singleton_subset_iff.2 h)
    have h2 : μ.real A ≤ 1 := by
      rw [← probReal_univ (μ := μ)]; exact measureReal_mono (Set.subset_univ _)
    rw [abs_le]; constructor <;> linarith
  · rw [Set.indicator_of_notMem h, sub_zero, abs_of_nonneg measureReal_nonneg]
    have h1 : μ.real A ≤ μ.real ({0}ᶜ) :=
      measureReal_mono (fun x hx hx0 => h (by rw [Set.mem_singleton_iff.1 hx0] at hx; exact hx))
    rw [measureReal_compl (ms' _), probReal_univ] at h1
    exact h1

lemma tv_piPo_dirac (a : K → ℝ) (ha : ∀ k, 0 ≤ a k) :
    MarkovChainCLT.tvDist (piPo a) (Measure.dirac 0) ≤ ∑ k, a k := by
  refine (tv_dirac_zero _).trans ?_
  rw [piPo_zero_real a ha]
  linarith [Real.add_one_le_exp (-∑ k, a k)]

lemma tv_piPo (a b : K → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) :
    MarkovChainCLT.tvDist (piPo a) (piPo b) ≤ ∑ k, |a k - b k| := by
  set c : K → ℝ := fun k => min (a k) (b k)
  set δ : K → ℝ := fun k => a k - c k
  set δ' : K → ℝ := fun k => b k - c k
  have hc : ∀ k, 0 ≤ c k := fun k => le_min (ha k) (hb k)
  have hδ : ∀ k, 0 ≤ δ k := fun k => sub_nonneg.2 (min_le_left _ _)
  have hδ' : ∀ k, 0 ≤ δ' k := fun k => sub_nonneg.2 (min_le_right _ _)
  have h1 : piPo a = piPo c ∗ piPo δ := by
    rw [piPo_conv c δ hc hδ]; congr 1; funext k; simp [c, δ]
  have h2 : piPo b = piPo c ∗ piPo δ' := by
    rw [piPo_conv c δ' hc hδ']; congr 1; funext k; simp [c, δ']
  rw [h1, h2]
  refine (tv_conv_left _ _ _).trans ?_
  refine (tv_triangle _ (Measure.dirac 0) _).trans ?_
  have e1 := tv_piPo_dirac δ hδ
  have e2 := (tv_symm (Measure.dirac (0 : K → ℕ)) (piPo δ')).trans (tv_piPo_dirac δ' hδ')
  have e3 : ∑ k, δ k + ∑ k, δ' k = ∑ k, |a k - b k| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [δ, δ', c]
    rcases le_total (a k) (b k) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  linarith

end Poi

end LCPProp1Aux

namespace LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

section LeCam
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `q_k = P(V = e_k)` for a single player with weights `w` and contribution `V`. -/
noncomputable def qv {α : Type*} [Fintype α] (w : α → ℝ) (V : α → (K → ℕ)) (k : K) : ℝ :=
  ∑ a, if V a = Pi.single k 1 then w a else 0

lemma qv_nonneg {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (V : α → (K → ℕ))
    (k : K) : 0 ≤ qv w V k :=
  Finset.sum_nonneg (fun a _ => by split_ifs; exact hw a; exact le_rfl)

lemma single_ne_zero (k : K) : (Pi.single k 1 : K → ℕ) ≠ 0 := by
  intro h
  have := congrFun h k
  simp at this

lemma single_inj {k j : K} (h : (Pi.single k 1 : K → ℕ) = Pi.single j 1) : k = j := by
  by_contra hkj
  have := congrFun h k
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hkj] at this
  exact one_ne_zero this

/-- Decomposition of a single-player law according to the value of `V`. -/
lemma single_decomp {α : Type*} [Fintype α] (w : α → ℝ) (V : α → (K → ℕ))
    (hV : ∀ a, V a = 0 ∨ ∃ k, V a = Pi.single k 1) (A : Set (K → ℕ)) :
    ∑ a, w a * A.indicator (fun _ => (1 : ℝ)) (V a) =
      A.indicator (fun _ => (1 : ℝ)) 0 * (∑ a, if V a = 0 then w a else 0) +
        ∑ k, A.indicator (fun _ => (1 : ℝ)) (Pi.single k 1) * qv w V k := by
  unfold qv
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun k a => A.indicator (fun _ => (1 : ℝ)) (Pi.single k 1) *
    if V a = Pi.single k 1 then w a else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rcases hV a with h0 | ⟨j, hj⟩
  · rw [h0, if_pos rfl]
    rw [Finset.sum_eq_zero (fun k _ => by rw [if_neg (Ne.symm (single_ne_zero k)), mul_zero])]
    ring
  · rw [hj, if_neg (single_ne_zero j), mul_zero, zero_add]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; ring
    · intro k _ hkj
      rw [if_neg (fun h => hkj (single_inj h).symm), mul_zero]
    · simp

lemma single_upper {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (V : α → (K → ℕ)) (hV : ∀ a, V a = 0 ∨ ∃ k, V a = Pi.single k 1)
    (A : Set (K → ℕ)) :
    (∑ a, ENNReal.ofReal (w a) • Measure.dirac (V a)).real A - (piPo (qv w V)).real A ≤
      (∑ k, qv w V k) ^ 2 := by
  classical
  set Q := ∑ k, qv w V k with hQ
  have hq0 := qv_nonneg w hw V
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun k _ => hq0 k)
  set ind : (K → ℕ) → ℝ := A.indicator (fun _ => (1 : ℝ)) with hind
  have hind01 : ∀ x, 0 ≤ ind x ∧ ind x ≤ 1 := by
    intro x; simp only [hind]; by_cases h : x ∈ A <;> simp [h]
  rw [law_real w hw V (ms' A), single_decomp w V hV A]
  -- the mass at zero
  have hZ : (∑ a, if V a = 0 then w a else 0) = 1 - Q := by
    have := single_decomp w V hV Set.univ
    simp only [Set.indicator_univ, mul_one, one_mul, hw1] at this
    rw [hQ]; linarith
  rw [hZ]
  -- lower bound for the Poisson side
  set e : K → (K → ℕ) := fun k => Pi.single k 1 with he
  have he_inj : Function.Injective e := fun k j h => single_inj h
  have h0img : (0 : K → ℕ) ∉ Finset.univ.image e := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro k h; exact single_ne_zero k h
  set F : Finset (K → ℕ) := (insert 0 (Finset.univ.image e)).filter (· ∈ A) with hF
  have hPF : (piPo (qv w V)).real (F : Set (K → ℕ)) ≤ (piPo (qv w V)).real A :=
    measureReal_mono (fun x hx => (Finset.mem_filter.1 hx).2)
  rw [← sum_measureReal_singleton, hF, Finset.sum_filter, Finset.sum_insert h0img,
    Finset.sum_image (fun k _ j _ h => he_inj h)] at hPF
  have hP0 := piPo_zero_real (qv w V) hq0
  have hP1 := piPo_single_real (qv w V) hq0
  rw [← hQ] at hP0 hP1
  have hind0 : (if (0 : K → ℕ) ∈ A then (piPo (qv w V)).real {0} else 0) =
      ind 0 * Real.exp (-Q) := by
    simp only [hind]; rw [hP0]; by_cases h : (0 : K → ℕ) ∈ A <;> simp [h]
  have hind1 : ∀ k, (if e k ∈ A then (piPo (qv w V)).real {e k} else 0) =
      ind (e k) * (qv w V k * Real.exp (-Q)) := by
    intro k; simp only [hind, he]; rw [hP1 k]; by_cases h : (Pi.single k 1 : K → ℕ) ∈ A <;> simp [h]
  rw [hind0, Finset.sum_congr rfl (fun k _ => hind1 k)] at hPF
  -- combine
  have hexp : 1 - Q ≤ Real.exp (-Q) := by linarith [Real.add_one_le_exp (-Q)]
  have hexp2 : 1 - Real.exp (-Q) ≤ Q := by linarith [Real.add_one_le_exp (-Q)]
  have hexp3 : 0 ≤ 1 - Real.exp (-Q) := by
    have := Real.exp_le_one_iff.2 (by linarith : -Q ≤ 0); linarith
  have hterm : ∀ k, ind (e k) * qv w V k - ind (e k) * (qv w V k * Real.exp (-Q)) ≤
      qv w V k * (1 - Real.exp (-Q)) := by
    intro k
    have := hind01 (e k)
    have h1 : ind (e k) * qv w V k - ind (e k) * (qv w V k * Real.exp (-Q)) =
        ind (e k) * (qv w V k * (1 - Real.exp (-Q))) := by ring
    rw [h1]
    calc ind (e k) * (qv w V k * (1 - Real.exp (-Q))) ≤ 1 * (qv w V k * (1 - Real.exp (-Q))) :=
          mul_le_mul_of_nonneg_right this.2 (mul_nonneg (hq0 k) hexp3)
      _ = _ := one_mul _
  have hsum : ∑ k, ind (e k) * qv w V k - ∑ k, ind (e k) * (qv w V k * Real.exp (-Q)) ≤
      Q * (1 - Real.exp (-Q)) := by
    rw [← Finset.sum_sub_distrib, hQ, Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => hterm k)
  have hz : ind 0 * (1 - Q) - ind 0 * Real.exp (-Q) ≤ 0 := by
    have := hind01 0
    have : ind 0 * (1 - Q - Real.exp (-Q)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos this.1 (by linarith)
    linarith
  have hQQ : Q * (1 - Real.exp (-Q)) ≤ Q ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hexp2 hQ0
  simp only [he] at hsum hz hPF ⊢
  linarith

lemma single_bound {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (V : α → (K → ℕ)) (hV : ∀ a, V a = 0 ∨ ∃ k, V a = Pi.single k 1) :
    MarkovChainCLT.tvDist (∑ a, ENNReal.ofReal (w a) • Measure.dirac (V a)) (piPo (qv w V)) ≤
      (∑ k, qv w V k) ^ 2 := by
  have := law_univ w hw hw1 V
  apply tv_le
  intro A _
  rw [abs_le]
  constructor
  · have h := single_upper w hw hw1 V hV Aᶜ
    rw [measureReal_compl (ms' A), measureReal_compl (ms' A), probReal_univ, probReal_univ] at h
    linarith
  · exact single_upper w hw hw1 V hV A

/-- Convolution of two finite laws. -/
lemma conv_law {M : Type*} [AddCommMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M]
    {α β : Type*} [Fintype α] [Fintype β] (c : α → ℝ≥0∞) (d : β → ℝ≥0∞) (x : α → M)
    (y : β → M) :
    (∑ a, c a • Measure.dirac (x a)) ∗ (∑ b, d b • Measure.dirac (y b)) =
      ∑ p : α × β, (c p.1 * d p.2) • Measure.dirac (x p.1 + y p.2) := by
  rw [← Measure.sum_fintype, ← Measure.sum_fintype, ← Measure.sum_fintype, Measure.conv,
    Measure.prod_sum, Measure.map_sum measurable_add.aemeasurable]
  congr 1; funext p
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' measurable_add, smul_smul]

/-- The law of `∑_i V_i(ω_i)` under the product weights `∏_i w_i(ω_i)`. -/
noncomputable def lawN {α : Type*} [Fintype α] {N : ℕ} (w : Fin N → α → ℝ)
    (V : Fin N → α → (K → ℕ)) : Measure (K → ℕ) :=
  ∑ ω : Fin N → α, ENNReal.ofReal (∏ i, w i (ω i)) • Measure.dirac (∑ i, V i (ω i))

lemma lawN_prob {α : Type*} [Fintype α] {N : ℕ} (w : Fin N → α → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hw1 : ∀ i, ∑ a, w i a = 1) (V : Fin N → α → (K → ℕ)) : IsProbabilityMeasure (lawN w V) := by
  unfold lawN
  apply law_univ
  · intro ω; exact Finset.prod_nonneg (fun i _ => hw i (ω i))
  · exact (Fintype.prod_sum (fun i a => w i a)).symm.trans (by simp [hw1])

lemma lawN_succ {α : Type*} [Fintype α] {N : ℕ} (w : Fin (N + 1) → α → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (V : Fin (N + 1) → α → (K → ℕ)) :
    lawN w V = (∑ a, ENNReal.ofReal (w 0 a) • Measure.dirac (V 0 a)) ∗
      lawN (fun i => w i.succ) (fun i => V i.succ) := by
  unfold lawN
  rw [conv_law]
  symm
  refine Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ (fun p => ?_)
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  rw [ENNReal.ofReal_mul (hw 0 p.1)]

theorem lecam {α : Type*} [Fintype α] : ∀ (N : ℕ) (w : Fin N → α → ℝ)
    (V : Fin N → α → (K → ℕ)), (∀ i a, 0 ≤ w i a) → (∀ i, ∑ a, w i a = 1) →
    (∀ i a, V i a = 0 ∨ ∃ k, V i a = Pi.single k 1) →
    MarkovChainCLT.tvDist (lawN w V) (piPo (fun k => ∑ i, qv (w i) (V i) k)) ≤
      ∑ i, (∑ k, qv (w i) (V i) k) ^ 2 := by
  intro N
  induction N with
  | zero =>
    intro w V _ _ _
    have h1 : lawN w V = Measure.dirac 0 := by
      unfold lawN; simp
    have h2 : (fun k => ∑ i : Fin 0, qv (w i) (V i) k) = fun _ => 0 := by
      funext k; simp
    rw [h1, h2]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    refine (tv_symm _ _).trans ((tv_piPo_dirac _ (fun _ => le_rfl)).trans ?_)
    simp
  | succ N ih =>
    intro w V hw hw1 hV
    have := law_univ (w 0) (hw 0) (hw1 0) (V 0)
    have := lawN_prob (fun i => w i.succ) (fun i => hw i.succ) (fun i => hw1 i.succ)
      (fun i => V i.succ)
    have hq : ∀ i k, 0 ≤ qv (w i) (V i) k := fun i k => qv_nonneg (w i) (hw i) (V i) k
    have hsplit : piPo (fun k => ∑ i, qv (w i) (V i) k) =
        piPo (qv (w 0) (V 0)) ∗ piPo (fun k => ∑ i : Fin N, qv (w i.succ) (V i.succ) k) := by
      rw [piPo_conv _ _ (hq 0) (fun k => Finset.sum_nonneg (fun i _ => hq i.succ k))]
      congr 1; funext k
      rw [Fin.sum_univ_succ]; rfl
    rw [lawN_succ w hw V, hsplit, Fin.sum_univ_succ]
    refine (tv_conv _ _ _ _).trans (add_le_add ?_ ?_)
    · exact single_bound (w 0) (hw 0) (hw1 0) (V 0) (hV 0)
    · exact ih (fun i => w i.succ) (fun i => V i.succ) (fun i => hw i.succ)
        (fun i => hw1 i.succ) (fun i => hV i.succ)

end LeCam

end LCPProp1Aux

namespace LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter LargeCongestion.Poisson
open scoped ENNReal NNReal Topology

section Game
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

/-- The weight of player `i`'s coordinate `(U_i, S_i) = a`. -/
def pw {N : ℕ} (u : Fin N → ℝ) (σ : Fin N → Finset E → ℝ) (i : Fin N)
    (a : Bool × Finset E) : ℝ :=
  (if a.1 then u i else 1 - u i) * σ i a.2

lemma pw_nonneg {N : ℕ} {S : T → Finset (Finset E)} {τ : Fin N → T} {u : Fin N → ℝ}
    {σ : Fin N → Finset E → ℝ} (hu : IsBernoulliGame u) (hσ : IsMixedProfile S τ σ) (i : Fin N)
    (a : Bool × Finset E) : 0 ≤ pw u σ i a := by
  unfold pw
  refine mul_nonneg ?_ (hσ.1 i a.2)
  split_ifs
  · exact (hu i).1.le
  · linarith [(hu i).2]

lemma sum_sigma_one' {N : ℕ} {S : T → Finset (Finset E)} {τ : Fin N → T}
    {σ : Fin N → Finset E → ℝ} (hσ : IsMixedProfile S τ σ) (j : Fin N) :
    ∑ s : Finset E, σ j s = 1 := by
  rw [← hσ.2.2 j]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  exact hσ.2.1 j s hs

lemma pw_sum_one {N : ℕ} {S : T → Finset (Finset E)} {τ : Fin N → T} {u : Fin N → ℝ}
    {σ : Fin N → Finset E → ℝ} (hσ : IsMixedProfile S τ σ) (i : Fin N) :
    ∑ a, pw u σ i a = 1 := by
  unfold pw
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_sigma_one' hσ i]
  ring

lemma pw_sum_true {N : ℕ} {S : T → Finset (Finset E)} {τ : Fin N → T} {u : Fin N → ℝ}
    {σ : Fin N → Finset E → ℝ} (hσ : IsMixedProfile S τ σ) (i : Fin N) :
    ∑ a, (if a.1 = true then pw u σ i a else 0) = u i := by
  unfold pw
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, Finset.sum_const_zero, add_zero]
  rw [← Finset.mul_sum, sum_sigma_one' hσ i, mul_one]

lemma law_eq_lawN {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ} (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (f : Outcome E N → (K → ℕ))
    (V : Fin N → Bool × Finset E → (K → ℕ)) (hf : ∀ ω, f ω = ∑ i, V i (ω i)) :
    law u σ f = lawN (pw u σ) V := by
  unfold law lawN
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [hf ω]
  rfl

lemma law_prob {X : Type*} [MeasurableSpace X] {N : ℕ} {S : T → Finset (Finset E)}
    {τ : Fin N → T} {u : Fin N → ℝ} {σ : Fin N → Finset E → ℝ} (hu : IsBernoulliGame u)
    (hσ : IsMixedProfile S τ σ) (f : Outcome E N → X) : IsProbabilityMeasure (law u σ f) := by
  unfold law
  apply law_univ
  · intro ω; exact Finset.prod_nonneg (fun i _ => pw_nonneg hu hσ i (ω i))
  · exact (Fintype.prod_sum (fun i a => pw u σ i a)).symm.trans (by simp [pw_sum_one hσ])

lemma law_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ} (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (f : Outcome E N → X) (g : X → Y) (hg : Measurable g) :
    law u σ (g ∘ f) = (law u σ f).map g := by
  unfold law
  rw [← Measure.sum_fintype, ← Measure.sum_fintype, Measure.map_sum hg.aemeasurable]
  congr 1; funext ω
  rw [Measure.map_smul, Measure.map_dirac' hg]
  rfl

lemma sum_qv_le {K : Type*} [Fintype K] [DecidableEq K] (w : Bool × Finset E → ℝ)
    (hw : ∀ a, 0 ≤ w a) (V : Bool × Finset E → (K → ℕ))
    (hV : ∀ a, V a = 0 ∨ ∃ k, V a = Pi.single k 1) (hV0 : ∀ a, a.1 = false → V a = 0) :
    ∑ k, qv w V k ≤ ∑ a, (if a.1 = true then w a else 0) := by
  have h := single_decomp w V hV Set.univ
  simp only [Set.indicator_univ, mul_one, one_mul] at h
  have h2 : ∑ a, w a - ∑ a, (if V a = 0 then w a else 0) ≤
      ∑ a, (if a.1 = true then w a else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun a _ => ?_)
    by_cases h1 : a.1 = true
    · rw [if_pos h1]; split_ifs <;> linarith [hw a]
    · have h1' : a.1 = false := by simpa using h1
      rw [if_pos (hV0 a h1'), if_neg h1]; simp
  linarith

/-! Flows -/

/-- Player `i`'s contribution to the flow vector. -/
def Vf {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (i : Fin N)
    (a : Bool × Finset E) : FlowIdx S → ℕ :=
  fun p => if τ i = p.1.1 ∧ a.1 = true ∧ a.2 = p.1.2 then 1 else 0

lemma Vf_cases {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (i : Fin N)
    (a : Bool × Finset E) : Vf S τ i a = 0 ∨ ∃ k, Vf S τ i a = Pi.single k 1 := by
  by_cases h : a.1 = true ∧ a.2 ∈ S (τ i)
  · right
    refine ⟨⟨(τ i, a.2), h.2⟩, ?_⟩
    funext p
    simp only [Vf]
    by_cases hp : p = ⟨(τ i, a.2), h.2⟩
    · subst hp; simp [h.1]
    · rw [Pi.single_eq_of_ne hp, if_neg]
      rintro ⟨h1, -, h3⟩
      exact hp (Subtype.ext (Prod.ext h1.symm h3.symm))
  · left
    funext p
    simp only [Vf, Pi.zero_apply]
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact h ⟨h2, by rw [h3, h1]; exact p.2⟩

lemma Vf_false {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (i : Fin N)
    (a : Bool × Finset E) (ha : a.1 = false) : Vf S τ i a = 0 := by
  funext p; simp [Vf, ha]

lemma qv_flow {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (i : Fin N) (k : FlowIdx S) :
    qv (pw u σ i) (Vf S τ i) k = if τ i = k.1.1 then u i * σ i k.1.2 else 0 := by
  have key : ∀ a, (Vf S τ i a = Pi.single k 1) ↔ (τ i = k.1.1 ∧ a = (true, k.1.2)) := by
    intro a
    constructor
    · intro h
      have hk := congrFun h k
      simp only [Vf, Pi.single_eq_same] at hk
      split_ifs at hk with hc
      · exact ⟨hc.1, Prod.ext hc.2.1 hc.2.2⟩
    · rintro ⟨h1, rfl⟩
      funext p
      simp only [Vf]
      by_cases hp : p = k
      · subst hp; simp [h1]
      · rw [Pi.single_eq_of_ne hp, if_neg]
        rintro ⟨h2, -, h3⟩
        exact hp (Subtype.ext (Prod.ext (h1 ▸ h2).symm h3.symm))
  unfold qv
  simp only [key]
  by_cases h : τ i = k.1.1
  · simp only [h, true_and, if_true]
    rw [Finset.sum_ite_eq']
    simp [pw]
  · simp [h]

lemma flow_bound {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (u : Fin N → ℝ)
    (hu : IsBernoulliGame u) (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) :
    MarkovChainCLT.tvDist (law u σ (flowVec S τ))
        (piPo (fun p : FlowIdx S => expFlow τ u σ p.1.1 p.1.2)) ≤ ∑ i, u i ^ 2 := by
  rw [law_eq_lawN u σ (flowVec S τ) (Vf S τ) (fun ω => by
    funext p; simp [flowVec, flowRV, Vf, Finset.sum_apply])]
  have h := lecam N (pw u σ) (Vf S τ) (fun i a => pw_nonneg hu hσ i a)
    (fun i => pw_sum_one hσ i) (fun i a => Vf_cases S τ i a)
  have hpo : (fun k : FlowIdx S => ∑ i, qv (pw u σ i) (Vf S τ i) k) =
      fun p => expFlow τ u σ p.1.1 p.1.2 := by
    funext p
    simp only [qv_flow, expFlow]
  rw [hpo] at h
  refine h.trans (Finset.sum_le_sum (fun i _ => ?_))
  have h1 := sum_qv_le (pw u σ i) (pw_nonneg hu hσ i) (Vf S τ i) (Vf_cases S τ i)
    (Vf_false S τ i)
  rw [pw_sum_true hσ i] at h1
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => qv_nonneg _ (pw_nonneg hu hσ i) _ k)) h1 2

/-! Loads -/

/-- Player `i`'s contribution `U_{i,e}` to the load of `e`, as a vector indexed by `Unit`. -/
def Vl (e : E) (a : Bool × Finset E) : Unit → ℕ :=
  fun _ => if a.1 = true ∧ e ∈ a.2 then 1 else 0

lemma Vl_cases (e : E) (a : Bool × Finset E) : Vl e a = 0 ∨ ∃ k, Vl e a = Pi.single k 1 := by
  by_cases h : a.1 = true ∧ e ∈ a.2
  · right; refine ⟨(), ?_⟩; funext p; simp [Vl, h]
  · left; funext p; simp [Vl, h]

lemma qv_load {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (i : Fin N) (e : E) :
    qv (pw u σ i) (Vl e) () = u i * sigmaE S τ σ i e := by
  have key : ∀ a : Bool × Finset E, (Vl e a = Pi.single () 1) ↔ (a.1 = true ∧ e ∈ a.2) := by
    intro a
    constructor
    · intro h
      have hk := congrFun h ()
      simp only [Vl, Pi.single_eq_same] at hk
      split_ifs at hk with hc
      exact hc
    · intro h; funext p; simp [Vl, h]
  unfold qv
  simp only [key]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, true_and, Bool.false_eq_true, false_and, if_false, Finset.sum_const_zero,
    add_zero]
  unfold sigmaE pw
  rw [Finset.mul_sum]
  simp only [if_true]
  rw [← Finset.sum_subset (Finset.subset_univ (S (τ i)))]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs <;> simp
  · intro s _ hs
    rw [hσ.2.1 i s hs]; simp

lemma load_bound {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (u : Fin N → ℝ)
    (hu : IsBernoulliGame u) (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (e : E) :
    MarkovChainCLT.tvDist (law u σ (fun ω => fun _ : Unit => loadRV e ω))
        (piPo (fun _ : Unit => expLoad S τ u σ e)) ≤ ∑ i, u i ^ 2 := by
  rw [law_eq_lawN u σ (fun ω => fun _ : Unit => loadRV e ω) (fun _ => Vl e) (fun ω => by
    funext p; simp [loadRV, useIndicator, Vl, Finset.sum_apply])]
  have h := lecam N (pw u σ) (fun _ => Vl e) (fun i a => pw_nonneg hu hσ i a)
    (fun i => pw_sum_one hσ i) (fun i a => Vl_cases e a)
  have hpo : (fun k : Unit => ∑ i, qv (pw u σ i) (Vl e) k) =
      fun _ => expLoad S τ u σ e := by
    funext p
    simp only [qv_load S τ u σ hσ, expLoad]
  rw [hpo] at h
  refine h.trans (Finset.sum_le_sum (fun i _ => ?_))
  have h1 := sum_qv_le (pw u σ i) (pw_nonneg hu hσ i) (Vl e) (Vl_cases e)
    (fun a ha => by funext p; simp [Vl, ha])
  rw [pw_sum_true hσ i] at h1
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => qv_nonneg _ (pw_nonneg hu hσ i) _ k)) h1 2

end Game

end LCPProp1Aux

namespace LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter LargeCongestion.Poisson
open scoped ENNReal NNReal Topology

section PMF

lemma lawN_real {K : Type*} [Fintype K] [DecidableEq K] {α : Type*} [Fintype α] {N : ℕ}
    (w : Fin N → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (V : Fin N → α → (K → ℕ)) (A : Set (K → ℕ)) :
    (lawN w V).real A = ∑ ω : Fin N → α,
      (∏ i, w i (ω i)) * A.indicator (fun _ => (1 : ℝ)) (∑ i, V i (ω i)) :=
  law_real _ (fun ω => Finset.prod_nonneg (fun i _ => hw i (ω i))) _ (ms' A)

lemma lawN_real_succ {K : Type*} [Fintype K] [DecidableEq K] {α : Type*} [Fintype α] {N : ℕ}
    (w : Fin (N + 1) → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (V : Fin (N + 1) → α → (K → ℕ))
    (A : Set (K → ℕ)) :
    (lawN w V).real A = ∑ a, w 0 a *
      (lawN (fun i => w i.succ) (fun i => V i.succ)).real {v | V 0 a + v ∈ A} := by
  rw [lawN_real w hw]
  simp_rw [lawN_real _ (fun i => hw i.succ), Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ (fun p => ?_)
  simp only [Fin.consEquiv, Equiv.coe_fn_mk]
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp only [Set.indicator]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1 h2
  · exact absurd h2 h1
  · ring

/-- The constant vector `m` on `Unit`. -/
def cst (m : ℕ) : Unit → ℕ := fun _ => m

lemma pow_ineq (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) :
    ∀ k : ℕ, s ^ (k + 1) + (k + 1) * q * s ^ k ≤ (s + q) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ s ^ k := pow_nonneg hs k
    have h2 : (s + q) ^ (k + 1 + 1) = (s + q) * (s + q) ^ (k + 1) := by ring
    rw [h2]
    have h3 : (s + q) * (s ^ (k + 1) + (k + 1) * q * s ^ k) ≤ (s + q) * (s + q) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h4 : s ^ (k + 1 + 1) + ((k + 1 : ℕ) + 1 : ℝ) * q * s ^ (k + 1) ≤
        (s + q) * (s ^ (k + 1) + (k + 1) * q * s ^ k) := by
      push_cast
      have : (s + q) * (s ^ (k + 1) + (k + 1) * q * s ^ k) - (s ^ (k + 1 + 1) +
          ((k : ℝ) + 1 + 1) * q * s ^ (k + 1)) = (k + 1) * q ^ 2 * s ^ k := by ring
      have h5 : 0 ≤ ((k : ℝ) + 1) * q ^ 2 * s ^ k := by positivity
      linarith
    exact h4.trans h3

theorem lawN_pmf {α : Type*} [Fintype α] : ∀ (N : ℕ) (w : Fin N → α → ℝ)
    (V : Fin N → α → (Unit → ℕ)), (∀ i a, 0 ≤ w i a) → (∀ i, ∑ a, w i a = 1) →
    (∀ i a, V i a = 0 ∨ ∃ k, V i a = Pi.single k 1) →
    ∀ m, (lawN w V).real {cst m} ≤ (∑ i, qv (w i) (V i) ()) ^ m / (m.factorial : ℝ) := by
  intro N
  induction N with
  | zero =>
    intro w V _ _ _ m
    have h1 : lawN w V = Measure.dirac 0 := by unfold lawN; simp
    rw [h1]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : (Measure.dirac (0 : Unit → ℕ)).real {cst 0} ≤ 1 := by
        rw [← probReal_univ (μ := Measure.dirac (0 : Unit → ℕ))]
        exact measureReal_mono (Set.subset_univ _)
      simpa using this
    · have : (0 : Unit → ℕ) ∉ ({cst m} : Set (Unit → ℕ)) := by
        intro h
        have := congrFun (Set.mem_singleton_iff.1 h) ()
        simp [cst] at this; omega
      rw [Measure.real, Measure.dirac_apply' _ (ms' _), Set.indicator_of_notMem this]
      simp [zero_pow hm.ne']
  | succ N ih =>
    intro w V hw hw1 hV m
    have := lawN_prob (fun i => w i.succ) (fun i => hw i.succ) (fun i => hw1 i.succ)
      (fun i => V i.succ)
    set L := lawN (fun i => w i.succ) (fun i => V i.succ) with hL
    set s := ∑ i : Fin N, qv (w i.succ) (V i.succ) () with hs
    set q := qv (w 0) (V 0) () with hq
    have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => qv_nonneg _ (hw i.succ) _ _)
    have hq0 : 0 ≤ q := qv_nonneg _ (hw 0) _ _
    have htot : ∑ i, qv (w i) (V i) () = q + s := by rw [Fin.sum_univ_succ]
    have hZ : (∑ a, if V 0 a = 0 then w 0 a else 0) = 1 - q := by
      have := single_decomp (w 0) (V 0) (hV 0) Set.univ
      simp only [Set.indicator_univ, mul_one, one_mul, hw1 0] at this
      have hq' : q = ∑ k, qv (w 0) (V 0) k := by simp [hq]
      rw [hq']; linarith
    have hq1 : q ≤ 1 := by
      have : 0 ≤ ∑ a, (if V 0 a = 0 then w 0 a else 0) :=
        Finset.sum_nonneg (fun a _ => by split_ifs; exact hw 0 a; exact le_rfl)
      linarith
    rw [lawN_real_succ w hw V, htot]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      calc ∑ a, w 0 a * L.real {v | V 0 a + v ∈ ({cst 0} : Set (Unit → ℕ))}
          ≤ ∑ a, w 0 a * 1 := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
            (by rw [← probReal_univ (μ := L)]; exact measureReal_mono (Set.subset_univ _))
            (hw 0 a))
        _ = 1 := by simp [hw1 0]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hterm : ∀ a, w 0 a * L.real {v | V 0 a + v ∈ ({cst (k + 1)} : Set (Unit → ℕ))} =
          (if V 0 a = 0 then w 0 a else 0) * L.real {cst (k + 1)} +
          (if V 0 a = Pi.single () 1 then w 0 a else 0) * L.real {cst k} := by
        intro a
        rcases hV 0 a with h0 | ⟨j, hj⟩
        · have hne : (0 : Unit → ℕ) ≠ Pi.single () 1 := (single_ne_zero ()).symm
          rw [if_pos h0, if_neg (h0 ▸ hne), h0]
          simp
        · have hj' : V 0 a = Pi.single () 1 := by rw [hj]
          rw [if_neg (hj' ▸ single_ne_zero ()), if_pos hj', hj']
          have hset : {v : Unit → ℕ | Pi.single () 1 + v ∈ ({cst (k + 1)} : Set (Unit → ℕ))} =
              {cst k} := by
            ext v
            simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, cst, funext_iff, Pi.add_apply,
              Pi.single_eq_same]
            constructor
            · intro h u; have := h u; omega
            · intro h u; have := h u; omega
          rw [hset]; ring
      rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul, hZ]
      have hk1 := ih (fun i => w i.succ) (fun i => V i.succ) (fun i => hw i.succ)
        (fun i => hw1 i.succ) (fun i => hV i.succ) (k + 1)
      have hk0 := ih (fun i => w i.succ) (fun i => V i.succ) (fun i => hw i.succ)
        (fun i => hw1 i.succ) (fun i => hV i.succ) k
      rw [← hL, ← hs] at hk1 hk0
      have hqdef : (∑ a, if V 0 a = Pi.single () 1 then w 0 a else 0) = q := rfl
      rw [hqdef]
      have hfac : ((k + 1).factorial : ℝ) = (k + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
      have hpow := pow_ineq s q hs0 hq0 k
      calc (1 - q) * L.real {cst (k + 1)} + q * L.real {cst k}
          ≤ (1 - q) * (s ^ (k + 1) / ((k + 1).factorial : ℝ)) + q * (s ^ k / (k.factorial : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hk1 (by linarith))
              (mul_le_mul_of_nonneg_left hk0 hq0)
        _ ≤ (q + s) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
            rw [hfac, add_comm q s]
            have hsk1 : 0 ≤ q * s ^ (k + 1) := mul_nonneg hq0 (pow_nonneg hs0 _)
            have key : (1 - q) * (s ^ (k + 1) / ((k + 1) * (k.factorial : ℝ))) +
                q * (s ^ k / (k.factorial : ℝ)) =
                ((1 - q) * s ^ (k + 1) + (k + 1) * q * s ^ k) / ((k + 1) * (k.factorial : ℝ)) := by
              field_simp
            rw [key]
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith [hpow, hsk1]

end PMF

end LCPProp1Aux

namespace LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter LargeCongestion.Poisson
open scoped ENNReal NNReal Topology

/-! ### Analysis: comparing a finitely supported law with a Poisson law -/

lemma approx_analysis (h : ℕ → ℝ) (P : ℕ → ℝ) (R : ℕ) (s X τ : ℝ) (hs : 0 ≤ s) (hsX : s ≤ X)
    (hP0 : ∀ m, 0 ≤ P m) (hPb : ∀ m, P m ≤ s ^ m / (m.factorial : ℝ)) (hPR : ∀ m, R ≤ m → P m = 0)
    (hτ : ∀ m, |P m - poissonPmf s m| ≤ τ)
    (hg : Summable (fun m : ℕ => |h m| * (X ^ m / (m.factorial : ℝ)))) (M : ℕ) :
    |∑ m ∈ Finset.range R, h m * P m - poissonMean h s| ≤
      (∑ m ∈ Finset.range M, |h m|) * τ +
        2 * ∑' j : ℕ, |h (j + M)| * (X ^ (j + M) / ((j + M).factorial : ℝ)) := by
  have hpo : ∀ m, poissonPmf s m ≤ X ^ m / (m.factorial : ℝ) := by
    intro m
    rw [poissonPmf_eq hs]
    have hk : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
    apply div_le_div_of_nonneg_right _ hk.le
    calc Real.exp (-s) * s ^ m ≤ 1 * s ^ m :=
          mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.2 (by linarith)) (pow_nonneg hs m)
      _ ≤ X ^ m := by rw [one_mul]; exact pow_le_pow_left₀ hs hsX m
  have hpo0 : ∀ m, 0 ≤ poissonPmf s m := fun m => measureReal_nonneg
  have hPX : ∀ m, P m ≤ X ^ m / (m.factorial : ℝ) := by
    intro m
    refine (hPb m).trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ hs hsX m) ?_)
    exact_mod_cast (Nat.factorial_pos m).le
  set a : ℕ → ℝ := fun m => h m * P m
  set b : ℕ → ℝ := fun m => h m * poissonPmf s m
  have ha : Summable a := summable_of_ne_finset_zero (s := Finset.range R) (fun m hm => by
    simp only [Finset.mem_range, not_lt] at hm
    simp [a, hPR m hm])
  have hb : Summable b := Summable.of_norm_bounded hg (fun m => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpo0 m)]
    exact mul_le_mul_of_nonneg_left (hpo m) (abs_nonneg _))
  have hsumA : ∑ m ∈ Finset.range R, h m * P m = ∑' m, a m :=
    (tsum_eq_sum (fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm
      simp [a, hPR m hm])).symm
  have hD : Summable (fun m => a m - b m) := ha.sub hb
  rw [hsumA, show poissonMean h s = ∑' m, b m from rfl, ← ha.tsum_sub hb,
    ← hD.sum_add_tsum_nat_add M]
  have hDb : ∀ m, |a m - b m| ≤ 2 * (|h m| * (X ^ m / (m.factorial : ℝ))) := by
    intro m
    simp only [a, b]
    rw [← mul_sub, abs_mul]
    have : |P m - poissonPmf s m| ≤ 2 * (X ^ m / (m.factorial : ℝ)) := by
      rw [abs_le]; constructor <;> linarith [hP0 m, hpo0 m, hPX m, hpo m]
    calc |h m| * |P m - poissonPmf s m| ≤ |h m| * (2 * (X ^ m / (m.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have hgM : Summable (fun j : ℕ => |h (j + M)| * (X ^ (j + M) / ((j + M).factorial : ℝ))) :=
    (summable_nat_add_iff M).2 hg
  have hhead : |∑ m ∈ Finset.range M, (a m - b m)| ≤ (∑ m ∈ Finset.range M, |h m|) * τ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun m _ => ?_)
    simp only [a, b]
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hτ m) (abs_nonneg _)
  have htail : |∑' j, (a (j + M) - b (j + M))| ≤
      2 * ∑' j : ℕ, |h (j + M)| * (X ^ (j + M) / ((j + M).factorial : ℝ)) := by
    have hsn : Summable (fun j => ‖a (j + M) - b (j + M)‖) :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hDb (j + M)) (hgM.mul_left 2)
    calc |∑' j, (a (j + M) - b (j + M))| ≤ ∑' j, ‖a (j + M) - b (j + M)‖ :=
          norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' j, 2 * (|h (j + M)| * (X ^ (j + M) / ((j + M).factorial : ℝ))) :=
          hsn.tsum_le_tsum (fun j => hDb (j + M)) (hgM.mul_left 2)
      _ = _ := tsum_mul_left
  exact (abs_add_le _ _).trans (add_le_add hhead htail)

/-! ### The other players' load as a Poisson-binomial variable -/

section Others
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

/-- Player `j`'s contribution to `Z_{i,e}`. -/
def Vo {N : ℕ} (i : Fin N) (e : E) (j : Fin N) (a : Bool × Finset E) : Unit → ℕ :=
  if j = i then 0 else Vl e a

lemma Vo_cases {N : ℕ} (i : Fin N) (e : E) (j : Fin N) (a : Bool × Finset E) :
    Vo i e j a = 0 ∨ ∃ k, Vo i e j a = Pi.single k 1 := by
  unfold Vo
  split_ifs
  · left; rfl
  · exact Vl_cases e a

lemma Vo_false {N : ℕ} (i : Fin N) (e : E) (j : Fin N) (a : Bool × Finset E)
    (ha : a.1 = false) : Vo i e j a = 0 := by
  unfold Vo; split_ifs
  · rfl
  · funext p; simp [Vl, ha]

lemma qv_others {N : ℕ} (S : T → Finset (Finset E)) (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (i : Fin N) (e : E) (j : Fin N) :
    qv (pw u σ j) (Vo i e j) () = if j = i then 0 else u j * sigmaE S τ σ j e := by
  by_cases h : j = i
  · rw [if_pos h]
    unfold qv Vo
    simp only [h, if_true]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [if_neg (single_ne_zero ()).symm]
  · rw [if_neg h, ← qv_load S τ u σ hσ j e]
    unfold Vo; simp only [h, if_false]

lemma others_eq {N : ℕ} (i : Fin N) (e : E) (ω : Outcome E N) :
    othersLoadRV i e ω = (∑ j, Vo i e j (ω j)) () := by
  rw [Finset.sum_apply, othersLoadRV]
  rw [← Finset.sum_erase Finset.univ (a := i) (by simp [Vo])]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp [Vo, Finset.ne_of_mem_erase hj, Vl, useIndicator]

lemma others_le {N : ℕ} (i : Fin N) (e : E) (ω : Outcome E N) :
    (∑ j, Vo i e j (ω j)) () ≤ N := by
  rw [Finset.sum_apply]
  calc ∑ j, Vo i e j (ω j) () ≤ ∑ _j : Fin N, 1 := Finset.sum_le_sum (fun j _ => by
        unfold Vo Vl; split_ifs <;> simp)
    _ = N := by simp

lemma cst_mem {v : Unit → ℕ} {m : ℕ} : v ∈ ({cst m} : Set (Unit → ℕ)) ↔ v () = m := by
  simp only [Set.mem_singleton_iff, cst, funext_iff]
  exact ⟨fun h => h (), fun h u => h⟩

lemma expect_others {N : ℕ} (u : Fin N → ℝ) (σ : Fin N → Finset E → ℝ)
    {S : T → Finset (Finset E)} {τ : Fin N → T} (hu : IsBernoulliGame u)
    (hσ : IsMixedProfile S τ σ) (i : Fin N) (e : E) (g : ℕ → ℝ) :
    expect u σ (fun ω => g (othersLoadRV i e ω)) =
      ∑ m ∈ Finset.range (N + 1), g m * (lawN (pw u σ) (Vo i e)).real {cst m} := by
  simp_rw [lawN_real (pw u σ) (fun j a => pw_nonneg hu hσ j a), Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  beta_reduce
  rw [others_eq i e ω]
  rw [Finset.sum_eq_single ((∑ j, Vo i e j (ω j)) ())]
  · rw [Set.indicator_of_mem (cst_mem.2 rfl)]
    unfold weight pw
    ring
  · intro m _ hm
    rw [Set.indicator_of_notMem (fun h => hm (cst_mem.1 h).symm)]
    ring
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (others_le i e ω))) h

end Others

end LCPProp1Aux

namespace LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter LargeCongestion.Poisson
open scoped ENNReal NNReal Topology

section Approx
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

lemma approx_game (S : T → Finset (Finset E)) (c : E → ℕ → ℝ) (hc : IsCostFamily c)
    (ν dmax : ℝ) (hd : 0 < dmax) (hM : MomentBound c ν dmax) {N : ℕ} (τ : Fin N → T)
    (u : Fin N → ℝ) (hu : IsBernoulliGame u) (σ : Fin N → Finset E → ℝ)
    (hσ : IsMixedProfile S τ σ) (htot : ∑ j, u j ≤ dmax) (i : Fin N) (e : E) (M : ℕ) :
    |expect u σ (fun ω => c e (1 + othersLoadRV i e ω)) - cBreve c e (expLoad S τ u σ e)| ≤
      (∑ m ∈ Finset.range M, |c e (1 + m)|) * ∑ j, u j ^ 2 +
        2 * ∑' j : ℕ, |c e (1 + (j + M))| * (dmax ^ (j + M) / ((j + M).factorial : ℝ)) +
        zeta c ν dmax * maxU u := by
  set h : ℕ → ℝ := fun k => c e (1 + k) with hh
  set μ := lawN (pw u σ) (Vo i e) with hμdef
  have hμ := lawN_prob (pw u σ) (fun j a => pw_nonneg hu hσ j a) (fun j => pw_sum_one hσ j)
    (Vo i e)
  set p : Fin N → ℝ := fun j => u j * sigmaE S τ σ j e with hp
  have hsig : ∀ j, 0 ≤ sigmaE S τ σ j e ∧ sigmaE S τ σ j e ≤ 1 := by
    intro j
    unfold sigmaE
    constructor
    · exact Finset.sum_nonneg (fun s _ => by split_ifs; exact hσ.1 j s; exact le_rfl)
    · rw [← hσ.2.2 j]
      exact Finset.sum_le_sum (fun s _ => by split_ifs; exact le_rfl; exact hσ.1 j s)
  have hp0 : ∀ j, 0 ≤ p j := fun j => mul_nonneg (hu j).1.le (hsig j).1
  have hpu : ∀ j, p j ≤ u j := fun j => mul_le_of_le_one_right (hu j).1.le (hsig j).2
  have hbdd : BddAbove (Set.range u) := (Set.finite_range u).bddAbove
  set z : ℝ := ∑ j, qv (pw u σ j) (Vo i e j) () with hzdef
  have hz : z = ∑ j, (if j = i then 0 else p j) := by
    rw [hzdef]; exact Finset.sum_congr rfl (fun j _ => qv_others S τ u σ hσ i e j)
  have hx : expLoad S τ u σ e = p i + z := by
    rw [hz, expLoad, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.sum_erase Finset.univ (a := i) (f := fun j => if j = i then 0 else p j) (by simp)]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  have hz0 : 0 ≤ z := by
    rw [hz]; exact Finset.sum_nonneg (fun j _ => by split_ifs; exact le_rfl; exact hp0 j)
  have hxd : expLoad S τ u σ e ≤ dmax :=
    le_trans (Finset.sum_le_sum (fun j _ => hpu j)) htot
  have hzd : z ≤ dmax := by linarith [hp0 i]
  -- the law of `Z_{i,e}` versus `Poisson(z)`
  have hlec := lecam N (pw u σ) (Vo i e) (fun j a => pw_nonneg hu hσ j a)
    (fun j => pw_sum_one hσ j) (fun j a => Vo_cases i e j a)
  have hτ : ∑ j, (∑ k, qv (pw u σ j) (Vo i e j) k) ^ 2 ≤ ∑ j, u j ^ 2 := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h1 := sum_qv_le (pw u σ j) (pw_nonneg hu hσ j) (Vo i e j) (Vo_cases i e j)
      (Vo_false i e j)
    rw [pw_sum_true hσ j] at h1
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => qv_nonneg _ (pw_nonneg hu hσ j) _ k))
      h1 2
  have hpiPo : (fun k : Unit => ∑ j, qv (pw u σ j) (Vo i e j) k) = fun _ => z := by
    funext k; rfl
  rw [hpiPo] at hlec
  have hPo : ∀ m, (piPo (fun _ : Unit => z)).real {cst m} = poissonPmf z m := by
    intro m
    rw [piPo_singleton_real _ (fun _ => hz0), poissonPmf_eq hz0]
    simp [cst]
  have hsing : ∀ m, |μ.real {cst m} - poissonPmf z m| ≤ ∑ j, u j ^ 2 := by
    intro m
    rw [← hPo m]
    exact (le_tv μ _ (ms' _)).trans (hlec.trans hτ)
  have hpmf := lawN_pmf N (pw u σ) (Vo i e) (fun j a => pw_nonneg hu hσ j a)
    (fun j => pw_sum_one hσ j) (fun j a => Vo_cases i e j a)
  have hsupp : ∀ m, N + 1 ≤ m → μ.real {cst m} = 0 := by
    intro m hm
    rw [hμdef, lawN_real (pw u σ) (fun j a => pw_nonneg hu hσ j a)]
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    rw [Set.indicator_of_notMem, mul_zero]
    intro hmem
    have := cst_mem.1 hmem
    have := others_le i e ω
    omega
  -- summability of `|h(m)| d_max^m / m!`
  have hsm := lemma_1_smooth c hc ν dmax hd hM e
  have hg : Summable (fun m : ℕ => |h m| * (dmax ^ m / (m.factorial : ℝ))) := by
    have := ((hsm.1 dmax ⟨hd.le, le_rfl⟩).abs).mul_left (Real.exp dmax)
    refine this.congr (fun m => ?_)
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ poissonPmf dmax m from measureReal_nonneg),
      poissonPmf_eq hd.le, Real.exp_neg]
    simp only [hh]
    have := Real.exp_pos dmax
    field_simp
  have hA := approx_analysis h (fun m => μ.real {cst m}) (N + 1) z dmax (∑ j, u j ^ 2) hz0 hzd
    (fun m => measureReal_nonneg) hpmf hsupp hsing hg M
  rw [← expect_others u σ hu hσ i e h] at hA
  -- Lipschitz continuity of `c̆_e` (Lemma 1)
  have hζ0 : 0 ≤ zeta c ν dmax :=
    le_trans (hsm.2.2 0 ⟨le_rfl, hd.le⟩).1 (hsm.2.2 0 ⟨le_rfl, hd.le⟩).2
  have hdiff : DifferentiableOn ℝ (cBreve c e) (Set.Icc 0 dmax) :=
    hsm.2.1.differentiableOn (by norm_num)
  have hbound : ∀ y ∈ Set.Icc 0 dmax,
      ‖derivWithin (cBreve c e) (Set.Icc 0 dmax) y‖ ≤ zeta c ν dmax := by
    intro y hy
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hsm.2.2 y hy).1, (hsm.2.2 y hy).2]
  have hlip := (convex_Icc 0 dmax).norm_image_sub_le_of_norm_derivWithin_le hdiff hbound
    (⟨hz0, hzd⟩ : z ∈ Set.Icc 0 dmax)
    (⟨le_trans hz0 (by linarith [hp0 i]), hxd⟩ : expLoad S τ u σ e ∈ Set.Icc 0 dmax)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hx, show p i + z - z = p i by ring,
    abs_of_nonneg (hp0 i)] at hlip
  have hpiU : p i ≤ maxU u := (hpu i).trans (le_ciSup hbdd i)
  have hcB : cBreve c e = poissonMean h := rfl
  rw [hcB] at hlip ⊢
  rw [← hx] at hlip
  have h2 : zeta c ν dmax * p i ≤ zeta c ν dmax * maxU u := mul_le_mul_of_nonneg_left hpiU hζ0
  calc |expect u σ (fun ω => h (othersLoadRV i e ω)) - poissonMean h (expLoad S τ u σ e)|
      = |(expect u σ (fun ω => h (othersLoadRV i e ω)) - poissonMean h z) +
          (poissonMean h z - poissonMean h (expLoad S τ u σ e))| := by ring_nf
    _ ≤ |expect u σ (fun ω => h (othersLoadRV i e ω)) - poissonMean h z| +
          |poissonMean h z - poissonMean h (expLoad S τ u σ e)| := abs_add_le _ _
    _ ≤ _ := by
        rw [abs_sub_comm (poissonMean h z)]
        simp only [hh] at hA hlip ⊢
        linarith

end Approx

end LCPProp1Aux

open MeasureTheory ProbabilityTheory Filter LargeCongestion.Poisson
open scoped Topology

namespace LCPThm2Aux

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

lemma sum_all_sigma (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) (g : Finset E → ℝ) :
    ∑ s : Finset E, σ j s * g s = ∑ s ∈ S (τ j), σ j s * g s := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  rw [hσ.2.1 j s hs, zero_mul]

lemma sum_weight_one (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) :
    ∑ p : Bool × Finset E, (if p.1 then u j else 1 - u j) * σ j p.2 = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h := sum_all_sigma S τ σ hσ j (fun _ => 1)
  simp only [mul_one] at h
  rw [h, hσ.2.2 j]
  ring

lemma expect_single (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (i : Fin N)
    (g : Bool × Finset E → ℝ) :
    expect u σ (fun ω => g (ω i)) =
      ∑ p : Bool × Finset E, ((if p.1 then u i else 1 - u i) * σ i p.2) * g p := by
  set w : Fin N → Bool × Finset E → ℝ := fun j p => (if p.1 then u j else 1 - u j) * σ j p.2
    with hw
  have key : ∀ ω : Outcome E N,
      weight u σ ω * g (ω i) = ∏ j, (w j (ω j) * if j = i then g (ω j) else 1) := by
    intro ω
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rfl
  unfold expect
  simp_rw [key]
  rw [← Fintype.prod_sum (fun j p => w j p * if j = i then g p else 1)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [Finset.prod_eq_one]
  · simp [w]
  · intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp only [hji, if_false, mul_one]
    exact sum_weight_one S τ u σ hσ j

lemma expect_load (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (e : E) :
    expect u σ (fun ω => (loadRV e ω : ℝ)) = expLoad S τ u σ e := by
  have hlin : expect u σ (fun ω => (loadRV e ω : ℝ)) =
      ∑ i, expect u σ (fun ω => ((useIndicator i e ω : ℕ) : ℝ)) := by
    unfold expect loadRV
    simp_rw [Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hlin]
  unfold expLoad
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := expect_single S τ u σ hσ i
    (fun p => ((if p.1 = true ∧ e ∈ p.2 then 1 else 0 : ℕ) : ℝ))
  have h2 : (fun ω : Outcome E N => ((useIndicator i e ω : ℕ) : ℝ)) =
      fun ω => ((if (ω i).1 = true ∧ e ∈ (ω i).2 then 1 else 0 : ℕ) : ℝ) := rfl
  rw [h2, this, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, true_and, Bool.false_eq_true, false_and, if_false, Nat.cast_zero,
    mul_zero, Finset.sum_const_zero, add_zero]
  unfold sigmaE
  rw [Finset.mul_sum]
  have h3 := sum_all_sigma S τ σ hσ i (fun s => if e ∈ s then u i else 0)
  calc ∑ s : Finset E, u i * σ i s * ((if e ∈ s then 1 else 0 : ℕ) : ℝ)
      = ∑ s : Finset E, σ i s * (if e ∈ s then u i else 0) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        split_ifs <;> simp; ring
    _ = ∑ s ∈ S (τ i), σ i s * (if e ∈ s then u i else 0) := h3
    _ = ∑ s ∈ S (τ i), u i * (if e ∈ s then σ i s else 0) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        split_ifs <;> ring

lemma sigmaE_mem (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (i : Fin N) (e : E) :
    0 ≤ sigmaE S τ σ i e ∧ sigmaE S τ σ i e ≤ 1 := by
  unfold sigmaE
  constructor
  · exact Finset.sum_nonneg (fun s _ => by split_ifs; exact hσ.1 i s; exact le_rfl)
  · rw [← hσ.2.2 i]
    exact Finset.sum_le_sum (fun s _ => by split_ifs; exact le_rfl; exact hσ.1 i s)

lemma expLoad_mem (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (hu : IsBernoulliGame u) (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (e : E)
    (dmax : ℝ) (htot : ∑ i, u i ≤ dmax) :
    expLoad S τ u σ e ∈ Set.Icc 0 dmax := by
  unfold expLoad
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hu i).1.le (sigmaE_mem S τ σ hσ i e).1)
  · refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) htot
    have := sigmaE_mem S τ σ hσ i e
    nlinarith [(hu i).1]

end LCPThm2Aux

open LCPThm2Aux LCPProp1Aux in
theorem solution {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (hS : StrategiesNonempty S) (c : E → ℕ → ℝ)
    (hc : IsCostFamily c) (d : T → ℝ) (ν dmax : ℝ) (h18 : Condition18 c d ν dmax)
    (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (u : ∀ n, Fin (N n) → ℝ)
    (hu : ∀ n, IsBernoulliGame (u n)) (h14 : Condition14 N τ u d)
    (σ : ∀ n, Fin (N n) → Finset E → ℝ) (hσ : ∀ n, IsBNE S c (τ n) (u n) (σ n)) :
    (∃ B : ℝ, ∀ n t s e,
        |expFlow (τ n) (u n) (σ n) t s| ≤ B ∧ |expLoad S (τ n) (u n) (σ n) e| ≤ B) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (y : T → Finset E → ℝ) (x : E → ℝ),
        (∀ t s, Tendsto (fun k => expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) t s) atTop
          (𝓝 (y t s))) →
        (∀ e, Tendsto (fun k => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e) atTop
          (𝓝 (x e))) →
        IsWardrop S (cBreve c) d y x ∧
          (∀ t, ∀ s ∈ S t, Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (flowRV (τ (φ k)) t s))
              (poissonMeasure (y t s).toNNReal)) atTop (𝓝 0)) ∧
          (∀ e, Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (loadRV e))
              (poissonMeasure (x e).toNNReal)) atTop (𝓝 0)) ∧
          Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (flowVec S (τ (φ k))))
              (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal))
            atTop (𝓝 0) := by
  have hmix : ∀ n, IsMixedProfile S (τ n) (σ n) := fun n => (hσ n).1
  obtain ⟨hB, hrest⟩ := proposition_1 S hS d N τ u hu h14 σ hmix
  refine ⟨hB, ?_⟩
  intro φ hφ y x hy hx
  obtain ⟨hfeas, hY, hX, hV⟩ := hrest φ hφ y x hy hx
  refine ⟨⟨hfeas, ?_⟩, hY, hX, hV⟩
  intro t s hs s' hs' hpos
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨_, h14b, h14c⟩ := h14
  have hd_nonneg : ∀ t, 0 ≤ d t := fun t =>
    ge_of_tendsto' (h14c t) (fun n => Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact (hu n i).1.le
      · exact le_rfl))
  have hdmax : 0 < dmax := lt_of_le_of_lt (Finset.sum_nonneg fun t _ => hd_nonneg t) h18.1
  have htot_eq : ∀ n, ∑ i, u n i = ∑ t, demand (τ n) (u n) t := by
    intro n
    unfold demand
    rw [Finset.sum_comm]
    simp
  have htot_ev : ∀ᶠ n in atTop, ∑ i, u n i ≤ dmax := by
    have hlim : Tendsto (fun n => ∑ t, demand (τ n) (u n) t) atTop (𝓝 (∑ t, d t)) :=
      tendsto_finsetSum _ (fun t _ => h14c t)
    filter_upwards [hlim.eventually (gt_mem_nhds h18.1)] with n hn
    rw [htot_eq]
    exact hn.le
  have hu1_ev : ∀ᶠ n in atTop, maxU (u n) < 1 := h14b.eventually (gt_mem_nhds one_pos)
  have hev1 : ∀ᶠ k in atTop, (∑ i, u (φ k) i ≤ dmax) ∧ maxU (u (φ k)) < 1 :=
    hφt.eventually (htot_ev.and hu1_ev)
  have hev : ∀ᶠ k in atTop, ((∑ i, u (φ k) i ≤ dmax) ∧ maxU (u (φ k)) < 1) ∧
      0 < expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) t s :=
    hev1.and ((hy t s).eventually (lt_mem_nhds hpos))
  -- continuity of the auxiliary costs
  have hcont : ∀ e, ContinuousOn (cBreve c e) (Set.Icc 0 dmax) := fun e =>
    (lemma_1_smooth c hc ν dmax hdmax h18.2 e).2.1.continuousOn
  have hmem_ev : ∀ e, ∀ᶠ k in atTop,
      expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e ∈ Set.Icc 0 dmax := fun e => by
    filter_upwards [hev1] with k hk
    exact expLoad_mem S (τ (φ k)) (u (φ k)) (hu _) (σ (φ k)) (hmix _) e dmax hk.1
  have hx_mem : ∀ e, x e ∈ Set.Icc 0 dmax := fun e =>
    isClosed_Icc.mem_of_tendsto (hx e) (hmem_ev e)
  have hcx : ∀ e, Tendsto (fun k => cBreve c e (expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e))
      atTop (𝓝 (cBreve c e (x e))) := fun e =>
    ((hcont e) (x e) (hx_mem e)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hx e, hmem_ev e⟩)
  -- tails of the cost series
  have hsm : ∀ e, (∀ x ∈ Set.Icc 0 dmax, Summable (fun k : ℕ => c e (1 + k) * poissonPmf x k)) :=
    fun e => (lemma_1_smooth c hc ν dmax hdmax h18.2 e).1
  set g : E → ℕ → ℝ := fun e m => |c e (1 + m)| * (dmax ^ m / (m.factorial : ℝ)) with hgdef
  set Tl : E → ℕ → ℝ := fun e M =>
    ∑' j : ℕ, |c e (1 + (j + M))| * (dmax ^ (j + M) / ((j + M).factorial : ℝ)) with hTldef
  have hTl : ∀ e, Tendsto (Tl e) atTop (𝓝 0) := fun e => tendsto_sum_nat_add (g e)
  have hU2 : Tendsto (fun k => ∑ i, u (φ k) i ^ 2) atTop (𝓝 0) := by
    have htot_lim : Tendsto (fun n => ∑ i, u n i) atTop (𝓝 (∑ t, d t)) := by
      simp_rw [htot_eq]; exact tendsto_finsetSum _ (fun t _ => h14c t)
    have hle : ∀ n, ∑ i, u n i ^ 2 ≤ maxU (u n) * ∑ i, u n i := fun n => by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [sq]
      exact mul_le_mul_of_nonneg_right (le_ciSup (Set.finite_range _).bddAbove i) (hu n i).1.le
    have hlim : Tendsto (fun n => maxU (u n) * ∑ i, u n i) atTop (𝓝 0) := by
      simpa using h14b.mul htot_lim
    exact squeeze_zero (fun k => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (fun k => hle (φ k)) (hlim.comp hφt)
  have hZm : Tendsto (fun k => zeta c ν dmax * maxU (u (φ k))) atTop (𝓝 0) := by
    simpa using (h14b.comp hφt).const_mul (zeta c ν dmax)
  set xL : ℕ → E → ℝ := fun k e => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e with hxL
  set C : ℝ := (s.card : ℝ) + s'.card with hC
  have hC0 : 0 ≤ C := by positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  set δ : ℝ := ε / (C + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  obtain ⟨M, hMδ⟩ : ∃ M, ∀ e, 2 * Tl e M ≤ δ / 3 := by
    have : ∀ᶠ M in atTop, ∀ e, 2 * Tl e M < δ / 3 := by
      rw [Filter.eventually_all]
      intro e
      have := ((hTl e).const_mul 2).eventually (gt_mem_nhds (show 2 * (0 : ℝ) < δ / 3 by
        linarith))
      exact this
    obtain ⟨M, hM⟩ := this.exists
    exact ⟨M, fun e => (hM e).le⟩
  have hev2 : ∀ᶠ k in atTop, (∀ e, (∑ m ∈ Finset.range M, |c e (1 + m)|) *
      ∑ i, u (φ k) i ^ 2 < δ / 3) ∧ zeta c ν dmax * maxU (u (φ k)) < δ / 3 := by
    refine Filter.Eventually.and ?_ (hZm.eventually (gt_mem_nhds (by linarith)))
    rw [Filter.eventually_all]
    intro e
    have := (hU2.const_mul (∑ m ∈ Finset.range M, |c e (1 + m)|)).eventually
      (gt_mem_nhds (show (∑ m ∈ Finset.range M, |c e (1 + m)|) * 0 < δ / 3 by
        rw [mul_zero]; linarith))
    exact this
  have hineq : ∀ᶠ k in atTop, ∑ e ∈ s, cBreve c e (xL k e) ≤
      ∑ e ∈ s', cBreve c e (xL k e) + C * δ := by
    filter_upwards [hev, hev2] with k ⟨⟨hk1, _⟩, hk3⟩ ⟨hk4, hk5⟩
    have hk3' : ∑ i : Fin (N (φ k)), (0 : ℝ) <
        ∑ i, (if τ (φ k) i = t then u (φ k) i * σ (φ k) i s else 0) := by
      simpa [expFlow] using hk3
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hk3'
    by_cases hτ : τ (φ k) i = t
    · rw [if_pos hτ] at hi
      have hσpos : 0 < σ (φ k) i s := pos_of_mul_pos_right hi (hu _ i).1.le
      have hsi : s ∈ S (τ (φ k) i) := hτ ▸ hs
      have hsi' : s' ∈ S (τ (φ k) i) := hτ ▸ hs'
      have hbne := (hσ (φ k)).2 i s hsi s' hsi' hσpos
      set A : E → ℝ := fun e => expect (u (φ k)) (σ (φ k))
        (fun ω => c e (1 + othersLoadRV i e ω)) with hA
      have happ : ∀ e, |A e - cBreve c e (xL k e)| ≤ δ := by
        intro e
        have h1 := approx_game S c hc ν dmax hdmax h18.2 (τ (φ k)) (u (φ k)) (hu _) (σ (φ k))
          (hmix _) hk1 i e M
        have h2 := hk4 e
        have h3 := hMδ e
        simp only [hTldef] at h3
        simp only [hA, hxL]
        linarith
      have hup : ∀ e, cBreve c e (xL k e) ≤ A e + δ := fun e =>
        by have := (abs_le.1 (happ e)); linarith [this.1]
      have hlo : ∀ e, A e ≤ cBreve c e (xL k e) + δ := fun e =>
        by have := (abs_le.1 (happ e)); linarith [this.2]
      calc ∑ e ∈ s, cBreve c e (xL k e) ≤ ∑ e ∈ s, (A e + δ) :=
            Finset.sum_le_sum (fun e _ => hup e)
        _ = ∑ e ∈ s, A e + s.card * δ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ e ∈ s', A e + s.card * δ := by linarith [hbne]
        _ ≤ ∑ e ∈ s', (cBreve c e (xL k e) + δ) + s.card * δ := by
            linarith [Finset.sum_le_sum (fun e (_ : e ∈ s') => hlo e)]
        _ = ∑ e ∈ s', cBreve c e (xL k e) + C * δ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hC]
            ring
    · rw [if_neg hτ] at hi
      exact absurd hi (lt_irrefl _)
  have hlimL : Tendsto (fun k => ∑ e ∈ s, cBreve c e (xL k e)) atTop
      (𝓝 (∑ e ∈ s, cBreve c e (x e))) := tendsto_finsetSum _ (fun e _ => hcx e)
  have hlimR : Tendsto (fun k => ∑ e ∈ s', cBreve c e (xL k e) + C * δ) atTop
      (𝓝 (∑ e ∈ s', cBreve c e (x e) + C * δ)) :=
    (tendsto_finsetSum _ (fun e _ => hcx e)).add_const _
  have hfin := le_of_tendsto_of_tendsto hlimL hlimR hineq
  have hCδ : C * δ ≤ ε := by
    rw [hδ, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith
