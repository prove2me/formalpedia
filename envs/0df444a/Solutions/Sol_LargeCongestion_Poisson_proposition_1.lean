-- Prove2me | solution 1 for LargeCongestion.Poisson.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:00:23.841345+00:00
-- url     : https://prove2.me/submissions/9d9c253a-fe77-422f-9be3-30a6b1d6764a

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game

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

open MeasureTheory ProbabilityTheory Filter LargeCongestion.Poisson LCPProp1Aux
open scoped Topology

theorem solution {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (hS : StrategiesNonempty S) (d : T → ℝ)
    (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (u : ∀ n, Fin (N n) → ℝ)
    (hu : ∀ n, IsBernoulliGame (u n)) (h14 : Condition14 N τ u d)
    (σ : ∀ n, Fin (N n) → Finset E → ℝ) (hσ : ∀ n, IsMixedProfile S (τ n) (σ n)) :
    (∃ B : ℝ, ∀ n t s e,
        |expFlow (τ n) (u n) (σ n) t s| ≤ B ∧ |expLoad S (τ n) (u n) (σ n) e| ≤ B) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (y : T → Finset E → ℝ) (x : E → ℝ),
        (∀ t s, Tendsto (fun k => expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) t s) atTop
          (𝓝 (y t s))) →
        (∀ e, Tendsto (fun k => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e) atTop
          (𝓝 (x e))) →
        IsFeasible S d y x ∧
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
  obtain ⟨_, h14b, h14c⟩ := h14
  -- total participation `∑_i u_i = ∑_t d^n_t`
  have htot_eq : ∀ n, ∑ i, u n i = ∑ t, demand (τ n) (u n) t := by
    intro n; unfold demand; rw [Finset.sum_comm]; simp
  have htot_lim : Tendsto (fun n => ∑ i, u n i) atTop (𝓝 (∑ t, d t)) := by
    simp_rw [htot_eq]; exact tendsto_finsetSum _ (fun t _ => h14c t)
  obtain ⟨Bt, hBt⟩ := htot_lim.bddAbove_range
  have hσle : ∀ n i s, σ n i s ≤ 1 := by
    intro n i s
    by_cases hs : s ∈ S (τ n i)
    · rw [← (hσ n).2.2 i]
      exact Finset.single_le_sum (fun s _ => (hσ n).1 i s) hs
    · rw [(hσ n).2.1 i s hs]; norm_num
  have hflow0 : ∀ n t s, 0 ≤ expFlow (τ n) (u n) (σ n) t s := fun n t s =>
    Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact mul_nonneg (hu n i).1.le ((hσ n).1 i s)
      · exact le_rfl)
  have hflow_le : ∀ n t s, expFlow (τ n) (u n) (σ n) t s ≤ ∑ i, u n i := fun n t s =>
    Finset.sum_le_sum (fun i _ => by
      split_ifs
      · exact mul_le_of_le_one_right (hu n i).1.le (hσle n i s)
      · exact (hu n i).1.le)
  have hsig : ∀ n i e, 0 ≤ sigmaE S (τ n) (σ n) i e ∧ sigmaE S (τ n) (σ n) i e ≤ 1 := by
    intro n i e
    unfold sigmaE
    constructor
    · exact Finset.sum_nonneg (fun s _ => by split_ifs; exact (hσ n).1 i s; exact le_rfl)
    · rw [← (hσ n).2.2 i]
      exact Finset.sum_le_sum (fun s _ => by split_ifs; exact le_rfl; exact (hσ n).1 i s)
  have hload0 : ∀ n e, 0 ≤ expLoad S (τ n) (u n) (σ n) e := fun n e =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (hu n i).1.le (hsig n i e).1)
  have hload_le : ∀ n e, expLoad S (τ n) (u n) (σ n) e ≤ ∑ i, u n i := fun n e =>
    Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hu n i).1.le (hsig n i e).2)
  refine ⟨⟨Bt, fun n t s e => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [abs_of_nonneg (hflow0 n t s)]; exact (hflow_le n t s).trans (hBt ⟨n, rfl⟩)
  · rw [abs_of_nonneg (hload0 n e)]; exact (hload_le n e).trans (hBt ⟨n, rfl⟩)
  intro φ hφ y x hy hx
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- (a) feasibility of the limit
  have hy0 : ∀ t s, 0 ≤ y t s := fun t s => ge_of_tendsto' (hy t s) (fun k => hflow0 _ t s)
  have hx0 : ∀ e, 0 ≤ x e := fun e => ge_of_tendsto' (hx e) (fun k => hload0 _ e)
  have hdem : ∀ n t, demand (τ n) (u n) t = ∑ s ∈ S t, expFlow (τ n) (u n) (σ n) t s := by
    intro n t
    unfold demand expFlow
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : τ n i = t
    · simp only [h, if_true]
      rw [← Finset.mul_sum, ← h, (hσ n).2.2 i, mul_one]
    · simp [h]
  have hld : ∀ n e, expLoad S (τ n) (u n) (σ n) e =
      ∑ t, ∑ s ∈ S t, if e ∈ s then expFlow (τ n) (u n) (σ n) t s else 0 := by
    intro n e
    unfold expLoad sigmaE expFlow
    have h1 : ∀ t, ∀ s ∈ S t, (if e ∈ s then ∑ i, (if τ n i = t then u n i * σ n i s else 0)
        else 0) = ∑ i, if τ n i = t then (if e ∈ s then u n i * σ n i s else 0) else 0 := by
      intro t s _
      split_ifs with he
      · rfl
      · simp
    rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (h1 t))]
    simp_rw [Finset.sum_comm (s := S _) (t := Finset.univ)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    have h2 : ∀ t, (∑ s ∈ S t, if τ n i = t then (if e ∈ s then u n i * σ n i s else 0) else 0) =
        if τ n i = t then ∑ s ∈ S t, (if e ∈ s then u n i * σ n i s else 0) else 0 := by
      intro t; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs <;> simp
  have hfeas : IsFeasible S d y x := by
    refine ⟨fun t => ?_, fun t s _ => hy0 t s, fun e => ?_⟩
    · have h1 : Tendsto (fun k => demand (τ (φ k)) (u (φ k)) t) atTop (𝓝 (d t)) :=
        (h14c t).comp hφt
      have h2 : Tendsto (fun k => demand (τ (φ k)) (u (φ k)) t) atTop
          (𝓝 (∑ s ∈ S t, y t s)) := by
        simp_rw [hdem]; exact tendsto_finsetSum _ (fun s _ => hy t s)
      exact tendsto_nhds_unique h1 h2
    · have h2 : Tendsto (fun k => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e) atTop
          (𝓝 (∑ t, ∑ s ∈ S t, if e ∈ s then y t s else 0)) := by
        simp_rw [hld]
        refine tendsto_finsetSum _ (fun t _ => tendsto_finsetSum _ (fun s _ => ?_))
        by_cases he : e ∈ s
        · simp only [he, if_true]; exact hy t s
        · simp only [he, if_false]; exact tendsto_const_nhds
      exact tendsto_nhds_unique (hx e) h2
  -- the error term `∑_i u_i^2 → 0`
  have hU2 : Tendsto (fun k => ∑ i, u (φ k) i ^ 2) atTop (𝓝 0) := by
    have hle : ∀ n, ∑ i, u n i ^ 2 ≤ maxU (u n) * ∑ i, u n i := fun n => by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [sq]
      exact mul_le_mul_of_nonneg_right (le_ciSup (Set.finite_range _).bddAbove i) (hu n i).1.le
    have hlim : Tendsto (fun n => maxU (u n) * ∑ i, u n i) atTop (𝓝 0) := by
      simpa using h14b.mul htot_lim
    exact squeeze_zero (fun k => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (fun k => hle (φ k)) (hlim.comp hφt)
  -- (c) the joint law of the flows
  have hjoint : Tendsto (fun k => MarkovChainCLT.tvDist
      (law (u (φ k)) (σ (φ k)) (flowVec S (τ (φ k))))
      (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal)) atTop (𝓝 0) := by
    have hbound : ∀ k, MarkovChainCLT.tvDist (law (u (φ k)) (σ (φ k)) (flowVec S (τ (φ k))))
        (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal) ≤
        ∑ i, u (φ k) i ^ 2 + ∑ p : FlowIdx S,
          |expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) p.1.1 p.1.2 - y p.1.1 p.1.2| := by
      intro k
      have := law_prob (hu (φ k)) (hσ (φ k)) (flowVec S (τ (φ k)))
      have hpi : (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal) =
          piPo (fun p : FlowIdx S => y p.1.1 p.1.2) := rfl
      rw [hpi]
      refine (tv_triangle _ (piPo (fun p : FlowIdx S =>
        expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) p.1.1 p.1.2)) _).trans (add_le_add ?_ ?_)
      · exact flow_bound S (τ (φ k)) (u (φ k)) (hu (φ k)) (σ (φ k)) (hσ (φ k))
      · exact tv_piPo _ _ (fun p => hflow0 _ _ _) (fun p => hy0 _ _)
    have hsum : Tendsto (fun k => ∑ i, u (φ k) i ^ 2 + ∑ p : FlowIdx S,
        |expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) p.1.1 p.1.2 - y p.1.1 p.1.2|) atTop (𝓝 0) := by
      have h2 : Tendsto (fun k => ∑ p : FlowIdx S,
          |expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) p.1.1 p.1.2 - y p.1.1 p.1.2|) atTop (𝓝 0) := by
        have := tendsto_finsetSum (Finset.univ : Finset (FlowIdx S))
          (fun p _ => ((hy p.1.1 p.1.2).sub_const (y p.1.1 p.1.2)).abs)
        simpa using this
      simpa using hU2.add h2
    exact squeeze_zero (fun k => by
      have := law_prob (hu (φ k)) (hσ (φ k)) (flowVec S (τ (φ k)))
      exact tv_nonneg _ _) hbound hsum
  refine ⟨hfeas, ?_, ?_, hjoint⟩
  · -- (b) flows
    intro t s hs
    have hle : ∀ k, MarkovChainCLT.tvDist (law (u (φ k)) (σ (φ k)) (flowRV (τ (φ k)) t s))
        (poissonMeasure (y t s).toNNReal) ≤ MarkovChainCLT.tvDist
        (law (u (φ k)) (σ (φ k)) (flowVec S (τ (φ k))))
        (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal) := by
      intro k
      have := law_prob (hu (φ k)) (hσ (φ k)) (flowVec S (τ (φ k)))
      have h1 : flowRV (τ (φ k)) t s =
          (fun v : FlowIdx S → ℕ => v ⟨(t, s), hs⟩) ∘ flowVec S (τ (φ k)) := rfl
      have h2 : poissonMeasure (y t s).toNNReal =
          (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal).map
            (fun v : FlowIdx S → ℕ => v ⟨(t, s), hs⟩) :=
        (measurePreserving_eval (fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal)
          ⟨(t, s), hs⟩).map_eq.symm
      rw [h1, law_comp _ _ _ _ (measurable_pi_apply _), h2]
      exact tv_map (measurable_pi_apply _) _ _
    exact squeeze_zero (fun k => by
      have := law_prob (hu (φ k)) (hσ (φ k)) (flowRV (τ (φ k)) t s)
      exact tv_nonneg _ _) hle hjoint
  · -- (b) loads
    intro e
    have hle : ∀ k, MarkovChainCLT.tvDist (law (u (φ k)) (σ (φ k)) (loadRV e))
        (poissonMeasure (x e).toNNReal) ≤ ∑ i, u (φ k) i ^ 2 +
          |expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e - x e| := by
      intro k
      have := law_prob (hu (φ k)) (hσ (φ k)) (fun ω => fun _ : Unit => loadRV e ω)
      have h1 : (loadRV e : Outcome E (N (φ k)) → ℕ) =
          (fun v : Unit → ℕ => v ()) ∘ (fun ω => fun _ : Unit => loadRV e ω) := rfl
      have h2 : poissonMeasure (x e).toNNReal =
          (piPo (fun _ : Unit => x e)).map (fun v : Unit → ℕ => v ()) :=
        (measurePreserving_eval (fun _ : Unit => poissonMeasure (x e).toNNReal) ()).map_eq.symm
      rw [h1, law_comp _ _ _ _ (measurable_pi_apply _), h2]
      refine (tv_map (measurable_pi_apply _) _ _).trans ?_
      refine (tv_triangle _ (piPo (fun _ : Unit => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e))
        _).trans (add_le_add ?_ ?_)
      · exact load_bound S (τ (φ k)) (u (φ k)) (hu (φ k)) (σ (φ k)) (hσ (φ k)) e
      · refine (tv_piPo _ _ (fun _ => hload0 _ _) (fun _ => hx0 e)).trans ?_
        simp
    have hsum : Tendsto (fun k => ∑ i, u (φ k) i ^ 2 +
        |expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e - x e|) atTop (𝓝 0) := by
      have h2 := ((hx e).sub_const (x e)).abs
      simpa using hU2.add h2
    exact squeeze_zero (fun k => by
      have := law_prob (hu (φ k)) (hσ (φ k)) (loadRV e)
      exact tv_nonneg _ _) hle hsum
