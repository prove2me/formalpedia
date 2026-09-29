-- Prove2me | solution 1 for JewellMRP.Discounted.exists_optimal_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:36:35.396694+00:00
-- url     : https://prove2.me/submissions/84f91e0e-d198-4d9c-a913-06023c9e2729

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

open MeasureTheory

lemma aux_jdo_ftilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    (α : ℝ) : 0 ≤ ftilde M z i j α :=
  setIntegral_nonneg measurableSet_Ioi (fun _ _ => (Real.exp_pos _).le)

lemma aux_jdo_ftilde_lt_one {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    {α : ℝ} (hα : 0 < α) : ftilde M z i j α < 1 := by
  have := M.F_prob z i j
  have hIoi : M.F z i j (Set.Ioi 0) = 1 := by
    rw [← Set.compl_Iic, prob_compl_eq_one_iff measurableSet_Iic]
    exact M.F_Iic_zero z i j
  have hbdd : ∀ t ∈ Set.Ioi (0:ℝ), ‖Real.exp (-(α * t))‖ ≤ 1 := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 < α * t := mul_pos hα ht
    linarith
  have hint : IntegrableOn (fun t => Real.exp (-(α * t))) (Set.Ioi 0) (M.F z i j) := by
    refine Integrable.mono' (integrable_const (1:ℝ)) ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbdd)
  have hint1 : IntegrableOn (fun _ => (1:ℝ)) (Set.Ioi 0) (M.F z i j) :=
    integrable_const (1:ℝ)
  have hpos : 0 < ∫ t in Set.Ioi (0:ℝ), (1 - Real.exp (-(α * t))) ∂(M.F z i j) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have : Function.support (fun t : ℝ => 1 - Real.exp (-(α * t))) ∩ Set.Ioi 0
          = Set.Ioi 0 := by
        ext t
        simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
        constructor
        · exact fun h => h.2
        · intro ht
          refine ⟨?_, ht⟩
          have h1 : Real.exp (-(α * t)) < 1 := by
            rw [Real.exp_lt_one_iff]
            have : 0 < α * t := mul_pos hα ht
            linarith
          linarith
      rw [this, hIoi]
      exact one_pos
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have := hbdd t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
      simp only [Pi.zero_apply]
      linarith
    · exact hint1.sub hint
  have hsub := integral_sub hint1 hint
  rw [hsub, setIntegral_const] at hpos
  simp only [Measure.real, hIoi, ENNReal.toReal_one, one_smul] at hpos
  unfold ftilde
  linarith

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

lemma aux_jdo_gamma (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ z i j, ftilde M z i j α ≤ γ := by
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max (fun o : Option (A × S × S) =>
    o.elim (0:ℝ) (fun x => ftilde M x.1 x.2.1 x.2.2 α))
  refine ⟨_, hx₀ none, ?_, fun z i j => hx₀ (some (z, i, j))⟩
  rcases x₀ with _ | ⟨z, i, j⟩
  · exact one_pos
  · exact aux_jdo_ftilde_lt_one M z i j hα

lemma aux_jdo_q_nonneg (M : MRP S A) (α : ℝ) (z : A) (i j : S) : 0 ≤ qtilde M α z i j :=
  mul_nonneg (M.p_nonneg z i j) (aux_jdo_ftilde_nonneg M z i j α)

lemma aux_jdo_qsum (M : MRP S A) {α γ : ℝ} (hγ : ∀ z i j, ftilde M z i j α ≤ γ) (z : A)
    (i : S) : ∑ j, qtilde M α z i j ≤ γ := by
  calc ∑ j, qtilde M α z i j ≤ ∑ j, M.p z i j * γ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hγ z i j) (M.p_nonneg z i j)
    _ = γ := by rw [← Finset.sum_mul, M.p_sum, one_mul]

lemma aux_jdo_test_le (M : MRP S A) {α γ : ℝ} (hγ : ∀ z i j, ftilde M z i j α ≤ γ) (z : A)
    (i : S) (v w : S → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ j, v j ≤ w j + c) :
    test M α z i v ≤ test M α z i w + γ * c := by
  unfold test
  have h1 : ∑ j, qtilde M α z i j * v j ≤ ∑ j, qtilde M α z i j * w j + γ * c := by
    calc ∑ j, qtilde M α z i j * v j
        ≤ ∑ j, (qtilde M α z i j * w j + qtilde M α z i j * c) :=
          Finset.sum_le_sum fun j _ => by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (h j) (aux_jdo_q_nonneg M α z i j)
      _ = ∑ j, qtilde M α z i j * w j + (∑ j, qtilde M α z i j) * c := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ ∑ j, qtilde M α z i j * w j + γ * c := by
          gcongr
          exact aux_jdo_qsum M hγ z i
  linarith

lemma aux_jdo_test_abs (M : MRP S A) {α γ : ℝ} (hγ : ∀ z i j, ftilde M z i j α ≤ γ) (z : A)
    (i : S) (v w : S → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ j, |v j - w j| ≤ c) :
    |test M α z i v - test M α z i w| ≤ γ * c := by
  have h1 := aux_jdo_test_le M hγ z i v w c hc (fun j => by
    have := (abs_le.mp (h j)).2; linarith)
  have h2 := aux_jdo_test_le M hγ z i w v c hc (fun j => by
    have := (abs_le.mp (h j)).1; linarith)
  rw [abs_le]
  constructor <;> linarith

lemma aux_jdo_maxTest_le (M : MRP S A) {α γ : ℝ} (hγ : ∀ z i j, ftilde M z i j α ≤ γ)
    (i : S) (v w : S → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ j, v j ≤ w j + c) :
    maxTest M α v i ≤ maxTest M α w i + γ * c := by
  unfold maxTest
  apply Finset.sup'_le
  intro z _
  calc test M α z i v ≤ test M α z i w + γ * c := aux_jdo_test_le M hγ z i v w c hc h
    _ ≤ _ := by
      gcongr
      exact Finset.le_sup' (fun z => test M α z i w) (Finset.mem_univ z)

lemma aux_jdo_lip (M : MRP S A) {α γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : ∀ z i j, ftilde M z i j α ≤ γ) :
    ∀ (n : ℕ) (π : ℕ → S → A) (V W : S → ℝ) (c : ℝ), 0 ≤ c → (∀ j, |V j - W j| ≤ c) →
      ∀ i, |policyReturn M α π V n i - policyReturn M α π W n i| ≤ γ ^ n * c := by
  intro n
  induction n with
  | zero =>
    intro π V W c hc h i
    simpa [policyReturn] using h i
  | succ n ih =>
    intro π V W c hc h i
    have hih := ih (fun k => π (k + 1)) V W c hc h
    simp only [policyReturn]
    have := aux_jdo_test_abs M hγ (π 0 i) i _ _ (γ ^ n * c) (by positivity) hih
    have heq : γ * (γ ^ n * c) = γ ^ (n + 1) * c := by ring
    linarith

lemma aux_jdo_shift (M : MRP S A) (α : ℝ) : ∀ (n : ℕ) (π : ℕ → S → A) (V : S → ℝ),
    policyReturn M α π V (n + 1) = policyReturn M α π (fun j => test M α (π n j) j V) n := by
  intro n
  induction n with
  | zero =>
    intro π V
    funext i
    simp [policyReturn]
  | succ n ih =>
    intro π V
    funext i
    rw [policyReturn]
    rw [ih]
    rfl

lemma aux_jdo_conv (M : MRP S A) {α γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hγ : ∀ z i j, ftilde M z i j α ≤ γ) (π : ℕ → S → A) (V : S → ℝ) (i : S) :
    ∃ x, Tendsto (fun n => policyReturn M α π V n i) atTop (𝓝 x) := by
  set D : ℝ := ∑ p : A × S, |test M α p.1 p.2 V - V p.2| with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hD : ∀ z j, |test M α z j V - V j| ≤ D := fun z j =>
    Finset.single_le_sum (f := fun p : A × S => |test M α p.1 p.2 V - V p.2|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ (z, j))
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_le_geometric γ D hγ1
  intro n
  rw [Real.dist_eq, aux_jdo_shift, abs_sub_comm, mul_comm]
  exact aux_jdo_lip M hγ0 hγ n π _ V D hD0 (fun j => hD (π n j) j) i

lemma aux_jdo_upper (M : MRP S A) {α γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : ∀ z i j, ftilde M z i j α ≤ γ)
    (v : S → ℝ) (hv : ∀ i, maxTest M α v i ≤ v i) (V : S → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ j, V j ≤ v j + c) :
    ∀ (n : ℕ) (π : ℕ → S → A) (i : S), policyReturn M α π V n i ≤ v i + γ ^ n * c := by
  intro n
  induction n with
  | zero =>
    intro π i
    simpa [policyReturn] using h i
  | succ n ih =>
    intro π i
    simp only [policyReturn]
    have h1 := aux_jdo_test_le M hγ (π 0 i) i _ v (γ ^ n * c) (by positivity)
      (ih (fun k => π (k + 1)))
    have h2 : test M α (π 0 i) i v ≤ maxTest M α v i :=
      Finset.le_sup' (fun z => test M α z i v) (Finset.mem_univ _)
    have heq : γ * (γ ^ n * c) = γ ^ (n + 1) * c := by ring
    linarith [hv i]

end JewellMRP.Discounted

open JewellMRP.Discounted

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ (d : S → A) (v : S → ℝ), SolvesEval M α d v ∧
      ∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S), ∃ x : ℝ,
        Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 x) ∧ x ≤ v i := by
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := aux_jdo_gamma M hα
  let T : (S → ℝ) → (S → ℝ) := fun v => maxTest M α v
  have hK : ContractingWith (⟨γ, hγ0⟩ : NNReal) T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    · exact NNReal.coe_lt_coe.mp hγ1
    · rw [dist_pi_le_iff (by positivity)]
      intro i
      have hvw : ∀ j, |v j - w j| ≤ dist v w := fun j => by
        rw [← Real.dist_eq]; exact dist_le_pi_dist v w j
      have h1 := aux_jdo_maxTest_le M hγ i v w (dist v w) dist_nonneg (fun j => by
        have := (abs_le.mp (hvw j)).2; linarith)
      have h2 := aux_jdo_maxTest_le M hγ i w v (dist v w) dist_nonneg (fun j => by
        have := (abs_le.mp (hvw j)).1; linarith)
      rw [Real.dist_eq, abs_le]
      show -(γ * dist v w) ≤ maxTest M α v i - maxTest M α w i ∧
        maxTest M α v i - maxTest M α w i ≤ γ * dist v w
      constructor <;> linarith
  set v := ContractingWith.fixedPoint T hK with hvdef
  have hfix : T v = v := hK.fixedPoint_isFixedPt
  have hmax : ∀ i, maxTest M α v i = v i := fun i => congrFun hfix i
  have hex : ∀ i, ∃ z, maxTest M α v i = test M α z i v := fun i => by
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A))
      (fun z => test M α z i v)
    exact ⟨z, hz⟩
  choose d hd using hex
  refine ⟨d, v, fun i => by rw [← hd i, hmax i], ?_⟩
  intro π V0 i
  obtain ⟨x, hx⟩ := aux_jdo_conv M hγ0 hγ1 hγ π V0 i
  refine ⟨x, hx, ?_⟩
  set c : ℝ := ∑ j, |V0 j - v j| with hcdef
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hc : ∀ j, V0 j ≤ v j + c := fun j => by
    have h1 : |V0 j - v j| ≤ c :=
      Finset.single_le_sum (f := fun j => |V0 j - v j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 := le_abs_self (V0 j - v j)
    linarith
  have hlim : Tendsto (fun n => v i + γ ^ n * c) atTop (𝓝 (v i)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const c
    simpa using tendsto_const_nhds.add this
  exact le_of_tendsto_of_tendsto' hx hlim
    (fun n => aux_jdo_upper M hγ0 hγ v (fun i => (hmax i).le) V0 c hc0 hc n π i)
