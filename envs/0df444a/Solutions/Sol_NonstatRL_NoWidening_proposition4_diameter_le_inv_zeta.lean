-- Prove2me | solution 1 for NonstatRL.NoWidening.proposition4_diameter_le_inv_zeta
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T09:19:37.579865+00:00
-- url     : https://prove2.me/submissions/adf534a3-78b8-4355-a4be-2991af3a96b2

import Definitions.Def_NonstatRL_PerStep_Window
set_option autoImplicit false
open BanditAlgorithm NonstatRL.PerStep
open scoped NNReal
noncomputable section
namespace NonstatRL.NoWidening

lemma countPlus_pos {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A) : 0 < countPlus st ac lo hi s a := by
  unfold countPlus
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))

lemma average_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ) (s : Fin S) (a : Fin A) (y : Fin S) :
    0 ≤ pBar M st ac lo hi s a y := by
  unfold pBar
  apply div_nonneg _ (countPlus_pos st ac lo hi s a).le
  exact Finset.sum_nonneg (fun q _ => by split_ifs <;> positivity)

lemma average_sum {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ) (s : Fin S) (a : Fin A)
    (hc : 0 < count st ac lo hi s a) : ∑ y, pBar M st ac lo hi s a y = 1 := by
  unfold pBar
  rw [← Finset.sum_div,Finset.sum_comm]
  have hsum : (∑ q ∈ Finset.Ico lo hi, ∑ y : Fin S,
      if st q=s ∧ ac q=a then ((M q).P s a y : ℝ) else 0) = count st ac lo hi s a := by
    calc
      _ = ∑ q ∈ Finset.Ico lo hi, if st q=s ∧ ac q=a then (1:ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : st q=s ∧ ac q=a
        · simp only [if_pos h]
          exact_mod_cast (M q).P_sum_one s a
        · simp [h]
      _ = _ := by simp [count,Finset.sum_boole]
  rw [hsum]
  unfold countPlus
  rw [max_eq_right hc]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hc)

lemma average_lower {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ) (s : Fin S) (a : Fin A) (y : Fin S)
    (hc : 0 < count st ac lo hi s a) (z : ℝ)
    (hz : ∀ q ∈ Finset.Ico lo hi, z ≤ ((M q).P s a y : ℝ)) :
    z ≤ pBar M st ac lo hi s a y := by
  unfold pBar
  apply (le_div_iff₀ (countPlus_pos st ac lo hi s a)).mpr
  have hsum := Finset.sum_le_sum (s := Finset.Ico lo hi) (f := fun q => if st q=s ∧ ac q=a then z else 0)
    (g := fun q => if st q=s ∧ ac q=a then ((M q).P s a y : ℝ) else 0)
    (fun q hq => by split_ifs <;> first | exact hz q hq | exact le_rfl)
  have hid : (∑ q ∈ Finset.Ico lo hi, if st q=s ∧ ac q=a then z else 0) =
      (count st ac lo hi s a : ℝ)*z := by
    rw [← Finset.sum_filter]
    simp [count]
  rw [hid] at hsum
  unfold countPlus
  rw [max_eq_right hc]
  simpa [mul_comm] using hsum

lemma phat_zero {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A)
    (hz : count st ac lo hi s a=0) : ∀ y, pHat st ac lo hi s a y=0 := by
  have hempty : ((Finset.Ico lo hi).filter (fun q => st q=s ∧ ac q=a))=∅ := Finset.card_eq_zero.mp hz
  intro y
  have hsubset : ((Finset.Ico lo hi).filter (fun q => st q=s ∧ ac q=a ∧ st (q+1)=y)) ⊆
      ((Finset.Ico lo hi).filter (fun q => st q=s ∧ ac q=a)) := by
    intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1,hq.2.1,hq.2.2.1⟩
  rw [hempty] at hsubset
  have hnil := Finset.subset_empty.mp hsubset
  simp [pHat,hnil]

lemma radius_one {S A : ℕ} (hS : 1 < S)
    (As : Fin S → Finset (Fin A)) (hAs : ∀ s, (As s).Nonempty)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    1 ≤ radP As T δ 1 := by
  have hs : (2:ℝ) ≤ S := by exact_mod_cast hS
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have htotal : (S:ℝ) ≤ ∑ s : Fin S, ((As s).card : ℝ) := by
    calc
      _ = ∑ s : Fin S, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun s _ => by exact_mod_cast (Finset.card_pos.mpr (hAs s)))
  have hnum : 2 ≤ (∑ s : Fin S, ((As s).card : ℝ))*(T:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ ∑ s : Fin S, ((As s).card : ℝ) from by positivity)]
  have harg : 2 ≤ (∑ s : Fin S, ((As s).card : ℝ))*(T:ℝ)/δ := by
    apply (le_div_iff₀ hδ.1).mpr
    linarith [hδ.2]
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hlog : (1/2:ℝ) ≤ Real.log ((∑ s : Fin S, ((As s).card : ℝ))*T/δ) :=
    hlog2.trans (Real.log_le_log (by norm_num) harg)
  have hinside : 1 ≤ 2*(S:ℝ)*Real.log ((∑ s : Fin S, ((As s).card : ℝ))*T/δ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (show 0≤2*(S:ℝ) from by positivity)]
  have hroot := Real.sqrt_le_sqrt hinside
  simp only [Real.sqrt_one] at hroot
  unfold radP
  rw [div_one]
  linarith

lemma unvisited_core {S A : ℕ} (hS : 1 < S)
    (As : Fin S → Finset (Fin A)) (hAs : ∀ s, (As s).Nonempty)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (hzero : count st ac lo hi s a = 0) :
    1 ≤ radP As T δ (countPlus st ac lo hi s a) ∧
      ∀ p : Fin S → ℝ, (∀ s', 0 ≤ p s') → (∑ s', p s') = 1 →
        p ∈ Hp As T δ st ac lo hi 0 s a := by
  have hplus : countPlus st ac lo hi s a=1 := by simp [countPlus,hzero]
  have hr : 1 ≤ radP As T δ (countPlus st ac lo hi s a) := by rw [hplus]; exact radius_one hS As hAs T hT δ hδ
  refine ⟨hr,?_⟩
  intro p hp hs
  refine ⟨hp,hs,?_⟩
  simp only [phat_zero st ac lo hi s a hzero,sub_zero,abs_of_nonneg (hp _),add_zero]
  rwa [hs]


lemma visited_core {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∀ s s', 0 < NonstatRL.PerStep.count st ac (τm - W) t s (a₂ s s') →
      ζ ≤ NonstatRL.PerStep.pBar M st ac (τm - W) t s (a₂ s s') s' ∧
      (fun y => NonstatRL.PerStep.pBar M st ac (τm - W) t s (a₂ s s') y) ∈
        NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s (a₂ s s') := by
  intro s s' hc
  refine ⟨average_lower M st ac (τm-W) t s (a₂ s s') s' hc ζ ?_,?_⟩
  · intro q hq
    exact hreach q ((Finset.mem_Ico.mp hq).2.trans ht) s s'
  · refine ⟨average_nonneg M st ac (τm-W) t s (a₂ s s'),
      average_sum M st ac (τm-W) t s (a₂ s s') hc,?_⟩
    simpa only [add_zero] using hEp s (a₂ s s') (ha₂ s s')



lemma model_core {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∃ Mw : FiniteMDP S A,
      (∀ s, ∀ a ∈ As s,
        (fun s' => (Mw.P s a s' : ℝ)) ∈ NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s a) ∧
      ∀ s s', ζ ≤ (Mw.P s (a₂ s s') s' : ℝ) := by
  classical
  let Q : Fin S → Fin A → Fin S → ℝ := fun s a y =>
    if count st ac (τm-W) t s a=0 then ((M 0).P s a y : ℝ)
    else pBar M st ac (τm-W) t s a y
  have hQ0 (s : Fin S) (a : Fin A) (y : Fin S) : 0 ≤ Q s a y := by
    dsimp [Q]
    split_ifs
    · positivity
    · exact average_nonneg M st ac (τm-W) t s a y
  have hQsum (s : Fin S) (a : Fin A) : ∑ y, Q s a y=1 := by
    by_cases hc : count st ac (τm-W) t s a=0
    · simp only [Q,if_pos hc]
      exact_mod_cast (M 0).P_sum_one s a
    · simpa only [Q,if_neg hc] using average_sum M st ac (τm-W) t s a (Nat.pos_of_ne_zero hc)
  let Mw : FiniteMDP S A := {
    P := fun s a y => Real.toNNReal (Q s a y)
    P_sum_one := fun s a => by
      apply NNReal.coe_injective
      simpa only [NNReal.coe_sum,Real.coe_toNNReal _ (hQ0 _ _ _),NNReal.coe_one] using hQsum s a
    r := fun _ _ => 0
    r_mem_Icc := fun _ _ => by simp }
  refine ⟨Mw,?_,?_⟩
  · intro s a ha
    change (fun y => (Real.toNNReal (Q s a y) : ℝ)) ∈ Hp As T δ st ac (τm-W) t 0 s a
    simp only [Real.coe_toNNReal _ (hQ0 _ _ _)]
    by_cases hc : count st ac (τm-W) t s a=0
    · have hT : 1 ≤ T := Nat.zero_lt_of_lt ht
      apply (unvisited_core hS As hAs T hT δ hδ st ac (τm-W) t s a ha hc).2
      · exact hQ0 s a
      · exact hQsum s a
    · refine ⟨hQ0 s a,hQsum s a,?_⟩
      simpa only [Q,if_neg hc,add_zero] using hEp s a ha
  · intro s s'
    change ζ ≤ (Real.toNNReal (Q s (a₂ s s') s') : ℝ)
    rw [Real.coe_toNNReal _ (hQ0 _ _ _)]
    by_cases hc : count st ac (τm-W) t s (a₂ s s')=0
    · simpa only [Q,if_pos hc] using hreach 0 (Nat.zero_lt_of_lt ht) s s'
    · simpa only [Q,if_neg hc] using
        (visited_core hS M As hAs T δ hδ st ac W τm t hτ ht ζ hζ a₂ ha₂ hreach hEp s s' (Nat.pos_of_ne_zero hc)).1


end NonstatRL.NoWidening
set_option autoImplicit false
open BanditAlgorithm MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace NonstatRL.HittingResearch

lemma step_action_ae {S A : ℕ} (M : FiniteMDP S A) (μ : MDPStateDistribution S)
    (f : Fin S → Fin A) (n : ℕ) (h : MDPTrajectory S A n) :
    ∀ᵐ p ∂(mdpStepKernel M μ (mdpMemorylessDetPolicy f) n h), p.2=f p.1 := by
  unfold mdpStepKernel
  apply Kernel.ae_compProd_of_ae_ae (Set.to_countable _).measurableSet
  filter_upwards [] with x
  simp [mdpMemorylessDetPolicy,Kernel.deterministic_apply]

lemma actions_ae {S A : ℕ} (M : FiniteMDP S A) (μ : MDPStateDistribution S)
    (f : Fin S → Fin A) (n : ℕ) :
    ∀ᵐ h ∂(mdpMeasure M μ (mdpMemorylessDetPolicy f) n), ∀ i, (h i).2=f (h i).1 := by
  induction n with
  | zero =>
    filter_upwards [] with h i
    exact i.elim0
  | succ n ih =>
    rw [mdpMeasure,ae_map_iff measurable_mdpTrajectorySnoc.aemeasurable (Set.to_countable _).measurableSet]
    apply Measure.ae_compProd_of_ae_ae (Set.to_countable _).measurableSet
    filter_upwards [ih] with h hh
    filter_upwards [step_action_ae M μ f n h] with p hp
    rw [Fin.forall_fin_succ']
    constructor
    · intro i
      simpa using hh i
    · simpa using hp

lemma step_state_event {S A : ℕ} (M : FiniteMDP S A) (μ : MDPStateDistribution S)
    (f : Fin S → Fin A) (n : ℕ) (h : MDPTrajectory S A (n+1)) (tgt : Fin S) :
    mdpStepKernel M μ (mdpMemorylessDetPolicy f) (n+1) h {p | p.1 ≠ tgt} =
      1-(M.P (h (Fin.last n)).1 (h (Fin.last n)).2 tgt : ℝ≥0∞) := by
  have hevent : {p : Fin S × Fin A | p.1 ≠ tgt} = ({tgt}ᶜ : Set (Fin S)) ×ˢ Set.univ := by ext p; simp
  rw [hevent,mdpStepKernel,Kernel.compProd_apply_prod (Set.to_countable _).measurableSet MeasurableSet.univ]
  simp only [measure_univ,one_mul,lintegral_one]
  rw [Measure.restrict_apply_univ]
  change (M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure {tgt}ᶜ = _
  rw [measure_compl (MeasurableSet.singleton tgt) (by simp)]
  simp only [measure_univ]
  congr 1
  simp [FiniteMDP.transitionDist,MDPStateDistribution.toMeasure,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply',Pi.single_apply,NNReal.smul_def]

noncomputable def avoids {S A : ℕ} (tgt : Fin S) (n : ℕ) : Set (MDPTrajectory S A (n+1)) :=
  {h | ∀ i, i ≠ 0 → (h i).1 ≠ tgt}

lemma avoids_snoc {S A : ℕ} (tgt : Fin S) (n : ℕ)
    (h : MDPTrajectory S A (n+1)) (p : Fin S × Fin A) :
    Fin.snoc h p ∈ avoids tgt (n+1) ↔ h ∈ avoids tgt n ∧ p.1 ≠ tgt := by
  simp only [avoids,Set.mem_setOf_eq,Fin.forall_fin_succ']
  simp

lemma avoids_step {S A : ℕ} (M : FiniteMDP S A) (μ : MDPStateDistribution S)
    (f : Fin S → Fin A) (tgt : Fin S) (n : ℕ) :
    mdpMeasure M μ (mdpMemorylessDetPolicy f) (n+2) (avoids tgt (n+1)) =
      ∫⁻ h in avoids tgt n, 1-(M.P (h (Fin.last n)).1 (h (Fin.last n)).2 tgt : ℝ≥0∞)
        ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) (n+1) := by
  have hp : (fun p : MDPTrajectory S A (n+1) × (Fin S × Fin A) => Fin.snoc p.1 p.2) ⁻¹' avoids tgt (n+1) =
      avoids tgt n ×ˢ {p | p.1 ≠ tgt} := by
    ext p
    exact avoids_snoc tgt n p.1 p.2
  rw [mdpMeasure,Measure.map_apply measurable_mdpTrajectorySnoc (Set.to_countable _).measurableSet,hp,
    Measure.compProd_apply_prod (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet]
  simp only [step_state_event]

lemma avoids_geometric {S A : ℕ} (M : FiniteMDP S A) (μ : MDPStateDistribution S)
    (f : Fin S → Fin A) (tgt : Fin S) (z : ℝ≥0∞)
    (hreach : ∀ x, z ≤ (M.P x (f x) tgt : ℝ≥0∞)) (n : ℕ) :
    mdpMeasure M μ (mdpMemorylessDetPolicy f) (n+1) (avoids tgt n) ≤ (1-z)^n := by
  induction n with
  | zero =>
    simp [avoids]
  | succ n ih =>
    rw [avoids_step]
    have hstep : ∀ᵐ h ∂(mdpMeasure M μ (mdpMemorylessDetPolicy f) (n+1)).restrict (avoids tgt n),
        1-(M.P (h (Fin.last n)).1 (h (Fin.last n)).2 tgt : ℝ≥0∞) ≤ 1-z := by
      filter_upwards [ae_restrict_of_ae (actions_ae M μ f (n+1))] with h hh
      rw [hh (Fin.last n)]
      exact tsub_le_tsub_left (hreach _) 1
    calc
      _ ≤ ∫⁻ _ in avoids tgt n, 1-z ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) (n+1) := lintegral_mono_ae hstep
      _ = (1-z)*mdpMeasure M μ (mdpMemorylessDetPolicy f) (n+1) (avoids tgt n) := by simp
      _ ≤ (1-z)*(1-z)^n := mul_le_mul' le_rfl ih
      _ = (1-z)^(n+1) := by rw [pow_succ]; exact mul_comm _ _


lemma hitTime_core {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt : Fin S)
    (ζ : ℝ) (hζ : 0 < ζ) (hreach : ∀ x, ζ ≤ (M.P x (f x) tgt : ℝ)) :
    ∀ s, NonstatRL.Oracle.hitTime M f s tgt ≤ ENNReal.ofReal (1/ζ) := by
  have hz1 : ζ ≤ 1 := by
    apply (hreach tgt).trans
    have h := Finset.single_le_sum (fun x (_ : x ∈ Finset.univ) => (M.P tgt (f tgt) x).coe_nonneg)
      (Finset.mem_univ tgt)
    have hs : (∑ x, (M.P tgt (f tgt) x : ℝ))=1 := by exact_mod_cast M.P_sum_one tgt (f tgt)
    simpa only [hs] using h
  have hz : ENNReal.ofReal ζ ≤ 1 := by exact_mod_cast ENNReal.ofReal_le_ofReal hz1
  intro s
  unfold NonstatRL.Oracle.hitTime
  calc
    _ ≤ ∑' n : ℕ, (1-ENNReal.ofReal ζ)^n := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact avoids_geometric M (mdpStateDirac s) f tgt (ENNReal.ofReal ζ)
        (fun x => by simpa using ENNReal.ofReal_le_ofReal (hreach x)) n
    _ = (1-(1-ENNReal.ofReal ζ))⁻¹ := ENNReal.tsum_geometric _
    _ = (ENNReal.ofReal ζ)⁻¹ := by rw [ENNReal.sub_sub_cancel (by simp) hz]
    _ = ENNReal.ofReal (1/ζ) := by simp [ENNReal.ofReal_inv_of_pos hζ]

end NonstatRL.HittingResearch

namespace NonstatRL.NoWidening
lemma root_core {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∃ Mw : FiniteMDP S A,
      (∀ s, ∀ a ∈ As s,
        (fun s' => (Mw.P s a s' : ℝ)) ∈ NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s a) ∧
      NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal (1 / ζ) := by
  obtain ⟨Mw,hm,hr⟩ := model_core hS M As hAs T δ hδ st ac W τm t hτ ht ζ hζ a₂ ha₂ hreach hEp
  refine ⟨Mw,hm,?_⟩
  apply iSup_le
  intro s
  apply iSup_le
  intro tgt
  exact iInf_le_of_le (fun x => a₂ x tgt) (iInf_le_of_le (fun x => ha₂ x tgt)
    (NonstatRL.HittingResearch.hitTime_core Mw (fun x => a₂ x tgt) tgt ζ hζ (fun x => hr x tgt) s))
end NonstatRL.NoWidening

open NonstatRL.NoWidening

theorem solution {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∃ Mw : FiniteMDP S A,
      (∀ s, ∀ a ∈ As s,
        (fun s' => (Mw.P s a s' : ℝ)) ∈ NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s a) ∧
      NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal (1 / ζ) := by exact root_core hS M As hAs T δ hδ st ac W τm t hτ ht ζ hζ a₂ ha₂ hreach hEp


#print axioms solution
