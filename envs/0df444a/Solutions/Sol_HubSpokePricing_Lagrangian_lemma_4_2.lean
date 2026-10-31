-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:53:55.737039+00:00
-- url     : https://prove2.me/submissions/05f902ec-a239-4f70-adbe-b39d7a3775a1

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokeL42Aux


open HubSpokePricing.Lagrangian Finset

abbrev E (m : ℕ) : Type := (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ)

def toSol {m : ℕ} (e : E m) : SpokeSol m := ⟨e.1, e.2.1, e.2.2⟩

lemma feas_zero (N : Network) (i : Fin N.n) :
    SpokeFeasible N i (toSol ((Pi.single 0 1, 0, 0) : E N.m)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [toSol]
    by_cases hx : x = 0
    · subst hx; simp
    · simp [Pi.single_apply, hx]
  · simp [toSol]
  · intro x; simp [toSol]
  · intro x; simp [toSol]
  · intro x; simp [toSol]
  · simp [toSol]
  · simp [toSol]

lemma obj_zero (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) :
    spokeObj N lam i (toSol ((Pi.single 0 1, 0, 0) : E N.m)) = 0 := by
  obtain ⟨_, _, _, _, _, _, hr⟩ := hN
  have h1 := (hr i).1.2.1
  have h2 := (hr i).2.2.1
  simp only [spokeObj, toSol]
  simp [h1, h2]
  right
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x = 0
  · subst hx; simp
  · simp [Pi.single_apply, hx]

lemma feas_closed (N : Network) (i : Fin N.n) :
    IsClosed {e : E N.m | SpokeFeasible N i (toSol e)} := by
  simp only [SpokeFeasible, toSol, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter (isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop))
    (IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
    (IsClosed.inter (isClosed_iInter fun x => IsClosed.inter
        (isClosed_le continuous_const (by fun_prop)) (isClosed_le (by fun_prop) continuous_const))
    (IsClosed.inter (isClosed_iInter fun x => IsClosed.inter
        (isClosed_le continuous_const (by fun_prop)) (isClosed_le (by fun_prop) continuous_const))
    (IsClosed.inter (isClosed_iInter fun x => isClosed_eq (by fun_prop) (by fun_prop))
    (IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
      (isClosed_eq (by fun_prop) continuous_const))))))

lemma feas_sub (N : Network) (i : Fin N.n) :
    {e : E N.m | SpokeFeasible N i (toSol e)} ⊆ Set.Icc (0, 0, 0) (1, 1, 1) := by
  intro e he
  obtain ⟨hp0, hp1, hdo, hdi, -⟩ := he
  simp only [toSol] at hp0 hp1 hdo hdi
  refine ⟨⟨fun x => hp0 x, fun x => (hdo x).1, fun x => (hdi x).1⟩,
    ⟨fun x => ?_, fun x => (hdo x).2, fun x => (hdi x).2⟩⟩
  show e.1 x ≤ 1
  rw [← hp1]
  exact Finset.single_le_sum (fun y _ => hp0 y) (Finset.mem_univ x)

lemma feas_compact (N : Network) (i : Fin N.n) :
    IsCompact {e : E N.m | SpokeFeasible N i (toSol e)} :=
  (isCompact_Icc).of_isClosed_subset (feas_closed N i) (feas_sub N i)

lemma obj_contOn (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) :
    ContinuousOn (fun e : E N.m => spokeObj N lam i (toSol e))
      {e : E N.m | SpokeFeasible N i (toSol e)} := by
  obtain ⟨_, _, _, _, _, _, hr⟩ := hN
  have hcO : ContinuousOn (N.rOut i) (Set.Icc 0 1) := (hr i).1.2.2.2.1.continuousOn
  have hcI : ContinuousOn (N.rIn i) (Set.Icc 0 1) := (hr i).2.2.2.2.1.continuousOn
  simp only [spokeObj, toSol]
  apply ContinuousOn.sub
  · apply continuousOn_finset_sum
    intro x _
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      exact hcO.comp (by fun_prop) (fun e he => (he.2.2.1 x))
    · apply ContinuousOn.mul continuousOn_const
      exact hcI.comp (by fun_prop) (fun e he => (he.2.2.2.1 x))
  · exact Continuous.continuousOn (by fun_prop)

/-- Existence of an optimal solution of the spoke problem (6), with the maximality property. -/
lemma spoke_max (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) :
    ∃ s : SpokeSol N.m, SpokeOptimal N lam i s ∧
      ∀ s' : SpokeSol N.m, SpokeFeasible N i s' → spokeObj N lam i s' ≤ h N lam i := by
  obtain ⟨e, he, hmax⟩ := (feas_compact N i).exists_isMaxOn ⟨_, feas_zero N i⟩
    (obj_contOn N hN lam i)
  have hG : IsGreatest (spokeObj N lam i '' {s | SpokeFeasible N i s})
      (spokeObj N lam i (toSol e)) := by
    refine ⟨⟨toSol e, he, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have : s = toSol (s.p, s.dOut, s.dIn) := rfl
    rw [this] at hs ⊢
    exact hmax hs
  have hh : h N lam i = spokeObj N lam i (toSol e) := hG.csSup_eq
  refine ⟨toSol e, ⟨he, hh.symm⟩, fun s' hs' => ?_⟩
  rw [hh]
  exact hG.2 ⟨s', hs', rfl⟩

lemma h_nonneg (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) : 0 ≤ h N lam i := by
  obtain ⟨s, -, hmax⟩ := spoke_max N hN lam i
  have := hmax _ (feas_zero N i)
  rwa [obj_zero N hN] at this

lemma mean_bounds (N : Network) (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeFeasible N i s) :
    0 ≤ ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ∧
      ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ≤ N.m := by
  obtain ⟨hp0, hp1, -⟩ := hs
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _) (hp0 x)
  · calc ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ≤ ∑ x : Fin (N.m + 1), (N.m : ℝ) * s.p x := by
          apply Finset.sum_le_sum
          intro x _
          apply mul_le_mul_of_nonneg_right _ (hp0 x)
          exact_mod_cast Nat.lt_succ_iff.mp x.2
      _ = N.m := by rw [← Finset.mul_sum, hp1, mul_one]

lemma h_lip (N : Network) (hN : N.Standing) (i : Fin N.n) (a b : ℝ) :
    h N a i ≤ h N b i + (N.m : ℝ) * dist a b := by
  obtain ⟨s, ⟨hs, hsa⟩, -⟩ := spoke_max N hN a i
  obtain ⟨-, -, hmaxb⟩ := spoke_max N hN b i
  have hb := hmaxb s hs
  have hdiff : spokeObj N a i s = spokeObj N b i s +
      (b - a) * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x := by
    simp only [spokeObj]; ring
  obtain ⟨hm0, hm1⟩ := mean_bounds N i s hs
  have : (b - a) * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ≤ (N.m : ℝ) * dist a b := by
    rw [Real.dist_eq]
    calc (b - a) * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x
        ≤ |a - b| * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x := by
          apply mul_le_mul_of_nonneg_right _ hm0
          rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ |a - b| * N.m := mul_le_mul_of_nonneg_left hm1 (abs_nonneg _)
      _ = _ := by ring
  rw [← hsa]; linarith

lemma h_cont (N : Network) (hN : N.Standing) (i : Fin N.n) : Continuous (fun l => h N l i) :=
  (LipschitzWith.of_le_add_mul' (N.m : ℝ) (fun a b => h_lip N hN i a b)).continuous

/-- Existence of an optimal solution `λ*(δ)` of (11) for `0 ≤ δ < m`. -/
lemma dual_exists (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m) :
    ∃ lam : ℝ, IsDualOpt N δ lam := by
  set F : ℝ → ℝ := fun l => Vbar N l - δ * l with hF
  have hFc : Continuous F := by
    simp only [hF, Vbar]
    have : Continuous (fun l => ∑ i, h N l i) := continuous_finset_sum _ fun i _ => h_cont N hN i
    fun_prop
  have hmd : 0 < (N.m : ℝ) - δ := by linarith
  set L : ℝ := F 0 / ((N.m : ℝ) - δ) with hL
  have hF0 : 0 ≤ F 0 := by
    simp only [hF, Vbar]; simp
    exact Finset.sum_nonneg fun i _ => h_nonneg N hN 0 i
  have hL0 : 0 ≤ L := div_nonneg hF0 hmd.le
  obtain ⟨l, hl, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_isMinOn
    ⟨0, ⟨le_rfl, hL0⟩⟩ hFc.continuousOn
  refine ⟨l, hl.1, fun l' hl' => ?_⟩
  change F l ≤ F l'
  by_cases h' : l' ≤ L
  · exact hmin ⟨hl', h'⟩
  · push_neg at h'
    have h1 : F l ≤ F 0 := hmin ⟨le_rfl, hL0⟩
    have h2 : ((N.m : ℝ) - δ) * L = F 0 := by rw [hL]; field_simp
    have h3 : ((N.m : ℝ) - δ) * L < ((N.m : ℝ) - δ) * l' := mul_lt_mul_of_pos_left h' hmd
    have h4 : 0 ≤ ∑ i, h N l' i := Finset.sum_nonneg fun i _ => h_nonneg N hN l' i
    have h5 : F l' = ((N.m : ℝ) - δ) * l' + ∑ i, h N l' i := by
      simp only [hF, Vbar]; ring
    linarith


lemma h_upper (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam) (i : Fin N.n) :
    h N lam i ≤ (N.qOut i + N.qIn i) * N.rbar := by
  obtain ⟨s, ⟨hs, hsv⟩, -⟩ := spoke_max N hN lam i
  rw [← hsv]
  obtain ⟨_, hqo, hqi, _, _, _, hr⟩ := hN
  have hro := (hr i).1.2.2.1
  have hri := (hr i).2.2.2.1
  have hm0 := (mean_bounds N i s hs).1
  obtain ⟨hp0, hp1, hdo, hdi, -⟩ := hs
  simp only [spokeObj]
  have h1 : ∑ x, s.p x * (N.qOut i * N.rOut i (s.dOut x) + N.qIn i * N.rIn i (s.dIn x)) ≤
      ∑ x, s.p x * ((N.qOut i + N.qIn i) * N.rbar) := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hp0 x)
    have a1 := hro (s.dOut x) ⟨(hdo x).1, (hdo x).2⟩
    have a2 := hri (s.dIn x) ⟨(hdi x).1, (hdi x).2⟩
    have := mul_le_mul_of_nonneg_left a1 (hqo i).le
    have := mul_le_mul_of_nonneg_left a2 (hqi i).le
    nlinarith
  rw [← Finset.sum_mul, hp1, one_mul] at h1
  have := mul_nonneg hlam hm0
  linarith

end HubSpokeL42Aux

open HubSpokePricing.Lagrangian

theorem solution (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m) :
    VR N δ ≤ VRstar N ∧ VRstar N ≤ VR N δ + N.rbar * δ / ((N.m : ℝ) - δ) := by
  have hm0 : (0 : ℝ) < N.m := lt_of_le_of_lt hδ0 hδm
  -- lower bound of the objective of (11) for any `0 ≤ d ≤ m`
  have hlow : ∀ d : ℝ, d ≤ N.m → ∀ l : {l : ℝ // 0 ≤ l}, 0 ≤ Vbar N l.1 - d * l.1 := by
    intro d hd l
    have : 0 ≤ ∑ i, h N l.1 i := Finset.sum_nonneg fun i _ => HubSpokeL42Aux.h_nonneg N hN _ i
    have : 0 ≤ ((N.m : ℝ) - d) * l.1 := mul_nonneg (by linarith) l.2
    simp only [Vbar]; nlinarith
  have hbdd : ∀ d : ℝ, d ≤ N.m →
      BddBelow (Set.range fun l : {l : ℝ // 0 ≤ l} => Vbar N l.1 - d * l.1) :=
    fun d hd => ⟨0, by rintro _ ⟨l, rfl⟩; exact hlow d hd l⟩
  obtain ⟨ls, hls0, hls⟩ := HubSpokeL42Aux.dual_exists N hN δ hδ0 hδm
  have hVRδ : VR N δ = Vbar N ls - δ * ls := by
    apply le_antisymm
    · exact ciInf_le (hbdd δ hδm.le) ⟨ls, hls0⟩
    · exact le_ciInf fun l => hls l.1 l.2
  have hδle : ∀ l : {l : ℝ // 0 ≤ l}, VR N δ ≤ Vbar N l.1 - δ * l.1 :=
    fun l => ciInf_le (hbdd δ hδm.le) l
  constructor
  · simp only [VRstar, VR]
    apply le_ciInf
    intro l
    have := hδle l
    have : 0 ≤ δ * l.1 := mul_nonneg hδ0 l.2
    simp only [VR] at *
    linarith
  · -- λ*(δ) ≤ r̄ / (m − δ)
    have hF0 : Vbar N 0 - δ * 0 ≤ N.rbar := by
      simp only [Vbar, mul_zero, sub_zero, zero_add]
      have hsum := hN.2.2.2.1
      calc ∑ i, h N 0 i ≤ ∑ i, (N.qOut i + N.qIn i) * N.rbar :=
            Finset.sum_le_sum fun i _ => HubSpokeL42Aux.h_upper N hN 0 le_rfl i
        _ = N.rbar := by rw [← Finset.sum_mul, hsum, one_mul]
    have hopt0 := hls 0 le_rfl
    have hsum0 : 0 ≤ ∑ i, h N ls i := Finset.sum_nonneg fun i _ => HubSpokeL42Aux.h_nonneg N hN _ i
    have hmd : 0 < (N.m : ℝ) - δ := by linarith
    have hlsb : ((N.m : ℝ) - δ) * ls ≤ N.rbar := by
      simp only [Vbar] at hopt0 hF0; nlinarith
    have hlsb' : δ * ls ≤ N.rbar * δ / ((N.m : ℝ) - δ) := by
      rw [le_div_iff₀ hmd]
      have := mul_le_mul_of_nonneg_left hlsb hδ0
      nlinarith
    have h0 : VRstar N ≤ Vbar N ls - 0 * ls := ciInf_le (hbdd 0 (by positivity)) ⟨ls, hls0⟩
    rw [hVRδ]
    linarith
