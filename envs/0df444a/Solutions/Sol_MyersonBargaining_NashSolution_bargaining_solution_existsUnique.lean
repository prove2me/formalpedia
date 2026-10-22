-- Prove2me | solution 1 for MyersonBargaining.NashSolution.bargaining_solution_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:51:07.085109+00:00
-- url     : https://prove2.me/submissions/6bc948e7-c7fd-4502-829a-72bbf5b5d094

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

set_option autoImplicit false

namespace MyersonSolB3

open MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

lemma Z_continuous (G : Problem ι A C) (i : ι) (b a : A i) :
    Continuous fun π : C → (∀ i, A i) → ℝ => Z G i π b a := by
  unfold Z
  fun_prop

lemma V_continuous (G : Problem ι A C) :
    Continuous fun π : C → (∀ i, A i) → ℝ => V G π := by
  apply continuous_pi
  intro k
  exact Z_continuous G k.1 k.2 k.2

def Mechs (G : Problem ι A C) : Set (C → (∀ i, A i) → ℝ) :=
  {π | IsChoiceMechanism π ∧ IsBIC G π}

lemma Mechs_closed (G : Problem ι A C) : IsClosed (Mechs G) := by
  have h1 : IsClosed {π : C → (∀ i, A i) → ℝ | ∀ c s, 0 ≤ π c s} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun s =>
      isClosed_le continuous_const ((continuous_apply s).comp (continuous_apply c))
  have h2 : IsClosed {π : C → (∀ i, A i) → ℝ | ∀ s, ∑ c, π c s = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun s => isClosed_eq (by fun_prop) continuous_const
  have h3 : IsClosed {π : C → (∀ i, A i) → ℝ | IsBIC G π} := by
    simp only [IsBIC, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (Z_continuous G i b a) (Z_continuous G i a a)
  have : Mechs G = ({π | ∀ c s, 0 ≤ π c s} ∩ {π | ∀ s, ∑ c, π c s = 1}) ∩
      {π | IsBIC G π} := by
    ext π
    simp only [Mechs, IsChoiceMechanism, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [this]
  exact (h1.inter h2).inter h3

lemma Mechs_compact (G : Problem ι A C) : IsCompact (Mechs G) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : C =>
      Set.pi Set.univ fun _ : (∀ i, A i) => Set.Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  apply hK.of_isClosed_subset (Mechs_closed G)
  intro π hπ
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro c s
  refine ⟨hπ.1.1 c s, ?_⟩
  calc π c s ≤ ∑ c', π c' s :=
        Finset.single_le_sum (fun c' _ => hπ.1.1 c' s) (Finset.mem_univ c)
    _ = 1 := hπ.1.2 s

lemma FStar_eq (G : Problem ι A C) : FStar G = (fun π => V G π) '' Mechs G := by
  ext x
  simp only [FStar, Mechs, Set.mem_setOf_eq, Set.mem_image, and_assoc]

lemma FPlus_compact (G : Problem ι A C) (cstar : C) : IsCompact (FPlus G cstar) := by
  have hc : IsCompact (FStar G) := by
    rw [FStar_eq]
    exact (Mechs_compact G).image (V_continuous G)
  have hcl : IsClosed {y : (Σ i, A i) → ℝ | ∀ k, conflictPayoff G cstar k ≤ y k} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)
  exact hc.inter_right hcl

lemma Z_mid (G : Problem ι A C) (π1 π2 : C → (∀ i, A i) → ℝ) (i : ι) (b a : A i) :
    Z G i (fun c s => (π1 c s + π2 c s) / 2) b a = (Z G i π1 b a + Z G i π2 b a) / 2 := by
  simp only [Z, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun c _ => ?_
  ring

lemma FPlus_mid (G : Problem ι A C) (cstar : C) (x y : (Σ i, A i) → ℝ)
    (hx : x ∈ FPlus G cstar) (hy : y ∈ FPlus G cstar) :
    (fun k => (x k + y k) / 2) ∈ FPlus G cstar := by
  obtain ⟨⟨π1, h1c, h1b, rfl⟩, hxt⟩ := hx
  obtain ⟨⟨π2, h2c, h2b, rfl⟩, hyt⟩ := hy
  refine ⟨⟨fun c s => (π1 c s + π2 c s) / 2, ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro c s
    have := h1c.1 c s
    have := h2c.1 c s
    positivity
  · intro s
    rw [← Finset.sum_div, Finset.sum_add_distrib, h1c.2 s, h2c.2 s]
    norm_num
  · intro i a b
    rw [Z_mid, Z_mid]
    have := h1b i a b
    have := h2b i a b
    linarith
  · funext k
    simp only [V]
    rw [Z_mid]
  · intro k
    have := hxt k
    have := hyt k
    simp only
    linarith

lemma Z_const (G : Problem ι A C) (cstar : C) (i : ι) (b a : A i) :
    Z G i (constMech (A := A) cstar) b a = conflictPayoff G cstar ⟨i, a⟩ := by
  simp [Z, constMech, conflictPayoff, mul_ite, ite_mul, Finset.sum_ite_eq']

lemma const_choice (cstar : C) : IsChoiceMechanism (constMech (A := A) cstar) := by
  refine ⟨fun c s => ?_, fun s => ?_⟩
  · simp only [constMech]
    split_ifs <;> norm_num
  · simp [constMech]

lemma const_BIC (G : Problem ι A C) (cstar : C) : IsBIC G (constMech (A := A) cstar) := by
  intro i a b
  rw [Z_const, Z_const]

lemma nash_continuous (G : Problem ι A C) (cstar : C) : Continuous (nashProduct G cstar) := by
  unfold nashProduct
  refine continuous_finset_prod _ fun i _ => continuous_finset_prod _ fun a _ => ?_
  exact (Real.continuous_rpow_const (G.marginal_pos i a).le).comp
    ((continuous_apply _).sub continuous_const)

lemma nash_eq_exp (G : Problem ι A C) (cstar : C) (x : (Σ i, A i) → ℝ)
    (hx : ∀ k, conflictPayoff G cstar k < x k) :
    nashProduct G cstar x = Real.exp (∑ i, ∑ a : A i,
      marginal G.P i a * Real.log (x ⟨i, a⟩ - conflictPayoff G cstar ⟨i, a⟩)) := by
  unfold nashProduct
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Real.rpow_def_of_pos (sub_pos.2 (hx _)), mul_comm]

lemma pos_of_nash_pos (G : Problem ι A C) (cstar : C) (x : (Σ i, A i) → ℝ)
    (hx : x ∈ FPlus G cstar) (hpos : 0 < nashProduct G cstar x) :
    ∀ k, conflictPayoff G cstar k < x k := by
  rintro ⟨i, a⟩
  rcases (hx.2 ⟨i, a⟩).lt_or_eq with h | h
  · exact h
  · exfalso
    have : nashProduct G cstar x = 0 := by
      unfold nashProduct
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      rw [← h, sub_self, Real.zero_rpow (G.marginal_pos i a).ne']
    linarith

lemma log_mid_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.log a + Real.log b) / 2 ≤ Real.log ((a + b) / 2) := by
  have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at this
  calc (Real.log a + Real.log b) / 2 = 1/2 * Real.log a + 1/2 * Real.log b := by ring
    _ ≤ Real.log (1/2 * a + 1/2 * b) := this
    _ = Real.log ((a + b) / 2) := by congr 1; ring

lemma log_mid_lt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (Real.log a + Real.log b) / 2 < Real.log ((a + b) / 2) := by
  have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb) hab
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at this
  calc (Real.log a + Real.log b) / 2 = 1/2 * Real.log a + 1/2 * Real.log b := by ring
    _ < Real.log (1/2 * a + 1/2 * b) := this
    _ = Real.log ((a + b) / 2) := by congr 1; ring

lemma main (G : Problem ι A C) (cstar : C)
    (h : ¬ IsIncentiveEfficient G (constMech (A := A) cstar)) :
    ∃! x : (Σ i, A i) → ℝ, IsBargainingSolution G cstar x := by
  set t := conflictPayoff G cstar with ht
  have hVc : V G (constMech (A := A) cstar) = t := by
    funext k
    exact Z_const G cstar k.1 k.2 k.2
  have hex : ∃ π', IsChoiceMechanism π' ∧ IsBIC G π' ∧
      StrictlyDominates (V G π') (V G (constMech (A := A) cstar)) := by
    by_contra hne
    exact h ⟨const_choice cstar, const_BIC G cstar, hne⟩
  obtain ⟨π', hπc, hπb, hdom⟩ := hex
  rw [hVc] at hdom
  have hy0 : V G π' ∈ FPlus G cstar := ⟨⟨π', hπc, hπb, rfl⟩, fun k => (hdom k).le⟩
  have hN0 : 0 < nashProduct G cstar (V G π') := by
    unfold nashProduct
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun a _ => ?_
    exact Real.rpow_pos_of_pos (sub_pos.2 (hdom _)) _
  -- existence
  obtain ⟨x, hxF, hxmax⟩ := (FPlus_compact G cstar).exists_isMaxOn ⟨_, hy0⟩
    (nash_continuous G cstar).continuousOn
  have hxsol : IsBargainingSolution G cstar x := ⟨hxF, fun y hy => hxmax hy⟩
  -- uniqueness
  have uniq : ∀ x1 x2, IsBargainingSolution G cstar x1 → IsBargainingSolution G cstar x2 →
      x1 = x2 := by
    intro x1 x2 h1 h2
    have hp1 : 0 < nashProduct G cstar x1 := lt_of_lt_of_le hN0 (h1.2 _ hy0)
    have hp2 : 0 < nashProduct G cstar x2 := lt_of_lt_of_le hN0 (h2.2 _ hy0)
    have heq : nashProduct G cstar x1 = nashProduct G cstar x2 :=
      le_antisymm (h2.2 _ h1.1) (h1.2 _ h2.1)
    have d1 := pos_of_nash_pos G cstar x1 h1.1 hp1
    have d2 := pos_of_nash_pos G cstar x2 h2.1 hp2
    by_contra hne
    obtain ⟨k0, hk0⟩ := Function.ne_iff.1 hne
    set z : (Σ i, A i) → ℝ := fun k => (x1 k + x2 k) / 2 with hz
    have hzF : z ∈ FPlus G cstar := FPlus_mid G cstar x1 x2 h1.1 h2.1
    have dz : ∀ k, t k < z k := by
      intro k
      have := d1 k
      have := d2 k
      simp only [hz]
      linarith
    have hzle : nashProduct G cstar z ≤ nashProduct G cstar x1 := h1.2 _ hzF
    rw [nash_eq_exp G cstar z dz, nash_eq_exp G cstar x1 d1] at hzle
    rw [nash_eq_exp G cstar x1 d1, nash_eq_exp G cstar x2 d2] at heq
    have hL := Real.exp_injective heq
    rw [Real.exp_le_exp] at hzle
    have key : (∑ i, ∑ a : A i, marginal G.P i a * Real.log (x1 ⟨i, a⟩ - t ⟨i, a⟩) +
        ∑ i, ∑ a : A i, marginal G.P i a * Real.log (x2 ⟨i, a⟩ - t ⟨i, a⟩)) / 2 <
        ∑ i, ∑ a : A i, marginal G.P i a * Real.log (z ⟨i, a⟩ - t ⟨i, a⟩) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_lt_sum
      · intro i _
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_le_sum
        intro a _
        have hm := G.marginal_pos i a
        have e : z ⟨i, a⟩ - t ⟨i, a⟩ =
            ((x1 ⟨i, a⟩ - t ⟨i, a⟩) + (x2 ⟨i, a⟩ - t ⟨i, a⟩)) / 2 := by
          simp only [hz]; ring
        rw [e]
        have := log_mid_le _ _ (sub_pos.2 (d1 ⟨i, a⟩)) (sub_pos.2 (d2 ⟨i, a⟩))
        nlinarith
      · refine ⟨k0.1, Finset.mem_univ _, ?_⟩
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_lt_sum
        · intro a _
          have hm := G.marginal_pos k0.1 a
          have e : z ⟨k0.1, a⟩ - t ⟨k0.1, a⟩ =
              ((x1 ⟨k0.1, a⟩ - t ⟨k0.1, a⟩) + (x2 ⟨k0.1, a⟩ - t ⟨k0.1, a⟩)) / 2 := by
            simp only [hz]; ring
          rw [e]
          have := log_mid_le _ _ (sub_pos.2 (d1 ⟨k0.1, a⟩)) (sub_pos.2 (d2 ⟨k0.1, a⟩))
          nlinarith
        · refine ⟨k0.2, Finset.mem_univ _, ?_⟩
          have hm := G.marginal_pos k0.1 k0.2
          have e : z ⟨k0.1, k0.2⟩ - t ⟨k0.1, k0.2⟩ =
              ((x1 ⟨k0.1, k0.2⟩ - t ⟨k0.1, k0.2⟩) + (x2 ⟨k0.1, k0.2⟩ - t ⟨k0.1, k0.2⟩)) / 2 := by
            simp only [hz]; ring
          rw [e]
          have hne' : x1 ⟨k0.1, k0.2⟩ - t ⟨k0.1, k0.2⟩ ≠ x2 ⟨k0.1, k0.2⟩ - t ⟨k0.1, k0.2⟩ := by
            intro hh
            apply hk0
            have : x1 ⟨k0.1, k0.2⟩ = x2 ⟨k0.1, k0.2⟩ := by linarith
            simpa using this
          have := log_mid_lt _ _ (sub_pos.2 (d1 ⟨k0.1, k0.2⟩)) (sub_pos.2 (d2 ⟨k0.1, k0.2⟩)) hne'
          nlinarith
    rw [← hL] at key
    linarith
  exact ⟨x, hxsol, fun y hy => uniq y x hy hxsol⟩

end MyersonSolB3

open MyersonBargaining.NashSolution in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (G : Problem ι A C) (cstar : C)
    (h : ¬ IsIncentiveEfficient G (constMech (A := A) cstar)) :
    ∃! x : (Σ i, A i) → ℝ, IsBargainingSolution G cstar x := by
  exact MyersonSolB3.main G cstar h
