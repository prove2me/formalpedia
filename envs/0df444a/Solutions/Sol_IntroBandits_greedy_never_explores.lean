-- Prove2me | solution 1 for IntroBandits.greedy_never_explores
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:05:55.113177+00:00
-- url     : https://prove2.me/submissions/aee1bb4a-0615-4e6f-b265-e141d7f88cfe

import Mathlib
import Definitions.Def_IntroBandits_Agents

set_option autoImplicit false

namespace P2Mf9

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits

/-- The event that every arm played so far is arm 1 (index `0`). -/
def Zset (n : ℕ) : Set (BanditHistory 2 n) := {h | ∀ i, (h i).1 = 0}

lemma measurableSet_arm {n : ℕ} (i : Fin n) (a : Fin 2) :
    MeasurableSet {h : BanditHistory 2 n | (h i).1 = a} :=
  (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton a)

lemma measurableSet_Zset (n : ℕ) : MeasurableSet (Zset n) := by
  have : Zset n = ⋂ i, {h : BanditHistory 2 n | (h i).1 = 0} := by
    ext h; simp [Zset]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_arm i 0

lemma bm_succ (ν : StochasticBandit 2) (π : BanditPolicy 2) (n : ℕ) :
    banditMeasure ν π (n+1) = ((banditMeasure ν π n).compProd (banditStepKernel ν π n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) p.1 p.2) := by
  rw [banditMeasure]

lemma stepSnoc (ν : StochasticBandit 2) (π : BanditPolicy 2) (n : ℕ) (h : BanditHistory 2 n)
    {E : Set (BanditHistory 2 (n+1))} (hE : MeasurableSet E) :
    banditStepKernel ν π n h (Prod.mk h ⁻¹' ((fun p : BanditHistory 2 n × (Fin 2 × ℝ) ↦
        Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) p.1 p.2) ⁻¹' E)) =
      ∑ b, ν.P b {r | Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) h (b, r) ∈ E} * π.select n h {b} := by
  rw [banditStepKernel, Kernel.compProd_apply (measurable_prodMk_left
    (measurable_banditHistorySnoc hE)), lintegral_fintype]
  rfl

/-- reward values as a finite type -/
abbrev V (fam : RewardFamily) := {x // x ∈ fam.values}

def zs {fam : RewardFamily} {n : ℕ} (s : Fin n → V fam) : BanditHistory 2 n :=
  fun i => (0, (s i : ℝ))

lemma zs_mem {fam : RewardFamily} {n : ℕ} (s : Fin n → V fam) : zs s ∈ Zset n :=
  fun _ => rfl

lemma zs_snoc {fam : RewardFamily} {n : ℕ} (s : Fin n → V fam) (v : V fam) :
    zs (Fin.snoc (α := fun _ => V fam) s v) =
      Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), (v : ℝ)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [zs, Fin.snoc_last]
  · simp [zs, Fin.snoc_castSucc]

lemma instanceOf_P (fam : RewardFamily) (μ : Fin 2 → ℝ) (a : Fin 2) :
    (instanceOf fam μ).P a = fam.D (μ a) := rfl

lemma D_apply_eq_sum (fam : RewardFamily) (x : ℝ) (A : Set ℝ) :
    fam.D x A = ∑ v : V fam, fam.D x {(v : ℝ)} * A.indicator 1 (v : ℝ) := by
  classical
  rw [← measure_inter_conull (s := A) (fam.supp x)]
  have h1 : A ∩ (fam.values : Set ℝ) = ↑(fam.values.filter (· ∈ A)) := by
    ext y; simp [and_comm]
  rw [h1, ← sum_measure_singleton, Finset.sum_filter, ← Finset.sum_coe_sort fam.values]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : (v : ℝ) ∈ A <;> simp [hv]

def snocE (fam : RewardFamily) (n : ℕ) : (Fin n → V fam) × V fam ≃ (Fin (n+1) → V fam) where
  toFun p := Fin.snoc (α := fun _ => V fam) p.1 p.2
  invFun s := (Fin.init s, s (Fin.last n))
  left_inv p := by simp [Fin.init_snoc, Fin.snoc_last]
  right_inv s := Fin.snoc_init_self s

/-- the policy-only weight of the all-arm-0 history with rewards `s` -/
noncomputable def wt (fam : RewardFamily) (π : BanditPolicy 2) :
    (n : ℕ) → (Fin n → V fam) → ENNReal
  | 0, _ => 1
  | n+1, s => wt fam π n (Fin.init s) * π.select n (zs (Fin.init s)) {0}

lemma wt_le_one (fam : RewardFamily) (π : BanditPolicy 2) :
    ∀ (n : ℕ) (s : Fin n → V fam), wt fam π n s ≤ 1
  | 0, _ => le_rfl
  | n+1, s => mul_le_one' (wt_le_one fam π n _) prob_le_one

lemma key (fam : RewardFamily) (π : BanditPolicy 2) (n : ℕ) :
    ∀ μ : Fin 2 → ℝ,
      (banditMeasure (instanceOf fam μ) π n).restrict (Zset n) =
        ∑ s, (wt fam π n s * ∏ i, fam.D (μ 0) {((s i : V fam) : ℝ)}) • Measure.dirac (zs s) := by
  induction n with
  | zero =>
    intro μ
    have hZ : Zset 0 = Set.univ := by
      ext h; simp [Zset]
    rw [hZ, Measure.restrict_univ, Fintype.sum_unique]
    simp only [wt, Finset.univ_eq_empty, Finset.prod_empty, mul_one, one_smul]
    have : zs (default : Fin 0 → V fam) = fun t => t.elim0 := funext fun i => i.elim0
    rw [this]
    rfl
  | succ n ih =>
    intro μ
    ext S hS
    have hSZ : MeasurableSet (S ∩ Zset (n+1)) := hS.inter (measurableSet_Zset _)
    rw [Measure.restrict_apply hS, bm_succ, Measure.map_apply measurable_banditHistorySnoc hSZ,
      Measure.compProd_apply (measurable_banditHistorySnoc hSZ),
      ← setLIntegral_eq_of_support_subset (s := Zset n), ih μ]
    · simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
        smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hS]
      rw [← (snocE fam n).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [stepSnoc _ _ _ _ hSZ, Fin.sum_univ_two]
      have h0 : {r | Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), r) ∈ S ∩ Zset (n+1)}
          = {r | Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), r) ∈ S} := by
        ext r
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
        intro _ i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Fin.snoc_last]
        · simp [Fin.snoc_castSucc, zs]
      have h1 : {r | Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((1 : Fin 2), r) ∈ S ∩ Zset (n+1)}
          = ∅ := by
        ext r
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro _ hz
        have := hz (Fin.last n)
        simp [Fin.snoc_last] at this
      rw [h0, h1, measure_empty, zero_mul, add_zero, instanceOf_P, D_apply_eq_sum,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [snocE, Equiv.coe_fn_mk, wt, Fin.init_snoc, Fin.prod_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last, zs_snoc]
      have hind : ({r | Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), r) ∈ S} :
          Set ℝ).indicator (1 : ℝ → ENNReal) (v : ℝ) =
          S.indicator (1 : BanditHistory 2 (n+1) → ENNReal) (Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), (v : ℝ))) := by
        by_cases hv : Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), (v : ℝ)) ∈ S
        · have hv' : (v : ℝ) ∈
              {r | Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), r) ∈ S} := hv
          simp only [Set.indicator_of_mem hv, Set.indicator_of_mem hv', Pi.one_apply]
        · have hv' : (v : ℝ) ∉
              {r | Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) (zs s) ((0 : Fin 2), r) ∈ S} := hv
          simp only [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv']
      rw [hind]
      ring
    · intro h hh
      by_contra hz
      apply hh
      simp only
      convert measure_empty (μ := banditStepKernel (instanceOf fam μ) π n h)
      ext q
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro _ hq
      apply hz
      intro i
      have := hq (Fin.castSucc i)
      simpa [Fin.snoc_castSucc] using this

/-- likelihood of `n` arm-0 rewards `s` under mean vector `μ` -/
noncomputable def Lk (fam : RewardFamily) (μ : Fin 2 → ℝ) {n : ℕ} (s : Fin n → V fam) : ENNReal :=
  ∏ i, fam.D (μ 0) {((s i : V fam) : ℝ)}

lemma Lk_ne_top (fam : RewardFamily) (μ : Fin 2 → ℝ) {n : ℕ} (s : Fin n → V fam) :
    Lk fam μ s ≠ ⊤ :=
  ENNReal.prod_ne_top fun _ _ => measure_ne_top _ _

/-- `E[(μ₁ − μ₂) 𝟙{S = s}]` -/
noncomputable def gap (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    {n : ℕ} (s : Fin n → V fam) : ℝ :=
  ∑ μ ∈ F, (P {μ} * Lk fam μ s).toReal * (μ 0 - μ 1)

noncomputable def Ssum (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (π : BanditPolicy 2) (n : ℕ) : ℝ :=
  ∑ s : Fin n → V fam, (wt fam π n s).toReal * gap P F fam s

lemma sum_D_toReal (fam : RewardFamily) (x : ℝ) :
    ∑ v : V fam, (fam.D x {(v : ℝ)}).toReal = 1 := by
  have h := D_apply_eq_sum fam x Set.univ
  simp only [measure_univ, Set.indicator_univ, Pi.one_apply, mul_one] at h
  rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ← h, ENNReal.toReal_one]

lemma Lk_snoc (fam : RewardFamily) (μ : Fin 2 → ℝ) {n : ℕ} (s : Fin n → V fam) (v : V fam) :
    Lk fam μ (Fin.snoc (α := fun _ => V fam) s v) = Lk fam μ s * fam.D (μ 0) {(v : ℝ)} := by
  simp only [Lk, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

lemma gap_snoc_sum (P : Measure (Fin 2 → ℝ)) [IsFiniteMeasure P] (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) {n : ℕ} (s : Fin n → V fam) :
    ∑ v : V fam, gap P F fam (Fin.snoc (α := fun _ => V fam) s v) = gap P F fam s := by
  simp only [gap, Lk_snoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [← mul_assoc, ENNReal.toReal_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_D_toReal, mul_one]

lemma posterior_singleton (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) {t : ℕ} (H : BanditHistory 2 t) (μ : Fin 2 → ℝ) (hμ : μ ∈ F) :
    IntroBandits.posterior P F fam H {μ} = P {μ} * likelihood fam μ H / evidence P F fam H := by
  classical
  simp only [IntroBandits.posterior, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single μ]
  · rw [Measure.dirac_apply_of_mem (Set.mem_singleton μ), mul_one]
  · intro b _ hb
    rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem (by simpa using hb)]
    simp
  · intro h; exact absurd hμ h

lemma likelihood_zs (fam : RewardFamily) (μ : Fin 2 → ℝ) {n : ℕ} (s : Fin n → V fam) :
    likelihood fam μ (zs s) = Lk fam μ s := rfl

lemma greedy_step (P : Measure (Fin 2 → ℝ)) [IsFiniteMeasure P] (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) {π : BanditPolicy 2} (hπ : IsGreedy P F fam π) {n : ℕ}
    (s : Fin n → V fam) (hg : 0 < gap P F fam s) : π.select n (zs s) {0} = 1 := by
  classical
  have hev : evidence P F fam (zs s) ≠ 0 := by
    intro h0
    simp only [evidence, likelihood_zs, Finset.sum_eq_zero_iff] at h0
    have : gap P F fam s = 0 := by
      refine Finset.sum_eq_zero fun μ hμ => ?_
      rw [h0 μ hμ]; simp
    linarith
  have hevt : evidence P F fam (zs s) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun μ _ => ENNReal.mul_ne_top (measure_ne_top _ _) (Lk_ne_top _ _ _)
  have hpos : 0 < (evidence P F fam (zs s)).toReal := ENNReal.toReal_pos hev hevt
  have hdiff : postMean P F fam (zs s) 0 - postMean P F fam (zs s) 1 =
      gap P F fam s / (evidence P F fam (zs s)).toReal := by
    simp only [postMean, gap]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [posterior_singleton P F fam _ μ hμ, likelihood_zs, ENNReal.toReal_div]
    ring
  have hlt : postMean P F fam (zs s) 1 < postMean P F fam (zs s) 0 := by
    have : 0 < gap P F fam s / (evidence P F fam (zs s)).toReal := div_pos hg hpos
    linarith
  have h1 := hπ n (zs s) hev
  have hsub : {a : Fin 2 | ∀ b, postMean P F fam (zs s) b ≤ postMean P F fam (zs s) a} ⊆
      ({0} : Set (Fin 2)) := by
    intro a ha
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with h | h
    · simp [h]
    · exfalso
      have := ha 0
      rw [h] at this
      linarith
  exact le_antisymm prob_le_one (h1 ▸ measure_mono hsub)

lemma Ssum_succ (P : Measure (Fin 2 → ℝ)) [IsFiniteMeasure P] (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) {π : BanditPolicy 2} (hπ : IsGreedy P F fam π) (n : ℕ) :
    Ssum P F fam π n ≤ Ssum P F fam π (n+1) := by
  simp only [Ssum]
  rw [← (snocE fam n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun s _ => ?_
  have hw : ∀ v, wt fam π (n+1) ((snocE fam n) (s, v)) =
      wt fam π n s * π.select n (zs s) {0} := by
    intro v
    simp only [snocE, Equiv.coe_fn_mk, wt, Fin.init_snoc]
  simp only [hw, ENNReal.toReal_mul]
  have hg : ∑ v : V fam, gap P F fam ((snocE fam n) (s, v)) = gap P F fam s :=
    gap_snoc_sum P F fam s
  rw [← Finset.mul_sum, hg]
  have hw0 : 0 ≤ (wt fam π n s).toReal := ENNReal.toReal_nonneg
  by_cases hpos : 0 < gap P F fam s
  · rw [greedy_step P F fam hπ s hpos, ENNReal.toReal_one, mul_one]
  · have hq1 : (π.select n (zs s) {0}).toReal ≤ 1 := by
      have := prob_le_one (μ := π.select n (zs s)) (s := {0})
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have hq0 : 0 ≤ (π.select n (zs s) {0}).toReal := ENNReal.toReal_nonneg
    have hle : gap P F fam s ≤ (π.select n (zs s) {0}).toReal * gap P F fam s := by
      nlinarith
    calc (wt fam π n s).toReal * gap P F fam s
        ≤ (wt fam π n s).toReal * ((π.select n (zs s) {0}).toReal * gap P F fam s) :=
          mul_le_mul_of_nonneg_left hle hw0
      _ = _ := by ring

lemma Ssum_zero (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (π : BanditPolicy 2) : Ssum P F fam π 0 = priorMean P F 0 - priorMean P F 1 := by
  simp only [Ssum, Fintype.sum_unique, wt, ENNReal.toReal_one, one_mul, gap, Lk,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one, priorMean]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

end P2Mf9

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem solution (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    {π : BanditPolicy 2} (hπ : IsGreedy P F fam π) (T : ℕ) :
    ENNReal.ofReal (priorMean P F 0 - priorMean P F 1) ≤
      jointMeasure P F fam π T (Set.univ ×ˢ {h | ∀ t, (h t).1 = 0}) := by
  classical
  have hX : jointMeasure P F fam π T (Set.univ ×ˢ {h | ∀ t, (h t).1 = 0}) =
      ∑ μ ∈ F, P {μ} * ∑ s, P2Mf9.wt fam π T s * P2Mf9.Lk fam μ s := by
    simp only [jointMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.prod_prod, measure_univ, one_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    have hZ : {h : BanditHistory 2 T | ∀ t, (h t).1 = 0} = P2Mf9.Zset T := rfl
    rw [hZ, ← Measure.restrict_apply_univ, P2Mf9.key fam π T μ]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rfl
  have hfin : ∀ μ (s : Fin T → P2Mf9.V fam), P {μ} * P2Mf9.Lk fam μ s ≠ ⊤ :=
    fun μ s => ENNReal.mul_ne_top (measure_ne_top _ _) (P2Mf9.Lk_ne_top _ _ _)
  have hwt : ∀ s : Fin T → P2Mf9.V fam, P2Mf9.wt fam π T s ≠ ⊤ :=
    fun s => ne_top_of_le_ne_top ENNReal.one_ne_top (P2Mf9.wt_le_one fam π T s)
  have hX' : jointMeasure P F fam π T (Set.univ ×ˢ {h | ∀ t, (h t).1 = 0}) =
      ∑ s, P2Mf9.wt fam π T s * ∑ μ ∈ F, P {μ} * P2Mf9.Lk fam μ s := by
    rw [hX]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun μ _ => ?_
    ring
  have hXt : jointMeasure P F fam π T (Set.univ ×ˢ {h | ∀ t, (h t).1 = 0}) ≠ ⊤ := by
    rw [hX']
    exact ENNReal.sum_ne_top.2 fun s _ => ENNReal.mul_ne_top (hwt s)
      (ENNReal.sum_ne_top.2 fun μ _ => hfin μ s)
  have hmono : Monotone (P2Mf9.Ssum P F fam π) :=
    monotone_nat_of_le_succ fun n => P2Mf9.Ssum_succ P F fam hπ n
  have h0T := hmono (Nat.zero_le T)
  rw [P2Mf9.Ssum_zero] at h0T
  have hTX : P2Mf9.Ssum P F fam π T ≤
      (jointMeasure P F fam π T (Set.univ ×ˢ {h | ∀ t, (h t).1 = 0})).toReal := by
    rw [hX', ENNReal.toReal_sum (fun s _ => ENNReal.mul_ne_top (hwt s)
      (ENNReal.sum_ne_top.2 fun μ _ => hfin μ s))]
    simp only [P2Mf9.Ssum, P2Mf9.gap]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun μ _ => hfin μ s)]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ hμ => ?_) ENNReal.toReal_nonneg
    have h0 := hunit μ hμ 0
    have h1 := hunit μ hμ 1
    have hd : μ 0 - μ 1 ≤ 1 := by
      simp only [Set.mem_Icc] at h0 h1; linarith
    have hn : 0 ≤ (P {μ} * P2Mf9.Lk fam μ s).toReal := ENNReal.toReal_nonneg
    nlinarith
  rw [← ENNReal.ofReal_toReal hXt]
  exact ENNReal.ofReal_le_ofReal (h0T.trans hTX)
