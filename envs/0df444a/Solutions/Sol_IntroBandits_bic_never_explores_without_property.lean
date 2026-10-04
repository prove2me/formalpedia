-- Prove2me | solution 1 for IntroBandits.bic_never_explores_without_property
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:07:02.2076+00:00
-- url     : https://prove2.me/submissions/4bad89de-1a6a-43be-91f0-cf3b601423e0

import Mathlib
import Definitions.Def_IntroBandits_Agents

set_option autoImplicit false

namespace P2M6b

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

lemma bm_marg (ν : StochasticBandit 2) (π : BanditPolicy 2) (t : ℕ) (a : Fin 2) :
    ∀ (n : ℕ) (htn : t < n), banditMeasure ν π n {h | (h ⟨t, htn⟩).1 = a} =
      banditMeasure ν π (t+1) {h | (h (Fin.last t)).1 = a} := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro htn
    rcases Nat.lt_succ_iff_lt_or_eq.1 htn with h | h
    · rw [bm_succ, Measure.map_apply measurable_banditHistorySnoc (measurableSet_arm _ _)]
      have hset : (fun p : BanditHistory 2 n × (Fin 2 × ℝ) ↦
          Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) p.1 p.2) ⁻¹' {h' | (h' ⟨t, htn⟩).1 = a} =
          Prod.fst ⁻¹' {h' : BanditHistory 2 n | (h' ⟨t, h⟩).1 = a} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        have : (⟨t, htn⟩ : Fin (n+1)) = Fin.castSucc ⟨t, h⟩ := rfl
        rw [this, Fin.snoc_castSucc]
      rw [hset, ← Measure.fst_apply (measurableSet_arm _ _), Measure.fst_compProd, ih h]
    · subst h; rfl

lemma bm_last (ν : StochasticBandit 2) (π : BanditPolicy 2) (t : ℕ) (a : Fin 2) :
    banditMeasure ν π (t+1) {h | (h (Fin.last t)).1 = a} =
      ∫⁻ h, π.select t h {a} ∂(banditMeasure ν π t) := by
  rw [bm_succ, Measure.map_apply measurable_banditHistorySnoc (measurableSet_arm _ _),
    Measure.compProd_apply (measurable_banditHistorySnoc (measurableSet_arm _ _))]
  refine lintegral_congr fun h => ?_
  rw [banditStepKernel, Kernel.compProd_apply
    (measurable_prodMk_left (measurable_banditHistorySnoc (measurableSet_arm _ _))),
    lintegral_fintype, Fin.sum_univ_two]
  rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with ha | ha <;> subst ha
  · have e0 : Prod.mk (0 : Fin 2) ⁻¹' (Prod.mk h ⁻¹' ((fun p : BanditHistory 2 t × (Fin 2 × ℝ) ↦
        Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) p.1 p.2) ⁻¹'
          {h' | (h' (Fin.last t)).1 = 0})) = Set.univ := by
      ext r; simp [Fin.snoc_last]
    have e1 : Prod.mk (1 : Fin 2) ⁻¹' (Prod.mk h ⁻¹' ((fun p : BanditHistory 2 t × (Fin 2 × ℝ) ↦
        Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) p.1 p.2) ⁻¹'
          {h' | (h' (Fin.last t)).1 = 0})) = ∅ := by
      ext r; simp [Fin.snoc_last]
    rw [e0, e1]; simp
  · have e0 : Prod.mk (0 : Fin 2) ⁻¹' (Prod.mk h ⁻¹' ((fun p : BanditHistory 2 t × (Fin 2 × ℝ) ↦
        Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) p.1 p.2) ⁻¹'
          {h' | (h' (Fin.last t)).1 = 1})) = ∅ := by
      ext r; simp [Fin.snoc_last]
    have e1 : Prod.mk (1 : Fin 2) ⁻¹' (Prod.mk h ⁻¹' ((fun p : BanditHistory 2 t × (Fin 2 × ℝ) ↦
        Fin.snoc (α := fun _ ↦ Fin 2 × ℝ) p.1 p.2) ⁻¹'
          {h' | (h' (Fin.last t)).1 = 1})) = Set.univ := by
      ext r; simp [Fin.snoc_last]
    rw [e0, e1]; simp

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

lemma key (fam : RewardFamily) (π : BanditPolicy 2) (n : ℕ) :
    ∃ w : (Fin n → V fam) → ENNReal, (∀ s, w s ≤ 1) ∧ ∀ μ : Fin 2 → ℝ,
      (banditMeasure (instanceOf fam μ) π n).restrict (Zset n) =
        ∑ s, (w s * ∏ i, fam.D (μ 0) {((s i : V fam) : ℝ)}) • Measure.dirac (zs s) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => le_rfl, fun μ => ?_⟩
    have hZ : Zset 0 = Set.univ := by
      ext h; simp [Zset]
    rw [hZ, Measure.restrict_univ, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, one_smul]
    have : zs (default : Fin 0 → V fam) = fun t => t.elim0 := funext fun i => i.elim0
    rw [this]
    rfl
  | succ n ih =>
    obtain ⟨w, hw1, hw⟩ := ih
    refine ⟨fun s' => w (Fin.init s') * π.select n (zs (Fin.init s')) {0},
      fun s' => mul_le_one' (hw1 _) prob_le_one, fun μ => ?_⟩
    ext S hS
    have hSZ : MeasurableSet (S ∩ Zset (n+1)) := hS.inter (measurableSet_Zset _)
    rw [Measure.restrict_apply hS, bm_succ, Measure.map_apply measurable_banditHistorySnoc hSZ,
      Measure.compProd_apply (measurable_banditHistorySnoc hSZ),
      ← setLIntegral_eq_of_support_subset (s := Zset n), hw μ]
    · simp only [lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac,
        smul_eq_mul, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
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
      simp only [snocE, Equiv.coe_fn_mk, Fin.init_snoc, Fin.prod_univ_castSucc,
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

end P2M6b

open MeasureTheory ProbabilityTheory BanditAlgorithm IntroBandits in
theorem solution (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    (hno : ¬ PriorAllowsExploration P F fam) {T : ℕ} {π : BanditPolicy 2}
    (hπ : IsStrictlyBIC F (jointMeasure P F fam π T) (fun h t ↦ (h t).1)) :
    ∀ t : Fin T, jointMeasure P F fam π T (Set.univ ×ˢ {h | (h t).1 = 1}) = 0 := by
  classical
  obtain ⟨_, hstrict⟩ := hπ
  have hno' : ∀ (n : ℕ) (s : Fin n → ℝ), gapNumerator P F fam s ≤ 0 := by
    intro n s
    by_contra h
    exact hno ⟨n, s, lt_of_not_ge h⟩
  have hjU : ∀ (E : Set (BanditHistory 2 T)), jointMeasure P F fam π T (Set.univ ×ˢ E) =
      ∑ μ ∈ F, P {μ} * banditMeasure (instanceOf fam μ) π T E := by
    intro E
    simp only [jointMeasure, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.prod_prod, measure_univ, one_mul]
  have hjS : ∀ (E : Set (BanditHistory 2 T)), ∀ μ ∈ F,
      jointMeasure P F fam π T ({μ} ×ˢ E) = P {μ} * banditMeasure (instanceOf fam μ) π T E := by
    intro E μ hμ
    simp only [jointMeasure, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.prod_prod]
    rw [Finset.sum_eq_single μ]
    · rw [Measure.dirac_apply_of_mem (Set.mem_singleton μ), one_mul]
    · intro b _ hb
      rw [Measure.dirac_apply' _ (measurableSet_singleton _),
        Set.indicator_of_notMem (by simpa using hb)]
      simp
    · intro h; exact absurd hμ h
  have main : ∀ k (hk : k < T),
      jointMeasure P F fam π T (Set.univ ×ˢ {h | (h ⟨k, hk⟩).1 = 1}) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    by_contra hne
    have hpos := hstrict ⟨k, hk⟩ hne
    obtain ⟨w, hw1, hw⟩ := P2M6b.key fam π k
    have hX : ∀ μ ∈ F, jointMeasure P F fam π T ({μ} ×ˢ {h | (h ⟨k, hk⟩).1 = 1}) =
        P {μ} * ∑ s, w s * (∏ i, fam.D (μ 0) {((s i : P2M6b.V fam) : ℝ)}) *
          π.select k (P2M6b.zs s) {1} := by
      intro μ hμ
      rw [hjS _ μ hμ]
      by_cases hP : P {μ} = 0
      · simp [hP]
      congr 1
      have hprev : ∀ j (hj : j < k),
          banditMeasure (instanceOf fam μ) π k {h | (h ⟨j, hj⟩).1 = 1} = 0 := by
        intro j hj
        have h0 := ih j hj (hj.trans hk)
        rw [hjU] at h0
        have := (Finset.sum_eq_zero_iff.1 h0) μ hμ
        rw [mul_eq_zero] at this
        rcases this with h | h
        · exact absurd h hP
        · rw [P2M6b.bm_marg _ _ j 1 T (hj.trans hk)] at h
          rw [P2M6b.bm_marg _ _ j 1 k hj]
          exact h
      have hZc : banditMeasure (instanceOf fam μ) π k (P2M6b.Zset k)ᶜ = 0 := by
        have : (P2M6b.Zset k)ᶜ = ⋃ j : Fin k, {h : BanditHistory 2 k | (h j).1 = 1} := by
          ext h
          simp only [P2M6b.Zset, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, Set.mem_iUnion]
          refine exists_congr fun j => ?_
          generalize (h j).1 = x
          fin_cases x <;> simp
        rw [this]
        exact measure_iUnion_null fun j => hprev j.val j.isLt
      have hres : (banditMeasure (instanceOf fam μ) π k).restrict (P2M6b.Zset k) =
          banditMeasure (instanceOf fam μ) π k :=
        Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hZc)
      rw [P2M6b.bm_marg _ _ k 1 T hk, P2M6b.bm_last, ← hres, hw μ]
      simp only [lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac,
        smul_eq_mul]
    have hfin : ∀ (μ : Fin 2 → ℝ) (s : Fin k → P2M6b.V fam),
        w s * (∏ i, fam.D (μ 0) {((s i : P2M6b.V fam) : ℝ)}) * π.select k (P2M6b.zs s) {1} ≠ ⊤ := by
      intro μ s
      refine ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 s)) ?_) (measure_ne_top _ _)
      exact ENNReal.prod_ne_top fun i _ => measure_ne_top _ _
    have hrw : ∀ μ ∈ F, (μ 1 - μ 0) *
        (jointMeasure P F fam π T ({μ} ×ˢ {h | (h ⟨k, hk⟩).1 = 1})).toReal =
        ∑ s, ((w s).toReal * (π.select k (P2M6b.zs s) {1}).toReal) *
          ((P {μ} * ∏ i, fam.D (μ 0) {((s i : P2M6b.V fam) : ℝ)}).toReal * (μ 1 - μ 0)) := by
      intro μ hμ
      rw [hX μ hμ, ENNReal.toReal_mul, ENNReal.toReal_sum (fun s _ => hfin μ s),
        Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [ENNReal.toReal_mul]
      ring
    have hle : ∑ μ ∈ F, (μ 1 - μ 0) *
        (jointMeasure P F fam π T ({μ} ×ˢ {h | (h ⟨k, hk⟩).1 = 1})).toReal ≤ 0 := by
      rw [Finset.sum_congr rfl hrw, Finset.sum_comm]
      refine Finset.sum_nonpos fun s _ => ?_
      rw [← Finset.mul_sum]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (hno' k (fun i => ((s i : P2M6b.V fam) : ℝ)))
    exact absurd hpos (not_lt.2 hle)
  intro t
  exact main t.val t.isLt
