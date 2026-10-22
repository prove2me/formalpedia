-- Prove2me | solution 2 for MDPFinance.Semicontinuous.measurable_maximizer_existence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:41:00.541257+00:00
-- url     : https://prove2.me/submissions/728aad71-49d8-4441-988c-1b0fec95dedd

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_StructureAssumption
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous


namespace MDPFinance.Semicontinuous

open Filter Topology Set PiNat

namespace MDPSel

/-- one lexicographic step -/
def stepK {E A : Type*} (φ : A → ℝ) (K : E → Set A) (x : E) : Set A :=
  {a | a ∈ K x ∧ ∀ b ∈ K x, φ a ≤ φ b}

lemma stepK_props {E A : Type*} [MeasurableSpace E] [TopologicalSpace A] [T2Space A]
    (φ : A → ℝ) (hφ : Continuous φ) (K : E → Set A)
    (hK : ∀ x, IsCompact (K x)) (hne : ∀ x, (K x).Nonempty)
    (hm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty}) :
    (∀ x, IsCompact (stepK φ K x)) ∧ (∀ x, (stepK φ K x).Nonempty) ∧
    (∀ F, IsClosed F → MeasurableSet {x | (stepK φ K x ∩ F).Nonempty}) := by
  have hcl : ∀ x, IsClosed (stepK φ K x) := by
    intro x
    have : stepK φ K x = K x ∩ ⋂ b ∈ K x, {a | φ a ≤ φ b} := by
      ext a; simp [stepK]
    rw [this]
    exact (hK x).isClosed.inter (isClosed_biInter fun b _ => isClosed_le hφ continuous_const)
  refine ⟨fun x => (hK x).of_isClosed_subset (hcl x) (fun a ha => ha.1), fun x => ?_, ?_⟩
  · obtain ⟨a, ha, hmin⟩ := (hK x).exists_isMinOn (hne x) hφ.continuousOn
    exact ⟨a, ha, fun b hb => hmin hb⟩
  · intro F hF
    -- characterization
    have key : {x | (stepK φ K x ∩ F).Nonempty} =
        ⋂ j : ℕ, ⋂ q : ℚ, ({x | (K x ∩ {a | φ a ≤ q}).Nonempty}ᶜ ∪
          {x | (K x ∩ (F ∩ {a | φ a ≤ (q : ℝ) + 1 / ((j : ℝ) + 1)})).Nonempty}) := by
      ext x
      simp only [mem_setOf_eq, mem_iInter, mem_union, mem_compl_iff]
      constructor
      · rintro ⟨a, ⟨haK, hamin⟩, haF⟩ j q
        by_cases h : (K x ∩ {a | φ a ≤ q}).Nonempty
        · right
          obtain ⟨b, hbK, hbq⟩ := h
          refine ⟨a, haK, haF, ?_⟩
          have := hamin b hbK
          simp only [mem_setOf_eq] at hbq ⊢
          have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
          linarith
        · left; exact h
      · intro H
        obtain ⟨a0, ha0, hmin0⟩ := (hK x).exists_isMinOn (hne x) hφ.continuousOn
        obtain ⟨q0, hq0⟩ := exists_rat_gt (φ a0)
        have hKF : (K x ∩ F).Nonempty := by
          rcases H 0 q0 with h | h
          · exact absurd ⟨a0, ha0, hq0.le⟩ h
          · obtain ⟨a, haK, haF, _⟩ := h
            exact ⟨a, haK, haF⟩
        obtain ⟨b, ⟨hbK, hbF⟩, hbmin⟩ :=
          ((hK x).inter_right hF).exists_isMinOn hKF hφ.continuousOn
        refine ⟨b, ⟨hbK, fun c hc => ?_⟩, hbF⟩
        have hc0 : φ a0 ≤ φ c := hmin0 hc
        suffices φ b ≤ φ a0 by linarith
        by_contra hlt
        push_neg at hlt
        obtain ⟨j, hj⟩ := exists_nat_gt (2 / (φ b - φ a0))
        have hpos : 0 < φ b - φ a0 := by linarith
        have hj' : 2 / ((j:ℝ) + 1) < φ b - φ a0 := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hj
          nlinarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show φ a0 < φ a0 + 1 / ((j:ℝ) + 1) by
          have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
          linarith)
        rcases H j q with h | h
        · exact h ⟨a0, ha0, hq1.le⟩
        · obtain ⟨c, hcK, hcF, hcq⟩ := h
          have := hbmin ⟨hcK, hcF⟩
          simp only [mem_setOf_eq] at hcq this
          have e : 2 / ((j:ℝ) + 1) = 1 / ((j:ℝ) + 1) + 1 / ((j:ℝ) + 1) := by ring
          linarith
    rw [key]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun q => ?_
    exact (hm _ (isClosed_le hφ continuous_const)).compl.union
      (hm _ (hF.inter (isClosed_le hφ continuous_const)))

def iterK {E A : Type*} (φ : ℕ → A → ℝ) (K : E → Set A) : ℕ → E → Set A
  | 0 => K
  | i + 1 => stepK (φ i) (iterK φ K i)

theorem select {E A : Type*} [MeasurableSpace E] [TopologicalSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (K : E → Set A) (hK : ∀ x, IsCompact (K x)) (hne : ∀ x, (K x).Nonempty)
    (hm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty}) :
    ∃ f : E → A, Measurable f ∧ ∀ x, f x ∈ K x := by
  by_cases hE : Nonempty E
  swap
  · refine ⟨fun x => (hE ⟨x⟩).elim, ?_, fun x => (hE ⟨x⟩).elim⟩
    exact fun s _ => by
      have : (fun x : E => (hE ⟨x⟩).elim : E → A) ⁻¹' s = ∅ := by
        ext x; exact (hE ⟨x⟩).elim
      rw [this]; exact MeasurableSet.empty
  obtain ⟨x0⟩ := hE
  haveI : Nonempty A := ⟨(hne x0).some⟩
  letI := TopologicalSpace.metrizableSpaceMetric A
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  let φ : ℕ → A → ℝ := fun i a => dist a (d i)
  have hφc : ∀ i, Continuous (φ i) := fun i => continuous_id.dist continuous_const
  have hsep : ∀ a b : A, (∀ i, φ i a = φ i b) → a = b := by
    intro a b h
    have : ∀ ε > 0, dist a b < ε := by
      intro ε hε
      obtain ⟨i, hi⟩ := hd.exists_dist_lt a (half_pos hε)
      have h1 := h i
      simp only [φ] at h1
      calc dist a b ≤ dist a (d i) + dist (d i) b := dist_triangle _ _ _
        _ = dist a (d i) + dist a (d i) := by rw [dist_comm (d i) b, ← h1]
        _ < ε := by have := dist_comm a (d i); linarith
    exact dist_le_zero.1 (le_of_forall_gt_imp_ge_of_dense fun ε hε => (this ε hε).le) |> fun h => h
  have P : ∀ i, (∀ x, IsCompact (iterK φ K i x)) ∧ (∀ x, (iterK φ K i x).Nonempty) ∧
      (∀ F, IsClosed F → MeasurableSet {x | (iterK φ K i x ∩ F).Nonempty}) := by
    intro i
    induction i with
    | zero => exact ⟨hK, hne, hm⟩
    | succ i ih => exact stepK_props (φ i) (hφc i) _ ih.1 ih.2.1 ih.2.2
  have hsub : ∀ x i, iterK φ K (i + 1) x ⊆ iterK φ K i x := fun x i a ha => ha.1
  have hinter : ∀ x F, IsClosed F → (∀ i, (iterK φ K i x ∩ F).Nonempty) →
      (⋂ i, (iterK φ K i x ∩ F)).Nonempty := by
    intro x F hF h
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro i; exact inter_subset_inter_left _ (hsub x i)
    · exact h
    · exact ((P 0).1 x).inter_right hF
    · intro i; exact ((P i).1 x).isClosed.inter hF
  have huniq : ∀ x a b, (∀ i, a ∈ iterK φ K i x) → (∀ i, b ∈ iterK φ K i x) → a = b := by
    intro x a b ha hb
    apply hsep
    intro i
    exact le_antisymm ((ha (i+1)).2 b (hb i)) ((hb (i+1)).2 a (ha i))
  have hex : ∀ x, ∃ a, ∀ i, a ∈ iterK φ K i x := by
    intro x
    obtain ⟨a, ha⟩ := hinter x univ isClosed_univ (fun i => by simpa using (P i).2.1 x)
    exact ⟨a, fun i => (mem_iInter.1 ha i).1⟩
  choose f hf using hex
  refine ⟨f, ?_, fun x => hf x 0⟩
  apply measurable_of_isClosed
  intro F hF
  have : f ⁻¹' F = ⋂ i, {x | (iterK φ K i x ∩ F).Nonempty} := by
    ext x
    simp only [mem_preimage, mem_iInter, mem_setOf_eq]
    constructor
    · intro h i; exact ⟨f x, hf x i, h⟩
    · intro h
      obtain ⟨a, ha⟩ := hinter x F hF h
      have ha' : ∀ i, a ∈ iterK φ K i x ∩ F := fun i => mem_iInter.1 ha i
      have : a = f x := huniq x a (f x) (fun i => (ha' i).1) (hf x)
      rw [← this]; exact (ha' 0).2
  rw [this]
  exact MeasurableSet.iInter fun i => (P i).2.2 F hF

end MDPSel


namespace NovikovSep

variable {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]

/-- A countable family of sets is (Borel-)separated if it is covered by a family of measurable
sets with empty intersection. -/
def Sep (S : ℕ → Set α) : Prop :=
  ∃ B : ℕ → Set α, (∀ n, MeasurableSet (B n)) ∧ (∀ n, S n ⊆ B n) ∧ ⋂ n, B n = ∅

lemma sep_union {S : ℕ → Set α} {k : ℕ} {S' : ℕ → Set α} (hS : S k = ⋃ i, S' i)
    (h : ∀ i, Sep (Function.update S k (S' i))) : Sep S := by
  choose B hBm hBs hBi using h
  refine ⟨fun n => if n = k then ⋃ i, B i k else ⋂ i, B i n, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs
    · exact MeasurableSet.iUnion fun i => hBm i k
    · exact MeasurableSet.iInter fun i => hBm i n
  · intro n
    dsimp only
    split_ifs with hn
    · subst hn
      rw [hS]
      refine iUnion_mono fun i => ?_
      have := hBs i n
      simpa using this
    · refine subset_iInter fun i => ?_
      have := hBs i n
      simpa [Function.update_of_ne hn] using this
  · ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hx
    have hk := hx k
    simp only [if_true] at hk
    obtain ⟨i, hi⟩ := mem_iUnion.1 hk
    have : x ∈ ⋂ n, B i n := by
      refine mem_iInter.2 fun n => ?_
      by_cases hn : n = k
      · subst hn; exact hi
      · have := hx n
        simp only [hn, if_false] at this
        exact mem_iInter.1 this i
    rw [hBi i] at this
    exact this

theorem novikov_range {f : ℕ → (ℕ → ℕ) → α} (hf : ∀ k, Continuous (f k))
    (h : ⋂ k, range (f k) = ∅) : Sep (fun k => range (f k)) := by
  by_contra hcon
  let Fam : (ℕ → ℕ) → (ℕ → ℕ → ℕ) → ℕ → Set α := fun ℓ s k => f k '' cylinder (s k) (ℓ k)
  have I : ∀ (ℓ : ℕ → ℕ) (s : ℕ → ℕ → ℕ) (k : ℕ), ¬ Sep (Fam ℓ s) →
      ∃ s' : ℕ → ℕ, s' ∈ cylinder (s k) (ℓ k) ∧
        ¬ Sep (Fam (Function.update ℓ k (ℓ k + 1)) (Function.update s k s')) := by
    intro ℓ s k hns
    by_contra H
    push_neg at H
    apply hns
    apply sep_union (k := k)
      (S' := fun i => f k '' cylinder (Function.update (s k) (ℓ k) i) (ℓ k + 1))
    · show f k '' cylinder (s k) (ℓ k) = ⋃ i, f k '' cylinder (Function.update (s k) (ℓ k) i) (ℓ k + 1)
      rw [← image_iUnion, ← iUnion_cylinder_update]
    · intro i
      have := H (Function.update (s k) (ℓ k) i) (update_mem_cylinder _ _ _)
      convert this using 1
      funext n
      by_cases hn : n = k
      · subst hn; simp [Fam]
      · simp [Fam, Function.update_of_ne hn]
  let St := {p : ℕ × (ℕ → ℕ) × (ℕ → ℕ → ℕ) // ¬ Sep (Fam p.2.1 p.2.2)}
  have step : ∀ p : St, ∃ q : St, q.1.1 = p.1.1 + 1 ∧
      q.1.2.1 = Function.update p.1.2.1 (Nat.unpair p.1.1).1
        (p.1.2.1 (Nat.unpair p.1.1).1 + 1) ∧
      ∃ s', s' ∈ cylinder (p.1.2.2 (Nat.unpair p.1.1).1) (p.1.2.1 (Nat.unpair p.1.1).1) ∧
        q.1.2.2 = Function.update p.1.2.2 (Nat.unpair p.1.1).1 s' := by
    rintro ⟨⟨m, ℓ, s⟩, hp⟩
    obtain ⟨s', hs', hns⟩ := I ℓ s (Nat.unpair m).1 hp
    exact ⟨⟨⟨m + 1, _, _⟩, hns⟩, rfl, rfl, s', hs', rfl⟩
  choose F hFm hFl hFs using step
  have h0 : Fam (fun _ => 0) (fun _ _ => 0) = fun k => range (f k) := by
    funext k; simp [Fam, cylinder_zero]
  let p0 : St := ⟨⟨0, fun _ => 0, fun _ _ => 0⟩, h0 ▸ hcon⟩
  let p : ℕ → St := fun n => F^[n] p0
  have prec : ∀ n, p (n + 1) = F (p n) := fun n => by
    simp only [p, Function.iterate_succ', Function.comp]
  have pm : ∀ m, (p m).1.1 = m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [prec, hFm, ih]
  -- notation
  let ℓ : ℕ → ℕ → ℕ := fun m => (p m).1.2.1
  let s : ℕ → ℕ → ℕ → ℕ := fun m => (p m).1.2.2
  have hl_succ : ∀ m k, ℓ (m + 1) k = if k = (Nat.unpair m).1 then ℓ m k + 1 else ℓ m k := by
    intro m k
    simp only [ℓ]
    rw [prec, hFl, pm]
    by_cases hk : k = (Nat.unpair m).1
    · subst hk; simp
    · simp [Function.update_of_ne hk, hk]
  have hl_mono : ∀ m k, ℓ m k ≤ ℓ (m + 1) k := by
    intro m k
    rw [hl_succ]
    split_ifs <;> omega
  have hl_mono' : ∀ k m m', m ≤ m' → ℓ m k ≤ ℓ m' k := by
    intro k m m' hmm
    induction hmm with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hl_mono _ _)
  have hs_succ : ∀ m k, s (m + 1) k ∈ cylinder (s m k) (ℓ m k) := by
    intro m k
    obtain ⟨s', hs', hq⟩ := hFs (p m)
    rw [pm] at hs' hq
    simp only [s, ℓ]
    rw [prec, hq]
    by_cases hk : k = (Nat.unpair m).1
    · subst hk; simpa using hs'
    · rw [Function.update_of_ne hk]; exact self_mem_cylinder _ _
  have hs_stab : ∀ k m m', m ≤ m' → s m' k ∈ cylinder (s m k) (ℓ m k) := by
    intro k m m' hmm
    induction hmm with
    | refl => exact self_mem_cylinder _ _
    | @step m' hle ih =>
      have h1 := hs_succ m' k
      have h2 : cylinder (s m' k) (ℓ m k) = cylinder (s m k) (ℓ m k) := mem_cylinder_iff_eq.1 ih
      rw [← h2]
      exact cylinder_anti _ (hl_mono' k m m' hle) h1
  have hl_unb : ∀ k L, ∃ m, L ≤ ℓ m k := by
    intro k L
    have key : ∀ j, j + 1 ≤ ℓ (Nat.pair k j + 1) k := by
      intro j
      induction j with
      | zero => rw [hl_succ, Nat.unpair_pair, if_pos (by rfl)]; omega
      | succ j ih =>
        rw [hl_succ, Nat.unpair_pair, if_pos (by rfl)]
        have := hl_mono' k (Nat.pair k j + 1) (Nat.pair k (j + 1))
          (Nat.pair_lt_pair_right k (Nat.lt_succ_self j))
        omega
    exact ⟨Nat.pair k L + 1, (key L).trans' (by omega)⟩
  have hM : ∀ k i, ∃ m, i + 1 ≤ ℓ m k := fun k i => hl_unb k (i + 1)
  choose Mf hMf using hM
  let x : ℕ → ℕ → ℕ := fun k i => s (Mf k i) k i
  have hx : ∀ m k, s m k ∈ cylinder (x k) (ℓ m k) := by
    intro m k
    rw [mem_cylinder_iff]
    intro i hi
    have h1 := hs_stab k m (max m (Mf k i)) (le_max_left _ _)
    have h2 := hs_stab k (Mf k i) (max m (Mf k i)) (le_max_right _ _)
    rw [mem_cylinder_iff] at h1 h2
    simp only [x]
    rw [← h1 i hi, ← h2 i (by have := hMf k i; omega)]
  have M' : ∀ m, ¬ Sep (fun k => f k '' cylinder (x k) (ℓ m k)) := by
    intro m
    have := (p m).2
    convert this using 2
    funext k
    show f k '' cylinder (x k) (ℓ m k) = f k '' cylinder (s m k) (ℓ m k)
    rw [mem_cylinder_iff_eq.1 (hx m k)]
  let y : ℕ → α := fun k => f k (x k)
  have hy : ∃ k, y 0 ≠ y k := by
    by_contra H
    push_neg at H
    have : y 0 ∈ ⋂ k, range (f k) := mem_iInter.2 fun k => H k ▸ mem_range_self _
    rw [h] at this
    exact this
  obtain ⟨k, hk⟩ := hy
  have hk0 : k ≠ 0 := by rintro rfl; exact hk rfl
  obtain ⟨u, v, u_open, v_open, xu, yv, huv⟩ := t2_separation hk
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  obtain ⟨εx, εxpos, hεx⟩ : ∃ εx > 0, Metric.ball (x 0) εx ⊆ f 0 ⁻¹' u :=
    Metric.mem_nhds_iff.1 ((hf 0).continuousAt.preimage_mem_nhds (u_open.mem_nhds xu))
  obtain ⟨εy, εypos, hεy⟩ : ∃ εy > 0, Metric.ball (x k) εy ⊆ f k ⁻¹' v :=
    Metric.mem_nhds_iff.1 ((hf k).continuousAt.preimage_mem_nhds (v_open.mem_nhds yv))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < min εx εy :=
    exists_pow_lt_of_lt_one (lt_min εxpos εypos) (by norm_num)
  obtain ⟨m1, hm1⟩ := hl_unb 0 n
  obtain ⟨m2, hm2⟩ := hl_unb k n
  have hn1 : n ≤ ℓ (max m1 m2) 0 := hm1.trans (hl_mono' 0 m1 _ (le_max_left _ _))
  have hn2 : n ≤ ℓ (max m1 m2) k := hm2.trans (hl_mono' k m2 _ (le_max_right _ _))
  apply M' (max m1 m2)
  refine ⟨fun j => if j = 0 then u else if j = k then v else univ, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    exacts [u_open.measurableSet, v_open.measurableSet, MeasurableSet.univ]
  · intro j
    dsimp only
    by_cases hj0 : j = 0
    · subst hj0
      simp only [if_true]
      rw [image_subset_iff]
      refine Subset.trans ?_ hεx
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      have : (1 / 2 : ℝ) ^ (ℓ (max m1 m2) 0) ≤ (1 / 2) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1
      exact (hz.trans this).trans_lt (hn.trans_le (min_le_left _ _))
    by_cases hjk : j = k
    · subst hjk
      simp only [hj0, if_false, if_true]
      rw [image_subset_iff]
      refine Subset.trans ?_ hεy
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      have : (1 / 2 : ℝ) ^ (ℓ (max m1 m2) j) ≤ (1 / 2) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
      exact (hz.trans this).trans_lt (hn.trans_le (min_le_right _ _))
    · simp [hj0, hjk]
  · ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hz
    have h1 := hz 0
    have h2 := hz k
    simp only [if_true, hk0, if_false] at h1 h2
    exact Set.disjoint_left.1 huv h1 h2

theorem novikov_analytic {A : ℕ → Set α} (hA : ∀ k, AnalyticSet (A k)) (h : ⋂ k, A k = ∅) :
    ∃ B : ℕ → Set α, (∀ k, MeasurableSet (B k)) ∧ (∀ k, A k ⊆ B k) ∧ ⋂ k, B k = ∅ := by
  by_cases hne : ∃ k, A k = ∅
  · obtain ⟨k, hk⟩ := hne
    refine ⟨fun j => if j = k then ∅ else univ, ?_, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs
      exacts [MeasurableSet.empty, MeasurableSet.univ]
    · intro j
      dsimp only
      split_ifs with hj
      · subst hj; rw [hk]
      · exact subset_univ _
    · ext x
      simp only [mem_iInter, mem_empty_iff_false, iff_false]
      intro hx
      have := hx k
      simp at this
  · push_neg at hne
    have : ∀ k, ∃ f : (ℕ → ℕ) → α, Continuous f ∧ range f = A k := by
      intro k
      have := hA k
      rw [AnalyticSet] at this
      exact this.resolve_left (hne k).ne_empty
    choose f hf hfr using this
    have h' : ⋂ k, range (f k) = ∅ := by simpa [hfr] using h
    obtain ⟨B, hBm, hBs, hBi⟩ := novikov_range hf h'
    exact ⟨B, hBm, fun k => (hfr k) ▸ hBs k, hBi⟩

end NovikovSep

namespace ProjBorel

open NovikovSep

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [StandardBorelSpace Y]

lemma analytic_of_measurable {s : Set (X × Y)} (hs : MeasurableSet s) : AnalyticSet s := by
  have := hs.analyticSet_image measurable_id
  simpa using this

lemma analytic_of_measurable' {s : Set X} (hs : MeasurableSet s) : AnalyticSet s := by
  have := hs.analyticSet_image measurable_id
  simpa using this

lemma analytic_proj {s : Set (X × Y)} (hs : MeasurableSet s) : AnalyticSet (Prod.fst '' s) :=
  hs.analyticSet_image measurable_fst

lemma exists_basis_seq : ∃ U : ℕ → Set Y, (∀ n, IsOpen (U n)) ∧
    ∀ (V : Set Y), IsOpen V → ∀ y ∈ V, ∃ n, y ∈ U n ∧ U n ⊆ V := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis Y
  obtain ⟨U, hU⟩ := (hbc.insert ∅).exists_eq_range (insert_nonempty _ _)
  refine ⟨U, fun n => ?_, fun V hV y hy => ?_⟩
  · have : U n ∈ insert ∅ b := hU ▸ mem_range_self n
    rcases mem_insert_iff.1 this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  · obtain ⟨W, hWb, hyW, hWV⟩ := hb.exists_subset_of_mem_open hy hV
    have : W ∈ range U := hU ▸ mem_insert_of_mem _ hWb
    obtain ⟨n, rfl⟩ := this
    exact ⟨n, hyW, hWV⟩

theorem open_sections_decomp {C : Set (X × Y)} (hC : MeasurableSet C)
    (hop : ∀ x, IsOpen {y | (x, y) ∈ C})
    (U : ℕ → Set Y) (hUo : ∀ n, IsOpen (U n))
    (hUb : ∀ V, IsOpen V → ∀ y ∈ V, ∃ n, y ∈ U n ∧ U n ⊆ V) :
    ∃ R : ℕ → Set (X × Y), (∀ n, MeasurableSet (R n)) ∧
      (∀ n, ∀ p ∈ R n, p.2 ∈ U n ∧ ∀ y ∈ U n, (p.1, y) ∈ C) ∧ C ⊆ ⋃ n, R n := by
  let Ac : ℕ → Set X := fun n => Prod.fst '' (Cᶜ ∩ univ ×ˢ U n)
  let S : ℕ → Set (X × Y) := fun n => (Ac n ×ˢ U n) ∪ (univ ×ˢ (U n)ᶜ)
  have hS : ∀ n, AnalyticSet (S n) := by
    intro n
    have hm : MeasurableSet (Cᶜ ∩ univ ×ˢ U n) :=
      hC.compl.inter (MeasurableSet.univ.prod (hUo n).measurableSet)
    have h1 : AnalyticSet (Ac n ×ˢ U n) := by
      have : Ac n ×ˢ U n =
          (fun p : (X × Y) × Y => (p.1.1, p.2)) '' ((Cᶜ ∩ univ ×ˢ U n) ×ˢ U n) := by
        ext ⟨x, y⟩
        simp only [Ac, mem_prod, mem_image, mem_inter_iff, mem_compl_iff, mem_univ, true_and,
          Prod.exists, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨x', y', ⟨hxy', hy'⟩, rfl⟩, hy⟩
          exact ⟨x', y', y, ⟨⟨hxy', hy'⟩, hy⟩, rfl, rfl⟩
        · rintro ⟨x', y', y'', ⟨⟨hxy', hy'⟩, hy⟩, rfl, rfl⟩
          exact ⟨⟨x', y', ⟨hxy', hy'⟩, rfl⟩, hy⟩
      rw [this]
      exact (hm.prod (hUo n).measurableSet).analyticSet_image
        (measurable_fst.fst.prodMk measurable_snd)
    have h2 : AnalyticSet (univ ×ˢ (U n)ᶜ : Set (X × Y)) :=
      analytic_of_measurable (MeasurableSet.univ.prod (hUo n).measurableSet.compl)
    show AnalyticSet ((Ac n ×ˢ U n) ∪ (univ ×ˢ (U n)ᶜ))
    rw [union_eq_iUnion]
    exact AnalyticSet.iUnion fun b => by cases b <;> simpa
  let T : ℕ → Set (X × Y) := fun n => Nat.rec C (fun k _ => S k) n
  have hT0 : T 0 = C := rfl
  have hTs : ∀ n, T (n + 1) = S n := fun n => rfl
  have hTa : ∀ n, AnalyticSet (T n) := by
    intro n
    cases n with
    | zero => exact analytic_of_measurable hC
    | succ n => exact hS n
  have hTi : ⋂ n, T n = ∅ := by
    ext p
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hp
    have hpC : p ∈ C := hp 0
    obtain ⟨n, hn1, hn2⟩ := hUb _ (hop p.1) p.2 hpC
    have hpS : p ∈ S n := hp (n + 1)
    rcases hpS with h | h
    · obtain ⟨⟨x', y'⟩, ⟨hxy', -, hy'⟩, hx'⟩ := h.1
      simp only at hx'
      subst hx'
      exact hxy' (hn2 hy')
    · exact h.2 hn1
  obtain ⟨W, hWm, hWs, hWi⟩ := novikov_analytic hTa hTi
  refine ⟨fun n => C ∩ (W (n + 1))ᶜ, fun n => hC.inter (hWm _).compl, ?_, ?_⟩
  · rintro n ⟨x, y⟩ ⟨hC', hW⟩
    have hS' : (x, y) ∉ S n := fun h => hW (hWs (n + 1) h)
    simp only [S, mem_union, mem_prod, mem_univ, true_and, mem_compl_iff, not_or, not_and,
      not_not] at hS'
    refine ⟨hS'.2, fun y' hy' => ?_⟩
    by_contra hc
    exact hS'.1 ⟨(x, y'), ⟨hc, mem_univ _, hy'⟩, rfl⟩ hS'.2
  · intro p hp
    have : p ∉ ⋂ n, W n := by rw [hWi]; exact notMem_empty p
    rw [mem_iInter] at this
    push_neg at this
    obtain ⟨j, hj⟩ := this
    cases j with
    | zero => exact absurd (hWs 0 hp) hj
    | succ n => exact mem_iUnion.2 ⟨n, hp, hj⟩

theorem proj_measurable_of_compactSpace [CompactSpace Y] {B : Set (X × Y)}
    (hB : MeasurableSet B) (hc : ∀ x, IsClosed {y | (x, y) ∈ B}) :
    MeasurableSet (Prod.fst '' B) := by
  obtain ⟨U, hUo, hUb⟩ := exists_basis_seq (Y := Y)
  have hop : ∀ x, IsOpen {y | (x, y) ∈ Bᶜ} := fun x => (hc x).isOpen_compl
  obtain ⟨R, hRm, hRs, hRc⟩ := open_sections_decomp hB.compl hop U hUo hUb
  let P : ℕ → Set X := fun n => Prod.fst '' R n
  have hP : ∀ n, AnalyticSet (P n) := fun n => analytic_proj (hRm n)
  have key : (Prod.fst '' B)ᶜ = ⋃ S : Finset ℕ,
      if (⋃ m ∈ S, U m) = univ then ⋂ n, (if n ∈ S then P n else univ) else ∅ := by
    ext x
    simp only [mem_compl_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right,
      not_exists, mem_iUnion]
    constructor
    · intro hx
      have hcov : (univ : Set Y) ⊆ ⋃ n : {n // x ∈ P n}, U n := by
        intro y _
        have : (x, y) ∈ ⋃ n, R n := hRc (hx y)
        obtain ⟨n, hn⟩ := mem_iUnion.1 this
        exact mem_iUnion.2 ⟨⟨n, ⟨(x, y), hn, rfl⟩⟩, (hRs n _ hn).1⟩
      obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun n : {n // x ∈ P n} => U n)
        (fun n => hUo n) hcov
      refine ⟨t.image Subtype.val, ?_⟩
      have hU' : (⋃ m ∈ t.image Subtype.val, U m) = univ := by
        apply eq_univ_of_univ_subset
        intro y hy
        obtain ⟨n, hn⟩ := mem_iUnion.1 (ht hy)
        obtain ⟨hnt, hyn⟩ := mem_iUnion.1 hn
        exact mem_iUnion₂.2 ⟨n.1, Finset.mem_image_of_mem _ hnt, hyn⟩
      rw [if_pos hU']
      refine mem_iInter.2 fun n => ?_
      split_ifs with hn
      · obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hn
        exact m.2
      · exact mem_univ _
    · rintro ⟨S, hS⟩ y
      split_ifs at hS with hU'
      · have : y ∈ ⋃ m ∈ S, U m := hU' ▸ mem_univ y
        obtain ⟨m, hmS, hym⟩ := mem_iUnion₂.1 this
        have hxm : x ∈ P m := by
          have := mem_iInter.1 hS m
          rwa [if_pos hmS] at this
        obtain ⟨⟨x', y'⟩, hR, hx'⟩ := hxm
        simp only at hx'
        subst hx'
        exact (hRs m _ hR).2 y hym
      · exact absurd hS (notMem_empty _)
  have hcomp : AnalyticSet (Prod.fst '' B)ᶜ := by
    rw [key]
    refine AnalyticSet.iUnion fun S => ?_
    split_ifs
    · refine AnalyticSet.iInter fun n => ?_
      split_ifs
      · exact hP n
      · exact analytic_of_measurable' MeasurableSet.univ
    · exact analyticSet_empty
  exact (analytic_proj hB).measurableSet_of_compl hcomp

/-- Novikov's theorem: the projection of a Borel set with compact sections is Borel. -/
theorem proj_measurable [TopologicalSpace.MetrizableSpace Y] {B : Set (X × Y)}
    (hB : MeasurableSet B) (hc : ∀ x, IsCompact {y | (x, y) ∈ B}) :
    MeasurableSet (Prod.fst '' B) := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · have : B = ∅ := eq_empty_of_forall_notMem fun p _ => hY.false p.2
    simp [this]
  letI := TopologicalSpace.metrizableSpaceMetric Y
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq Y
  let e : Y → ℕ → ℝ := fun y i => min (dist y (d i)) 1
  have he : Continuous e :=
    continuous_pi fun i => (continuous_id.dist continuous_const).min continuous_const
  have hinj : Function.Injective e := by
    intro y y' hyy'
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨i, hi⟩ := hd.exists_dist_lt y (half_pos (lt_min hε (by norm_num : (0:ℝ) < 1)))
    have h1 : e y i = e y' i := congrFun hyy' i
    have hlt : dist y (d i) < 1 := by
      have := min_le_right ε 1
      linarith
    have hyi : e y i = dist y (d i) := min_eq_left hlt.le
    have hy'i : dist y' (d i) = dist y (d i) := by
      have h2 : min (dist y' (d i)) 1 = dist y (d i) := by
        have : e y' i = min (dist y' (d i)) 1 := rfl
        rw [← this, ← h1, hyi]
      rcases le_or_gt (dist y' (d i)) 1 with h | h
      · rw [min_eq_left h] at h2; exact h2
      · rw [min_eq_right h.le] at h2; linarith
    calc dist y y' ≤ dist y (d i) + dist (d i) y' := dist_triangle _ _ _
      _ = dist y (d i) + dist y (d i) := by rw [dist_comm (d i) y', hy'i]
      _ ≤ ε := by have := min_le_left ε 1; linarith
  let K : Set (ℕ → ℝ) := closure (range e)
  have hKc : IsCompact K := by
    have hsub : range e ⊆ Set.pi univ (fun _ => Icc (0:ℝ) 1) := by
      rintro _ ⟨y, rfl⟩ i _
      exact ⟨le_min dist_nonneg zero_le_one, min_le_right _ _⟩
    exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset isClosed_closure
      (closure_minimal hsub (isClosed_set_pi fun _ _ => isClosed_Icc))
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  haveI : PolishSpace K := isClosed_closure.polishSpace
  let e' : Y → K := fun y => ⟨e y, subset_closure (mem_range_self y)⟩
  have he' : Continuous e' := he.subtype_mk _
  have hinj' : Function.Injective e' := fun y y' h => hinj (congrArg Subtype.val h)
  let g : X × Y → X × K := Prod.map id e'
  have hg : Measurable g := measurable_id.prodMap he'.measurable
  have hginj : Function.Injective g := Function.Injective.prodMap Function.injective_id hinj'
  have hB' : MeasurableSet (g '' B) := hB.image_of_measurable_injOn hg hginj.injOn
  have hsec : ∀ x, {k | (x, k) ∈ g '' B} = e' '' {y | (x, y) ∈ B} := by
    intro x
    ext k
    simp only [mem_setOf_eq, mem_image, Prod.exists]
    constructor
    · rintro ⟨x', y', hxy', hxk⟩
      simp only [g, Prod.map, id, Prod.mk.injEq] at hxk
      obtain ⟨rfl, rfl⟩ := hxk
      exact ⟨y', hxy', rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨x, y, hy, rfl⟩
  have hc' : ∀ x, IsClosed {k | (x, k) ∈ g '' B} := by
    intro x
    rw [hsec]
    exact ((hc x).image he').isClosed
  have := proj_measurable_of_compactSpace hB' hc'
  have heq : Prod.fst '' (g '' B) = Prod.fst '' B := by
    rw [image_image]; rfl
  rwa [heq] at this

end ProjBorel

namespace BP

open ProjBorel

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
  [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]

def Sec (D : Set (X × Y)) (x : X) : Set Y := {y | (x, y) ∈ D}

noncomputable def Tsup (D : Set (X × Y)) (L : X × Y → EReal) (x : X) : EReal :=
  ⨆ y ∈ Sec D x, L (x, y)

theorem tsup_measurable {D : Set (X × Y)} (hD : MeasurableSet D) (hc : ∀ x, IsCompact (Sec D x))
    {L : X × Y → EReal} (hL : Measurable L)
    (hu : ∀ x, UpperSemicontinuousOn (fun y => L (x, y)) (Sec D x)) :
    Measurable (Tsup D L) := by
  apply measurable_of_Ioi
  intro q
  have key : Tsup D L ⁻¹' Ioi q = ⋃ r : ℚ, ⋃ (_ : q < ((r : ℝ) : EReal)),
      Prod.fst '' (D ∩ L ⁻¹' Ici ((r : ℝ) : EReal)) := by
    ext x
    simp only [mem_preimage, mem_Ioi, Tsup, mem_iUnion]
    constructor
    · intro h
      rw [lt_biSup_iff] at h
      obtain ⟨y, hy, hlt⟩ := h
      obtain ⟨r, hqr, hry⟩ := EReal.exists_rat_btwn_of_lt hlt
      exact ⟨r, hqr, (x, y), ⟨hy, hry.le⟩, rfl⟩
    · rintro ⟨r, hqr, ⟨x', y⟩, ⟨hy, hry⟩, hx⟩
      simp only at hx
      subst hx
      rw [lt_biSup_iff]
      exact ⟨y, hy, hqr.trans_le hry⟩
  rw [key]
  refine MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ => ?_
  apply proj_measurable (hD.inter (hL measurableSet_Ici))
  intro x
  exact (hu x).isCompact_inter_preimage_Ici (hc x) _

theorem bp_select {D : Set (X × Y)} (hD : MeasurableSet D) (hc : ∀ x, IsCompact (Sec D x))
    (hne : ∀ x, (Sec D x).Nonempty) {L : X × Y → EReal} (hL : Measurable L)
    (hu : ∀ x, UpperSemicontinuousOn (fun y => L (x, y)) (Sec D x)) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ D ∧ L (x, f x) = Tsup D L x := by
  have hT := tsup_measurable hD hc hL hu
  let K : X → Set Y := fun x => Sec D x ∩ (fun y => L (x, y)) ⁻¹' Ici (Tsup D L x)
  have hKc : ∀ x, IsCompact (K x) := fun x => (hu x).isCompact_inter_preimage_Ici (hc x) _
  have hKne : ∀ x, (K x).Nonempty := by
    intro x
    obtain ⟨y, hy, hmax⟩ := (hu x).exists_isMaxOn (hne x) (hc x)
    refine ⟨y, hy, ?_⟩
    show Tsup D L x ≤ L (x, y)
    exact iSup₂_le fun y' hy' => hmax hy'
  have hKm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty} := by
    intro F hF
    let KK : Set (X × Y) := D ∩ {p | Tsup D L p.1 ≤ L p} ∩ univ ×ˢ F
    have hKKm : MeasurableSet KK :=
      (hD.inter (measurableSet_le (hT.comp measurable_fst) hL)).inter
        (MeasurableSet.univ.prod hF.measurableSet)
    have : {x | (K x ∩ F).Nonempty} = Prod.fst '' KK := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyD, hyT⟩, hyF⟩
        exact ⟨(x, y), ⟨⟨hyD, hyT⟩, mem_univ _, hyF⟩, rfl⟩
      · rintro ⟨⟨x', y⟩, ⟨⟨hyD, hyT⟩, -, hyF⟩, hx⟩
        simp only at hx
        subst hx
        exact ⟨y, ⟨hyD, hyT⟩, hyF⟩
    rw [this]
    apply proj_measurable hKKm
    intro x
    have : {y | (x, y) ∈ KK} = K x ∩ F := by
      ext y
      simp only [KK, K, Sec, mem_setOf_eq, mem_inter_iff, mem_prod, mem_univ, true_and,
        mem_preimage, mem_Ici]
    rw [this]
    exact (hKc x).inter_right hF
  obtain ⟨f, hfm, hfK⟩ := MDPSel.select K hKc hKne hKm
  refine ⟨f, hfm, fun x => ⟨(hfK x).1, le_antisymm ?_ (hfK x).2⟩⟩
  exact le_biSup (fun y => L (x, y)) (hfK x).1

end BP

lemma L_measurable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (hn : n < N) (v : E → EReal) (hv : Measurable v) :
    Measurable (L M n v) := by
  have hr : Measurable fun xa => (M.r n xa : EReal) :=
    measurable_coe_real_ereal.comp (M.hr_meas n hn)
  have h1 : Measurable fun xa => ∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa) :=
    Measurable.lintegral_kernel (κ := M.Q n) (f := fun x' => (v x' ⊔ 0).toENNReal) (by fun_prop)
  have h2 : Measurable fun xa => ∫⁻ x', ((-v x') ⊔ 0).toENNReal ∂(M.Q n xa) :=
    Measurable.lintegral_kernel (κ := M.Q n) (f := fun x' => ((-v x') ⊔ 0).toENNReal)
      (by fun_prop)
  unfold L erealIntegral
  exact hr.add ((measurable_coe_ennreal_ereal.comp h1).add
    (measurable_coe_ennreal_ereal.comp h2).neg)

theorem mme_core {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hD_compact : ∀ x, IsCompact (M.Dx n x))
    (hL_usc : ∀ x, UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x)) :
    Measurable (T M n v) ∧ ∃ f, IsMaximizer M n v f := by
  have hT : T M n v = BP.Tsup (M.D n) (L M n v) := rfl
  have hc : ∀ x, IsCompact (BP.Sec (M.D n) x) := hD_compact
  have hne : ∀ x, (BP.Sec (M.D n) x).Nonempty := by
    obtain ⟨f, _, hf⟩ := M.hD_sel n hn
    exact fun x => ⟨f x, hf x⟩
  have hLm := L_measurable M n hn v hv.1
  refine ⟨hT ▸ BP.tsup_measurable (M.hD_meas n hn) hc hLm hL_usc, ?_⟩
  obtain ⟨f, hfm, hf⟩ := BP.bp_select (M.hD_meas n hn) hc hne hLm hL_usc
  exact ⟨f, ⟨hfm, fun x => (hf x).1⟩, funext fun x => (hf x).2⟩

lemma L_bound {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (c : ℝ) (hc : 0 ≤ c) (hvc : ∀ x, (v x ⊔ 0) ≤ ((c * b x : ℝ) : EReal))
    (xa : E × A) (hxa : xa ∈ M.D n) :
    L M n v xa ≤ (((cr + c * αb) * b xa.1 : ℝ) : EReal) := by
  have hP : ∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa) ≤ ENNReal.ofReal (c * (αb * b xa.1)) := by
    calc ∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa)
        ≤ ∫⁻ x', ENNReal.ofReal c * ENNReal.ofReal (b x') ∂(M.Q n xa) := by
          apply lintegral_mono
          intro x'
          have h1 := EReal.toENNReal_le_toENNReal (hvc x')
          rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe,
            ENNReal.ofReal_mul hc] at h1
          exact h1
      _ = ENNReal.ofReal c * ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q n xa) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (αb * b xa.1) := by
          gcongr; exact hb.hQ n hn xa hxa
      _ = ENNReal.ofReal (c * (αb * b xa.1)) := (ENNReal.ofReal_mul hc).symm
  have hI : erealIntegral (M.Q n xa) v ≤ ((c * (αb * b xa.1) : ℝ) : EReal) := by
    unfold erealIntegral
    have hneg : -((∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂(M.Q n xa) : ENNReal) : EReal) ≤ 0 :=
      by rw [EReal.neg_le, neg_zero]; exact EReal.coe_ennreal_nonneg _
    have hnn : 0 ≤ c * (αb * b xa.1) :=
      mul_nonneg hc (mul_nonneg hb.hαb (hb.hb_nonneg _))
    calc _ ≤ ((∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa) : ENNReal) : EReal) :=
          add_le_of_nonpos_right hneg
      _ ≤ ((ENNReal.ofReal (c * (αb * b xa.1)) : ENNReal) : EReal) :=
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hP
      _ = _ := by rw [EReal.coe_ennreal_ofReal, max_eq_left hnn]
  have hr : M.r n xa ≤ cr * b xa.1 := le_trans (le_max_left _ _) (hb.hr n hn xa hxa)
  unfold L
  calc (M.r n xa : EReal) + erealIntegral (M.Q n xa) v
      ≤ ((cr * b xa.1 : ℝ) : EReal) + ((c * (αb * b xa.1) : ℝ) : EReal) :=
        add_le_add (EReal.coe_le_coe_iff.2 hr) hI
    _ = _ := by rw [← EReal.coe_add]; congr 1; ring

lemma T_bound {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hTm : Measurable (T M n v)) :
    T M n v ∈ IBbPlus b := by
  obtain ⟨_, _, c, hc, hvc⟩ := hv
  have hK : 0 ≤ cr + c * αb := add_nonneg hb.hcr (mul_nonneg hc hb.hαb)
  have hle : ∀ x, T M n v x ≤ (((cr + c * αb) * b x : ℝ) : EReal) := by
    intro x
    exact iSup₂_le fun a ha => L_bound M b cr cg αb hb n hn v c hc hvc (x, a) ha
  refine ⟨hTm, fun x => ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle x), cr + c * αb, hK,
    fun x => sup_le (hle x) ?_⟩
  exact EReal.coe_nonneg.2 (mul_nonneg hK (hb.hb_nonneg x))

lemma g_mem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) :
    (fun x => (M.g x : EReal)) ∈ IBbPlus b := by
  refine ⟨measurable_coe_real_ereal.comp M.hg_meas, fun x => EReal.coe_ne_top _, cg, hb.hcg,
    fun x => ?_⟩
  have h := hb.hg x
  refine sup_le (EReal.coe_le_coe_iff.2 (le_trans (le_max_left _ _) h)) ?_
  exact EReal.coe_nonneg.2 (le_trans (le_max_right _ _) h)


theorem san_compact_core {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (hD_compact : ∀ n < N, ∀ x, IsCompact (M.Dx n x))
    (hQ_usc : ∀ n < N, ∀ v ∈ IBbPlus b, ∀ x,
        UpperSemicontinuousOn (fun a => erealIntegral (M.Q n (x, a)) v) (M.Dx n x))
    (hr_usc : ∀ n < N, ∀ x, UpperSemicontinuousOn (fun a => M.r n (x, a)) (M.Dx n x)) :
    StructureAssumption M (fun _ => IBbPlus b) (fun n => {f | IsDecisionRule M n f}) := by
  have hLusc : ∀ n < N, ∀ v ∈ IBbPlus b, ∀ x,
      UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x) := by
    intro n hn v hv x a ha
    have h1 : UpperSemicontinuousOn (fun a => ((M.r n (x, a) : ℝ) : EReal)) (M.Dx n x) :=
      continuous_coe_real_ereal.comp_upperSemicontinuousOn (hr_usc n hn x)
        (fun a b h => EReal.coe_le_coe_iff.2 h)
    exact UpperSemicontinuousWithinAt.add' (h1 a ha) (hQ_usc n hn v hv x a ha)
      (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))
  refine ⟨fun _ v hv => ⟨hv.1, hv.2.1⟩, fun _ _ f hf => hf, g_mem M b cr cg αb hb,
    fun n hn v hv => ?_, fun n hn v hv => ?_⟩
  · obtain ⟨hTm, _⟩ := mme_core M b cr cg αb hb n hn v hv (hD_compact n hn) (hLusc n hn v hv)
    exact T_bound M b cr cg αb hb n hn v hv hTm
  · obtain ⟨_, f, hf⟩ := mme_core M b cr cg αb hb n hn v hv (hD_compact n hn) (hLusc n hn v hv)
    exact ⟨f, hf.1, hf⟩

end MDPFinance.Semicontinuous

open MDPFinance.Semicontinuous


theorem solution {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hD_compact : ∀ x, IsCompact (M.Dx n x))
    (hL_usc : ∀ x, UpperSemicontinuousOn (fun a => L M n v (x, a)) (M.Dx n x)) :
    Measurable (T M n v) ∧ ∃ f, IsMaximizer M n v f := by
  exact mme_core M b cr cg αb hb n hn v hv hD_compact hL_usc
