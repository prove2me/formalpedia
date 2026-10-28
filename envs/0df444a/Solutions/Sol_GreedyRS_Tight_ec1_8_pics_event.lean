-- Prove2me | solution 1 for GreedyRS.Tight.ec1_8_pics_event
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:47:20.569789+00:00
-- url     : https://prove2.me/submissions/a0bad9e3-30cc-4e09-b67f-1c7f0695be57

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace G8
open GreedyRS.Greedy GreedyRS.Tight

/-! ### `ℕ∞`-valued first-hitting infima -/

lemma iInf_coe_eq_iff (p : ℕ → Prop) (m : ℕ) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = m ↔ p m ∧ ∀ n, p n → m ≤ n := by
  constructor
  · intro h
    have hle : ∀ n, p n → m ≤ n := by
      intro n hn
      have : (m : ℕ∞) ≤ n := h ▸ iInf₂_le n hn
      exact_mod_cast this
    refine ⟨?_, hle⟩
    by_contra hpm
    have : ((m + 1 : ℕ) : ℕ∞) ≤ ⨅ (n : ℕ) (_ : p n), (n : ℕ∞) := by
      refine le_iInf₂ fun n hn => ?_
      have h1 := hle n hn
      have h2 : n ≠ m := fun h => hpm (h ▸ hn)
      exact_mod_cast (show m + 1 ≤ n by omega)
    rw [h] at this
    have : m + 1 ≤ m := by exact_mod_cast this
    omega
  · rintro ⟨hpm, hle⟩
    apply le_antisymm
    · exact iInf₂_le m hpm
    · exact le_iInf₂ fun n hn => by exact_mod_cast hle n hn

lemma iInf_coe_le (p : ℕ → Prop) (n : ℕ) (hn : p n) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) ≤ n := iInf₂_le n hn

lemma le_iInf_coe (p : ℕ → Prop) (a : ℕ) (h : ∀ n, p n → a ≤ n) :
    (a : ℕ∞) ≤ ⨅ (n : ℕ) (_ : p n), (n : ℕ∞) := le_iInf₂ fun n hn => by exact_mod_cast h n hn

lemma one_le_prefixCross (yi y : ℕ → ℝ) (m : ℕ) : (1 : ℕ∞) ≤ prefixCross yi y m := by
  unfold prefixCross
  exact le_iInf₂ fun n hn => by exact_mod_cast hn.1

/-- If `prefixCross` is the finite value `N`, then `N` satisfies the crossing condition. -/
lemma prefixCross_spec (yi y : ℕ → ℝ) (m N : ℕ) (h : prefixCross yi y m = N) :
    1 ≤ N ∧ ∀ j ∈ Finset.Icc 1 m, yi N < y j := by
  unfold prefixCross at h
  exact ((iInf_coe_eq_iff _ N).1 h).1

lemma prefixCross_le (yi y : ℕ → ℝ) (m s : ℕ) (hs : 1 ≤ s) (h : ∀ j ∈ Finset.Icc 1 m, yi s < y j) :
    prefixCross yi y m ≤ s := by
  unfold prefixCross
  exact iInf_coe_le _ s ⟨hs, h⟩

lemma crossBelow_spec (y : ℕ → ℝ) (b : ℝ) (m : ℕ) (h : crossBelow y b 1 = m) :
    1 ≤ m ∧ y m < b ∧ ∀ n, 1 ≤ n → n < m → b ≤ y n := by
  unfold crossBelow at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := (iInf_coe_eq_iff _ m).1 h
  refine ⟨h1, h2, fun n hn hnm => ?_⟩
  by_contra hlt
  have := h3 n ⟨hn, not_le.1 hlt⟩
  omega

/-! ### Greedy dynamics -/

lemma leader_spec (k : ℕ) (hk : 0 < k) (x : ℕ → ℕ → ℝ) (s : ℕ → ℕ) :
    leader k x s < k ∧ ∀ j < k, runMean x j (s j) ≤ runMean x (leader k x s) (s (leader k x s)) := by
  classical
  have h := Nat.find_spec (exists_leader k hk x s)
  simp only [leader, hk, dif_pos]
  convert h using 2

lemma sizes_succ (k n0 : ℕ) (x : ℕ → ℕ → ℝ) (t i : ℕ) :
    efgSizes k n0 x (t + 1) i =
      if i = leader k x (efgSizes k n0 x t) then efgSizes k n0 x t i + 1
      else efgSizes k n0 x t i := by
  simp only [efgSizes, Function.update_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

lemma sizes_pos (k : ℕ) (x : ℕ → ℕ → ℝ) (t i : ℕ) : 1 ≤ efgSizes k 1 x t i := by
  induction t with
  | zero => simp [efgSizes]
  | succ t ih =>
    rw [sizes_succ]; split_ifs <;> omega

lemma sizes_sum (k : ℕ) (hk : 0 < k) (x : ℕ → ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ Finset.range k, efgSizes k 1 x t i = k + t := by
  induction t with
  | zero => simp [efgSizes]
  | succ t ih =>
    have hl := (leader_spec k hk x (efgSizes k 1 x t)).1
    have : ∑ i ∈ Finset.range k, efgSizes k 1 x (t + 1) i =
        ∑ i ∈ Finset.range k, (efgSizes k 1 x t i +
          if i = leader k x (efgSizes k 1 x t) then 1 else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sizes_succ]; split_ifs <;> simp
    rw [this, Finset.sum_add_distrib, ih, Finset.sum_ite_eq']
    simp [Finset.mem_range.2 hl]
    ring

lemma sizes_zero_succ_le (k : ℕ) (x : ℕ → ℕ → ℝ) (t : ℕ) :
    efgSizes k 1 x (t + 1) 0 ≤ efgSizes k 1 x t 0 + 1 := by
  rw [sizes_succ]; split_ifs <;> omega

/-- The pathwise content of (EC.1.8). -/
theorem pathwise (k B m : ℕ) (x : ℕ → ℕ → ℝ)
    (hm1 : 1 ≤ m) (hmin : ∀ n, 1 ≤ n → n < m → runMean x 0 m < runMean x 0 n)
    (hnotie : ∀ i, 1 ≤ i → i < k → ∀ s n, 1 ≤ s → 1 ≤ n → runMean x i s ≠ runMean x 0 n)
    (hlow : (∑ i ∈ Finset.Ico 1 k, prefixCross (runMean x i) (runMean x 0) (m - 1)) + m ≤ B)
    (hup : (B : ℕ∞) < (∑ i ∈ Finset.Ico 1 k, prefixCross (runMean x i) (runMean x 0) m) + m) :
    greedySelect k B x ≠ 0 := by
  -- k ≥ 1
  have hk : 0 < k := by
    by_contra hk0
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty, zero_add] at hlow hup
    exact absurd (lt_of_lt_of_le hup hlow) (lt_irrefl _)
  set N : ℕ → ℕ∞ := fun i => prefixCross (runMean x i) (runMean x 0) (m - 1) with hN
  set N' : ℕ → ℕ∞ := fun i => prefixCross (runMean x i) (runMean x 0) m with hN'
  -- B ≥ k
  have hsumN : ((k - 1 : ℕ) : ℕ∞) ≤ ∑ i ∈ Finset.Ico 1 k, N i := by
    have : ∑ i ∈ Finset.Ico 1 k, (1 : ℕ∞) ≤ ∑ i ∈ Finset.Ico 1 k, N i :=
      Finset.sum_le_sum fun i _ => one_le_prefixCross _ _ _
    simpa using this
  have hkB : k ≤ B := by
    have : ((k - 1 : ℕ) : ℕ∞) + m ≤ B := le_trans (by gcongr) hlow
    have : (k - 1) + m ≤ B := by exact_mod_cast this
    omega
  set T := B - k with hT
  have hBT : B = k + T := by omega
  set s : ℕ → ℕ → ℕ := fun t => efgSizes k 1 x t with hs
  have hsplit : ∀ t, ((k + t : ℕ) : ℕ∞) =
      (s t 0 : ℕ∞) + ∑ i ∈ Finset.Ico 1 k, (s t i : ℕ∞) := by
    intro t
    rw [← sizes_sum k hk x t, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
    push_cast; rfl
  -- Step A: alternative 0 reaches `m` observations within the budget.
  have hA : ∃ t0 ≤ T, s t0 0 = m := by
    by_contra hno
    push Not at hno
    have hlt : ∀ t ≤ T, s t 0 < m := by
      intro t
      induction t with
      | zero =>
        intro _
        have h0 : s 0 0 = 1 := by simp [hs, efgSizes]
        have := hno 0 (Nat.zero_le _)
        omega
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have h2 := sizes_zero_succ_le k x t
        have h3 := hno (t + 1) ht
        simp only [hs] at h1 h3 ⊢
        omega
    have hbound : ∀ t ≤ T, ∀ i ∈ Finset.Ico 1 k, (s t i : ℕ∞) ≤ N i := by
      intro t
      induction t with
      | zero =>
        intro _ i _
        have h0 : s 0 i = 1 := by simp [hs, efgSizes]
        rw [h0]; exact_mod_cast one_le_prefixCross _ _ _
      | succ t ih =>
        intro ht i hi
        have ih' := ih (by omega) i hi
        simp only [hs] at ih' ⊢
        rw [sizes_succ]
        split_ifs with hli
        · -- `i` is the leader at time `t`
          have hne : (efgSizes k 1 x t i : ℕ∞) ≠ N i := by
            intro heq
            obtain ⟨-, hcross⟩ := prefixCross_spec _ _ _ _ heq.symm
            have h0pos := sizes_pos k x t 0
            have h0lt := hlt t (by omega)
            have hc := hcross (efgSizes k 1 x t 0)
              (Finset.mem_Icc.2 ⟨h0pos, by simp only [hs] at h0lt; omega⟩)
            have hlead := (leader_spec k hk x (efgSizes k 1 x t)).2 0 hk
            rw [← hli] at hlead
            linarith
          have hlt' : (efgSizes k 1 x t i : ℕ∞) < N i := lt_of_le_of_ne ih' hne
          push_cast
          exact Order.add_one_le_of_lt hlt'
        · exact ih'
    have hsum : ∑ i ∈ Finset.Ico 1 k, (s T i : ℕ∞) ≤ ∑ i ∈ Finset.Ico 1 k, N i :=
      Finset.sum_le_sum fun i hi => hbound T le_rfl i hi
    have h0 : (s T 0 : ℕ∞) < m := by exact_mod_cast hlt T le_rfl
    have hfin : ∑ i ∈ Finset.Ico 1 k, N i ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hlow
      exact absurd hlow (by simp)
    have : ((k + T : ℕ) : ℕ∞) < (B : ℕ∞) := by
      rw [hsplit T]
      calc (s T 0 : ℕ∞) + ∑ i ∈ Finset.Ico 1 k, (s T i : ℕ∞)
          < (m : ℕ∞) + ∑ i ∈ Finset.Ico 1 k, N i := by
            rw [add_comm (m : ℕ∞)]
            rw [add_comm (s T 0 : ℕ∞)]
            have hfin' : ∑ i ∈ Finset.Ico 1 k, (s T i : ℕ∞) ≠ ⊤ := by
              rw [← Nat.cast_sum]; exact ENat.coe_ne_top _
            exact ENat.add_lt_add_of_le_of_lt hfin' hsum h0
        _ = (∑ i ∈ Finset.Ico 1 k, N i) + m := add_comm _ _
        _ ≤ B := hlow
    rw [hBT] at this
    exact lt_irrefl _ this
  obtain ⟨t0, ht0T, ht0⟩ := hA
  -- Step B: alternative 0 is never the leader while it holds `m` observations.
  have hkey : ∀ t ≤ T, s t 0 = m → leader k x (s t) ≠ 0 := by
    intro t htT hsm hl0
    have hlead := (leader_spec k hk x (s t)).2
    rw [hl0, hsm] at hlead
    have hle : ∀ j ∈ Finset.Ico 1 k, N' j ≤ (s t j : ℕ∞) := by
      intro j hj
      obtain ⟨hj1, hjk⟩ := Finset.mem_Ico.1 hj
      apply prefixCross_le _ _ _ _ (sizes_pos k x t j)
      intro n hn
      obtain ⟨hn1, hnm⟩ := Finset.mem_Icc.1 hn
      have h1 : runMean x j (s t j) < runMean x 0 m :=
        lt_of_le_of_ne (hlead j hjk) (hnotie j hj1 hjk _ _ (sizes_pos k x t j) hm1)
      rcases lt_or_eq_of_le hnm with hlt | heq
      · exact h1.trans (hmin n hn1 hlt)
      · rw [heq]; exact h1
    have hsum : ∑ j ∈ Finset.Ico 1 k, N' j ≤ ∑ j ∈ Finset.Ico 1 k, (s t j : ℕ∞) :=
      Finset.sum_le_sum hle
    have : (∑ j ∈ Finset.Ico 1 k, N' j) + m ≤ B := by
      calc (∑ j ∈ Finset.Ico 1 k, N' j) + m ≤ (∑ j ∈ Finset.Ico 1 k, (s t j : ℕ∞)) + s t 0 := by
            rw [hsm]; gcongr
        _ = ((k + t : ℕ) : ℕ∞) := by rw [hsplit t, add_comm]
        _ ≤ B := by exact_mod_cast (show k + t ≤ B by omega)
    exact absurd (lt_of_lt_of_le hup this) (lt_irrefl _)
  have hstay : ∀ t, t0 ≤ t → t ≤ T → s t 0 = m := by
    intro t ht0t
    induction t, ht0t using Nat.le_induction with
    | base => intro _; exact ht0
    | succ t ht0t ih =>
      intro htT
      have h1 := ih (by omega)
      have hne := hkey t (by omega) h1
      simp only [hs] at h1 hne ⊢
      rw [sizes_succ, if_neg (fun h => hne h.symm)]
      exact h1
  have hfinal := hkey T le_rfl (hstay T ht0T le_rfl)
  simp only [greedySelect, efgSelect, one_mul]
  rw [← hT]
  exact hfinal

end G8

namespace G8b
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω]

lemma indep_eq_null (P : Measure Ω) [IsProbabilityMeasure P] (Y R : Ω → ℝ) (hY : Measurable Y)
    (hR : Measurable R) (hind : IndepFun R Y P) (hna : ∀ r, P.map Y {r} = 0) :
    P {ω | Y ω = R ω} = 0 := by
  have hD : MeasurableSet {p : ℝ × ℝ | p.2 = p.1} := measurableSet_eq_fun measurable_snd measurable_fst
  have hpre : {ω | Y ω = R ω} = (fun ω => (R ω, Y ω)) ⁻¹' {p : ℝ × ℝ | p.2 = p.1} := rfl
  rw [hpre, ← Measure.map_apply (hR.prodMk hY) hD,
    (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable hY.aemeasurable).1 hind,
    Measure.prod_apply hD]
  have : ∀ r : ℝ, (Prod.mk r ⁻¹' {p : ℝ × ℝ | p.2 = p.1}) = {r} := by
    intro r; ext y; simp
  simp_rw [this, hna, lintegral_zero]

lemma tie_null (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (i s n : ℕ) (hi : i ≠ 0) (hvi : v i ≠ 0)
    (hs : 1 ≤ s) (hn : 1 ≤ n) :
    P {ω | runMean (fun i j => X i j ω) i s = runMean (fun i j => X i j ω) 0 n} = 0 := by
  classical
  set q : ℕ × ℕ := (i, s - 1) with hq
  set F : Finset (ℕ × ℕ) := (Finset.range n).image (fun j => ((0 : ℕ), j)) ∪
    (Finset.range (s - 1)).image (fun j => (i, j)) with hF
  have hqF : q ∉ F := by
    intro hmem
    rcases Finset.mem_union.1 hmem with h | h
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.1 h
      have := congrArg Prod.fst hj
      simp only [hq] at this
      exact hi this.symm
    · obtain ⟨j, hj, hj'⟩ := Finset.mem_image.1 h
      have := congrArg Prod.snd hj'
      simp only [hq] at this
      have := Finset.mem_range.1 hj
      omega
  set g : ℕ × ℕ → ℝ → ℝ := fun p x =>
    if p.1 = 0 then ((s : ℝ) / n) * x else if p = q then x else -x with hg
  have hgm : ∀ p, Measurable (g p) := by
    intro p
    by_cases h1 : p.1 = 0
    · simp only [hg, h1, if_true]; exact measurable_const.mul measurable_id
    · by_cases h2 : p = q
      · have : g p = id := by ext x; simp only [hg, if_neg h1, if_pos h2, id]
        rw [this]; exact measurable_id
      · simp only [hg, h1, h2, if_false]; exact measurable_neg
  set Z : ℕ × ℕ → Ω → ℝ := fun p => g p ∘ (fun ω => X p.1 p.2 ω) with hZ
  have hZind : iIndepFun Z P := hX.indep.comp g hgm
  have hZm : ∀ p, Measurable (Z p) := fun p => (hgm p).comp (hX.meas p.1 p.2)
  have hind : IndepFun (∑ p ∈ F, Z p) (Z q) P := hZind.indepFun_finsetSum_of_notMem hZm hqF
  have hZq : Z q = X i (s - 1) := by
    ext ω; simp [hZ, hg, hq, hi]
  rw [hZq] at hind
  have hRm : Measurable (∑ p ∈ F, Z p) := by
    have h := Finset.measurable_sum F (fun p _ => hZm p)
    convert h using 1; ext ω; simp
  have hna : ∀ r, P.map (X i (s - 1)) {r} = 0 := by
    intro r; rw [hX.law i (s - 1)]
    exact gaussianReal_absolutelyContinuous _ hvi (by simp)
  have hnull := indep_eq_null P (X i (s - 1)) (∑ p ∈ F, Z p) (hX.meas i (s - 1)) hRm hind hna
  refine measure_mono_null ?_ hnull
  intro ω hω
  simp only [Set.mem_setOf_eq, runMean] at hω ⊢
  -- compute the sum
  have hdisj : Disjoint ((Finset.range n).image (fun j => ((0 : ℕ), j)))
      ((Finset.range (s - 1)).image (fun j => (i, j))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_image] at hp1 hp2
    obtain ⟨j1, _, rfl⟩ := hp1
    obtain ⟨j2, _, h⟩ := hp2
    simp only [Prod.mk.injEq] at h
    exact hi h.1
  have hsum : (∑ p ∈ F, Z p) ω = ((s : ℝ) / n) * (∑ j ∈ Finset.range n, X 0 j ω) -
      ∑ j ∈ Finset.range (s - 1), X i j ω := by
    rw [Finset.sum_apply, hF, Finset.sum_union hdisj, Finset.sum_image (by simp),
      Finset.sum_image (by simp), Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    have e1 : ∑ x ∈ Finset.range n, Z (0, x) ω = ∑ x ∈ Finset.range n, (s : ℝ) / n * X 0 x ω := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hZ, hg]
    have e2 : ∑ x ∈ Finset.range (s - 1), Z (i, x) ω = ∑ x ∈ Finset.range (s - 1), -X i x ω := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : (i, j) ≠ q := by
        simp only [hq, ne_eq, Prod.mk.injEq, not_and]
        intro _; have := Finset.mem_range.1 hj; omega
      simp only [hZ, hg, Function.comp_apply, if_neg hi, if_neg hj']
    rw [e1, e2]
  rw [hsum]
  have hsplit : ∑ j ∈ Finset.range s, X i j ω =
      ∑ j ∈ Finset.range (s - 1), X i j ω + X i (s - 1) ω := by
    conv_lhs => rw [show s = (s - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
  rw [hsplit] at hω
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp at hω ⊢
  linarith

end G8b

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (hv : ∀ i, 0 < v i) (k B : ℕ) (γp : ℝ) :
    P {ω | ∃ m : ℕ, GreedyRS.Greedy.crossBelow (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) (μ 0 - γp) 1 = m ∧
        (∑ i ∈ Finset.Ico 1 k, GreedyRS.Tight.prefixCross (GreedyRS.Greedy.runMean (fun i j => X i j ω) i)
            (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) (m - 1)) + m ≤ B ∧
        (B : ℕ∞) < (∑ i ∈ Finset.Ico 1 k, GreedyRS.Tight.prefixCross (GreedyRS.Greedy.runMean (fun i j => X i j ω) i)
            (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) m) + m}
      ≤ P {ω | GreedyRS.Greedy.greedySelect k B (fun i j => X i j ω) ≠ 0} := by
  set Ties : Set Ω := ⋃ i : ℕ, ⋃ s : ℕ, ⋃ n : ℕ, {ω | 1 ≤ i ∧ 1 ≤ s ∧ 1 ≤ n ∧
    GreedyRS.Greedy.runMean (fun i j => X i j ω) i s = GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n}
    with hTies
  have hTnull : P Ties = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun s => measure_iUnion_null fun n => ?_
    by_cases h : 1 ≤ i ∧ 1 ≤ s ∧ 1 ≤ n
    · refine measure_mono_null (fun ω hω => hω.2.2.2) ?_
      exact G8b.tie_null P μ v X hX i s n (by omega) (hv i).ne' h.2.1 h.2.2
    · have : {ω : Ω | 1 ≤ i ∧ 1 ≤ s ∧ 1 ≤ n ∧
          GreedyRS.Greedy.runMean (fun i j => X i j ω) i s =
            GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩
      rw [this, measure_empty]
  refine (measure_mono (t := {ω | GreedyRS.Greedy.greedySelect k B (fun i j => X i j ω) ≠ 0} ∪ Ties)
    ?_).trans ((measure_union_le _ _).trans (by rw [hTnull, add_zero]))
  intro ω hω
  by_cases hT : ω ∈ Ties
  · exact Or.inr hT
  left
  obtain ⟨m, hcb, hlow, hup⟩ := hω
  obtain ⟨hm1, hym, hbef⟩ := G8.crossBelow_spec _ _ _ hcb
  refine G8.pathwise k B m (fun i j => X i j ω) hm1
    (fun n hn hnm => lt_of_lt_of_le hym (hbef n hn hnm)) ?_ hlow hup
  intro i hi _ s n hs hn heq
  exact hT (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨n, hi, hs, hn, heq⟩⟩⟩)
