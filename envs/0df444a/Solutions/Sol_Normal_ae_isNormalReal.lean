-- Prove2me | solution 1 for Normal.ae_isNormalReal
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:42:18.695869+00:00
-- url     : https://prove2.me/submissions/ac39e181-fb51-4a1f-9a94-83c22fc6799e

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

open Normal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

local notation "μI" => (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ico (0:ℝ) 1))

/-! ## Digits and the shift map -/

/-- The base-`b` shift `x ↦ {b x}`. -/
private noncomputable def shiftB (b : ℕ) (x : ℝ) : ℝ := Int.fract ((b : ℝ) * x)

private lemma digit_lt (b : ℕ) (hb : 0 < b) (x : ℝ) (n : ℕ) : digit b x n < b := by
  unfold digit
  have h1 := Int.emod_nonneg ⌊x * (b:ℝ) ^ (n + 1)⌋ (by exact_mod_cast hb.ne' : (b:ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos ⌊x * (b:ℝ) ^ (n + 1)⌋ (by exact_mod_cast hb : (0:ℤ) < b)
  omega

private lemma digit_succ (b : ℕ) (x : ℝ) (n : ℕ) :
    digit b x (n + 1) = digit b (shiftB b x) n := by
  unfold digit shiftB
  have : Int.fract ((b:ℝ) * x) * (b:ℝ) ^ (n + 1)
      = x * (b:ℝ) ^ (n + 1 + 1) - ((⌊(b:ℝ) * x⌋ * (b:ℤ) ^ n * b : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [this, Int.floor_sub_intCast]
  congr 1
  rw [Int.sub_emod, Int.mul_emod_left, sub_zero, Int.emod_emod]

private lemma digit_add_int (b : ℕ) (x : ℝ) (m : ℤ) (n : ℕ) :
    digit b (x + m) n = digit b x n := by
  unfold digit
  have : (x + m) * (b:ℝ) ^ (n + 1) = x * (b:ℝ) ^ (n + 1) + ((m * (b:ℤ) ^ n * b : ℤ) : ℝ) := by
    push_cast; ring
  rw [this, Int.floor_add_intCast]
  congr 1
  rw [Int.add_mul_emod_self_right]

private lemma digit_iter (b : ℕ) (i : ℕ) :
    ∀ (x : ℝ) (j : ℕ), digit b x (i + j) = digit b ((shiftB b)^[i] x) j := by
  induction i with
  | zero => intro x j; simp
  | succ i ih =>
    intro x j
    rw [Function.iterate_succ_apply, ← ih, show i + 1 + j = (i + j) + 1 by ring, digit_succ]

private lemma measurable_digit (b : ℕ) (n : ℕ) : Measurable (fun x : ℝ => digit b x n) := by
  unfold digit
  exact (measurable_from_top (f := fun z : ℤ => (z % (b:ℤ)).toNat)).comp
    (Int.measurable_floor.comp (measurable_id.mul_const _))

private lemma measurable_shiftB (b : ℕ) : Measurable (shiftB b) := by
  unfold shiftB
  exact measurable_fract.comp (measurable_id.const_mul _)

/-! ## The one-digit measure computation -/

private lemma key_set (b : ℕ) (hb : 2 ≤ b) (d : ℕ) (hd : d < b) (D : Set ℝ) :
    {x : ℝ | digit b x 0 = d} ∩ shiftB b ⁻¹' D ∩ Set.Ico 0 1 =
      (fun x : ℝ => (b:ℝ) * x) ⁻¹' ((fun y : ℝ => y + (-(d:ℝ))) ⁻¹' (D ∩ Set.Ico 0 1)) := by
  have hbpos : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hdb : (d:ℝ) + 1 ≤ b := by exact_mod_cast hd
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ico]
  constructor
  · rintro ⟨⟨hdig, hD⟩, h0, h1⟩
    have hfl : ⌊(b:ℝ) * x⌋ = d := by
      have hlo : (0:ℤ) ≤ ⌊(b:ℝ) * x⌋ := Int.floor_nonneg.mpr (by positivity)
      have hhi : ⌊(b:ℝ) * x⌋ < b := by
        rw [Int.floor_lt]; push_cast; nlinarith
      unfold digit at hdig
      simp only [zero_add, pow_one] at hdig
      rw [mul_comm, Int.emod_eq_of_lt hlo hhi] at hdig
      omega
    have hfr : Int.fract ((b:ℝ) * x) = (b:ℝ) * x + -(d:ℝ) := by
      rw [Int.fract, hfl]; push_cast; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [← hfr]; exact hD
    · rw [← hfr]; exact Int.fract_nonneg _
    · rw [← hfr]; exact Int.fract_lt_one _
  · rintro ⟨hD, h0, h1⟩
    have hfl : ⌊(b:ℝ) * x⌋ = d := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hfr : Int.fract ((b:ℝ) * x) = (b:ℝ) * x + -(d:ℝ) := by
      rw [Int.fract, hfl]; push_cast; ring
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · unfold digit
      simp only [zero_add, pow_one]
      rw [mul_comm, hfl, Int.emod_eq_of_lt (by omega) (by omega)]
      simp
    · show Int.fract _ ∈ D
      rw [hfr]; exact hD
    · nlinarith
    · nlinarith

private lemma key_measure (b : ℕ) (hb : 2 ≤ b) (d : ℕ) (hd : d < b) (D : Set ℝ) :
    μI ({x : ℝ | digit b x 0 = d} ∩ shiftB b ⁻¹' D) = (b : ℝ≥0∞)⁻¹ * μI D := by
  have hbpos : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  rw [Measure.restrict_apply' measurableSet_Ico, Measure.restrict_apply' measurableSet_Ico,
    key_set b hb d hd D, Real.volume_preimage_mul_left hbpos.ne', measure_preimage_add_right]
  congr 1
  rw [abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos hbpos, ENNReal.ofReal_natCast]

private lemma muI_univ : μI Set.univ = 1 := by
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ico]; simp

private lemma muI_prob : IsProbabilityMeasure μI := ⟨muI_univ⟩

private lemma shift_preserves (b : ℕ) (hb : 2 ≤ b) (D : Set ℝ) (hD : MeasurableSet D) :
    μI (shiftB b ⁻¹' D) = μI D := by
  have hcover : shiftB b ⁻¹' D =
      ⋃ d ∈ Finset.range b, ({x : ℝ | digit b x 0 = d} ∩ shiftB b ⁻¹' D) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Finset.mem_range, exists_prop]
    constructor
    · intro h; exact ⟨digit b x 0, digit_lt b (by omega) x 0, rfl, h⟩
    · rintro ⟨_, _, _, h⟩; exact h
  rw [hcover, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun d hd => key_measure b hb d (Finset.mem_range.1 hd) D),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : b ≠ 0)) (ENNReal.natCast_ne_top b),
      one_mul]
  · intro d _ d' _ hne
    exact Set.disjoint_left.2 fun x h1 h2 => hne (h1.1.symm.trans h2.1)
  · intro d _
    exact (measurable_digit b 0 (measurableSet_singleton d)).inter (measurable_shiftB b hD)

private lemma iter_preserves (b : ℕ) (hb : 2 ≤ b) (m : ℕ) :
    ∀ D : Set ℝ, MeasurableSet D → μI ((shiftB b)^[m] ⁻¹' D) = μI D := by
  induction m with
  | zero => intro D _; rfl
  | succ m ih =>
    intro D hD
    rw [Function.iterate_succ, Set.preimage_comp,
      shift_preserves b hb _ ((measurable_shiftB b).iterate m hD), ih D hD]

/-! ## Cylinders -/

/-- Points whose first `|u|` base-`b` digits spell `u`. -/
private def Cyl (b : ℕ) (u : List ℕ) : Set ℝ :=
  {y | ∀ j : Fin u.length, digit b y j = u.get j}

private lemma measurableSet_Cyl (b : ℕ) (u : List ℕ) : MeasurableSet (Cyl b u) := by
  have : Cyl b u = ⋂ j : Fin u.length, (fun y => digit b y j) ⁻¹' {u.get j} := by
    ext y; simp [Cyl]
  rw [this]
  exact MeasurableSet.iInter fun j => measurable_digit b j (measurableSet_singleton _)

private lemma Cyl_cons (b : ℕ) (d : ℕ) (u : List ℕ) :
    Cyl b (d :: u) = {x : ℝ | digit b x 0 = d} ∩ shiftB b ⁻¹' Cyl b u := by
  ext x
  simp only [Cyl, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · intro h
    refine ⟨h ⟨0, by simp⟩, fun j => ?_⟩
    have := h j.succ
    simpa [digit_succ] using this
  · rintro ⟨h0, h⟩ j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using h0
    · simpa [digit_succ] using h j

private lemma Cyl_measure (b : ℕ) (hb : 2 ≤ b) (u : List ℕ) (hu : ∀ d ∈ u, d < b)
    (D : Set ℝ) (hD : MeasurableSet D) :
    μI (Cyl b u ∩ (shiftB b)^[u.length] ⁻¹' D) = (b : ℝ≥0∞)⁻¹ ^ u.length * μI D := by
  induction u generalizing D with
  | nil => simp [Cyl]
  | cons d u ih =>
    have hset : Cyl b (d :: u) ∩ (shiftB b)^[(d :: u).length] ⁻¹' D =
        {x : ℝ | digit b x 0 = d} ∩ shiftB b ⁻¹' (Cyl b u ∩ (shiftB b)^[u.length] ⁻¹' D) := by
      rw [Cyl_cons, List.length_cons, Function.iterate_succ, Set.preimage_comp,
        Set.preimage_inter, Set.inter_assoc]
    rw [hset, key_measure b hb d (hu d (by simp)) _,
      ih (fun d' hd' => hu d' (by simp [hd'])) D hD, List.length_cons, pow_succ']
    ring

/-! ## Window events -/

/-- The event "the word `w` occurs at position `i` of the base-`b` digits". -/
private def Ev (b : ℕ) (w : List ℕ) (i : ℕ) : Set ℝ :=
  {x | ∀ j : Fin w.length, digit b x (i + j) = w.get j}

private lemma Ev_eq (b : ℕ) (w : List ℕ) (i : ℕ) : Ev b w i = (shiftB b)^[i] ⁻¹' Cyl b w := by
  ext x; simp [Ev, Cyl, digit_iter]

private lemma measurableSet_Ev (b : ℕ) (w : List ℕ) (i : ℕ) : MeasurableSet (Ev b w i) := by
  rw [Ev_eq]; exact (measurable_shiftB b).iterate i (measurableSet_Cyl b w)

private lemma Ev_measure (b : ℕ) (hb : 2 ≤ b) (w : List ℕ) (hw : ∀ d ∈ w, d < b) (i : ℕ) :
    μI (Ev b w i) = (b : ℝ≥0∞)⁻¹ ^ w.length := by
  rw [Ev_eq, iter_preserves b hb i _ (measurableSet_Cyl b w)]
  have := Cyl_measure b hb w hw Set.univ MeasurableSet.univ
  rwa [Set.preimage_univ, Set.inter_univ, muI_univ, mul_one] at this

private lemma Ev_inter_measure (b : ℕ) (hb : 2 ≤ b) (w : List ℕ) (hw : ∀ d ∈ w, d < b)
    (i g : ℕ) :
    μI (Ev b w i ∩ Ev b w (i + w.length + g)) =
      (b : ℝ≥0∞)⁻¹ ^ w.length * (b : ℝ≥0∞)⁻¹ ^ w.length := by
  have h1 : Ev b w (i + w.length + g) =
      (shiftB b)^[i] ⁻¹' ((shiftB b)^[w.length] ⁻¹' ((shiftB b)^[g] ⁻¹' Cyl b w)) := by
    rw [Ev_eq, ← Set.preimage_comp, ← Set.preimage_comp, ← Function.iterate_add,
      ← Function.iterate_add, show g + (w.length + i) = i + w.length + g by ring]
  rw [h1, Ev_eq, ← Set.preimage_inter,
    iter_preserves b hb i _ ((measurableSet_Cyl b w).inter ((measurable_shiftB b).iterate _
      ((measurable_shiftB b).iterate g (measurableSet_Cyl b w)))),
    Cyl_measure b hb w hw _ ((measurable_shiftB b).iterate g (measurableSet_Cyl b w)),
    iter_preserves b hb g _ (measurableSet_Cyl b w)]
  have := Cyl_measure b hb w hw Set.univ MeasurableSet.univ
  rw [Set.preimage_univ, Set.inter_univ, muI_univ, mul_one] at this
  rw [this]

/-! ## Indicators: independence and identical distribution -/

private lemma indepFun_indicator_of_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : μ (A ∩ B) = μ A * μ B) :
    IndepFun (A.indicator (fun _ => (1:ℝ))) (B.indicator (fun _ => (1:ℝ))) μ := by
  have hAB : IndepSet A B μ := (indepSet_iff_measure_inter_eq_mul hA hB μ).2 h
  refine Indep.indicator_indepFun (m := MeasurableSpace.generateFrom {A}) (1:ℝ)
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton A)) ?_
  refine indep_of_indep_of_le_right hAB ?_
  have hm : Measurable[MeasurableSpace.generateFrom {B}] (B.indicator (fun _ => (1:ℝ))) :=
    Measurable.indicator measurable_const
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton B))
  exact hm.comap_le

open Classical in
private lemma indicator_preimage_eq {Ω : Type*} (C : Set Ω) (S : Set ℝ) :
    C.indicator (fun _ => (1:ℝ)) ⁻¹' S =
      (if (1:ℝ) ∈ S then C else ∅) ∪ (if (0:ℝ) ∈ S then Cᶜ else ∅) := by
  ext x
  by_cases hx : x ∈ C <;> by_cases h1 : (1:ℝ) ∈ S <;> by_cases h0 : (0:ℝ) ∈ S <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, h1, h0]

private lemma identDistrib_indicator {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : μ A = μ B) :
    IdentDistrib (A.indicator (fun _ => (1:ℝ))) (B.indicator (fun _ => (1:ℝ))) μ μ where
  aemeasurable_fst := (measurable_const.indicator hA).aemeasurable
  aemeasurable_snd := (measurable_const.indicator hB).aemeasurable
  map_eq := by
    classical
    ext S hS
    rw [Measure.map_apply (measurable_const.indicator hA) hS,
      Measure.map_apply (measurable_const.indicator hB) hS,
      indicator_preimage_eq, indicator_preimage_eq]
    have hc : μ Aᶜ = μ Bᶜ := by
      rw [measure_compl hA (measure_ne_top μ A), measure_compl hB (measure_ne_top μ B), h]
    split_ifs <;> simp [h, hc]

/-! ## The strong law along one residue class -/

private lemma slln_residue (b : ℕ) (hb : 2 ≤ b) (w : List ℕ) (hw : ∀ d ∈ w, d < b) (r : ℕ) :
    ∀ᵐ x ∂μI, Tendsto (fun M : ℕ =>
      (∑ j ∈ Finset.range M, (Ev b w (w.length * j + r)).indicator (fun _ => (1:ℝ)) x) / M)
      atTop (𝓝 ((b:ℝ) ^ w.length)⁻¹) := by
  have := muI_prob
  set k := w.length with hk
  let X : ℕ → ℝ → ℝ := fun j => (Ev b w (k * j + r)).indicator (fun _ => (1:ℝ))
  have hint : Integrable (X 0) μI :=
    (integrable_const (1:ℝ)).indicator (measurableSet_Ev b w _)
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g μI) X) := by
    have key : ∀ j j' : ℕ, j < j' → IndepFun (X j) (X j') μI := by
      intro j j' hjj
      obtain ⟨t, rfl⟩ : ∃ t, j' = j + 1 + t := ⟨j' - j - 1, by omega⟩
      have he : k * (j + 1 + t) + r = (k * j + r) + k + k * t := by ring
      refine indepFun_indicator_of_mul (measurableSet_Ev b w _) (measurableSet_Ev b w _) ?_
      rw [he, Ev_inter_measure b hb w hw, Ev_measure b hb w hw, Ev_measure b hb w hw]
    intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j j' h
    · exact (key j' j h).symm
  have hident : ∀ j, IdentDistrib (X j) (X 0) μI μI := fun j =>
    identDistrib_indicator (measurableSet_Ev b w _) (measurableSet_Ev b w _)
      (by rw [Ev_measure b hb w hw, Ev_measure b hb w hw])
  have hmean : μI[X 0] = ((b:ℝ) ^ k)⁻¹ := by
    show ∫ x, (Ev b w (k * 0 + r)).indicator (fun _ => (1:ℝ)) x ∂μI = _
    rw [integral_indicator_const _ (measurableSet_Ev b w _), smul_eq_mul, mul_one,
      measureReal_def, Ev_measure b hb w hw]
    simp [ENNReal.toReal_pow, ENNReal.toReal_inv, hk]
  have := strong_law_ae_real X hint hindep hident
  rw [hmean] at this
  exact this

/-! ## From a subsequence `k M` to all `N` -/

private lemma abs_sub_le_of_step (f : ℕ → ℝ) (hstep : ∀ N, |f (N + 1) - f N| ≤ 1) (a : ℕ) :
    ∀ t : ℕ, |f (a + t) - f a| ≤ t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    calc |f (a + (t + 1)) - f a| = |(f (a + t + 1) - f (a + t)) + (f (a + t) - f a)| := by
          rw [← add_assoc]; congr 1; ring
      _ ≤ |f (a + t + 1) - f (a + t)| + |f (a + t) - f a| := abs_add_le _ _
      _ ≤ 1 + t := add_le_add (hstep _) ih
      _ = ((t + 1 : ℕ) : ℝ) := by push_cast; ring

private lemma tendsto_of_subseq (k : ℕ) (hk : 0 < k) (f : ℕ → ℝ) (c : ℝ)
    (hstep : ∀ N, |f (N + 1) - f N| ≤ 1)
    (h : Tendsto (fun M : ℕ => f (k * M) / ((k * M : ℕ) : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => f N / N) atTop (𝓝 c) := by
  have hdiv : Tendsto (fun N : ℕ => N / k) atTop atTop := Nat.tendsto_div_const_atTop hk.ne'
  have h1 : Tendsto (fun N : ℕ => f (k * (N / k)) / ((k * (N / k) : ℕ) : ℝ)) atTop (𝓝 c) :=
    h.comp hdiv
  have hzero : Tendsto (fun N : ℕ => (k : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (k:ℝ)
  have h2 : Tendsto (fun N : ℕ => ((k * (N / k) : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have hz : Tendsto (fun N : ℕ => ((N % k : ℕ) : ℝ) / N) atTop (𝓝 0) := by
      refine squeeze_zero (fun N => by positivity) (fun N => ?_) hzero
      exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.mod_lt N hk).le) (Nat.cast_nonneg _)
    have h1' : Tendsto (fun N : ℕ => 1 - ((N % k : ℕ) : ℝ) / N) atTop (𝓝 1) := by
      simpa using hz.const_sub 1
    refine h1'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hdm : ((k * (N / k) : ℕ) : ℝ) + ((N % k : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.div_add_mod N k
    field_simp
    linarith
  have h3 : Tendsto (fun N : ℕ => (f N - f (k * (N / k))) / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) hzero
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have := abs_sub_le_of_step f hstep (k * (N / k)) (N % k)
    rw [Nat.div_add_mod] at this
    exact this.trans (by exact_mod_cast (Nat.mod_lt N hk).le)
  have := (h1.mul h2).add h3
  rw [mul_one, add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  have hq : 0 < k * (N / k) := Nat.mul_pos hk (Nat.div_pos hN hk)
  have hq' : ((k * (N / k) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp
  ring

private lemma sum_range_mul_eq (g : ℕ → ℝ) (k M : ℕ) :
    ∑ i ∈ Finset.range (k * M), g i =
      ∑ r ∈ Finset.range k, ∑ j ∈ Finset.range M, g (k * j + r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]

/-! ## Normality on `[0, 1)` for one word -/

private lemma core (b : ℕ) (hb : 2 ≤ b) (w : List ℕ) (hw : ∀ d ∈ w, d < b)
    (hk : 0 < w.length) :
    ∀ᵐ x ∂μI, Tendsto (fun N : ℕ => (count (digit b x) w N : ℝ) / N) atTop
      (𝓝 ((b:ℝ) ^ w.length)⁻¹) := by
  filter_upwards [ae_all_iff.2 (slln_residue b hb w hw)] with x hx
  set k := w.length with hkdef
  set c : ℝ := ((b:ℝ) ^ k)⁻¹ with hcdef
  let f : ℕ → ℝ := fun N => ∑ i ∈ Finset.range N, (Ev b w i).indicator (fun _ => (1:ℝ)) x
  have hcount : (fun N : ℕ => (count (digit b x) w N : ℝ) / N) = fun N => f N / N := by
    funext N
    congr 1
    unfold count
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Set.indicator_apply, Ev]
  rw [hcount]
  refine tendsto_of_subseq k hk f c ?_ ?_
  · intro N
    simp only [f, Finset.sum_range_succ, add_sub_cancel_left]
    by_cases h : x ∈ Ev b w N <;> simp [h]
  · have hlim : Tendsto (fun M : ℕ => (∑ r ∈ Finset.range k,
        (∑ j ∈ Finset.range M, (Ev b w (k * j + r)).indicator (fun _ => (1:ℝ)) x) / M) / k)
        atTop (𝓝 ((∑ r ∈ Finset.range k, c) / k)) :=
      (tendsto_finsetSum _ (fun r _ => hx r)).div_const _
    have hc : (∑ r ∈ Finset.range k, c) / k = c := by
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    rw [hc] at hlim
    refine hlim.congr (fun M => ?_)
    simp only [f]
    rw [sum_range_mul_eq, ← Finset.sum_div]
    push_cast
    ring

/-! ## From `[0, 1)` to `ℝ` by periodicity -/

private lemma ae_of_ae_Ico (P : ℝ → Prop) (hP : ∀ (x : ℝ) (m : ℤ), P (x + m) ↔ P x)
    (h : ∀ᵐ x ∂μI, P x) : ∀ᵐ x ∂(volume : Measure ℝ), P x := by
  rw [ae_restrict_iff' measurableSet_Ico] at h
  have h2 : ∀ m : ℤ, ∀ᵐ x ∂(volume : Measure ℝ), x + (m:ℝ) ∈ Set.Ico (0:ℝ) 1 → P (x + (m:ℝ)) :=
    fun m => (measurePreserving_add_right volume (m:ℝ)).quasiMeasurePreserving.ae h
  filter_upwards [ae_all_iff.2 h2] with x hx
  rw [← hP x (-⌊x⌋)]
  apply hx
  constructor
  · push_cast; linarith [Int.floor_le x]
  · push_cast; linarith [Int.lt_floor_add_one x]

private lemma ae_word (b : ℕ) (hb : 2 ≤ b) (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun N : ℕ => (count (digit b x) w N : ℝ) / N) atTop
      (𝓝 ((b:ℝ) ^ w.length)⁻¹) := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · refine Eventually.of_forall (fun x => ?_)
    have hw0 : w = [] := List.length_eq_zero_iff.1 h0
    subst hw0
    have hc : ∀ N, count (digit b x) [] N = N := by
      intro N; unfold count; simp
    simp only [hc, List.length_nil, pow_zero, inv_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  · refine ae_of_ae_Ico _ (fun x m => ?_) (core b hb w hw hpos)
    have : digit b (x + m) = digit b x := funext (digit_add_int b x m)
    rw [this]

theorem solution :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ b : ℕ, 2 ≤ b → IsNormalReal b x := by
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · have : ∀ᵐ x ∂(volume : Measure ℝ), IsNormalReal b x := by
      unfold IsNormalReal IsNormalSeq
      rw [ae_all_iff]
      intro w
      by_cases hw : ∀ d ∈ w, d < b
      · filter_upwards [ae_word b hb w hw] with x hx _ using hx
      · exact Eventually.of_forall (fun x h => absurd h hw)
    filter_upwards [this] with x hx _ using hx
  · exact Eventually.of_forall (fun x h => absurd h hb)
