-- Prove2me | solution 1 for GreedyRS.EFG.eq5_1_crossing_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:46:07.513986+00:00
-- url     : https://prove2.me/submissions/53407466-5573-47ec-be04-56a6dd21dd28

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GRSHelp
open GreedyRS.Greedy

lemma crossTime_le {x : ℝ} {n0 n : ℕ} {z : ℕ → ℝ} (h1 : n0 ≤ n) (h2 : zbar z n < x) :
    crossTime x n0 z ≤ n := iInf₂_le n ⟨h1, h2⟩

lemma le_crossTime {x : ℝ} {n0 : ℕ} {z : ℕ → ℝ} {m : ℕ∞}
    (h : ∀ n, n0 ≤ n → zbar z n < x → m ≤ n) : m ≤ crossTime x n0 z :=
  le_iInf₂ fun n hn => h n hn.1 hn.2

lemma crossTime_anti {x y : ℝ} (hxy : x ≤ y) (n0 : ℕ) (z : ℕ → ℝ) :
    crossTime y n0 z ≤ crossTime x n0 z :=
  le_crossTime fun _ h1 h2 => crossTime_le h1 (h2.trans_le hxy)

lemma crossTime_spec {x : ℝ} {n0 : ℕ} {z : ℕ → ℝ} (h : crossTime x n0 z < ⊤) :
    ∃ n : ℕ, crossTime x n0 z = n ∧ n0 ≤ n ∧ zbar z n < x := by
  have hne : ({n | n0 ≤ n ∧ zbar z n < x} : Set ℕ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply h.ne
    apply le_antisymm le_top
    apply le_crossTime
    intro n h1 h2
    have : n ∈ ({n | n0 ≤ n ∧ zbar z n < x} : Set ℕ) := ⟨h1, h2⟩
    rw [hne] at this; exact this.elim
  refine ⟨sInf {n | n0 ≤ n ∧ zbar z n < x}, ?_, Nat.sInf_mem hne⟩
  rw [ENat.natCast_sInf hne]
  rfl

lemma measurable_zbar (n : ℕ) : Measurable (fun z : ℕ → ℝ => zbar z n) := by
  unfold zbar
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)

lemma measurable_crossTime_enn (x : ℝ) (n0 : ℕ) :
    Measurable (fun z => ((crossTime x n0 z : ℕ∞) : ℝ≥0∞)) := by
  have : (fun z => ((crossTime x n0 z : ℕ∞) : ℝ≥0∞)) =
      fun z => ⨅ n : ℕ, (if n0 ≤ n ∧ zbar z n < x then (n : ℝ≥0∞) else ⊤) := by
    funext z
    unfold crossTime
    rw [ENat.toENNReal_iInf]
    congr 1; funext n
    rw [ENat.toENNReal_iInf]
    by_cases h : n0 ≤ n ∧ zbar z n < x
    · simp [h]
    · simp [h]
  rw [this]
  apply Measurable.iInf
  intro n
  apply Measurable.ite _ measurable_const measurable_const
  by_cases hn : n0 ≤ n
  · simp only [hn, true_and]
    exact measurableSet_lt (measurable_zbar n) measurable_const
  · simp [hn]

lemma measurable_crossTime (x : ℝ) (n0 : ℕ) : Measurable (crossTime x n0) := by
  apply measurable_to_countable'
  intro m
  have : crossTime x n0 ⁻¹' {m} = (fun z => ((crossTime x n0 z : ℕ∞) : ℝ≥0∞)) ⁻¹' {(m : ℝ≥0∞)} := by
    ext z; simp
  rw [this]
  exact measurable_crossTime_enn x n0 (measurableSet_singleton _)

instance : IsProbabilityMeasure stdNormalSeq := by
  unfold stdNormalSeq; infer_instance

lemma iIndep_coord : iIndepFun (fun (i : ℕ) (z : ℕ → ℝ) => z i) stdNormalSeq := by
  unfold stdNormalSeq
  exact iIndepFun_infinitePi (X := fun _ ω => ω) (fun _ => measurable_id)

lemma map_coord (i : ℕ) : stdNormalSeq.map (fun z : ℕ → ℝ => z i) = gaussianReal 0 1 := by
  unfold stdNormalSeq
  exact Measure.infinitePi_map_eval _ i

lemma map_partialSum (n : ℕ) :
    stdNormalSeq.map (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) = gaussianReal 0 (n : ℝ≥0) := by
  induction n with
  | zero =>
    simp [gaussianReal_zero_var]
  | succ n ih =>
    have hind : IndepFun (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) (fun z : ℕ → ℝ => z n)
        stdNormalSeq :=
      iIndep_coord.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i)
        (by simp)
    have hfun : (fun z : ℕ → ℝ => ∑ j ∈ Finset.range (n + 1), z j) =
        (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) + (fun z : ℕ → ℝ => z n) := by
      funext z; simp [Finset.sum_range_succ]
    have h1 : stdNormalSeq.map (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) =
        gaussianReal 0 (n : ℝ≥0) := by
      have : (∑ j ∈ Finset.range n, (fun (z : ℕ → ℝ) => z j)) =
          (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) := by funext z; simp
      rw [this, ih]
    rw [hfun, gaussianReal_add_gaussianReal_of_indepFun hind h1 (map_coord n)]
    simp

lemma map_zbar_null (n : ℕ) (hn : 1 ≤ n) (a : ℝ) : stdNormalSeq {z | zbar z n = a} = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hset : {z : ℕ → ℝ | zbar z n = a} =
      (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) ⁻¹' {n * a} := by
    ext z; simp only [zbar, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; field_simp
    · intro h; rw [h]; field_simp
  rw [hset, ← Measure.map_apply (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
    (measurableSet_singleton _), map_partialSum]
  have hv : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact gaussianReal_absolutelyContinuous 0 hv (Real.volume_singleton)

lemma zbar_Ico_pos (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a < b) :
    0 < stdNormalSeq {z | a ≤ zbar z n ∧ zbar z n < b} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {z : ℕ → ℝ | a ≤ zbar z n ∧ zbar z n < b} =
      (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n, z j) ⁻¹' Set.Ico (n * a) (n * b) := by
    ext z; simp only [zbar, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
    rw [le_div_iff₀ hn', div_lt_iff₀ hn']
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, ← Measure.map_apply (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
    measurableSet_Ico, map_partialSum]
  have hv : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [pos_iff_ne_zero]
  intro h0
  have h1 := gaussianReal_absolutelyContinuous' 0 hv h0
  rw [Real.volume_Ico, ENNReal.ofReal_eq_zero] at h1
  nlinarith

lemma iSup_C_right (n0 : ℕ) (hn0 : 1 ≤ n0) (x0 : ℝ) :
    ⨆ m : ℕ, Cn0 (x0 + 1 / ((m : ℝ) + 1)) n0 = Cn0 x0 n0 := by
  unfold Cn0
  have hmono : Monotone (fun (m : ℕ) (z : ℕ → ℝ) =>
      ((crossTime (x0 + 1 / ((m : ℝ) + 1)) n0 z : ℕ∞) : ℝ≥0∞)) := by
    intro m m' hmm z
    apply ENat.toENNReal_le.mpr
    apply crossTime_anti
    have : (1 : ℝ) / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm 1)
    linarith
  rw [← lintegral_iSup (fun m => measurable_crossTime_enn _ n0) hmono]
  apply lintegral_congr_ae
  have hae : ∀ᵐ z ∂stdNormalSeq, ∀ n : ℕ, zbar z (n + 1) ≠ x0 := by
    rw [ae_all_iff]
    intro n
    have := map_zbar_null (n + 1) (by omega) x0
    rw [measure_eq_zero_iff_ae_notMem] at this
    exact this
  filter_upwards [hae] with z hz
  rw [← ENat.toENNReal_iSup]
  congr 1
  apply le_antisymm
  · exact iSup_le fun m => crossTime_anti (le_add_of_nonneg_right (by positivity)) n0 z
  · -- crossTime x0 ≤ ⨆ T_m
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (⨆ m : ℕ, crossTime (x0 + 1 / ((m : ℝ) + 1)) n0 z) = N :=
      ENat.ne_top_iff_exists.mp (ne_top_of_lt hcon) |>.imp fun _ h => h.symm
    have hNlt : (N : ℕ∞) < crossTime x0 n0 z := hN ▸ hcon
    -- every n ∈ [n0, N] has zbar n > x0
    have hgt : ∀ n, n0 ≤ n → n ≤ N → x0 < zbar z n := by
      intro n h1 h2
      rcases lt_trichotomy (zbar z n) x0 with h | h | h
      · have := crossTime_le h1 h
        have : (N : ℕ∞) < n := lt_of_lt_of_le hNlt this
        exact absurd (by exact_mod_cast this : N < n) (not_lt.mpr h2)
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact absurd h (hz k)
      · exact h
    classical
    let mm : ℕ → ℕ := fun n =>
      if h : x0 < zbar z n then Classical.choose (exists_nat_one_div_lt (sub_pos.mpr h)) else 0
    let M := (Finset.range (N + 1)).sup mm
    have hM : (N : ℕ∞) < crossTime (x0 + 1 / ((M : ℝ) + 1)) n0 z := by
      refine lt_of_lt_of_le ?_ (le_crossTime (m := ((N + 1 : ℕ) : ℕ∞)) ?_)
      · exact_mod_cast Nat.lt_succ_self N
      intro n h1 h2
      by_contra hcon2
      have hnN : n ≤ N := by
        by_contra h3; exact hcon2 (by exact_mod_cast (show N + 1 ≤ n by omega))
      have hx := hgt n h1 hnN
      have hmm : mm n ≤ M := Finset.le_sup (f := mm) (Finset.mem_range.mpr (by omega))
      have hspec : 1 / ((mm n : ℝ) + 1) < zbar z n - x0 := by
        simp only [mm, dif_pos hx]
        exact Classical.choose_spec (exists_nat_one_div_lt (sub_pos.mpr hx))
      have : (1 : ℝ) / ((M : ℝ) + 1) ≤ 1 / ((mm n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm 1)
      linarith
    have := le_iSup (fun m : ℕ => crossTime (x0 + 1 / ((m : ℝ) + 1)) n0 z) M
    rw [hN] at this
    exact absurd (lt_of_lt_of_le hM this) (lt_irrefl _)

end GRSHelp

namespace GRSBlock
open GreedyRS.Greedy GRSHelp

/-- block averages map: `T z l = (∑_{r < n0} z (l * n0 + r)) / √n0`. -/
noncomputable def T (n0 : ℕ) (z : ℕ → ℝ) : ℕ → ℝ :=
  fun l => (∑ r : Fin n0, z (l * n0 + r)) / Real.sqrt n0

lemma f_inj (n0 : ℕ) : Function.Injective (fun p : ℕ × Fin n0 => p.1 * n0 + (p.2 : ℕ)) := by
  rintro ⟨a, r⟩ ⟨b, s⟩ h
  simp only at h
  have hr := r.isLt; have hs := s.isLt
  have h1 : a = b := by
    have e1 : (a * n0 + r) / n0 = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, zero_add]
    have e2 : (b * n0 + s) / n0 = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs, zero_add]
    rw [← e1, ← e2, h]
  subst h1
  have : (r : ℕ) = s := by omega
  exact Prod.ext rfl (Fin.ext this)

lemma map_block_gauss (n0 : ℕ) (hn0 : 1 ≤ n0) :
    (Measure.infinitePi (fun _ : Fin n0 => gaussianReal 0 1)).map
      (fun u : Fin n0 → ℝ => (∑ r, u r) / Real.sqrt n0) = gaussianReal 0 1 := by
  have h1 : (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map (fun z (r : Fin n0) => z (r : ℕ)) =
      Measure.infinitePi (fun _ : Fin n0 => gaussianReal 0 1) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => gaussianReal 0 1) Fin.val_injective
  rw [← h1, Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 : ((fun u : Fin n0 → ℝ => (∑ r, u r) / Real.sqrt n0) ∘ fun z (r : Fin n0) => z (r : ℕ)) =
      (fun y => y / Real.sqrt n0) ∘ (fun z : ℕ → ℝ => ∑ j ∈ Finset.range n0, z j) := by
    funext z
    simp only [Function.comp]
    rw [Fin.sum_univ_eq_sum_range (fun j => z j)]
  rw [h2, ← Measure.map_map (by fun_prop) (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))]
  have h3 := map_partialSum n0
  unfold stdNormalSeq at h3
  rw [h3, gaussianReal_map_div_const]
  congr 1
  · simp
  · ext
    have hpos : (0 : ℝ) < n0 := by exact_mod_cast hn0
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_natCast]
    rw [Real.sq_sqrt hpos.le, div_self hpos.ne']

lemma measurable_T (n0 : ℕ) : Measurable (T n0) := by
  unfold T
  apply measurable_pi_lambda
  intro l
  exact (Finset.measurable_sum _ (fun (r : Fin n0) _ => measurable_pi_apply (l * n0 + (r : ℕ)))).div_const _

lemma map_T (n0 : ℕ) (hn0 : 1 ≤ n0) : stdNormalSeq.map (T n0) = stdNormalSeq := by
  have hT : T n0 = (fun (u : ℕ → Fin n0 → ℝ) l => (∑ r, u l r) / Real.sqrt n0) ∘
      (MeasurableEquiv.curry ℕ (Fin n0) ℝ) ∘ (fun z (p : ℕ × Fin n0) => z (p.1 * n0 + p.2)) := by
    funext z l; rfl
  rw [hT, ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold stdNormalSeq
  rw [Measure.map_infinitePi_infinitePi_of_inj (f_inj n0)]
  rw [show (Measure.infinitePi fun (p : ℕ × Fin n0) => gaussianReal 0 1) =
    Measure.infinitePi fun (p : ℕ × Fin n0) => (fun (_ : ℕ) (_ : Fin n0) => gaussianReal (0:ℝ) 1) p.1 p.2
    from rfl]
  rw [Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin n0) => gaussianReal (0:ℝ) 1)]
  have hpi := Measure.infinitePi_map_pi (μ := fun _ : ℕ => Measure.infinitePi fun _ : Fin n0 => gaussianReal (0:ℝ) 1)
    (f := fun _ (u : Fin n0 → ℝ) => (∑ r, u r) / Real.sqrt n0) (fun _ => by fun_prop)
  rw [show (fun (u : ℕ → Fin n0 → ℝ) l => (∑ r, u l r) / Real.sqrt n0) =
    (fun x i => (fun (_ : ℕ) (u : Fin n0 → ℝ) => (∑ r, u r) / Real.sqrt n0) i (x i)) from rfl, hpi]
  congr 1
  funext l
  exact map_block_gauss n0 hn0

lemma sum_blocks (n0 : ℕ) (z : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (m * n0), z j = ∑ l ∈ Finset.range m, ∑ r : Fin n0, z (l * n0 + r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.succ_mul, Finset.sum_range_add,
      Fin.sum_univ_eq_sum_range (fun r => z (m * n0 + r))]

lemma zbar_block (n0 : ℕ) (hn0 : 1 ≤ n0) (z : ℕ → ℝ) (m : ℕ) :
    zbar z (m * n0) = zbar (T n0 z) m / Real.sqrt n0 := by
  have hpos : (0 : ℝ) < n0 := by exact_mod_cast hn0
  have hs : Real.sqrt n0 ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hss : Real.sqrt n0 * Real.sqrt n0 = n0 := Real.mul_self_sqrt hpos.le
  unfold zbar T
  rw [sum_blocks, ← Finset.sum_div, div_div, div_div]
  congr 1
  push_cast
  linear_combination (-(m : ℝ)) * hss

lemma blockCross_eq (x : ℝ) (n0 : ℕ) (hn0 : 1 ≤ n0) (z : ℕ → ℝ) :
    GreedyRS.EFG.blockCross x n0 z = crossTime (Real.sqrt n0 * x) 1 (T n0 z) := by
  have hpos : (0 : ℝ) < Real.sqrt n0 := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  unfold GreedyRS.EFG.blockCross crossTime
  refine iInf_congr fun m => iInf_congr_Prop ?_ fun _ => rfl
  rw [zbar_block n0 hn0, div_lt_iff₀ hpos, mul_comm x]

end GRSBlock

open GreedyRS.Greedy GRSHelp GRSBlock in
theorem solution (n0 : ℕ) (hn0 : 1 ≤ n0) (x : ℝ) :
    (∀ z, GreedyRS.Greedy.crossTime x 1 z ≤ GreedyRS.Greedy.crossTime x n0 z) ∧
    (∀ z, GreedyRS.Greedy.crossTime x n0 z ≤ (n0 : ℕ∞) * GreedyRS.EFG.blockCross x n0 z) ∧
    (∀ s : Set ℕ∞, GreedyRS.Greedy.stdNormalSeq (GreedyRS.EFG.blockCross x n0 ⁻¹' s) =
      GreedyRS.Greedy.stdNormalSeq (GreedyRS.Greedy.crossTime (Real.sqrt n0 * x) 1 ⁻¹' s)) := by
  refine ⟨fun z => ?_, fun z => ?_, fun s => ?_⟩
  · exact le_crossTime fun n h1 h2 => crossTime_le (by omega) h2
  · rw [blockCross_eq x n0 hn0]
    rcases eq_or_ne (crossTime (Real.sqrt n0 * x) 1 (T n0 z)) ⊤ with h | h
    · rw [h, ENat.mul_top (by exact_mod_cast (show n0 ≠ 0 by omega))]; exact le_top
    obtain ⟨m, hm, h1, h2⟩ := crossTime_spec (lt_top_iff_ne_top.mpr h)
    rw [hm]
    have hpos : (0 : ℝ) < Real.sqrt n0 := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
    have : zbar z (m * n0) < x := by
      rw [zbar_block n0 hn0, div_lt_iff₀ hpos, mul_comm x]; exact h2
    have hle := crossTime_le (n := m * n0) (show n0 ≤ m * n0 from Nat.le_mul_of_pos_left n0 h1) this
    calc crossTime x n0 z ≤ ((m * n0 : ℕ) : ℕ∞) := hle
      _ = (n0 : ℕ∞) * (m : ℕ∞) := by push_cast; ring
  · have hfun : GreedyRS.EFG.blockCross x n0 = crossTime (Real.sqrt n0 * x) 1 ∘ T n0 := by
      funext z; exact blockCross_eq x n0 hn0 z
    rw [hfun, Set.preimage_comp, ← Measure.map_apply (measurable_T n0)
      (measurable_crossTime _ 1 (MeasurableSet.of_discrete)), map_T n0 hn0]
