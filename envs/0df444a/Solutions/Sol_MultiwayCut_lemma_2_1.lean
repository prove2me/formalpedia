-- Prove2me | solution 1 for MultiwayCut.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:22:03.601404+00:00
-- url     : https://prove2.me/submissions/a2b365a0-dcb3-40a6-abd2-3814527606ee

import Mathlib
import Definitions.Def_MultiwayCut_ExpClocks
import Definitions.Def_MultiwayCut_CutDensity

open MeasureTheory

namespace Aux_MultiwayCut_theorem_1_2_density

open MultiwayCut MeasureTheory ProbabilityTheory Set

/-! ### Shifts -/

lemma shA {k : ℕ} (z : Fin k → ℝ) (a b : Fin k) (ε : ℝ) (c : Fin k) :
    ijShift z a b ε c =
      z c + ε * ((if c = a then (1:ℝ) else 0) - (if c = b then (1:ℝ) else 0)) := by
  simp only [ijShift, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]

lemma sh_a {k : ℕ} (z : Fin k → ℝ) {a b : Fin k} (h : a ≠ b) (ε : ℝ) :
    ijShift z a b ε a = z a + ε := by
  rw [shA, if_pos rfl, if_neg h]; ring

lemma sh_b {k : ℕ} (z : Fin k → ℝ) {a b : Fin k} (h : a ≠ b) (ε : ℝ) :
    ijShift z a b ε b = z b - ε := by
  rw [shA, if_neg (Ne.symm h), if_pos rfl]; ring

lemma sh_o {k : ℕ} (z : Fin k → ℝ) {a b c : Fin k} (hca : c ≠ a) (hcb : c ≠ b) (ε : ℝ) :
    ijShift z a b ε c = z c := by
  rw [shA, if_neg hca, if_neg hcb]; ring

/-! ### The exponential law -/

instance instE : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

lemma gpdf_eq (x : ℝ) :
    gammaPDF 1 1 x = if 0 ≤ x then ENNReal.ofReal (Real.exp (-x)) else 0 := by
  rw [gammaPDF_eq]
  split_ifs with h
  · congr 1
    simp
  · simp

lemma measurable_gpdf : Measurable (gammaPDF 1 1) :=
  (measurable_gammaPDFReal 1 1).ennreal_ofReal

lemma E_Ioi (t : ℝ) (ht : 0 ≤ t) :
    expMeasure 1 (Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun (f := gammaPDF 1 1) (g := fun x => ENNReal.ofReal (Real.exp (-x)))
      measurableSet_Ioi (fun x hx => by rw [gpdf_eq, if_pos (le_trans ht (le_of_lt hx))]),
    ← ofReal_integral_eq_lintegral_ofReal, integral_exp_neg_Ioi]
  · have hI : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi t) := by
      simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) t
    exact hI
  · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)

lemma E_Iio0 : expMeasure 1 (Iio (0 : ℝ)) = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma E_singleton (c : ℝ) : expMeasure 1 {c} = 0 := by
  rw [expMeasure, gammaMeasure]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

lemma lint_E (g : ℝ → ENNReal) (hg : Measurable g) (c : ℝ) (hc : 0 ≤ c)
    (hgx : ∀ x, 0 ≤ x → g x = ENNReal.ofReal (Real.exp (-(c * x)))) :
    ∫⁻ x, g x ∂(expMeasure 1) = ENNReal.ofReal (1 / (c + 1)) := by
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ measurable_gpdf hg]
  have h1 : (gammaPDF 1 1 * g) =
      (Ici (0 : ℝ)).indicator (fun x => ENNReal.ofReal (Real.exp ((-(c + 1)) * x))) := by
    funext x
    simp only [Pi.mul_apply]
    rw [gpdf_eq]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, hgx x hx, indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    · rw [if_neg hx, zero_mul, indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
  have hneg : -(c + 1) < 0 := by linarith
  rw [h1, lintegral_indicator measurableSet_Ici, ← ofReal_integral_eq_lintegral_ofReal,
    integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hneg]
  · congr 1
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq]
  · have hI : IntegrableOn (fun x : ℝ => Real.exp ((-(c + 1)) * x)) (Ici 0) :=
      (integrableOn_exp_mul_Ioi hneg 0).congr_set_ae Ioi_ae_eq_Ici.symm
    exact hI
  · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)

/-! ### Races between exponential clocks -/

def Win {n : ℕ} (w : Fin (n + 1) → ℝ) (l : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  {Z | ∀ m, m ≠ l → 0 < w m → Z l * w m < Z m * w l}

def Bad {n : ℕ} (w : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {Z | (∃ m, Z m < 0) ∨ ∃ m m', m ≠ m' ∧ 0 < w m ∧ 0 < w m' ∧ Z m * w m' = Z m' * w m}

lemma win_meas {n : ℕ} (w : Fin (n + 1) → ℝ) (l : Fin (n + 1)) : MeasurableSet (Win w l) := by
  have e : Win w l = ⋂ m, {Z : Fin (n + 1) → ℝ | m ≠ l → 0 < w m → Z l * w m < Z m * w l} := by
    ext Z
    simp [Win]
  rw [e]
  refine MeasurableSet.iInter (fun m => ?_)
  by_cases h : m ≠ l ∧ 0 < w m
  · have e2 : {Z : Fin (n + 1) → ℝ | m ≠ l → 0 < w m → Z l * w m < Z m * w l} =
        {Z | Z l * w m < Z m * w l} := by
      ext Z
      simp only [Set.mem_setOf_eq]
      exact ⟨fun hZ => hZ h.1 h.2, fun hZ _ _ => hZ⟩
    rw [e2]
    exact measurableSet_lt ((measurable_pi_apply l).mul_const _)
      ((measurable_pi_apply m).mul_const _)
  · have e2 : {Z : Fin (n + 1) → ℝ | m ≠ l → 0 < w m → Z l * w m < Z m * w l} = Set.univ := by
      ext Z
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [e2]
    exact MeasurableSet.univ

lemma race {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : ∀ m, 0 ≤ w m) (l : Fin (n + 1)) (hl : 0 < w l) :
    clockLaw (n + 1) (Win w l) = ENNReal.ofReal (w l / ∑ m, w m) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) l
  set T : Set (ℝ × (Fin n → ℝ)) :=
    {p | ∀ j : Fin n, 0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} with hTdef
  have hT : MeasurableSet T := by
    have e : T = ⋂ j : Fin n, {p : ℝ × (Fin n → ℝ) |
        0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} := by
      ext p
      simp [hTdef]
    rw [e]
    refine MeasurableSet.iInter (fun j => ?_)
    by_cases hj : 0 < w (l.succAbove j)
    · have e2 : {p : ℝ × (Fin n → ℝ) |
          0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} =
          {p | p.1 * w (l.succAbove j) < p.2 j * w l} := by
        ext p
        simp only [Set.mem_setOf_eq]
        exact ⟨fun hp => hp hj, fun hp _ => hp⟩
      rw [e2]
      exact measurableSet_lt (measurable_fst.mul_const _)
        (((measurable_pi_apply j).comp measurable_snd).mul_const _)
    · have e2 : {p : ℝ × (Fin n → ℝ) |
          0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} = Set.univ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1
        exact absurd h1 hj
      rw [e2]
      exact MeasurableSet.univ
  have hWin : Win w l = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) l) ⁻¹' T := by
    ext Z
    simp only [Win, Set.mem_setOf_eq, Set.mem_preimage, hTdef]
    constructor
    · intro h j hj
      exact h _ (Fin.succAbove_ne l j) hj
    · intro h m hm hwm
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hm
      exact h j hwm
  have hsum : ∑ m, w m = w l + ∑ j : Fin n, w (l.succAbove j) := Fin.sum_univ_succAbove w l
  have hS0 : 0 ≤ ∑ j : Fin n, w (l.succAbove j) := Finset.sum_nonneg (fun j _ => hw _)
  rw [hWin, clockLaw, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
  have hmeas : Measurable fun x : ℝ =>
      (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T) :=
    measurable_measure_prodMk_left hT
  have key := lint_E (fun x : ℝ =>
      (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T)) hmeas
    ((∑ j : Fin n, w (l.succAbove j)) / w l) (div_nonneg hS0 hl.le) (by
      intro x hx
      have hslice : Prod.mk x ⁻¹' T = Set.pi Set.univ (fun j : Fin n =>
          if 0 < w (l.succAbove j) then Ioi (x * w (l.succAbove j) / w l) else Set.univ) := by
        ext y
        simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
          true_implies]
        refine forall_congr' (fun j => ?_)
        by_cases hj : 0 < w (l.succAbove j)
        · rw [if_pos hj, Set.mem_Ioi, div_lt_iff₀ hl]
          exact ⟨fun h => h hj, fun h _ => h⟩
        · rw [if_neg hj]
          exact ⟨fun _ => Set.mem_univ _, fun _ h => absurd h hj⟩
      have hfac : ∀ j : Fin n, expMeasure 1 (if 0 < w (l.succAbove j) then
          Ioi (x * w (l.succAbove j) / w l) else Set.univ) =
          ENNReal.ofReal (Real.exp (-(x * w (l.succAbove j) / w l))) := by
        intro j
        by_cases hj : 0 < w (l.succAbove j)
        · rw [if_pos hj, E_Ioi _ (div_nonneg (mul_nonneg hx hj.le) hl.le)]
        · have hj0 : w (l.succAbove j) = 0 := le_antisymm (not_lt.mp hj) (hw _)
          rw [if_neg hj, measure_univ, hj0, mul_zero, zero_div, neg_zero, Real.exp_zero,
            ENNReal.ofReal_one]
      show (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T) = _
      rw [hslice, Measure.pi_pi]
      calc ∏ j : Fin n, (expMeasure (1 : ℝ)) (if 0 < w (l.succAbove j) then
            Ioi (x * w (l.succAbove j) / w l) else Set.univ)
          = ∏ j : Fin n, ENNReal.ofReal (Real.exp (-(x * w (l.succAbove j) / w l))) :=
            Finset.prod_congr rfl (fun j _ => hfac j)
        _ = ENNReal.ofReal (Real.exp (-((∑ j : Fin n, w (l.succAbove j)) / w l * x))) := by
            rw [← ENNReal.ofReal_prod_of_nonneg
              (f := fun j => Real.exp (-(x * w (l.succAbove j) / w l)))
              (fun j _ => (Real.exp_pos _).le), ← Real.exp_sum]
            congr 2
            rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum]
            ring)
  have key' : ∫⁻ x, (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T)
      ∂((fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) l) =
      ENNReal.ofReal (1 / ((∑ j : Fin n, w (l.succAbove j)) / w l + 1)) := key
  rw [key', hsum]
  congr 1
  rw [div_add_one hl.ne', one_div_div, add_comm]

lemma neg_null {n : ℕ} (m : Fin (n + 1)) : clockLaw (n + 1) {Z | Z m < 0} = 0 := by
  have hmp := measurePreserving_eval (fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) m
  have e : {Z : Fin (n + 1) → ℝ | Z m < 0} = Function.eval m ⁻¹' Iio 0 := rfl
  rw [e, clockLaw, hmp.measure_preimage measurableSet_Iio.nullMeasurableSet]
  exact E_Iio0

lemma tie_null {n : ℕ} (m m' : Fin (n + 1)) (hmm : m ≠ m') (a b : ℝ) (ha : 0 < a) :
    clockLaw (n + 1) {Z | Z m * a = Z m' * b} = 0 := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) m
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hmm)
  set T : Set (ℝ × (Fin n → ℝ)) := {p | p.1 * a = p.2 j * b} with hTdef
  have hT : MeasurableSet T := measurableSet_eq_fun (measurable_fst.mul_const _)
    (((measurable_pi_apply j).comp measurable_snd).mul_const _)
  have hset : {Z : Fin (n + 1) → ℝ | Z m * a = Z m' * b} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) m) ⁻¹' T := by
    ext Z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hTdef]
    rw [← hj]
    rfl
  rw [hset, clockLaw, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
  refine (lintegral_congr (fun y => ?_)).trans lintegral_zero
  have e : (fun x => (x, y)) ⁻¹' T = {y j * b / a} := by
    ext x
    simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [eq_div_iff ha.ne']
  rw [e]
  exact E_singleton _

lemma bad_null {n : ℕ} (w : Fin (n + 1) → ℝ) : clockLaw (n + 1) (Bad w) = 0 := by
  have h1 : Bad w ⊆ (⋃ m, {Z : Fin (n + 1) → ℝ | Z m < 0}) ∪
      ⋃ m, ⋃ m', {Z : Fin (n + 1) → ℝ |
        m ≠ m' ∧ 0 < w m ∧ 0 < w m' ∧ Z m * w m' = Z m' * w m} := by
    intro Z hZ
    rcases hZ with ⟨m, hm⟩ | ⟨m, m', h⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨m, hm⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨m', h⟩⟩)
  refine measure_mono_null h1 (measure_union_null (measure_iUnion_null (fun m => neg_null m))
    (measure_iUnion_null (fun m => measure_iUnion_null (fun m' => ?_))))
  by_cases hc : m ≠ m' ∧ 0 < w m ∧ 0 < w m'
  · exact measure_mono_null (fun Z hZ => hZ.2.2.2) (tie_null m m' hc.1 (w m') (w m) hc.2.2)
  · have e : {Z : Fin (n + 1) → ℝ | m ≠ m' ∧ 0 < w m ∧ 0 < w m' ∧ Z m * w m' = Z m' * w m} =
        ∅ := by
      ext Z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hc ⟨h.1, h.2.1, h.2.2.1⟩
    rw [e]
    exact measure_empty

lemma win_label {n : ℕ} (w : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (hl : 0 < w l)
    (Z : Fin (n + 1) → ℝ) (hZ : Z ∈ Win w l) : expClock Z w = l := by
  have hlS : l ∈ Finset.univ.filter
      (fun i => 0 < w i ∧ ∀ j, 0 < w j → Z i * w j ≤ Z j * w i) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hl, fun j hj => ?_⟩
    by_cases hjl : j = l
    · subst hjl
      exact le_refl _
    · exact (hZ j hjl hj).le
  have huniq : ∀ i ∈ Finset.univ.filter
      (fun i => 0 < w i ∧ ∀ j, 0 < w j → Z i * w j ≤ Z j * w i), i = l := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hil
    have h1 := hi.2.2 l hl
    have h2 := hZ i hil hi.2.1
    linarith
  simp only [expClock]
  rw [dif_pos ⟨l, hlS⟩]
  exact huniq _ (Finset.min'_mem _ _)

lemma label_sub {n : ℕ} (w : Fin (n + 1) → ℝ) (hsupp : ∃ m, 0 < w m) (l : Fin (n + 1))
    (Z : Fin (n + 1) → ℝ) (hZ : expClock Z w = l) : (0 < w l ∧ Z ∈ Win w l) ∨ Z ∈ Bad w := by
  have hne : (Finset.univ.filter
      (fun i => 0 < w i ∧ ∀ j, 0 < w j → Z i * w j ≤ Z j * w i)).Nonempty := by
    obtain ⟨m0, hm0⟩ := hsupp
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => 0 < w i))
      (fun i => Z i / w i) ⟨m0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm0⟩⟩
    rw [Finset.mem_filter] at hi
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2, fun j hj => ?_⟩⟩
    have h := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    rw [div_le_div_iff₀ hi.2 hj] at h
    exact h
  simp only [expClock] at hZ
  rw [dif_pos hne] at hZ
  have hmem := Finset.min'_mem _ hne
  rw [hZ, Finset.mem_filter] at hmem
  obtain ⟨_, hwl, hle⟩ := hmem
  by_cases hwin : Z ∈ Win w l
  · exact Or.inl ⟨hwl, hwin⟩
  · right
    simp only [Win, Set.mem_setOf_eq, not_forall, not_lt] at hwin
    obtain ⟨m, hml, hwm, hge⟩ := hwin
    have hle' := hle m hwm
    exact Or.inr ⟨l, m, Ne.symm hml, hwl, hwm, le_antisymm hle' hge⟩

lemma diff_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A B N : Set α) (hB : MeasurableSet B) (hBA : B ⊆ A ∪ N) (hN : μ N = 0) :
    μ (A \ B) ≤ μ A - μ B := by
  have h1 := measure_sdiff_add_inter (μ := μ) A hB
  have h2 : μ B ≤ μ (A ∩ B) := by
    calc μ B ≤ μ (B ∩ A) + μ (B \ A) := measure_le_inter_add_sdiff μ B A
      _ ≤ μ (A ∩ B) + μ N := by
          rw [Set.inter_comm]
          exact add_le_add le_rfl (measure_mono (fun x hx => (hBA hx.1).resolve_left hx.2))
      _ = μ (A ∩ B) := by rw [hN, add_zero]
  apply ENNReal.le_sub_of_add_le_right (measure_ne_top μ B)
  calc μ (A \ B) + μ B ≤ μ (A \ B) + μ (A ∩ B) := add_le_add le_rfl h2
    _ = μ A := h1

/-! ### Lemma 2.1: the exponential clocks separation bound -/

set_option maxHeartbeats 1600000 in
lemma sepExp_le {n : ℕ} (u v : Fin (n + 1) → ℝ) (hu : u ∈ stdSimplex ℝ (Fin (n + 1)))
    (hv : v ∈ stdSimplex ℝ (Fin (n + 1))) (a b : Fin (n + 1)) (hab : a ≠ b) (ε : ℝ)
    (hε : 0 ≤ ε) (huv : v = ijShift u a b ε) : sepExp u v ≤ ε * (2 - u a - u b) := by
  haveI : IsProbabilityMeasure (clockLaw (n + 1)) := by
    unfold clockLaw
    infer_instance
  have hva : v a = u a + ε := by rw [huv, sh_a u hab]
  have hvb : v b = u b - ε := by rw [huv, sh_b u hab]
  have hvo : ∀ m, m ≠ a → m ≠ b → v m = u m := fun m h1 h2 => by rw [huv, sh_o u h1 h2]
  have hu0 : ∀ m, 0 ≤ u m := hu.1
  have hv0 : ∀ m, 0 ≤ v m := hv.1
  have hsupp : ∃ m, 0 < u m := by
    by_contra h
    push_neg at h
    have h1 : ∑ m, u m ≤ 0 := Finset.sum_nonpos (fun m _ => h m)
    have h2 := hu.2
    linarith
  have hvb0 : 0 ≤ u b - ε := by rw [← hvb]; exact hv0 b
  have hab2 : u a + u b ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {a, b})
      (f := u) (fun m _ _ => hu0 m)
    rw [Finset.sum_pair hab, hu.2] at h
    exact h
  set ws : Fin (n + 1) → ℝ := fun m => if m = a then u a + ε else u m with hws
  have hws0 : ∀ m, 0 ≤ ws m := by
    intro m
    simp only [hws]
    split_ifs
    · linarith [hu0 a]
    · exact hu0 m
  have hwsum : ∑ m, ws m = 1 + ε := by
    have e : ∀ m, ws m = u m + (if m = a then ε else 0) := by
      intro m
      simp only [hws]
      split_ifs with h
      · rw [h]
      · ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_add_distrib, hu.2,
      Finset.sum_ite_eq']
    simp
  set μ := clockLaw (n + 1) with hμ
  -- reduction to a race
  have hred : ∀ (l : Fin (n + 1)) (W' : Set (Fin (n + 1) → ℝ)),
      W' ⊆ {Z | expClock Z v = l} ∪ Bad u →
      {Z | expClock Z u = l} \ {Z | expClock Z v = l} ⊆ (Win u l \ W') ∪ Bad u := by
    intro l W' hW' Z hZ
    rcases label_sub u hsupp l Z hZ.1 with ⟨_, hwin⟩ | hbad
    · by_cases hW : Z ∈ W'
      · rcases hW' hW with h | h
        · exact absurd h hZ.2
        · exact Or.inr h
      · exact Or.inl ⟨hwin, hW⟩
    · exact Or.inr hbad
  -- the three cases
  have bound_a : μ ({Z | expClock Z u = a} \ {Z | expClock Z v = a}) ≤ ENNReal.ofReal 0 := by
    have hsub : {Z | expClock Z u = a} \ {Z | expClock Z v = a} ⊆ Bad u := by
      intro Z hZ
      rcases label_sub u hsupp a Z hZ.1 with ⟨hpos, hwin⟩ | hbad
      · by_cases hneg : ∃ m, Z m < 0
        · exact Or.inl hneg
        · push_neg at hneg
          exfalso
          apply hZ.2
          have hvap : 0 < v a := by rw [hva]; linarith
          refine win_label v a hvap Z (fun m hm hvm => ?_)
          rw [hva]
          by_cases hmb : m = b
          · rw [hmb] at hm hvm ⊢
            rw [hvb] at hvm ⊢
            have hub : 0 < u b := by linarith
            have h1 := hwin b hm hub
            nlinarith [mul_nonneg (hneg a) hε, mul_nonneg (hneg b) hε]
          · rw [hvo m hm hmb] at hvm ⊢
            have h1 := hwin m hm hvm
            nlinarith [mul_nonneg (hneg m) hε]
      · exact hbad
    calc μ _ ≤ μ (Bad u) := measure_mono hsub
      _ = 0 := bad_null u
      _ ≤ ENNReal.ofReal 0 := bot_le
  have bound_b : μ ({Z | expClock Z u = b} \ {Z | expClock Z v = b}) ≤ ENNReal.ofReal ε := by
    by_cases hub : u b = 0
    · have hsub : {Z | expClock Z u = b} \ {Z | expClock Z v = b} ⊆ Bad u := by
        intro Z hZ
        rcases label_sub u hsupp b Z hZ.1 with ⟨hpos, _⟩ | hbad
        · exact absurd hub (ne_of_gt hpos)
        · exact hbad
      calc μ _ ≤ μ (Bad u) := measure_mono hsub
        _ = 0 := bad_null u
        _ ≤ ENNReal.ofReal ε := bot_le
    have hubp : 0 < u b := lt_of_le_of_ne (hu0 b) (Ne.symm hub)
    by_cases hvbz : u b - ε = 0
    · have hsub : {Z | expClock Z u = b} \ {Z | expClock Z v = b} ⊆ Win u b ∪ Bad u := by
        intro Z hZ
        rcases label_sub u hsupp b Z hZ.1 with ⟨_, hwin⟩ | hbad
        · exact Or.inl hwin
        · exact Or.inr hbad
      calc μ _ ≤ μ (Win u b ∪ Bad u) := measure_mono hsub
        _ ≤ μ (Win u b) + μ (Bad u) := measure_union_le _ _
        _ = ENNReal.ofReal ε := by
          rw [bad_null u, add_zero, hμ, race u hu0 b hubp, hu.2, div_one]
          congr 1
          linarith
    · have hvbp : 0 < v b := by rw [hvb]; exact lt_of_le_of_ne hvb0 (Ne.symm hvbz)
      have hsub := hred b (Win v b) (fun Z hZ => Or.inl (win_label v b hvbp Z hZ))
      have hincl : Win v b ⊆ Win u b ∪ Bad u := by
        intro Z hZ
        by_cases hneg : ∃ m, Z m < 0
        · exact Or.inr (Or.inl hneg)
        · push_neg at hneg
          left
          intro m hm hum
          by_cases hma : m = a
          · rw [hma] at hm hum ⊢
            have hvap : 0 < v a := by rw [hva]; linarith
            have h1 := hZ a hm hvap
            rw [hva, hvb] at h1
            nlinarith [mul_nonneg (hneg a) hε, mul_nonneg (hneg b) hε]
          · have hvm : v m = u m := hvo m hma hm
            have h1 := hZ m hm (by rw [hvm]; exact hum)
            rw [hvm, hvb] at h1
            nlinarith [mul_nonneg (hneg m) hε]
      calc μ _ ≤ μ ((Win u b \ Win v b) ∪ Bad u) := measure_mono hsub
        _ ≤ μ (Win u b \ Win v b) + μ (Bad u) := measure_union_le _ _
        _ ≤ (μ (Win u b) - μ (Win v b)) + 0 :=
          add_le_add (diff_le μ _ _ _ (win_meas v b) hincl (bad_null u)) (bad_null u).le
        _ = ENNReal.ofReal ε := by
          rw [add_zero, hμ, race u hu0 b hubp, race v hv0 b hvbp, hu.2, hv.2, div_one, div_one,
            ← ENNReal.ofReal_sub _ (hv0 b), hvb]
          congr 1
          ring
  have bound_R : ∀ l, l ≠ a → l ≠ b →
      μ ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) ≤
        ENNReal.ofReal (u l - u l / (1 + ε)) := by
    intro l hla hlb
    by_cases hul : u l = 0
    · have hsub : {Z | expClock Z u = l} \ {Z | expClock Z v = l} ⊆ Bad u := by
        intro Z hZ
        rcases label_sub u hsupp l Z hZ.1 with ⟨hpos, _⟩ | hbad
        · exact absurd hul (ne_of_gt hpos)
        · exact hbad
      calc μ _ ≤ μ (Bad u) := measure_mono hsub
        _ = 0 := bad_null u
        _ ≤ _ := bot_le
    have hulp : 0 < u l := lt_of_le_of_ne (hu0 l) (Ne.symm hul)
    have hwsl : ws l = u l := by simp only [hws, if_neg hla]
    have hvl : v l = u l := hvo l hla hlb
    have hincl1 : Win ws l ⊆ Win u l ∪ Bad u := by
      intro Z hZ
      by_cases hneg : ∃ m, Z m < 0
      · exact Or.inr (Or.inl hneg)
      · push_neg at hneg
        left
        intro m hm hum
        by_cases hma : m = a
        · rw [hma] at hm hum ⊢
          have hwa : ws a = u a + ε := by simp only [hws, if_pos rfl]
          have h1 := hZ a hm (by rw [hwa]; linarith)
          rw [hwa, hwsl] at h1
          nlinarith [mul_nonneg (hneg l) hε]
        · have hwm : ws m = u m := by simp only [hws, if_neg hma]
          have h1 := hZ m hm (by rw [hwm]; exact hum)
          rw [hwm, hwsl] at h1
          exact h1
    have hincl2 : Win ws l ⊆ {Z | expClock Z v = l} ∪ Bad u := by
      intro Z hZ
      by_cases hneg : ∃ m, Z m < 0
      · exact Or.inr (Or.inl hneg)
      · push_neg at hneg
        left
        refine win_label v l (by rw [hvl]; exact hulp) Z (fun m hm hvm => ?_)
        rw [hvl]
        by_cases hma : m = a
        · rw [hma] at hm hvm ⊢
          have hwa : ws a = u a + ε := by simp only [hws, if_pos rfl]
          have h1 := hZ a hm (by rw [hwa, ← hva]; exact hvm)
          rw [hwa, hwsl] at h1
          rw [hva]
          exact h1
        · by_cases hmb : m = b
          · rw [hmb] at hm hvm ⊢
            have hwb : ws b = u b := by simp only [hws, if_neg (Ne.symm hab)]
            rw [hvb] at hvm ⊢
            have hub : 0 < u b := by linarith
            have h1 := hZ b hm (by rw [hwb]; exact hub)
            rw [hwb, hwsl] at h1
            nlinarith [mul_nonneg (hneg l) hε]
          · have hwm : ws m = u m := by simp only [hws, if_neg hma]
            have hvm' : v m = u m := hvo m hma hmb
            rw [hvm'] at hvm ⊢
            have h1 := hZ m hm (by rw [hwm]; exact hvm)
            rw [hwm, hwsl] at h1
            exact h1
    have hsub := hred l (Win ws l) hincl2
    have hdiv0 : 0 ≤ u l / (1 + ε) := div_nonneg (hu0 l) (by linarith)
    calc μ _ ≤ μ ((Win u l \ Win ws l) ∪ Bad u) := measure_mono hsub
      _ ≤ μ (Win u l \ Win ws l) + μ (Bad u) := measure_union_le _ _
      _ ≤ (μ (Win u l) - μ (Win ws l)) + 0 :=
        add_le_add (diff_le μ _ _ _ (win_meas ws l) hincl1 (bad_null u)) (bad_null u).le
      _ = ENNReal.ofReal (u l - u l / (1 + ε)) := by
        rw [add_zero, hμ, race u hu0 l hulp, race ws hws0 l (by rw [hwsl]; exact hulp), hu.2,
          hwsum, div_one, hwsl, ← ENNReal.ofReal_sub _ hdiv0]
  -- assemble
  set B : Fin (n + 1) → ℝ := fun l =>
    if l = b then ε else if l = a then 0 else u l - u l / (1 + ε) with hB
  have hTl : ∀ l, μ ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) ≤ ENNReal.ofReal (B l) := by
    intro l
    by_cases hlb : l = b
    · rw [hlb]
      simp only [hB, if_pos rfl]
      exact bound_b
    · by_cases hla : l = a
      · rw [hla]
        simp only [hB, if_neg hab, if_pos rfl]
        exact bound_a
      · simp only [hB, if_neg hlb, if_neg hla]
        exact bound_R l hla hlb
  have hB0 : ∀ l, 0 ≤ B l := by
    intro l
    simp only [hB]
    split_ifs
    · exact hε
    · exact le_refl _
    · exact sub_nonneg.mpr (div_le_self (hu0 l) (by linarith))
  have hBle : ∀ l, B l ≤ ε * u l + (if l = b then ε * (1 - u b) else 0) -
      (if l = a then ε * u a else 0) := by
    intro l
    simp only [hB]
    by_cases hlb : l = b
    · rw [if_pos hlb, if_pos hlb, if_neg (fun h => hab (h.symm.trans hlb)), hlb]
      linarith
    · by_cases hla : l = a
      · rw [if_neg hlb, if_pos hla, if_neg hlb, if_pos hla, hla]
        linarith
      · rw [if_neg hlb, if_neg hla, if_neg hlb, if_neg hla]
        have h1 : u l - ε * u l ≤ u l / (1 + ε) := by
          rw [le_div_iff₀ (by linarith)]
          nlinarith [mul_nonneg (hu0 l) (sq_nonneg ε)]
        linarith
  have hsumC : ∑ l, (ε * u l + (if l = b then ε * (1 - u b) else 0) -
      (if l = a then ε * u a else 0)) = ε * (2 - u a - u b) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hu.2,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  have hBsum : ∑ l, B l ≤ ε * (2 - u a - u b) := by
    rw [← hsumC]
    exact Finset.sum_le_sum (fun l _ => hBle l)
  have hcover : {Z | expClock Z u ≠ expClock Z v} ⊆
      ⋃ l, ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) := by
    intro Z hZ
    exact Set.mem_iUnion.mpr ⟨expClock Z u, rfl, fun h => hZ (Eq.symm h)⟩
  have hS : μ {Z | expClock Z u ≠ expClock Z v} ≤ ENNReal.ofReal (ε * (2 - u a - u b)) := by
    calc μ {Z | expClock Z u ≠ expClock Z v}
        ≤ μ (⋃ l, ({Z | expClock Z u = l} \ {Z | expClock Z v = l})) := measure_mono hcover
      _ ≤ ∑ l, μ ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) :=
          measure_iUnion_fintype_le μ _
      _ ≤ ∑ l, ENNReal.ofReal (B l) := Finset.sum_le_sum (fun l _ => hTl l)
      _ = ENNReal.ofReal (∑ l, B l) := (ENNReal.ofReal_sum_of_nonneg (fun l _ => hB0 l)).symm
      _ ≤ ENNReal.ofReal (ε * (2 - u a - u b)) := ENNReal.ofReal_le_ofReal hBsum
  have hnn : 0 ≤ ε * (2 - u a - u b) := mul_nonneg hε (by linarith)
  unfold sepExp
  exact ENNReal.toReal_le_of_le_ofReal hnn hS

end Aux_MultiwayCut_theorem_1_2_density

open MultiwayCut in
theorem solution {k : ℕ} [NeZero k] (u v : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k))
    (hv : v ∈ stdSimplex ℝ (Fin k)) (i j : Fin k) (hij : i ≠ j) (ε : ℝ) (hε : 0 ≤ ε)
    (huv : v = ijShift u i j ε) :
    sepExp u v ≤ ε * (2 - u i - u j) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := NeZero.ne k; omega⟩
  exact Aux_MultiwayCut_theorem_1_2_density.sepExp_le u v hu hv i j hij ε hε huv
