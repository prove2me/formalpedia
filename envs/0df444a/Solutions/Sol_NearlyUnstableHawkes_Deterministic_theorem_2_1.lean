-- Prove2me | solution 1 for NearlyUnstableHawkes.Deterministic.theorem_2_1
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T14:32:07.814754+00:00
-- url     : https://prove2.me/submissions/65380a3f-cd9d-4c70-a859-bdb82ab33a43

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace D4e31

open NearlyUnstableHawkes.Heston

/-! ### Counting functions of finite sets of reals -/

/-- `#{y ∈ F : y ≤ t}`. -/
noncomputable def cnt (F : Finset ℝ) (t : ℝ) : ℕ := (F.filter (fun y => y ≤ t)).card

lemma cnt_mono (F : Finset ℝ) {s t : ℝ} (h : s ≤ t) : cnt F s ≤ cnt F t := by
  unfold cnt
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, hy.2.trans h⟩

lemma cnt_eventually_right (F : Finset ℝ) (t : ℝ) :
    ∀ᶠ u in 𝓝[≥] t, cnt F u = cnt F t := by
  have h1 : ∀ᶠ u in 𝓝[≥] t, ∀ y ∈ F, t < y → u < y := by
    rw [Filter.eventually_all_finset]
    intro y _
    by_cases hty : t < y
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hty)] with u hu _ using hu
    · exact Filter.Eventually.of_forall (fun u h => absurd h hty)
  filter_upwards [h1, self_mem_nhdsWithin] with u hu htu
  have htu' : t ≤ u := htu
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro y hy
  constructor
  · intro hyu
    by_contra hyt
    push Not at hyt
    exact absurd hyu (not_le.mpr (hu y hy hyt))
  · intro hyt
    exact hyt.trans htu'

lemma cnt_eventually_left (F : Finset ℝ) (t : ℝ) :
    ∀ᶠ u in 𝓝[<] t, cnt F u = (F.filter (fun y => y < t)).card := by
  have h1 : ∀ᶠ u in 𝓝[<] t, ∀ y ∈ F, y < t → y < u := by
    rw [Filter.eventually_all_finset]
    intro y _
    by_cases hyt : y < t
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hyt)] with u hu _ using hu
    · exact Filter.Eventually.of_forall (fun u h => absurd h hyt)
  filter_upwards [h1, self_mem_nhdsWithin] with u hu hut
  have hut' : u < t := hut
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro y hy
  constructor
  · intro hyu
    exact lt_of_le_of_lt hyu hut'
  · intro hyt
    exact (hu y hy hyt).le

lemma leftLim_cnt (F : Finset ℝ) (t : ℝ) :
    Function.leftLim (fun u => (cnt F u : ℝ)) t = ((F.filter (fun y => y < t)).card : ℝ) := by
  apply leftLim_eq_of_tendsto
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [cnt_eventually_left F t] with u hu
  rw [hu]

lemma jump_cnt (F : Finset ℝ) (t : ℝ) :
    jump (fun u => (cnt F u : ℝ)) t = if t ∈ F then 1 else 0 := by
  unfold jump
  rw [leftLim_cnt]
  have hsplit : F.filter (fun y => y ≤ t) =
      F.filter (fun y => y < t) ∪ F.filter (fun y => y = t) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro y _
    exact le_iff_lt_or_eq
  have hdisj : Disjoint (F.filter (fun y => y < t)) (F.filter (fun y => y = t)) := by
    rw [Finset.disjoint_filter]
    intro y _ h1 h2
    exact (ne_of_lt h1) h2
  show ((cnt F t : ℕ) : ℝ) - _ = _
  unfold cnt
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.filter_eq']
  split_ifs <;> simp

lemma jumpSumOn_cnt (F : Finset ℝ) (g : ℝ → ℝ) (S : Set ℝ) [DecidablePred (· ∈ S)] :
    jumpSumOn (fun u => (cnt F u : ℝ)) g S = ∑ y ∈ F.filter (fun y => y ∈ S), g y := by
  unfold jumpSumOn
  refine (finsum_congr fun s => ?_).trans (finsum_mem_coe_finset g _)
  rw [finsum_eq_if, finsum_eq_if, jump_cnt]
  by_cases hF : s ∈ F <;> by_cases hS : s ∈ S <;> simp [hF, hS]

lemma isSimpleCounting_cnt {Ω : Type*} [MeasurableSpace Ω] (G : Ω → Finset ℝ)
    (hG : ∀ ω, ∀ y ∈ G ω, 0 < y) (hmeas : ∀ t, Measurable (fun ω => cnt (G ω) t)) :
    IsSimpleCounting (fun t ω => cnt (G ω) t) where
  meas := hmeas
  zero := fun ω => by
    show cnt (G ω) 0 = 0
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy
    exact not_le.mpr (hG ω y hy)
  mono := fun ω s _ t _ hst => cnt_mono _ hst
  rcont := fun ω t _ => by
    unfold ContinuousWithinAt
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [cnt_eventually_right (G ω) t] with u hu
    simp only [path, hu]
  unit_jumps := fun ω t _ => by
    show jump (fun u => (cnt (G ω) u : ℝ)) t ≤ 1
    rw [jump_cnt]
    split_ifs <;> norm_num

lemma cnt_sub_ge (F E : Finset ℝ) {a b : ℝ} (hab : a ≤ b) (hE : E ⊆ F) (hEab : ∀ y ∈ E, a < y ∧ y ≤ b) :
    E.card ≤ cnt F b - cnt F a := by
  apply Nat.le_sub_of_add_le
  unfold cnt
  have hdisj : Disjoint (F.filter (fun y => y ≤ a)) E := by
    rw [Finset.disjoint_left]
    intro y hy hyE
    simp only [Finset.mem_filter] at hy
    exact absurd hy.2 (not_le.mpr (hEab y hyE).1)
  rw [add_comm, ← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_union.mp hy with hy | hy
  · simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.trans hab⟩
  · simp only [Finset.mem_filter]
    exact ⟨hE hy, (hEab y hy).2⟩

/-! ### Saturation of the natural filtration -/

lemma natFiltration2_saturated {Ω : Type*} (Np Nm : ℝ → Ω → ℕ) (a : ℝ)
    (A : Set Ω) (hA : MeasurableSet[natFiltration2 Np Nm a] A) {ω ω' : Ω}
    (h : ∀ s ∈ Icc (0 : ℝ) a, Np s ω' = Np s ω ∧ Nm s ω' = Nm s ω) (hω : ω ∈ A) : ω' ∈ A := by
  let F : Ω → (Icc (0 : ℝ) a → ℕ × ℕ) := fun ω s => (Np s ω, Nm s ω)
  have hle : natFiltration2 Np Nm a ≤ MeasurableSpace.comap F ⊤ := by
    refine iSup₂_le fun s hs => sup_le ?_ ?_
    · have : Np s = (fun f : Icc (0 : ℝ) a → ℕ × ℕ => (f ⟨s, hs⟩).1) ∘ F := rfl
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono le_top
    · have : Nm s = (fun f : Icc (0 : ℝ) a → ℕ × ℕ => (f ⟨s, hs⟩).2) ∘ F := rfl
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono le_top
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.mp (hle _ hA)
  rw [← hB] at hω ⊢
  have hF : F ω' = F ω := funext fun s => Prod.ext (h s s.2).1 (h s s.2).2
  simp only [Set.mem_preimage] at hω ⊢
  rw [hF]
  exact hω

/-! ### The sample space: lists of clusters -/

/-- A cluster `(k, m, j, isPlus)`: points in the dyadic cell `(m/2^k, (m+1)/2^k)`; `j` is a free tag. -/
abbrev Cl := ℕ × ℕ × ℕ × Bool

abbrev Om := List Cl

/-- The `r` points of a cluster: `(m(r+1)+i+1)/(2^k(r+1))`, `i < r`. -/
noncomputable def clPts (c : Cl) (r : ℕ) : List ℝ :=
  (List.range r).map (fun i =>
    ((c.2.1 * (r + 1) + i + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ c.1 * ((r : ℝ) + 1)))

/-- The size of the head cluster of a list: `2^(encode ℓ + 1)`. -/
def csize (ℓ : Om) : ℕ := 2 ^ (Encodable.encode ℓ + 1)

noncomputable def plusL : Om → List ℝ
  | [] => []
  | c :: ℓ => (if c.2.2.2 then clPts c (csize (c :: ℓ)) else []) ++ plusL ℓ

noncomputable def minusL : Om → List ℝ
  | [] => []
  | c :: ℓ => (if c.2.2.2 then [] else (clPts c (csize (c :: ℓ))).map (fun x => Real.sqrt 2 * x)) ++
      minusL ℓ

noncomputable def plusSet (ω : Om) : Finset ℝ := (plusL ω).toFinset

noncomputable def minusSet (ω : Om) : Finset ℝ := (minusL ω).toFinset

lemma clPts_rat (c : Cl) (r : ℕ) : ∀ x ∈ clPts c r, ∃ q : ℚ, 0 < q ∧ (q : ℝ) = x := by
  intro x hx
  simp only [clPts, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  refine ⟨((c.2.1 * (r + 1) + i + 1 : ℕ) : ℚ) / ((2 : ℚ) ^ c.1 * ((r : ℚ) + 1)),
    by positivity, by push_cast; ring⟩

lemma clPts_pos (c : Cl) (r : ℕ) : ∀ x ∈ clPts c r, 0 < x := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := clPts_rat c r x hx
  exact_mod_cast hq

lemma clPts_nodup (c : Cl) (r : ℕ) : (clPts c r).Nodup := by
  unfold clPts
  refine List.Nodup.map ?_ (List.nodup_range)
  intro i i' h
  have hD : (0 : ℝ) < (2 : ℝ) ^ c.1 * ((r : ℝ) + 1) := by positivity
  have h' := (div_left_inj' hD.ne').mp h
  have h'' : (c.2.1 * (r + 1) + i + 1 : ℕ) = c.2.1 * (r + 1) + i' + 1 := by
    exact_mod_cast h'
  omega

lemma clPts_card (c : Cl) (r : ℕ) : (clPts c r).toFinset.card = r := by
  rw [List.toFinset_card_of_nodup (clPts_nodup c r)]
  simp [clPts]

lemma clPts_card_sqrt (c : Cl) (r : ℕ) :
    ((clPts c r).map (fun x => Real.sqrt 2 * x)).toFinset.card = r := by
  have hinj : Function.Injective (fun x : ℝ => Real.sqrt 2 * x) := by
    intro x y h
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    exact mul_left_cancel₀ h2 h
  rw [List.toFinset_card_of_nodup ((clPts_nodup c r).map hinj)]
  simp [clPts]

/-- All points of a cluster lie in `(m/2^k, (m+1)/2^k]`. -/
lemma clPts_bounds (c : Cl) (r : ℕ) : ∀ x ∈ clPts c r,
    (c.2.1 : ℝ) / 2 ^ c.1 < x ∧ x ≤ ((c.2.1 : ℝ) + 1) / 2 ^ c.1 := by
  intro x hx
  simp only [clPts, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ c.1 := by positivity
  have hi' : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  push_cast
  constructor
  · rw [div_lt_div_iff₀ h2 (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) h2]
    nlinarith

/-- Every window `(a, b]` with `0 ≤ a < b` contains the points of all clusters of some cell. -/
lemma exists_cell (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∃ k m : ℕ, ∀ j : ℕ, ∀ s : Bool, ∀ r : ℕ, ∀ x ∈ clPts (k, m, j, s) r, a < x ∧ x ≤ b := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < (b - a) / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨k, ⌊a * 2 ^ k⌋₊ + 1, fun j s r x hx => ?_⟩
  have hb := clPts_bounds (k, ⌊a * 2 ^ k⌋₊ + 1, j, s) r x hx
  simp only at hb
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hfl := Nat.lt_floor_add_one (a * 2 ^ k)
  have hfl2 := Nat.floor_le (by positivity : 0 ≤ a * 2 ^ k)
  have hk' : ((1 : ℝ) / 2) ^ k * 2 ^ k = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀ _ h2.ne']
  constructor
  · refine lt_of_le_of_lt ?_ hb.1
    rw [le_div_iff₀ h2]
    push_cast
    linarith
  · refine hb.2.trans ?_
    rw [div_le_iff₀ h2]
    push_cast
    have h4 : 2 < (b - a) * 2 ^ k := by nlinarith
    nlinarith

lemma plusL_rat (ω : Om) : ∀ x ∈ plusL ω, ∃ q : ℚ, 0 < q ∧ (q : ℝ) = x := by
  induction ω with
  | nil => simp [plusL]
  | cons c ℓ ih =>
    intro x hx
    simp only [plusL, List.mem_append] at hx
    rcases hx with hx | hx
    · split_ifs at hx with h
      · exact clPts_rat _ _ x hx
      · simp at hx
    · exact ih x hx

lemma minusL_sqrt (ω : Om) : ∀ x ∈ minusL ω, ∃ q : ℚ, 0 < q ∧ Real.sqrt 2 * q = x := by
  induction ω with
  | nil => simp [minusL]
  | cons c ℓ ih =>
    intro x hx
    simp only [minusL, List.mem_append] at hx
    rcases hx with hx | hx
    · split_ifs at hx with h
      · simp at hx
      · simp only [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨q, hq, rfl⟩ := clPts_rat _ _ y hy
        exact ⟨q, hq, rfl⟩
    · exact ih x hx

lemma plus_minus_disjoint (ω : Om) (t : ℝ) : ¬ (t ∈ plusSet ω ∧ t ∈ minusSet ω) := by
  rintro ⟨hp, hm⟩
  simp only [plusSet, minusSet, List.mem_toFinset] at hp hm
  obtain ⟨q, -, hq⟩ := plusL_rat ω t hp
  obtain ⟨q', hq'0, hq'⟩ := minusL_sqrt ω t hm
  apply irrational_sqrt_two
  refine ⟨q / q', ?_⟩
  have : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'0.ne'
  push_cast
  rw [hq, ← hq']
  field_simp

lemma plusSet_pos (ω : Om) : ∀ y ∈ plusSet ω, 0 < y := by
  intro y hy
  simp only [plusSet, List.mem_toFinset] at hy
  obtain ⟨q, hq, rfl⟩ := plusL_rat ω y hy
  exact_mod_cast hq

lemma minusSet_pos (ω : Om) : ∀ y ∈ minusSet ω, 0 < y := by
  intro y hy
  simp only [minusSet, List.mem_toFinset] at hy
  obtain ⟨q, hq, rfl⟩ := minusL_sqrt ω y hy
  have : (0 : ℝ) < q := by exact_mod_cast hq
  positivity

lemma plusSet_cons_true (c : Cl) (hc : c.2.2.2 = true) (ω : Om) :
    plusSet (c :: ω) = (clPts c (csize (c :: ω))).toFinset ∪ plusSet ω := by
  simp [plusSet, plusL, hc, List.toFinset_append]

lemma plusSet_cons_false (c : Cl) (hc : c.2.2.2 = false) (ω : Om) :
    plusSet (c :: ω) = plusSet ω := by
  simp [plusSet, plusL, hc]

lemma minusSet_cons_false (c : Cl) (hc : c.2.2.2 = false) (ω : Om) :
    minusSet (c :: ω) =
      ((clPts c (csize (c :: ω))).map (fun x => Real.sqrt 2 * x)).toFinset ∪ minusSet ω := by
  simp [minusSet, minusL, hc, List.toFinset_append]

lemma minusSet_cons_true (c : Cl) (hc : c.2.2.2 = true) (ω : Om) :
    minusSet (c :: ω) = minusSet ω := by
  simp [minusSet, minusL, hc]

lemma cnt_union_of_gt (X Y : Finset ℝ) (s : ℝ) (h : ∀ y ∈ X, s < y) :
    cnt (X ∪ Y) s = cnt Y s := by
  unfold cnt
  rw [Finset.filter_union]
  have : X.filter (fun y => y ≤ s) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro y hy
    exact not_le.mpr (h y hy)
  rw [this, Finset.empty_union]


open scoped Nat

/-! ### The exponential kernel `φ₁ = φ₂ = e^{-s}/2` -/

noncomputable def phiE (s : ℝ) : ℝ := Real.exp (-s) / 2

lemma phiE_sum (s : ℝ) : phiE s + phiE s = Real.exp (-s) := by unfold phiE; ring

lemma phiE_pos (s : ℝ) : 0 < phiE s := by unfold phiE; positivity

lemma intOn_exp_neg : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
  simpa using exp_neg_integrableOn_Ioi 0 one_pos

lemma phiE_hasDeriv (s : ℝ) : HasDerivAt phiE (-(Real.exp (-s)) / 2) s := by
  have h1 : HasDerivAt (fun y : ℝ => -y) (-1) s := (hasDerivAt_id s).neg
  exact (((Real.hasDerivAt_exp (-s)).comp s h1).div_const 2).congr_deriv (by ring)

lemma phiE_deriv_facts : ∃ φ' : ℝ → ℝ, (∀ s, 0 ≤ s → HasDerivWithinAt phiE (φ' s) (Set.Ici 0) s) ∧
    (∃ C : ℝ, ∀ s, 0 ≤ s → |φ' s| ≤ C) ∧ IntegrableOn φ' (Set.Ici 0) := by
  refine ⟨fun s => -(Real.exp (-s)) / 2, fun s _ => (phiE_hasDeriv s).hasDerivWithinAt,
    ⟨1 / 2, fun s hs => ?_⟩, ?_⟩
  · have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h0 : 0 < Real.exp (-s) := Real.exp_pos _
    rw [abs_div, abs_neg, abs_of_pos h0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact intOn_exp_neg.neg.div_const 2

lemma kernelA3 : KernelAssumption3 phiE phiE 1 where
  nonneg₁ := fun s _ => (phiE_pos s).le
  nonneg₂ := fun s _ => (phiE_pos s).le
  meas₁ := by unfold phiE; fun_prop
  meas₂ := by unfold phiE; fun_prop
  integrable := by
    simp_rw [phiE_sum]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact intOn_exp_neg
  mass_eq_one := by
    simp_rw [phiE_sum]
    rw [integral_Ici_eq_integral_Ioi]
    exact integral_exp_neg_Ioi_zero
  integrable_mean := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show Real.exp (-x) * x ^ ((2 : ℝ) - 1) = x * (phiE x + phiE x)
    rw [phiE_sum, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  mean_eq := by
    rw [integral_Ici_eq_integral_Ioi]
    have h : ∫ x in Ioi (0 : ℝ), x * (phiE x + phiE x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((2 : ℝ) - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      show x * (phiE x + phiE x) = Real.exp (-x) * x ^ ((2 : ℝ) - 1)
      rw [phiE_sum, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      ring
    rw [h, ← Real.Gamma_eq_integral (by norm_num), Real.Gamma_two]
  support₂ := by
    have : {s : ℝ | 0 ≤ s ∧ phiE s ≠ 0} = Ici 0 := by
      ext s
      simp [(phiE_pos s).ne']
    rw [this, Real.volume_Ici]
    exact ENNReal.zero_lt_top
  deriv₁ := phiE_deriv_facts
  deriv₂ := phiE_deriv_facts

/-! ### Sequences -/

noncomputable def TSeq (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

noncomputable def aSeq (n : ℕ) : ℝ := 1 - 1 / 2 * (1 / ((n : ℝ) + 1))

lemma TSeq_pos (n : ℕ) : 0 < TSeq n := by unfold TSeq; positivity

lemma TSeq_tendsto : Tendsto TSeq atTop atTop :=
  tendsto_atTop_mono (fun n => show (n : ℝ) + 1 ≤ TSeq n by
    unfold TSeq; have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith)
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

lemma aSeq_pos (n : ℕ) : 0 < aSeq n := by
  unfold aSeq
  have : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  linarith

lemma aSeq_lt_one (n : ℕ) : aSeq n < 1 := by
  unfold aSeq
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-! ### The measures -/

noncomputable def wt (ℓ : Om) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (Encodable.encode ℓ + 1)

def mOm : MeasurableSpace Om := ⊤

noncomputable abbrev NpO : ℝ → Om → ℕ := fun t ω => cnt (plusSet ω) t

noncomputable abbrev NmO : ℝ → Om → ℕ := fun t ω => cnt (minusSet ω) t

lemma wt_ne_zero (ℓ : Om) : wt ℓ ≠ 0 := by
  unfold wt
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)

lemma wt_mul_csize (ℓ : Om) : wt ℓ * (csize ℓ : ℝ≥0∞) = 1 := by
  unfold wt csize
  push_cast
  rw [← ENNReal.inv_pow]
  exact ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

noncomputable def Zc : ℝ≥0∞ := ∑' ℓ : Om, wt ℓ

lemma Zc_le_one : Zc ≤ 1 := by
  unfold Zc wt
  calc ∑' ℓ : Om, (2⁻¹ : ℝ≥0∞) ^ (Encodable.encode ℓ + 1)
      ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) :=
        ENNReal.tsum_comp_le_tsum_of_injective Encodable.encode_injective
          (fun n => (2⁻¹ : ℝ≥0∞) ^ (n + 1))
    _ = 1 := by
        simp_rw [pow_succ]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

lemma Zc_ne_top : Zc ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top Zc_le_one

lemma Zc_ne_zero : Zc ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (wt_ne_zero [])) (ENNReal.le_tsum []))

section Meas

attribute [local instance] mOm

lemma mscOm : MeasurableSingletonClass Om := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] mscOm

noncomputable def Q0 : Measure Om := Measure.sum (fun ℓ => wt ℓ • Measure.dirac ℓ)

lemma Q0_univ : Q0 univ = Zc := by
  rw [Q0, Measure.sum_apply _ MeasurableSet.univ]
  simp [Zc]

noncomputable def PmL (L : Om) : Measure Om :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac L + (2⁻¹ * Zc⁻¹) • Q0

lemma PmL_prob (L : Om) : IsProbabilityMeasure (PmL L) := by
  constructor
  rw [PmL, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, Q0_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_assoc, ENNReal.inv_mul_cancel Zc_ne_zero Zc_ne_top,
    mul_one, ENNReal.inv_two_add_inv_two]

lemma setLIntegral_PmL_ge (L : Om) (A : Set Om) (f : Om → ℝ≥0∞) :
    (2⁻¹ * Zc⁻¹) * ∑' ℓ, wt ℓ * A.indicator f ℓ ≤ ∫⁻ ω in A, f ω ∂(PmL L) := by
  rw [← lintegral_indicator (show MeasurableSet A from MeasurableSpace.measurableSet_top), PmL,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, Q0,
    lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac]
  exact le_add_self

lemma setLIntegral_top (L : Om) (A : Set Om) (f : Om → ℝ≥0∞) (ext : ℕ → Om)
    (hinj : Function.Injective ext) (hA : ∀ j, ext j ∈ A) (K : ℝ≥0∞) (hK : K ≠ 0)
    (hf : ∀ j, K ≤ wt (ext j) * f (ext j)) : ∫⁻ ω in A, f ω ∂(PmL L) = ⊤ := by
  refine top_unique (le_trans ?_ (setLIntegral_PmL_ge L A f))
  have h1 : ∑' _ : ℕ, K = ⊤ := ENNReal.tsum_const_eq_top_of_ne_zero hK
  have h2 : ∑' _ : ℕ, K ≤ ∑' ℓ, wt ℓ * A.indicator f ℓ := by
    calc ∑' _ : ℕ, K ≤ ∑' j, wt (ext j) * A.indicator f (ext j) :=
          ENNReal.tsum_le_tsum (fun j => by rw [Set.indicator_of_mem (hA j)]; exact hf j)
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun ℓ => wt ℓ * A.indicator f ℓ)
  rw [h1, top_le_iff] at h2
  rw [h2, ENNReal.mul_top (mul_ne_zero (by norm_num) (ENNReal.inv_ne_zero.mpr Zc_ne_top))]

end Meas

/-! ### Lower bounds for the intensity -/

lemma lint_lower (h : ℝ → ℝ) (C a mid b : ℝ) (hamid : a ≤ mid) (hC : ∀ s ∈ Ioc mid b, C ≤ h s) :
    ENNReal.ofReal C * ENNReal.ofReal (b - mid) ≤ ∫⁻ s in Ioc a b, ENNReal.ofReal (h s) := by
  calc ENNReal.ofReal C * ENNReal.ofReal (b - mid) = ∫⁻ s in Ioc mid b, ENNReal.ofReal C := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ ≤ ∫⁻ s in Ioc mid b, ENNReal.ofReal (h s) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Eventually.of_forall fun s hs => ENNReal.ofReal_le_ofReal (hC s hs)))
    _ ≤ ∫⁻ s in Ioc a b, ENNReal.ofReal (h s) := lintegral_mono_set (Ioc_subset_Ioc_left hamid)

lemma intensity_ge (F G E : Finset ℝ) (hE : E ⊆ F) (an T s mid : ℝ) (ha : 0 < an)
    (hEpos : ∀ y ∈ E, 0 < y ∧ y ≤ mid) (hs : mid < s) (hsT : s ≤ T) :
    (E.card : ℝ) * (an * (Real.exp (-T) / 2)) ≤
      intensity 1 (fun s => an * phiE s) (fun s => an * phiE s) (fun u => (cnt F u : ℝ))
        (fun u => (cnt G u : ℝ)) s := by
  unfold intensity
  rw [jumpSumOn_cnt, jumpSumOn_cnt]
  refine le_trans ?_ (le_add_of_nonneg_right
    (Finset.sum_nonneg fun y _ => mul_nonneg ha.le (phiE_pos _).le))
  refine le_trans ?_ (le_add_of_nonneg_left zero_le_one)
  have h3 : (E.card : ℝ) * (an * (Real.exp (-T) / 2)) ≤ ∑ y ∈ E, an * phiE (s - y) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro y hy
    unfold phiE
    have : Real.exp (-T) ≤ Real.exp (-(s - y)) :=
      Real.exp_le_exp.mpr (by linarith [(hEpos y hy).1])
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  refine le_trans h3 (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro y hy
    rw [Finset.mem_filter]
    exact ⟨hE hy, (hEpos y hy).1, (hEpos y hy).2.trans hs.le⟩
  · intro y _ _
    exact mul_nonneg ha.le (phiE_pos _).le


/-! ### The one-dimensional (CIR) intensity of a finite-set counting path -/

lemma cir_intensity_eq (ω : Om) (μ : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    NearlyUnstableHawkes.CIR.intensity μ f NpO t ω =
      μ + jumpSumOn (fun u => (cnt (plusSet ω) u : ℝ)) (fun s => f (t - s)) (Ioc 0 t) := by
  unfold NearlyUnstableHawkes.CIR.intensity jumpSumOn
  congr 1
  refine finsum_congr fun s => ?_
  simp only [Set.mem_Ioc, and_assoc]
  rfl

lemma cir_intensity_ge (ω : Om) (E : Finset ℝ) (hE : E ⊆ plusSet ω) (an T s mid : ℝ) (ha : 0 < an)
    (hEpos : ∀ y ∈ E, 0 < y ∧ y ≤ mid) (hs : mid < s) (hsT : s ≤ T) :
    (E.card : ℝ) * (an * (Real.exp (-T) / 2)) ≤
      NearlyUnstableHawkes.CIR.intensity 1 (fun s => an * (phiE s + phiE s)) NpO s ω := by
  rw [cir_intensity_eq, jumpSumOn_cnt]
  refine le_trans ?_ (le_add_of_nonneg_left zero_le_one)
  have h3 : (E.card : ℝ) * (an * (Real.exp (-T) / 2)) ≤
      ∑ y ∈ E, an * (phiE (s - y) + phiE (s - y)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro y hy
    have h1 : Real.exp (-T) ≤ Real.exp (-(s - y)) :=
      Real.exp_le_exp.mpr (by linarith [(hEpos y hy).1])
    have hp : 0 < phiE (s - y) := phiE_pos _
    unfold phiE at hp ⊢
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  refine le_trans h3 (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro y hy
    rw [Finset.mem_filter]
    exact ⟨hE hy, (hEpos y hy).1, (hEpos y hy).2.trans hs.le⟩
  · intro y _ _
    exact mul_nonneg ha.le (add_nonneg (phiE_pos _).le (phiE_pos _).le)

lemma natFil_le {Ω : Type*} (N : ℝ → Ω → ℕ) (a : ℝ) :
    NearlyUnstableHawkes.CIR.natFiltration N a ≤ natFiltration2 N N a :=
  iSup₂_mono fun _ _ => le_sup_left

/-! ### Assumptions 1 and 2 for `φ = e^{-s}` -/

lemma assumption1 : NearlyUnstableHawkes.CIR.Assumption1 (fun s => phiE s + phiE s)
    (fun s => -(Real.exp (-s))) 1 where
  nonneg := fun s _ => add_nonneg (phiE_pos s).le (phiE_pos s).le
  measurable := (kernelA3.meas₁.add kernelA3.meas₁).comp measurable_subtype_coe
  integrable := kernelA3.integrable
  mass := kernelA3.mass_eq_one
  moment_integrable := kernelA3.integrable_mean
  moment := kernelA3.mean_eq
  deriv := fun s _ =>
    ((phiE_hasDeriv s).add (phiE_hasDeriv s)).hasDerivWithinAt.congr_deriv (by ring)
  deriv_bounded := ⟨1, fun s hs => by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)⟩
  deriv_integrable := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact intOn_exp_neg.neg

/-! ### The intensity identity, both sides infinite -/

section Meas2

attribute [local instance] mOm

lemma hext_plus : ∀ (ℓ₀ : Om) (a mid : ℝ), 0 ≤ a → a < mid → ∃ ext : ℕ → Om, ∃ Es : ℕ → Finset ℝ,
      Function.Injective ext ∧ ∀ j, plusSet (ext j) = Es j ∪ plusSet ℓ₀ ∧
        minusSet (ext j) = minusSet ℓ₀ ∧
        (Es j).card = csize (ext j) ∧ ∀ y ∈ Es j, a < y ∧ y ≤ mid := by
  intro ℓ₀ a mid ha hmid
  obtain ⟨k, m, hc⟩ := exists_cell a mid ha hmid
  refine ⟨fun j => (k, m, j, true) :: ℓ₀,
    fun j => (clPts (k, m, j, true) (csize ((k, m, j, true) :: ℓ₀))).toFinset, ?_, fun j => ?_⟩
  · intro j j' h
    simp only [List.cons.injEq, Prod.mk.injEq] at h
    exact h.1.2.2.1
  · refine ⟨plusSet_cons_true _ rfl ℓ₀, minusSet_cons_true _ rfl ℓ₀, clPts_card _ _, ?_⟩
    intro y hy
    rw [List.mem_toFinset] at hy
    exact hc j true _ y hy

lemma id_cir (L : Om) (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ TSeq n) (A : Set Om)
    (hsat : ∀ ω ω' : Om, (∀ s ∈ Icc (0 : ℝ) a, cnt (plusSet ω') s = cnt (plusSet ω) s) →
      ω ∈ A → ω' ∈ A) :
    ∫⁻ ω in A, ((cnt (plusSet ω) b - cnt (plusSet ω) a : ℕ) : ℝ≥0∞) ∂(PmL L) =
      ∫⁻ ω in A, (∫⁻ s in Ioc a b, ENNReal.ofReal (NearlyUnstableHawkes.CIR.intensity 1
        (fun s => aSeq n * (phiE s + phiE s)) NpO s ω)) ∂(PmL L) := by
  by_cases hAe : A = ∅
  · subst hAe
    simp
  obtain ⟨ℓ₀, hℓ₀⟩ := Set.nonempty_iff_ne_empty.mpr hAe
  have hmid : a < (a + b) / 2 := by linarith
  have hmidb : (a + b) / 2 < b := by linarith
  obtain ⟨ext, Es, hinj, hE⟩ := hext_plus ℓ₀ a ((a + b) / 2) ha hmid
  have hextA : ∀ j, ext j ∈ A := by
    intro j
    refine hsat ℓ₀ (ext j) (fun s hs => ?_) hℓ₀
    rw [(hE j).1, cnt_union_of_gt]
    intro y hy
    exact lt_of_le_of_lt hs.2 ((hE j).2.2.2 y hy).1
  have hsub : ∀ j, Es j ⊆ plusSet (ext j) := fun j => by
    rw [(hE j).1]
    exact Finset.subset_union_left
  have hL : ∫⁻ ω in A, ((cnt (plusSet ω) b - cnt (plusSet ω) a : ℕ) : ℝ≥0∞) ∂(PmL L) = ⊤ := by
    refine setLIntegral_top L A _ ext hinj hextA 1 one_ne_zero (fun j => ?_)
    have hc : csize (ext j) ≤ cnt (plusSet (ext j)) b - cnt (plusSet (ext j)) a := by
      rw [← (hE j).2.2.1]
      exact cnt_sub_ge _ _ hab.le (hsub j)
        (fun y hy => ⟨((hE j).2.2.2 y hy).1, ((hE j).2.2.2 y hy).2.trans hmidb.le⟩)
    calc (1 : ℝ≥0∞) = wt (ext j) * (csize (ext j) : ℝ≥0∞) := (wt_mul_csize _).symm
      _ ≤ _ := by gcongr
  have hK : ENNReal.ofReal (aSeq n * (Real.exp (-TSeq n) / 2)) *
      ENNReal.ofReal (b - (a + b) / 2) ≠ 0 := by
    have h1 : 0 < aSeq n * (Real.exp (-TSeq n) / 2) := mul_pos (aSeq_pos n) (by positivity)
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr h1).ne' (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hR : ∫⁻ ω in A, (∫⁻ s in Ioc a b, ENNReal.ofReal (NearlyUnstableHawkes.CIR.intensity 1
        (fun s => aSeq n * (phiE s + phiE s)) NpO s ω)) ∂(PmL L) = ⊤ := by
    refine setLIntegral_top L A _ ext hinj hextA _ hK (fun j => ?_)
    have hlow : ∀ s ∈ Ioc ((a + b) / 2) b,
        (csize (ext j) : ℝ) * (aSeq n * (Real.exp (-TSeq n) / 2)) ≤
          NearlyUnstableHawkes.CIR.intensity 1 (fun s => aSeq n * (phiE s + phiE s)) NpO s (ext j) := by
      intro s hs
      rw [← (hE j).2.2.1]
      exact cir_intensity_ge (ext j) (Es j) (hsub j) (aSeq n) (TSeq n) s ((a + b) / 2)
        (aSeq_pos n) (fun y hy => ⟨ha.trans_lt ((hE j).2.2.2 y hy).1, ((hE j).2.2.2 y hy).2⟩) hs.1
        (hs.2.trans hb)
    have hint := lint_lower _ _ a ((a + b) / 2) b hmid.le hlow
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc] at hint
    calc _ = wt (ext j) * ((csize (ext j) : ℝ≥0∞) *
          (ENNReal.ofReal (aSeq n * (Real.exp (-TSeq n) / 2)) *
          ENNReal.ofReal (b - (a + b) / 2))) := by rw [← mul_assoc, wt_mul_csize, one_mul]
      _ ≤ _ := by gcongr
  rw [hL, hR]

lemma hawkesCIR (L : Om) (n : ℕ) :
    NearlyUnstableHawkes.CIR.IsHawkes (PmL L) 1 (fun s => aSeq n * (phiE s + phiE s)) (TSeq n)
      NpO where
  meas := fun _ _ => measurable_from_top
  zero := (isSimpleCounting_cnt plusSet plusSet_pos (fun _ => measurable_from_top)).zero
  mono := (isSimpleCounting_cnt plusSet plusSet_pos (fun _ => measurable_from_top)).mono
  rcont := (isSimpleCounting_cnt plusSet plusSet_pos (fun _ => measurable_from_top)).rcont
  unit_jumps := (isSimpleCounting_cnt plusSet plusSet_pos (fun _ => measurable_from_top)).unit_jumps
  intensity_id := fun a b ha hab hb A hA =>
    id_cir L n a b ha hab hb A
      (fun ω ω' h hω => natFiltration2_saturated NpO NpO a A (natFil_le NpO a A hA)
        (fun s hs => ⟨h s hs, h s hs⟩) hω)

end Meas2

/-! ### The deterministic-setting kernel assumption and Hawkes property -/

lemma aSeq_tendsto : Tendsto aSeq atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ))
  rw [mul_zero, sub_zero] at h
  exact h

lemma regime_eq (n : ℕ) : TSeq n * (1 - aSeq n) = ((n : ℝ) + 1) / 2 := by
  unfold TSeq aSeq
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp <;> ring

lemma regime : Tendsto (fun n => TSeq n * (1 - aSeq n)) atTop atTop := by
  simp_rw [regime_eq]
  exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_div_const (by norm_num)

lemma kernelDet : NearlyUnstableHawkes.Deterministic.KernelAssumption (fun s => phiE s + phiE s)
    (fun s => -(Real.exp (-s))) 1 where
  nonnegative := assumption1.nonneg
  measurable := assumption1.measurable
  integrable := assumption1.integrable
  mass := assumption1.mass
  moment_integrable := assumption1.moment_integrable
  moment := assumption1.moment
  derivative := assumption1.deriv
  derivative_bounded := assumption1.deriv_bounded
  derivative_integrable := assumption1.deriv_integrable

section Meas5

attribute [local instance] mOm

lemma hawkesDet (L : Om) (n : ℕ) :
    NearlyUnstableHawkes.Deterministic.IsHawkes (PmL L) 1
      (NearlyUnstableHawkes.Deterministic.scaledKernel (aSeq n) (fun s => phiE s + phiE s))
      (TSeq n) NpO where
  baseline_pos := one_pos
  kernel_nonnegative := fun s _ =>
    mul_nonneg (aSeq_pos n).le (add_nonneg (phiE_pos s).le (phiE_pos s).le)
  kernel_measurable := by
    have hm : Measurable (fun s : ℝ => aSeq n * (phiE s + phiE s)) := by
      unfold phiE; fun_prop
    exact hm.comp measurable_subtype_coe
  kernel_integrable := by
    show IntegrableOn (fun s => aSeq n * (phiE s + phiE s)) (Set.Ici 0)
    exact assumption1.integrable.const_mul (aSeq n)
  counting :=
    { measurable := (hawkesCIR L n).meas
      zero := (hawkesCIR L n).zero
      monotone := (hawkesCIR L n).mono
      right_continuous := (hawkesCIR L n).rcont
      unit_jumps := fun ω t ht _ => (hawkesCIR L n).unit_jumps ω t ht }
  intensity_id := (hawkesCIR L n).intensity_id

end Meas5

/-! ### Infinite expected count, hence infinite squared deviation -/

section Meas6

attribute [local instance] mOm

lemma lint_N_top (L : Om) (t : ℝ) (ht : 0 < t) :
    ∫⁻ ω, ((NpO t ω : ℕ) : ℝ≥0∞) ∂(PmL L) = ⊤ := by
  rw [← setLIntegral_univ]
  obtain ⟨ext, Es, hinj, hE⟩ := hext_plus [] 0 t le_rfl ht
  refine setLIntegral_top L univ _ ext hinj (fun _ => mem_univ _) 1 one_ne_zero (fun j => ?_)
  have hsub : Es j ⊆ plusSet (ext j) := by
    rw [(hE j).1]
    exact Finset.subset_union_left
  have hc : csize (ext j) ≤ cnt (plusSet (ext j)) t := by
    rw [← (hE j).2.2.1]
    exact le_trans (cnt_sub_ge _ _ ht.le hsub (fun y hy => (hE j).2.2.2 y hy)) (Nat.sub_le _ _)
  show (1 : ℝ≥0∞) ≤ wt (ext j) * ((cnt (plusSet (ext j)) t : ℕ) : ℝ≥0∞)
  calc (1 : ℝ≥0∞) = wt (ext j) * (csize (ext j) : ℝ≥0∞) := (wt_mul_csize _).symm
    _ ≤ _ := by gcongr

lemma dev_top (L : Om) (n : ℕ) :
    ∫⁻ ω, (NearlyUnstableHawkes.Deterministic.scaledDeviation (aSeq n) (TSeq n) NpO (PmL L) ω) ^ 2
      ∂(PmL L) = ⊤ := by
  haveI := PmL_prob L
  have hT := TSeq_pos n
  have htop := lint_N_top L (TSeq n * 1) (by rw [mul_one]; exact hT)
  have hnotint : ¬ Integrable (fun ω => (NpO (TSeq n * 1) ω : ℝ)) (PmL L) := by
    intro hi
    have h := hi.lintegral_lt_top
    simp_rw [ENNReal.ofReal_natCast] at h
    rw [htop] at h
    exact lt_irrefl _ h
  have hmean : ∫ ω', (NpO (TSeq n * 1) ω' : ℝ) ∂(PmL L) = 0 := integral_undef hnotint
  have hcpos : 0 < (1 - aSeq n) / TSeq n := div_pos (by linarith [aSeq_lt_one n]) hT
  have hpt : ∀ ω, ENNReal.ofReal ((1 - aSeq n) / TSeq n) ^ 2 * ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞) ≤
      (NearlyUnstableHawkes.Deterministic.scaledDeviation (aSeq n) (TSeq n) NpO (PmL L) ω) ^ 2 := by
    intro ω
    have h1 : ENNReal.ofReal ((1 - aSeq n) / TSeq n *
        |(NpO (TSeq n * 1) ω : ℝ) - ∫ ω', (NpO (TSeq n * 1) ω' : ℝ) ∂(PmL L)|) ≤
        NearlyUnstableHawkes.Deterministic.scaledDeviation (aSeq n) (TSeq n) NpO (PmL L) ω := by
      unfold NearlyUnstableHawkes.Deterministic.scaledDeviation
      exact le_iSup₂_of_le (f := fun (v : ℝ) (_ : v ∈ Set.Icc (0 : ℝ) 1) =>
        ENNReal.ofReal ((1 - aSeq n) / TSeq n *
          |(NpO (TSeq n * v) ω : ℝ) - ∫ ω', (NpO (TSeq n * v) ω' : ℝ) ∂(PmL L)|))
        (1 : ℝ) ⟨zero_le_one, le_rfl⟩ le_rfl
    rw [hmean, sub_zero, abs_of_nonneg (Nat.cast_nonneg _), ENNReal.ofReal_mul hcpos.le,
      ENNReal.ofReal_natCast] at h1
    have hk : ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞) ≤ ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞) ^ 2 := by
      exact_mod_cast Nat.le_self_pow two_ne_zero _
    calc ENNReal.ofReal ((1 - aSeq n) / TSeq n) ^ 2 * ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal ((1 - aSeq n) / TSeq n) ^ 2 * ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞) ^ 2 := by
          gcongr
      _ = (ENNReal.ofReal ((1 - aSeq n) / TSeq n) * ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞)) ^ 2 := by
          rw [mul_pow]
      _ ≤ _ := by gcongr
  refine top_unique ?_
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal ((1 - aSeq n) / TSeq n) ^ 2 *
        ∫⁻ ω, ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞) ∂(PmL L) := by
        rw [htop, ENNReal.mul_top (pow_ne_zero 2 (ENNReal.ofReal_pos.mpr hcpos).ne')]
    _ = ∫⁻ ω, ENNReal.ofReal ((1 - aSeq n) / TSeq n) ^ 2 * ((NpO (TSeq n * 1) ω : ℕ) : ℝ≥0∞)
        ∂(PmL L) := (lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).symm
    _ ≤ _ := lintegral_mono hpt

end Meas6

end D4e31

open NearlyUnstableHawkes.Deterministic in
theorem solution : ¬ (∀ {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T a : ℕ → ℝ) (μ m : ℝ) (φ φ' : ℝ → ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ)
    (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (ha : Tendsto a atTop (𝓝 1)) (hμ : 0 < μ)
    (hφ : KernelAssumption φ φ' m)
    (hN : ∀ n, IsHawkes (P n) μ (scaledKernel (a n) φ) (T n) (N n))
    (hregime : Tendsto (fun n => T n * (1 - a n)) atTop atTop),
    Tendsto (fun n => ∫⁻ ω, (scaledDeviation (a n) (T n) (N n) (P n) ω) ^ 2 ∂P n)
      atTop (𝓝 0)) := by
  intro H
  have hprob : ∀ _ : ℕ, IsProbabilityMeasure (D4e31.PmL ([] : D4e31.Om)) :=
    fun _ => D4e31.PmL_prob _
  have h := @H (fun _ => D4e31.Om) (fun _ => D4e31.mOm) (fun _ => D4e31.PmL []) hprob
    D4e31.TSeq D4e31.aSeq 1 1 (fun s => D4e31.phiE s + D4e31.phiE s) (fun s => -(Real.exp (-s)))
    (fun _ => D4e31.NpO) D4e31.TSeq_pos D4e31.TSeq_tendsto D4e31.aSeq_pos D4e31.aSeq_lt_one
    D4e31.aSeq_tendsto one_pos D4e31.kernelDet (fun n => D4e31.hawkesDet _ n) D4e31.regime
  have h2 : Tendsto (fun _ : ℕ => (⊤ : ℝ≥0∞)) atTop (𝓝 0) :=
    Tendsto.congr (fun n => D4e31.dev_top [] n) h
  exact ENNReal.top_ne_zero (tendsto_const_nhds_iff.mp h2)
