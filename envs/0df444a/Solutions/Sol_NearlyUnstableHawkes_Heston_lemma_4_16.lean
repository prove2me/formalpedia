-- Prove2me | solution 1 for NearlyUnstableHawkes.Heston.lemma_4_16
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T10:38:07.572569+00:00
-- url     : https://prove2.me/submissions/a5b89f13-2617-49e6-9a10-a5d9a9b00941

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace D7ade

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

noncomputable def TSeq (n : ℕ) : ℝ := (n : ℝ) + 1

noncomputable def aSeq (n : ℕ) : ℝ := 1 - 1 / 2 * (1 / ((n : ℝ) + 1))

lemma TSeq_pos (n : ℕ) : 0 < TSeq n := by unfold TSeq; positivity

lemma TSeq_tendsto : Tendsto TSeq atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

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

lemma T_one_sub_a (n : ℕ) : TSeq n * (1 - aSeq n) = 1 / 2 := by
  unfold TSeq aSeq
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma assumption3 : Assumption3 aSeq phiE phiE 1 := by
  refine ⟨aSeq_pos, aSeq_lt_one, ?_, kernelA3⟩
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ))
  rw [mul_zero, sub_zero] at h
  exact h

lemma h3 : Tendsto (fun n => TSeq n * (1 - aSeq n)) atTop (𝓝 (1 / 2)) := by
  simp_rw [T_one_sub_a]
  exact tendsto_const_nhds

/-! ### The resolvent of `a e^{-s}` -/

lemma convPow_exp (a : ℝ) (k : ℕ) (t : ℝ) :
    NearlyUnstableHawkes.Deterministic.convPow (fun s => a * (phiE s + phiE s)) k t =
      a ^ (k + 1) * t ^ k * Real.exp (-t) / (k ! : ℝ) := by
  induction k generalizing t with
  | zero => simp [NearlyUnstableHawkes.Deterministic.convPow, phiE_sum]
  | succ k ih =>
    show NearlyUnstableHawkes.Deterministic.conv
      (NearlyUnstableHawkes.Deterministic.convPow (fun s => a * (phiE s + phiE s)) k)
      (fun s => a * (phiE s + phiE s)) t = _
    unfold NearlyUnstableHawkes.Deterministic.conv
    have hint : ∀ s : ℝ,
        NearlyUnstableHawkes.Deterministic.convPow (fun s => a * (phiE s + phiE s)) k (t - s) *
          (a * (phiE s + phiE s)) =
        (a ^ (k + 2) * Real.exp (-t) / (k ! : ℝ)) * (t - s) ^ k := by
      intro s
      rw [ih, phiE_sum]
      have he : Real.exp (-(t - s)) * Real.exp (-s) = Real.exp (-t) := by
        rw [← Real.exp_add]; ring_nf
      field_simp
      rw [← he]
      ring
    simp_rw [hint]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ k) t, sub_self, sub_zero,
      integral_pow, Nat.factorial_succ]
    push_cast
    have : (k ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

lemma psiPlus_exp (a t : ℝ) :
    psiPlus a phiE phiE t = a * Real.exp (-(1 - a) * t) := by
  unfold psiPlus NearlyUnstableHawkes.Heston.resolvent
  simp_rw [convPow_exp]
  have h := NormedSpace.expSeries_div_hasSum_exp (a * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (a * Real.exp (-t))
  have hfun : (fun k : ℕ => a ^ (k + 1) * t ^ k * Real.exp (-t) / (k ! : ℝ)) =
      fun k : ℕ => a * Real.exp (-t) * ((a * t) ^ k / (k ! : ℝ)) := by
    funext k
    rw [mul_pow, pow_succ]
    ring
  rw [hfun, h2.tsum_eq, mul_assoc, ← Real.exp_add]
  ring_nf

lemma int_psiPlus (a : ℝ) (ha : a < 1) :
    ∫ s in Ioi (0 : ℝ), psiPlus a phiE phiE s = a / (1 - a) := by
  simp_rw [psiPlus_exp]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  have : (1 : ℝ) - a ≠ 0 := by linarith
  simp only [mul_zero, Real.exp_zero]
  field_simp

lemma rhoPlus_eq (n : ℕ) (x : ℝ) :
    rhoPlus (TSeq n) (aSeq n) phiE phiE x =
      1 / 2 * Real.exp (-(1 - aSeq n) * (TSeq n * x)) := by
  unfold rhoPlus
  rw [int_psiPlus _ (aSeq_lt_one n), psiPlus_exp]
  have ha := aSeq_pos n
  have h1 : (1 : ℝ) - aSeq n ≠ 0 := by linarith [aSeq_lt_one n]
  have hT := T_one_sub_a n
  field_simp
  rw [hT]
  norm_num

lemma assumption4 : Assumption4 TSeq aSeq phiE phiE := by
  refine ⟨1 / 2, by norm_num, fun n x hx => ?_⟩
  rw [rhoPlus_eq]
  have h1 : 0 ≤ (1 - aSeq n) * (TSeq n * x) :=
    mul_nonneg (by linarith [aSeq_lt_one n]) (mul_nonneg (TSeq_pos n).le hx)
  have h2 : Real.exp (-(1 - aSeq n) * (TSeq n * x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  rw [abs_of_pos (by positivity)]
  linarith


/-! ### The kernels `φ₁ = 3e^{-s}/4`, `φ₂ = e^{-s}/4` -/

noncomputable def phi1 (s : ℝ) : ℝ := 3 / 2 * phiE s

noncomputable def phi2 (s : ℝ) : ℝ := 1 / 2 * phiE s

lemma phi12_sum (s : ℝ) : phi1 s + phi2 s = phiE s + phiE s := by unfold phi1 phi2; ring

lemma phiE_le_phi1 (s : ℝ) : phiE s ≤ phi1 s := by unfold phi1; linarith [phiE_pos s]

lemma phi2_nonneg (s : ℝ) : 0 ≤ phi2 s := by unfold phi2; linarith [phiE_pos s]

lemma deriv_scale (c : ℝ) (hc : 0 ≤ c) : ∃ φ' : ℝ → ℝ,
    (∀ s, 0 ≤ s → HasDerivWithinAt (fun s => c * phiE s) (φ' s) (Set.Ici 0) s) ∧
    (∃ C : ℝ, ∀ s, 0 ≤ s → |φ' s| ≤ C) ∧ IntegrableOn φ' (Set.Ici 0) := by
  obtain ⟨φ', hd, ⟨C, hC⟩, hi⟩ := phiE_deriv_facts
  refine ⟨fun s => c * φ' s, fun s hs => (hd s hs).const_mul c, ⟨c * C, fun s hs => ?_⟩,
    hi.const_mul c⟩
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hC s hs) hc

lemma kernelA3' : KernelAssumption3 phi1 phi2 1 where
  nonneg₁ := fun s _ => (phiE_pos s).le.trans (phiE_le_phi1 s)
  nonneg₂ := fun s _ => phi2_nonneg s
  meas₁ := by unfold phi1 phiE; fun_prop
  meas₂ := by unfold phi2 phiE; fun_prop
  integrable := by simp_rw [phi12_sum]; exact kernelA3.integrable
  mass_eq_one := by simp_rw [phi12_sum]; exact kernelA3.mass_eq_one
  integrable_mean := by simp_rw [phi12_sum]; exact kernelA3.integrable_mean
  mean_eq := by simp_rw [phi12_sum]; exact kernelA3.mean_eq
  support₂ := by
    have : {s : ℝ | 0 ≤ s ∧ phi2 s ≠ 0} = Ici 0 := by
      ext s
      simp [phi2, (phiE_pos s).ne']
    rw [this, Real.volume_Ici]
    exact ENNReal.zero_lt_top
  deriv₁ := deriv_scale (3 / 2) (by norm_num)
  deriv₂ := deriv_scale (1 / 2) (by norm_num)

lemma assumption3' : Assumption3 aSeq phi1 phi2 1 :=
  ⟨aSeq_pos, aSeq_lt_one, assumption3.2.2.1, kernelA3'⟩

lemma psiPlus12 (a : ℝ) : psiPlus a phi1 phi2 = psiPlus a phiE phiE := by
  funext t
  unfold psiPlus
  simp_rw [phi12_sum]

lemma assumption4' : Assumption4 TSeq aSeq phi1 phi2 := by
  obtain ⟨K, hK, h⟩ := assumption4
  refine ⟨K, hK, fun n x hx => ?_⟩
  have e : rhoPlus (TSeq n) (aSeq n) phi1 phi2 x = rhoPlus (TSeq n) (aSeq n) phiE phiE x := by
    unfold rhoPlus
    rw [psiPlus12]
  rw [e]
  exact h n x hx

lemma psiSigned12 (a t : ℝ) : psiSigned a phi1 phi2 t = a / 2 * Real.exp (-(1 - a / 2) * t) := by
  have hf : phiSignedT a phi1 phi2 = fun s => a / 2 * (phiE s + phiE s) := by
    funext s
    unfold phiSignedT phi1 phi2
    ring
  have e : psiSigned a phi1 phi2 t = psiPlus (a / 2) phiE phiE t := by
    unfold psiSigned psiPlus
    rw [hf]
  rw [e, psiPlus_exp]

lemma tail12 (a y : ℝ) (ha : a < 2) :
    ∫ s in Ioi y, psiSigned a phi1 phi2 s = a / 2 / (1 - a / 2) * Real.exp (-(1 - a / 2) * y) := by
  simp_rw [psiSigned12]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) y, neg_div_neg_eq]
  ring

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

lemma intensity_ge (φ₁ φ₂ : ℝ → ℝ) (hφ1 : ∀ s, phiE s ≤ φ₁ s) (hφ2 : ∀ s, 0 ≤ φ₂ s)
    (F G E : Finset ℝ) (hE : E ⊆ F) (an T s mid : ℝ) (ha : 0 < an)
    (hEpos : ∀ y ∈ E, 0 < y ∧ y ≤ mid) (hs : mid < s) (hsT : s ≤ T) :
    (E.card : ℝ) * (an * (Real.exp (-T) / 2)) ≤
      intensity 1 (fun s => an * φ₁ s) (fun s => an * φ₂ s) (fun u => (cnt F u : ℝ))
        (fun u => (cnt G u : ℝ)) s := by
  unfold intensity
  rw [jumpSumOn_cnt, jumpSumOn_cnt]
  refine le_trans ?_ (le_add_of_nonneg_right
    (Finset.sum_nonneg fun y _ => mul_nonneg ha.le (hφ2 _)))
  refine le_trans ?_ (le_add_of_nonneg_left zero_le_one)
  have h3 : (E.card : ℝ) * (an * (Real.exp (-T) / 2)) ≤ ∑ y ∈ E, an * φ₁ (s - y) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro y hy
    have hp := hφ1 (s - y)
    unfold phiE at hp
    have : Real.exp (-T) ≤ Real.exp (-(s - y)) :=
      Real.exp_le_exp.mpr (by linarith [(hEpos y hy).1])
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  refine le_trans h3 (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro y hy
    rw [Finset.mem_filter]
    exact ⟨hE hy, (hEpos y hy).1, (hEpos y hy).2.trans hs.le⟩
  · intro y _ _
    exact mul_nonneg ha.le ((phiE_pos _).le.trans (hφ1 _))

/-! ### The intensity identity, both sides infinite -/

section Meas2

attribute [local instance] mOm

lemma id_generic (φ₁ φ₂ : ℝ → ℝ) (hφ1 : ∀ s, phiE s ≤ φ₁ s) (hφ2 : ∀ s, 0 ≤ φ₂ s) (L : Om) (n : ℕ) (S1 S2 : Om → Finset ℝ)
    (hext : ∀ (ℓ₀ : Om) (a mid : ℝ), 0 ≤ a → a < mid → ∃ ext : ℕ → Om, ∃ Es : ℕ → Finset ℝ,
      Function.Injective ext ∧ ∀ j, S1 (ext j) = Es j ∪ S1 ℓ₀ ∧ S2 (ext j) = S2 ℓ₀ ∧
        (Es j).card = csize (ext j) ∧ ∀ y ∈ Es j, a < y ∧ y ≤ mid)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ TSeq n) (A : Set Om)
    (hsat : ∀ ω ω' : Om, (∀ s ∈ Icc (0 : ℝ) a, cnt (S1 ω') s = cnt (S1 ω) s ∧
      cnt (S2 ω') s = cnt (S2 ω) s) → ω ∈ A → ω' ∈ A) :
    ∫⁻ ω in A, ((cnt (S1 ω) b - cnt (S1 ω) a : ℕ) : ℝ≥0∞) ∂(PmL L) =
      ∫⁻ ω in A, (∫⁻ s in Ioc a b, ENNReal.ofReal (intensity 1 (fun s => aSeq n * φ₁ s)
        (fun s => aSeq n * φ₂ s) (fun u => (cnt (S1 ω) u : ℝ)) (fun u => (cnt (S2 ω) u : ℝ)) s))
        ∂(PmL L) := by
  by_cases hAe : A = ∅
  · subst hAe
    simp
  obtain ⟨ℓ₀, hℓ₀⟩ := Set.nonempty_iff_ne_empty.mpr hAe
  have hmid : a < (a + b) / 2 := by linarith
  have hmidb : (a + b) / 2 < b := by linarith
  obtain ⟨ext, Es, hinj, hE⟩ := hext ℓ₀ a ((a + b) / 2) ha hmid
  have hextA : ∀ j, ext j ∈ A := by
    intro j
    refine hsat ℓ₀ (ext j) (fun s hs => ⟨?_, ?_⟩) hℓ₀
    · rw [(hE j).1, cnt_union_of_gt]
      intro y hy
      exact lt_of_le_of_lt hs.2 ((hE j).2.2.2 y hy).1
    · rw [(hE j).2.1]
  have hsub : ∀ j, Es j ⊆ S1 (ext j) := fun j => by
    rw [(hE j).1]
    exact Finset.subset_union_left
  have hL : ∫⁻ ω in A, ((cnt (S1 ω) b - cnt (S1 ω) a : ℕ) : ℝ≥0∞) ∂(PmL L) = ⊤ := by
    refine setLIntegral_top L A _ ext hinj hextA 1 one_ne_zero (fun j => ?_)
    have hc : csize (ext j) ≤ cnt (S1 (ext j)) b - cnt (S1 (ext j)) a := by
      rw [← (hE j).2.2.1]
      exact cnt_sub_ge _ _ hab.le (hsub j)
        (fun y hy => ⟨((hE j).2.2.2 y hy).1, ((hE j).2.2.2 y hy).2.trans hmidb.le⟩)
    calc (1 : ℝ≥0∞) = wt (ext j) * (csize (ext j) : ℝ≥0∞) := (wt_mul_csize _).symm
      _ ≤ _ := by gcongr
  have hK : ENNReal.ofReal (aSeq n * (Real.exp (-TSeq n) / 2)) *
      ENNReal.ofReal (b - (a + b) / 2) ≠ 0 := by
    have h1 : 0 < aSeq n * (Real.exp (-TSeq n) / 2) := mul_pos (aSeq_pos n) (by positivity)
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr h1).ne' (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hR : ∫⁻ ω in A, (∫⁻ s in Ioc a b, ENNReal.ofReal (intensity 1 (fun s => aSeq n * φ₁ s)
        (fun s => aSeq n * φ₂ s) (fun u => (cnt (S1 ω) u : ℝ)) (fun u => (cnt (S2 ω) u : ℝ)) s))
        ∂(PmL L) = ⊤ := by
    refine setLIntegral_top L A _ ext hinj hextA _ hK (fun j => ?_)
    have hlow : ∀ s ∈ Ioc ((a + b) / 2) b, (csize (ext j) : ℝ) * (aSeq n * (Real.exp (-TSeq n) / 2)) ≤
        intensity 1 (fun s => aSeq n * φ₁ s) (fun s => aSeq n * φ₂ s)
          (fun u => (cnt (S1 (ext j)) u : ℝ)) (fun u => (cnt (S2 (ext j)) u : ℝ)) s := by
      intro s hs
      rw [← (hE j).2.2.1]
      exact intensity_ge φ₁ φ₂ hφ1 hφ2 (S1 (ext j)) (S2 (ext j)) (Es j) (hsub j) (aSeq n) (TSeq n) s ((a + b) / 2)
        (aSeq_pos n) (fun y hy => ⟨ha.trans_lt ((hE j).2.2.2 y hy).1, ((hE j).2.2.2 y hy).2⟩) hs.1
        (hs.2.trans hb)
    have hint := lint_lower _ _ a ((a + b) / 2) b hmid.le hlow
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc] at hint
    calc _ = wt (ext j) * ((csize (ext j) : ℝ≥0∞) * (ENNReal.ofReal (aSeq n * (Real.exp (-TSeq n) / 2)) *
          ENNReal.ofReal (b - (a + b) / 2))) := by rw [← mul_assoc, wt_mul_csize, one_mul]
      _ ≤ _ := by gcongr
  rw [hL, hR]

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

lemma hext_minus : ∀ (ℓ₀ : Om) (a mid : ℝ), 0 ≤ a → a < mid → ∃ ext : ℕ → Om, ∃ Es : ℕ → Finset ℝ,
      Function.Injective ext ∧ ∀ j, minusSet (ext j) = Es j ∪ minusSet ℓ₀ ∧
        plusSet (ext j) = plusSet ℓ₀ ∧
        (Es j).card = csize (ext j) ∧ ∀ y ∈ Es j, a < y ∧ y ≤ mid := by
  intro ℓ₀ a mid ha hmid
  have hs2 : 0 < Real.sqrt 2 := by positivity
  obtain ⟨k, m, hc⟩ := exists_cell (a / Real.sqrt 2) (mid / Real.sqrt 2) (div_nonneg ha hs2.le)
    (div_lt_div_of_pos_right hmid hs2)
  refine ⟨fun j => (k, m, j, false) :: ℓ₀,
    fun j => ((clPts (k, m, j, false) (csize ((k, m, j, false) :: ℓ₀))).map
      (fun x => Real.sqrt 2 * x)).toFinset, ?_, fun j => ?_⟩
  · intro j j' h
    simp only [List.cons.injEq, Prod.mk.injEq] at h
    exact h.1.2.2.1
  · refine ⟨minusSet_cons_false _ rfl ℓ₀, plusSet_cons_false _ rfl ℓ₀, clPts_card_sqrt _ _, ?_⟩
    intro y hy
    rw [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h := hc j false _ x hx
    constructor
    · have := (div_lt_iff₀' hs2).mp h.1
      exact this
    · exact (le_div_iff₀' hs2).mp h.2

lemma hawkes2 (L : Om) (n : ℕ) :
    IsHawkes2 (PmL L) 1 (fun s => aSeq n * phi1 s) (fun s => aSeq n * phi2 s) (TSeq n) NpO NmO where
  countPlus := isSimpleCounting_cnt plusSet plusSet_pos (fun _ => measurable_from_top)
  countMinus := isSimpleCounting_cnt minusSet minusSet_pos (fun _ => measurable_from_top)
  no_common_jumps := fun ω t _ => by
    show jump (fun u => (cnt (plusSet ω) u : ℝ)) t = 0 ∨ jump (fun u => (cnt (minusSet ω) u : ℝ)) t = 0
    rw [jump_cnt, jump_cnt]
    by_cases hp : t ∈ plusSet ω
    · right
      rw [if_neg (fun hm => plus_minus_disjoint ω t ⟨hp, hm⟩)]
    · left
      rw [if_neg hp]
  intensityPlus_id := fun a b ha hab hb A hA =>
    id_generic phi1 phi2 phiE_le_phi1 phi2_nonneg L n plusSet minusSet hext_plus a b ha hab hb A
      (fun ω ω' h hω => natFiltration2_saturated NpO NmO a A hA (fun s hs => h s hs) hω)
  intensityMinus_id := fun a b ha hab hb A hA =>
    id_generic phi1 phi2 phiE_le_phi1 phi2_nonneg L n minusSet plusSet hext_minus a b ha hab hb A
      (fun ω ω' h hω => natFiltration2_saturated NpO NmO a A hA
        (fun s hs => ⟨(h s hs).2, (h s hs).1⟩) hω)

end Meas2

/-! ### The remainder `R^T` is large with probability at least one half -/

lemma lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]
    omega

def Bnd2 (n : ℕ) : ℕ := 8 * n + 10

lemma exists_big2 (N : ℕ) : ∃ j : ℕ, N ≤ Encodable.encode ([((2 : ℕ), (0 : ℕ), j, true)] : Om) := by
  have hinj : Function.Injective
      (fun j : ℕ => Encodable.encode ([((2 : ℕ), (0 : ℕ), j, true)] : Om)) := by
    intro j j' h
    have := Encodable.encode_injective h
    simpa using this
  exact (hinj.nat_tendsto_atTop.eventually_ge_atTop N).exists

noncomputable def jr (n : ℕ) : ℕ := Classical.choose (exists_big2 (Bnd2 n))

noncomputable def lr (n : ℕ) : Om := [((2 : ℕ), (0 : ℕ), jr n, true)]

/-- The integrand `u ↦ ∫_{T(t − u/T)}^∞ ψ^T` of `R^T_t` at `t = 1/(4T)`. -/
noncomputable def gR (n : ℕ) (s : ℝ) : ℝ :=
  ∫ r in Ioi (TSeq n * (1 / (4 * TSeq n) - s / TSeq n)), psiSigned (aSeq n) phi1 phi2 r

lemma rem_eq (n : ℕ) :
    remainderR (TSeq n) 1 (aSeq n) phi1 phi2 NpO NmO (1 / (4 * TSeq n)) (lr n) =
      ((jumpSumOn (path NpO (lr n)) (gR n) (Ioc 0 (TSeq n * (1 / (4 * TSeq n)))) -
          ∫ u in (0 : ℝ)..(TSeq n * (1 / (4 * TSeq n))),
            gR n u * lamPlus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n)) -
        (jumpSumOn (path NmO (lr n)) (gR n) (Ioc 0 (TSeq n * (1 / (4 * TSeq n)))) -
          ∫ u in (0 : ℝ)..(TSeq n * (1 / (4 * TSeq n))),
            gR n u * lamMinus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n))) / TSeq n := rfl

noncomputable def cR (n : ℕ) : ℝ := aSeq n / 2 / (1 - aSeq n / 2)

lemma lr_plus (n : ℕ) : plusSet (lr n) = (clPts ((2 : ℕ), (0 : ℕ), jr n, true) (csize (lr n))).toFinset := by
  have hplus : plusSet (lr n) =
      (clPts ((2 : ℕ), (0 : ℕ), jr n, true) (csize (lr n))).toFinset ∪ plusSet [] :=
    plusSet_cons_true _ rfl []
  have h0 : plusSet [] = ∅ := rfl
  rw [h0, Finset.union_empty] at hplus
  exact hplus

lemma lr_minus (n : ℕ) : minusSet (lr n) = ∅ := by
  have hminus : minusSet (lr n) = minusSet [] := minusSet_cons_true _ rfl []
  rw [hminus]
  rfl

lemma lr_card (n : ℕ) : (plusSet (lr n)).card = csize (lr n) := by rw [lr_plus, clPts_card]

lemma lr_big (n : ℕ) : 8 * (n : ℝ) + 10 ≤ (csize (lr n) : ℝ) := by
  have hE : Bnd2 n ≤ Encodable.encode (lr n) := Classical.choose_spec (exists_big2 (Bnd2 n))
  have hR : Bnd2 n < csize (lr n) := by
    unfold csize
    have := lt_two_pow' (Encodable.encode (lr n) + 1)
    omega
  have hK : ((Bnd2 n : ℕ) : ℝ) ≤ (csize (lr n) : ℝ) := by exact_mod_cast hR.le
  have hB : ((Bnd2 n : ℕ) : ℝ) = 8 * (n : ℝ) + 10 := by unfold Bnd2; push_cast; ring
  rw [hB] at hK
  exact hK

lemma lr_bounds (n : ℕ) : ∀ y ∈ plusSet (lr n), 0 < y ∧ y ≤ 1 / 4 := by
  intro y hy
  rw [lr_plus, List.mem_toFinset] at hy
  have hb := clPts_bounds _ _ y hy
  have e1 : (((2 : ℕ), (0 : ℕ), jr n, true) : Cl).2.1 = 0 := rfl
  have e2 : (((2 : ℕ), (0 : ℕ), jr n, true) : Cl).1 = 2 := rfl
  rw [e1, e2] at hb
  norm_num at hb
  exact ⟨hb.1, hb.2⟩

lemma TSeq_ge_one (n : ℕ) : (1 : ℝ) ≤ TSeq n := by
  unfold TSeq
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma aSeq_ge (n : ℕ) : (1 / 2 : ℝ) ≤ aSeq n := by
  unfold aSeq
  have : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  linarith

lemma hTt (n : ℕ) : TSeq n * (1 / (4 * TSeq n)) = 1 / 4 := by
  rw [mul_one_div, div_mul_eq_div_div_swap, div_self (TSeq_pos n).ne']

lemma cR_ge (n : ℕ) : (1 / 4 : ℝ) ≤ cR n := by
  have ha1 := aSeq_ge n
  have ha2 := aSeq_lt_one n
  have hb0 : 0 < 1 - aSeq n / 2 := by linarith
  have hb1 : 1 - aSeq n / 2 ≤ 1 := by linarith
  unfold cR
  rw [le_div_iff₀ hb0]
  have : aSeq n / 2 * (1 - aSeq n / 2) ≤ aSeq n / 2 := mul_le_of_le_one_right (by linarith) hb1
  nlinarith

lemma cR_pos (n : ℕ) : 0 < cR n := lt_of_lt_of_le (by norm_num) (cR_ge n)

lemma gR_eq (n : ℕ) (s : ℝ) : gR n s = cR n * Real.exp (-(1 - aSeq n / 2) * (1 / 4 - s)) := by
  have ha2 := aSeq_lt_one n
  unfold gR cR
  rw [tail12 _ _ (by linarith)]
  have e : TSeq n * (1 / (4 * TSeq n) - s / TSeq n) = 1 / 4 - s := by
    rw [mul_sub, hTt, mul_div_cancel₀ s (TSeq_pos n).ne']
  rw [e]

lemma gR_le (n : ℕ) (s : ℝ) (hs : s ≤ 1 / 4) : gR n s ≤ cR n := by
  have ha2 := aSeq_lt_one n
  have hb0 : 0 ≤ 1 - aSeq n / 2 := by linarith
  have hs' : 0 ≤ 1 / 4 - s := by linarith
  rw [gR_eq]
  have : Real.exp (-(1 - aSeq n / 2) * (1 / 4 - s)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_mul]
    exact neg_nonpos.mpr (mul_nonneg hb0 hs')
  calc _ ≤ cR n * 1 := mul_le_mul_of_nonneg_left this (cR_pos n).le
    _ = _ := mul_one _

lemma gR_nonneg (n : ℕ) (s : ℝ) : 0 ≤ gR n s := by
  rw [gR_eq]
  exact mul_nonneg (cR_pos n).le (Real.exp_pos _).le

lemma gR_ge (n : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) : cR n * (3 / 4) ≤ gR n s := by
  have ha1 := aSeq_ge n
  have ha2 := aSeq_lt_one n
  have hb1 : 1 - aSeq n / 2 ≤ 1 := by linarith
  rw [gR_eq]
  have hz : (1 - aSeq n / 2) * (1 / 4 - s) ≤ 1 / 4 := by
    have : (1 - aSeq n / 2) * (1 / 4 - s) ≤ 1 / 4 - s := mul_le_of_le_one_left (by linarith) hb1
    linarith
  have h1 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-(1 - aSeq n / 2) * (1 / 4 - s)) := by
    rw [Real.exp_le_exp, neg_mul]
    exact neg_le_neg hz
  have h2 : -(1 / 4 : ℝ) + 1 ≤ Real.exp (-(1 / 4 : ℝ)) := Real.add_one_le_exp _
  exact mul_le_mul_of_nonneg_left (by linarith) (cR_pos n).le

lemma Jp_ge (n : ℕ) : (csize (lr n) : ℝ) * (cR n * (3 / 4)) ≤
    jumpSumOn (path NpO (lr n)) (gR n) (Ioc 0 (1 / 4)) := by
  have hJp : jumpSumOn (path NpO (lr n)) (gR n) (Ioc 0 (1 / 4)) =
      ∑ y ∈ (plusSet (lr n)).filter (fun y => y ∈ Ioc (0 : ℝ) (1 / 4)), gR n y :=
    jumpSumOn_cnt (plusSet (lr n)) (gR n) (Ioc 0 (1 / 4))
  have hfilt : (plusSet (lr n)).filter (fun y => y ∈ Ioc (0 : ℝ) (1 / 4)) = plusSet (lr n) :=
    Finset.filter_true_of_mem (fun y hy => ⟨(lr_bounds n y hy).1, (lr_bounds n y hy).2⟩)
  rw [hJp, hfilt, ← lr_card, ← nsmul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _
    (fun y hy => gR_ge n y (lr_bounds n y hy).1.le (lr_bounds n y hy).2)

lemma Jm_zero (n : ℕ) : jumpSumOn (path NmO (lr n)) (gR n) (Ioc 0 (1 / 4)) = 0 := by
  have e := jumpSumOn_cnt (minusSet (lr n)) (gR n) (Ioc 0 (1 / 4))
  rw [lr_minus, Finset.filter_empty, Finset.sum_empty] at e
  exact e

lemma phi1_term_le (n : ℕ) (u y : ℝ) (hyu : y ≤ u) : aSeq n * phi1 (u - y) ≤ 1 := by
  have hex : Real.exp (-(u - y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (sub_nonneg.mpr hyu)
  have hphi : phi1 (u - y) ≤ 3 / 4 := by
    unfold phi1 phiE
    linarith
  have hphi0 : 0 ≤ phi1 (u - y) := (phiE_pos _).le.trans (phiE_le_phi1 _)
  calc aSeq n * phi1 (u - y) ≤ 1 * (3 / 4) :=
        mul_le_mul (aSeq_lt_one n).le hphi hphi0 zero_le_one
    _ ≤ 1 := by norm_num

lemma lamP_ub (n : ℕ) (u : ℝ) : lamPlus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n) ≤ 1 + csize (lr n) := by
  have e1 := jumpSumOn_cnt (plusSet (lr n)) (fun s => aSeq n * phi1 (u - s)) (Ioc 0 u)
  have e2 := jumpSumOn_cnt (minusSet (lr n)) (fun s => aSeq n * phi2 (u - s)) (Ioc 0 u)
  rw [lr_minus, Finset.filter_empty, Finset.sum_empty] at e2
  have hsum := Finset.sum_le_card_nsmul ((plusSet (lr n)).filter (fun y => y ∈ Ioc (0 : ℝ) u))
    (fun y => aSeq n * phi1 (u - y)) 1 (fun y hy => phi1_term_le n u y (Finset.mem_filter.mp hy).2.2)
  have hcf : (((plusSet (lr n)).filter (fun y => y ∈ Ioc (0 : ℝ) u)).card : ℝ) ≤ csize (lr n) := by
    rw [← lr_card]
    exact_mod_cast Finset.card_filter_le _ _
  rw [nsmul_eq_mul, mul_one] at hsum
  show 1 + jumpSumOn (fun t => (cnt (plusSet (lr n)) t : ℝ)) (fun s => aSeq n * phi1 (u - s)) (Ioc 0 u) +
    jumpSumOn (fun t => (cnt (minusSet (lr n)) t : ℝ)) (fun s => aSeq n * phi2 (u - s)) (Ioc 0 u) ≤ _
  rw [e1, lr_minus, e2]
  linarith

lemma lamP_lb (n : ℕ) (u : ℝ) : 0 ≤ lamPlus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n) := by
  have h := intensity_ge phi1 phi2 phiE_le_phi1 phi2_nonneg (plusSet (lr n)) (minusSet (lr n)) ∅
    (Finset.empty_subset _) (aSeq n) u u (u - 1) (aSeq_pos n) (by simp) (by linarith) le_rfl
  rw [Finset.card_empty, Nat.cast_zero, zero_mul] at h
  exact h

lemma lamM_lb (n : ℕ) (u : ℝ) : 0 ≤ lamMinus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n) := by
  have h := intensity_ge phi1 phi2 phiE_le_phi1 phi2_nonneg (minusSet (lr n)) (plusSet (lr n)) ∅
    (Finset.empty_subset _) (aSeq n) u u (u - 1) (aSeq_pos n) (by simp) (by linarith) le_rfl
  rw [Finset.card_empty, Nat.cast_zero, zero_mul] at h
  exact h

lemma Ip_le (n : ℕ) : ∫ u in (0 : ℝ)..(1 / 4), gR n u * lamPlus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n) ≤
    cR n * (1 + csize (lr n)) * (1 / 4) := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1 / 4) (C := cR n * (1 + csize (lr n)))
    (f := fun u => gR n u * lamPlus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n)) (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gR_nonneg n u), abs_of_nonneg (lamP_lb n u)]
      exact mul_le_mul (gR_le n u hu.2) (lamP_ub n u) (lamP_lb n u) (cR_pos n).le)
  rw [sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), Real.norm_eq_abs] at hn
  exact (le_abs_self _).trans hn

lemma Im_nonneg (n : ℕ) :
    0 ≤ ∫ u in (0 : ℝ)..(1 / 4), gR n u * lamMinus 1 (aSeq n) phi1 phi2 NpO NmO u (lr n) :=
  intervalIntegral.integral_nonneg (by norm_num) (fun u _ => mul_nonneg (gR_nonneg n u) (lamM_lb n u))

lemma rem_big (n : ℕ) :
    1 < |remainderR (TSeq n) 1 (aSeq n) phi1 phi2 NpO NmO (1 / (4 * TSeq n)) (lr n)| := by
  rw [rem_eq, hTt, Jm_zero]
  have hJ := Jp_ge n
  have hIp := Ip_le n
  have hIm := Im_nonneg n
  have hK := lr_big n
  have hc4 := cR_ge n
  have hTn : TSeq n = (n : ℝ) + 1 := rfl
  have hK2 : 0 ≤ (csize (lr n) : ℝ) / 2 - 1 / 4 := by linarith
  have hlow2 : 1 / 4 * ((csize (lr n) : ℝ) / 2 - 1 / 4) ≤ cR n * ((csize (lr n) : ℝ) / 2 - 1 / 4) :=
    mul_le_mul_of_nonneg_right hc4 hK2
  have e : cR n * ((csize (lr n) : ℝ) / 2 - 1 / 4) =
      (csize (lr n) : ℝ) * (cR n * (3 / 4)) - cR n * (1 + csize (lr n)) * (1 / 4) := by ring
  rw [lt_abs]
  left
  rw [lt_div_iff₀ (TSeq_pos n), one_mul, hTn]
  linarith

section MeasR

attribute [local instance] mOm

noncomputable def Pr (n : ℕ) : Measure Om := PmL (lr n)

lemma not_ucp : ¬ TendstoUCP01Zero Pr (fun n => remainderR (TSeq n) 1 (aSeq n) phi1 phi2 NpO NmO) := by
  intro h
  have hlim := h 1 one_pos
  have hge : ∀ n, (2⁻¹ : ℝ≥0∞) ≤ Pr n {ω | ∃ t ∈ Icc (0 : ℝ) 1,
      1 < |remainderR (TSeq n) 1 (aSeq n) phi1 phi2 NpO NmO t ω|} := by
    intro n
    have hT1 : (1 : ℝ) ≤ TSeq n := by
      unfold TSeq
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hmem : lr n ∈ {ω : Om | ∃ t ∈ Icc (0 : ℝ) 1,
        1 < |remainderR (TSeq n) 1 (aSeq n) phi1 phi2 NpO NmO t ω|} := by
      refine ⟨1 / (4 * TSeq n), ⟨by positivity, ?_⟩, rem_big n⟩
      rw [div_le_one (by positivity)]
      linarith
    calc (2⁻¹ : ℝ≥0∞) = 2⁻¹ * Measure.dirac (lr n) {ω : Om | ∃ t ∈ Icc (0 : ℝ) 1,
          1 < |remainderR (TSeq n) 1 (aSeq n) phi1 phi2 NpO NmO t ω|} := by
          rw [Measure.dirac_apply_of_mem hmem, mul_one]
      _ ≤ _ := by
          rw [Pr, PmL, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
          exact le_self_add
  have hpos : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).2 _ hpos).exists
  exact absurd (hge N) (not_le.mpr hN)

end MeasR

end D7ade

open NearlyUnstableHawkes.Heston in
theorem solution : ¬ (∀ {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hA3 : Assumption3 a φ₁ φ₂ m)
    (hA4 : Assumption4 T a φ₁ φ₂)
    (lam : ℝ) (hlam : 0 < lam) (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (μ : ℝ) (hμ : 0 < μ) (Np Nm : ∀ n, ℝ → Ω n → ℕ)
    (hH : ∀ n, IsHawkes2 (P n) μ (fun s => a n * φ₁ s) (fun s => a n * φ₂ s) (T n) (Np n) (Nm n)),
    TendstoUCP01Zero P (fun n => remainderR (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n))) := by
  intro H
  have hprob : ∀ n, IsProbabilityMeasure (D7ade.Pr n) := fun n => D7ade.PmL_prob _
  exact D7ade.not_ucp
    (@H (fun _ => D7ade.Om) (fun _ => D7ade.mOm) D7ade.Pr hprob D7ade.TSeq D7ade.TSeq_pos
      D7ade.TSeq_tendsto D7ade.aSeq D7ade.phi1 D7ade.phi2 1 D7ade.assumption3' D7ade.assumption4'
      (1 / 2) (by norm_num) D7ade.h3 1 one_pos (fun _ => D7ade.NpO) (fun _ => D7ade.NmO)
      (fun n => D7ade.hawkes2 _ n))
