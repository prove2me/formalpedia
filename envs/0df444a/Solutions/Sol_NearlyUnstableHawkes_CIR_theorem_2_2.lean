-- Prove2me | solution 1 for NearlyUnstableHawkes.CIR.theorem_2_2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T14:16:08.545365+00:00
-- url     : https://prove2.me/submissions/36761634-35b7-4d5f-b26c-da75579a2a17

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting
import Definitions.Def_EthierKurtz_SolvesBrownianSDE

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Dfc2c

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

lemma assumption2 : NearlyUnstableHawkes.CIR.Assumption2 TSeq aSeq (fun s => phiE s + phiE s) := by
  obtain ⟨K, hK, h⟩ := assumption4
  exact ⟨K, hK, fun n x hx => h n x hx⟩

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

/-! ### The price is huge with probability at least one half -/

lemma lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]
    omega

lemma exists_big (N : ℕ) : ∃ j : ℕ, N ≤ Encodable.encode ([((0 : ℕ), (0 : ℕ), j, true)] : Om) := by
  have hinj : Function.Injective
      (fun j : ℕ => Encodable.encode ([((0 : ℕ), (0 : ℕ), j, true)] : Om)) := by
    intro j j' h
    have := Encodable.encode_injective h
    simpa using this
  exact (hinj.nat_tendsto_atTop.eventually_ge_atTop N).exists


lemma timechange_one {l : ℝ → ℝ} (hl : NearlyUnstableHawkes.CIR.IsTimeChange01 l) : l 1 = 1 := by
  obtain ⟨-, hmono, himg⟩ := hl
  have h1 : (1 : ℝ) ∈ l '' Icc 0 1 := by rw [himg]; exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨t, ht, hlt⟩ := h1
  have hl1 : l 1 ∈ Icc (0 : ℝ) 1 := by rw [← himg]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  rcases eq_or_lt_of_le ht.2 with h | h
  · have h' : t = 1 := h
    subst h'
    exact hlt
  · have := hmono ht ⟨zero_le_one, le_rfl⟩ h
    exfalso
    linarith [hl1.2]

/-! ### The rescaled count is huge with probability at least one half -/

noncomputable def jbigV (n : ℕ) : ℕ := Classical.choose (exists_big (2 * n * (n + 1) ^ 2))

noncomputable def lstarV (n : ℕ) : Om := [((0 : ℕ), (0 : ℕ), jbigV n, true)]

/-- The rescaled count `V` of the counterexample (all processes equal to `NpO`). -/
noncomputable abbrev VO : ∀ n : ℕ, ℝ → (fun _ : ℕ => Om) n → ℝ :=
  NearlyUnstableHawkes.CIR.V (Ω := fun _ : ℕ => Om) TSeq aSeq (fun _ => NpO)

lemma V_lstar (n : ℕ) : (n : ℝ) ≤ VO n 1 (lstarV n) := by
  have hE : 2 * n * (n + 1) ^ 2 ≤ Encodable.encode (lstarV n) :=
    Classical.choose_spec (exists_big (2 * n * (n + 1) ^ 2))
  have hR : 2 * n * (n + 1) ^ 2 < csize (lstarV n) := by
    unfold csize
    have := lt_two_pow' (Encodable.encode (lstarV n) + 1)
    omega
  have hplus : plusSet (lstarV n) =
      (clPts ((0 : ℕ), (0 : ℕ), jbigV n, true) (csize (lstarV n))).toFinset ∪ plusSet [] :=
    plusSet_cons_true _ rfl []
  have hcntp : cnt (plusSet (lstarV n)) (1 * TSeq n) = csize (lstarV n) := by
    rw [hplus]
    unfold cnt
    rw [Finset.filter_true_of_mem]
    · have h0 : plusSet [] = ∅ := rfl
      rw [h0, Finset.union_empty, clPts_card]
    · intro y hy
      have h0 : plusSet [] = ∅ := rfl
      rw [h0, Finset.union_empty, List.mem_toFinset] at hy
      have hb := (clPts_bounds _ _ y hy).2
      simp only [Nat.cast_zero, zero_add, pow_zero, div_one] at hb
      have : (1 : ℝ) ≤ 1 * TSeq n := by
        unfold TSeq
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      linarith
  show (n : ℝ) ≤ (1 - aSeq n) / TSeq n * ((cnt (plusSet (lstarV n)) (1 * TSeq n) : ℕ) : ℝ)
  rw [hcntp]
  have key : (1 - aSeq n) / TSeq n = 1 / (2 * ((n : ℝ) + 1) ^ 2) := by
    unfold aSeq TSeq
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hc : ((2 * n * (n + 1) ^ 2 : ℕ) : ℝ) < (csize (lstarV n) : ℝ) := by exact_mod_cast hR
  push_cast at hc
  generalize ((csize (lstarV n) : ℕ) : ℝ) = c at hc ⊢
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) ^ 2 := mul_pos two_pos (pow_pos hn1 2)
  rw [key, div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  have e : (n : ℝ) * (2 * ((n : ℝ) + 1) ^ 2) = 2 * (n : ℝ) * ((n : ℝ) + 1) ^ 2 := by ring
  rw [e]
  exact hc.le

section Meas3

attribute [local instance] mOm

noncomputable def PmV (n : ℕ) : Measure Om := PmL (lstarV n)

lemma PmV_ge (n : ℕ) : (2⁻¹ : ℝ≥0∞) ≤ PmV n {ω | (n : ℝ) ≤ VO n 1 ω} := by
  have hmem : lstarV n ∈ {ω : Om | (n : ℝ) ≤ VO n 1 ω} := V_lstar n
  calc (2⁻¹ : ℝ≥0∞) = 2⁻¹ * Measure.dirac (lstarV n) {ω : Om | (n : ℝ) ≤ VO n 1 ω} := by
        rw [Measure.dirac_apply_of_mem hmem, mul_one]
    _ ≤ PmV n {ω | (n : ℝ) ≤ VO n 1 ω} := by
        rw [PmV, PmL, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
        exact le_self_add

end Meas3

section Meas4

attribute [local instance] mOm

lemma not_convV {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (x : ℝ → Ω' → ℝ) :
    ¬ NearlyUnstableHawkes.CIR.ConvInLawSkorohod01 (Ω := fun _ : ℕ => Om) PmV VO P' x := by
  rintro ⟨Ω'', m'', P'', W, W', hP'', hW, -, hae⟩
  let one : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  let Y : ℕ → Ω'' → ℝ := fun n ω => W n ω 1
  let Yl : Ω'' → ℝ := fun ω => W' ω 1
  have hE : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ≤ P'' {ω | (n : ℝ) ≤ Y n ω} := by
    intro n
    have hS : MeasurableSet {f : Icc (0 : ℝ) 1 → ℝ | (n : ℝ) ≤ f one} :=
      measurableSet_le measurable_const (measurable_pi_apply one)
    have := (hW n).measure_mem_eq hS
    have e1 : (fun ω (t : Icc (0 : ℝ) 1) => W n ω t.val) ⁻¹'
        {f : Icc (0 : ℝ) 1 → ℝ | (n : ℝ) ≤ f one} = {ω | (n : ℝ) ≤ Y n ω} := rfl
    rw [e1] at this
    rw [this]
    exact PmV_ge n
  have hlim : ∀ᵐ ω ∂P'', Tendsto (fun n => Y n ω) atTop (𝓝 (Yl ω)) := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, -, l, hl, hunif, -⟩ := hω
    have h1 := hunif.tendsto_at (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    have hl1 : ∀ n, l n 1 = 1 := fun n => timechange_one (hl n)
    simp only [Function.comp_apply, hl1] at h1
    exact h1
  have hev : ∀ᵐ ω ∂P'', ∃ N : ℕ, ∀ n ≥ N, Y n ω < n := by
    filter_upwards [hlim] with ω hω
    have h1 := hω.eventually (gt_mem_nhds (lt_add_one (Yl ω)))
    have h2 := tendsto_natCast_atTop_atTop.eventually_gt_atTop (Yl ω + 1)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h1.and h2)
    exact ⟨N, fun n hn => (hN n hn).1.trans (hN n hn).2⟩
  let G : ℕ → Set Ω'' := fun N => {ω | ∀ n ≥ N, Y n ω < n}
  have hGmono : Monotone G := by
    intro N N' hNN' ω hω n hn
    exact hω n (le_trans hNN' hn)
  have hnull : P'' (⋃ N, G N)ᶜ = 0 := by
    rw [ae_iff] at hev
    refine le_antisymm (le_trans (measure_mono ?_) hev.le) zero_le
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hω
    simp only [Set.mem_setOf_eq, not_exists]
    exact fun N => hω N
  have hU : P'' (⋃ N, G N) = 1 := by
    apply le_antisymm prob_le_one
    calc (1 : ℝ≥0∞) = P'' univ := measure_univ.symm
      _ ≤ P'' (⋃ N, G N) + P'' (⋃ N, G N)ᶜ := measure_univ_le_add_compl _
      _ = P'' (⋃ N, G N) := by rw [hnull, add_zero]
  have htend := tendsto_measure_iUnion_atTop (μ := P'') hGmono
  rw [hU] at htend
  have hlt : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.mpr ENNReal.one_lt_two
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 htend).1 _ hlt)
  have hGN := hN N le_rfl
  have hYm : AEMeasurable (Y N) P'' :=
    (measurable_pi_apply one).comp_aemeasurable (hW N).aemeasurable_fst
  have hnm : NullMeasurableSet {ω | (N : ℝ) ≤ Y N ω} P'' := nullMeasurableSet_le aemeasurable_const hYm
  have hsum := measure_add_measure_compl₀ hnm
  rw [measure_univ] at hsum
  have hsubG : G N ⊆ {ω | (N : ℝ) ≤ Y N ω}ᶜ := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    exact hω N le_rfl
  have hc : (2⁻¹ : ℝ≥0∞) < P'' {ω | (N : ℝ) ≤ Y N ω}ᶜ :=
    lt_of_lt_of_le hGN (measure_mono hsubG)
  have h1 : (2⁻¹ : ℝ≥0∞) + 2⁻¹ < 2⁻¹ + P'' {ω | (N : ℝ) ≤ Y N ω}ᶜ :=
    ENNReal.add_lt_add_left (by norm_num) hc
  have h2 : (2⁻¹ : ℝ≥0∞) + P'' {ω | (N : ℝ) ≤ Y N ω}ᶜ ≤
      P'' {ω | (N : ℝ) ≤ Y N ω} + P'' {ω | (N : ℝ) ≤ Y N ω}ᶜ := add_le_add (hE N) le_rfl
  rw [ENNReal.inv_two_add_inv_two] at h1
  rw [hsum] at h2
  exact lt_irrefl _ (lt_of_lt_of_le h1 h2)

end Meas4

end Dfc2c

open NearlyUnstableHawkes.CIR in
theorem solution : ¬ (∀ {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T a : ℕ → ℝ) (φ φ' : ℝ → ℝ) (m lam μ : ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ)
    (hTpos : ∀ n, 0 < T n)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 1))
    (hμ : 0 < μ) (hlam : 0 < lam)
    (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (hφ : Assumption1 φ φ' m) (hρ : Assumption2 T a φ)
    (hN : ∀ n, IsHawkes (P n) μ (fun s => a n * φ s) (T n) (N n)),
    (∃ (Ω' : Type) (m' : MeasurableSpace Ω'),
      letI := m'
      ∃ P' : Measure Ω', IsProbabilityMeasure P' ∧
        ∃ (B X : ℝ≥0 → Ω' → EthierKurtz.SDEState 1),
          EthierKurtz.IsStandardBrownian P' B ∧
          EthierKurtz.SolvesBrownianSDE P' (cirDiff lam m)
            (cirDrift μ lam m) B (fun _ => 0) X) ∧
    (∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      (B X : ℝ≥0 → Ω' → EthierKurtz.SDEState 1),
      IsProbabilityMeasure P' →
      EthierKurtz.IsStandardBrownian P' B →
      EthierKurtz.SolvesBrownianSDE P' (cirDiff lam m)
        (cirDrift μ lam m) B (fun _ => 0) X →
      ConvInLawSkorohod01 P (C T a μ φ N) P'
        (fun t ω => X t.toNNReal ω 0) ∧
      ConvInLawSkorohod01 P (V T a N) P'
        (fun t ω => ∫ s in (0 : ℝ)..t, X s.toNNReal ω 0))) := by
  intro H
  have hprob : ∀ n, IsProbabilityMeasure (Dfc2c.PmV n) := fun n => Dfc2c.PmL_prob _
  obtain ⟨⟨Ω', mΩ', P', hP', B, X, hB, hX⟩, hconv⟩ :=
    @H (fun _ => Dfc2c.Om) (fun _ => Dfc2c.mOm) Dfc2c.PmV hprob Dfc2c.TSeq Dfc2c.aSeq
      (fun s => Dfc2c.phiE s + Dfc2c.phiE s) (fun s => -(Real.exp (-s))) 1 (1 / 2) 1
      (fun _ => Dfc2c.NpO) Dfc2c.TSeq_pos Dfc2c.aSeq_pos Dfc2c.aSeq_lt_one Dfc2c.TSeq_tendsto
      Dfc2c.assumption3.2.2.1 one_pos (by norm_num) Dfc2c.h3 Dfc2c.assumption1 Dfc2c.assumption2
      (fun n => Dfc2c.hawkesCIR _ n)
  exact Dfc2c.not_convV P' _ (@hconv Ω' mΩ' P' B X hP' hB hX).2
