-- Prove2me | solution 1 for MartOT.Shadow.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:38:46.781264+00:00
-- url     : https://prove2.me/submissions/db01064d-3212-4e54-9a63-b5591f3a78c3

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Definitions.Def_MartOT_Shadow_ConvergesInM

open MeasureTheory Filter Topology BoundedContinuousFunction
open MartOT.Var MartOT.Shadow

/-! ### Part 1: Convex supporting lines, `integralE`, and `ConvexLE` -/

private lemma convexOn_exists_supporting_line {ϕ : ℝ → ℝ} (hϕ : ConvexOn ℝ Set.univ ϕ) (b : ℝ) :
    ∃ a : ℝ, ∀ x : ℝ, ϕ b + a * (x - b) ≤ ϕ x := by
  let S : Set ℝ := {s | ∃ x : ℝ, x < b ∧ s = (ϕ b - ϕ x) / (b - x)}
  have hS_ne : S.Nonempty := ⟨(ϕ b - ϕ (b - 1)) / (b - (b - 1)), b - 1, by linarith, rfl⟩
  have hS_ub : ∀ y : ℝ, b < y → ∀ s ∈ S, s ≤ (ϕ y - ϕ b) / (y - b) := by
    intro y hby s ⟨x, hxb, hs⟩
    rw [hs]
    exact hϕ.slope_mono_adjacent trivial trivial hxb hby
  have hS_bdd : BddAbove S := ⟨(ϕ (b + 1) - ϕ b) / ((b + 1) - b), hS_ub (b + 1) (by linarith)⟩
  refine ⟨sSup S, fun x => ?_⟩
  rcases lt_trichotomy x b with hlt | rfl | hgt
  · have hle : (ϕ b - ϕ x) / (b - x) ≤ sSup S := le_csSup hS_bdd ⟨x, hlt, rfl⟩
    have hpos : 0 < b - x := sub_pos.mpr hlt
    have hmul : ϕ b - ϕ x ≤ sSup S * (b - x) := (div_le_iff₀ hpos).mp hle
    linarith
  · simp
  · have hle : sSup S ≤ (ϕ x - ϕ b) / (x - b) := csSup_le hS_ne (hS_ub x hgt)
    have hpos : 0 < x - b := sub_pos.mpr hgt
    have hmul : sSup S * (x - b) ≤ ϕ x - ϕ b := (le_div_iff₀ hpos).mp hle
    linarith

private lemma convexOn_univ_continuous {ϕ : ℝ → ℝ} (hϕ : ConvexOn ℝ Set.univ ϕ) :
    Continuous ϕ :=
  continuousOn_univ.mp (by simpa [interior_univ] using hϕ.continuousOn_interior)

private lemma integralE_eq_sub_lintegral (μ : Measure ℝ) (f : ℝ → ℝ) :
    integralE μ f =
      ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
        ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal) := by
  unfold integralE ModelRiskOT.Duality.extIntegral
  have h1 : (fun x => ((f x : EReal)).toENNReal) = fun x => ENNReal.ofReal (f x) := rfl
  have h2 : (fun x => (-(f x : EReal)).toENNReal) = fun x => ENNReal.ofReal (-f x) := by
    ext x
    rw [← EReal.coe_neg]
    rfl
  rw [h1, h2]

private lemma lintegral_ofReal_lt_top_of_integrable {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f μ) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤ := by
  refine (lintegral_mono fun x => ?_).trans_lt hf.2
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self (f x))

private lemma ereal_coe_ennreal_eq_coe_toReal {a : ENNReal} (ha : a ≠ ⊤) :
    (a : EReal) = ((a.toReal : ℝ) : EReal) := by
  lift a to NNReal using ha
  rw [ENNReal.coe_toReal]
  rfl

private lemma ereal_sub_ennreal_of_ne_top {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a : EReal) - (b : EReal) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  rw [ereal_coe_ennreal_eq_coe_toReal ha, ereal_coe_ennreal_eq_coe_toReal hb, EReal.coe_sub]

private lemma integralE_eq_coe_integral {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ) :
    integralE μ f = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  rw [integralE_eq_sub_lintegral, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  exact ereal_sub_ennreal_of_ne_top
    (lintegral_ofReal_lt_top_of_integrable hf).ne
    (lintegral_ofReal_lt_top_of_integrable hf.neg).ne

private lemma integralE_mono {μ : Measure ℝ} {g f : ℝ → ℝ} (hle : ∀ x, g x ≤ f x) :
    integralE μ g ≤ integralE μ f := by
  rw [integralE_eq_sub_lintegral, integralE_eq_sub_lintegral, sub_eq_add_neg, sub_eq_add_neg]
  have hpos : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
    lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
  have hneg : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (-g x) ∂μ :=
    lintegral_mono fun x => ENNReal.ofReal_le_ofReal (neg_le_neg (hle x))
  exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
    (EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg))

private lemma integralE_smul_dirac (c : ENNReal) (hc : c ≠ ⊤) (b : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) :
    integralE (c • Measure.dirac b) f = ((c.toReal * f b : ℝ) : EReal) := by
  have hm1 : Measurable (fun x => ENNReal.ofReal (f x)) := ENNReal.measurable_ofReal.comp hf
  have hm2 : Measurable (fun x => ENNReal.ofReal (-f x)) := ENNReal.measurable_ofReal.comp hf.neg
  rw [integralE_eq_sub_lintegral, lintegral_smul_measure, lintegral_smul_measure,
    smul_eq_mul, smul_eq_mul, lintegral_dirac' b hm1, lintegral_dirac' b hm2]
  rw [ereal_sub_ennreal_of_ne_top (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top)]
  congr 1
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  cases le_total 0 (f b) with
  | inl h =>
    rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  | inr h =>
    rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

private lemma inM_smul_dirac (c : ENNReal) (hc : c ≠ ⊤) (b : ℝ) :
    InM (c • Measure.dirac b) := by
  have : IsFiniteMeasure (c • Measure.dirac b) := ⟨by simp [hc.lt_top]⟩
  exact ⟨this, (integrable_dirac (by simp)).smul_measure hc⟩

private lemma convexLE_smul_dirac_of_barycenter {μ : Measure ℝ} (hμ : InM μ) (b : ℝ)
    (hb : (μ Set.univ).toReal * b = ∫ x, x ∂μ) :
    ConvexLE (μ Set.univ • Measure.dirac b) μ := by
  have : IsFiniteMeasure μ := hμ.1
  have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  refine ⟨inM_smul_dirac _ hfin b, hμ, fun ϕ hϕ => ?_⟩
  obtain ⟨a, ha⟩ := convexOn_exists_supporting_line hϕ b
  have hsub : Integrable (fun x : ℝ => x - b) μ := hμ.2.sub (integrable_const b)
  have hmul : Integrable (fun x : ℝ => a * (x - b)) μ := hsub.const_mul a
  let g : ℝ → ℝ := fun x => ϕ b + a * (x - b)
  have hg_int : Integrable g μ := (integrable_const (ϕ b)).add hmul
  have hg_val : ∫ x, g x ∂μ = (μ Set.univ).toReal * ϕ b := by
    change ∫ x, (ϕ b + a * (x - b)) ∂μ = (μ Set.univ).toReal * ϕ b
    rw [integral_add (integrable_const (ϕ b)) hmul, integral_const, smul_eq_mul, Measure.real,
      integral_const_mul, integral_sub hμ.2 (integrable_const b), integral_const, smul_eq_mul,
      Measure.real, ← hb]
    ring
  rw [integralE_smul_dirac _ hfin b (convexOn_univ_continuous hϕ).measurable, ← hg_val,
    ← integralE_eq_coe_integral hg_int]
  exact integralE_mono ha

private lemma lintegral_neg_convex_lt_top {μ : Measure ℝ} (hμ : InM μ) {ϕ : ℝ → ℝ}
    (hϕ : ConvexOn ℝ Set.univ ϕ) :
    ∫⁻ x, ENNReal.ofReal (-ϕ x) ∂μ < ⊤ := by
  have : IsFiniteMeasure μ := hμ.1
  obtain ⟨a, ha⟩ := convexOn_exists_supporting_line hϕ 0
  let g : ℝ → ℝ := fun x => ϕ 0 + a * (x - 0)
  have hg : Integrable g μ :=
    (integrable_const (ϕ 0)).add ((hμ.2.sub (integrable_const 0)).const_mul a)
  refine (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (neg_le_neg (ha x))).trans_lt ?_
  exact lintegral_ofReal_lt_top_of_integrable hg.neg

private lemma ereal_add_sub_add_ennreal {p₁ p₂ q₁ q₂ : ENNReal} (hq₁ : q₁ ≠ ⊤) (hq₂ : q₂ ≠ ⊤) :
    ((p₁ + p₂ : ENNReal) : EReal) - ((q₁ + q₂ : ENNReal) : EReal) =
      ((p₁ : EReal) - (q₁ : EReal)) + ((p₂ : EReal) - (q₂ : EReal)) := by
  by_cases hp₁ : p₁ = ⊤
  · subst hp₁
    have hq12 : q₁ + q₂ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hq₁, hq₂⟩
    have h2_ne_bot : (p₂ : EReal) - (q₂ : EReal) ≠ ⊥ := by
      rw [ereal_coe_ennreal_eq_coe_toReal hq₂, sub_eq_add_neg, ← EReal.coe_neg]
      intro hbot
      rcases EReal.add_eq_bot_iff.mp hbot with h | h
      · exact EReal.coe_ennreal_ne_bot p₂ h
      · exact EReal.coe_ne_bot (-q₂.toReal) h
    rw [top_add, EReal.coe_ennreal_top, ereal_coe_ennreal_eq_coe_toReal hq12,
      ereal_coe_ennreal_eq_coe_toReal hq₁, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.top_add_of_ne_bot h2_ne_bot]
  · by_cases hp₂ : p₂ = ⊤
    · subst hp₂
      have hq12 : q₁ + q₂ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hq₁, hq₂⟩
      have h1_ne_bot : (p₁ : EReal) - (q₁ : EReal) ≠ ⊥ := by
        rw [ereal_sub_ennreal_of_ne_top hp₁ hq₁]
        exact EReal.coe_ne_bot _
      rw [add_top, EReal.coe_ennreal_top, ereal_coe_ennreal_eq_coe_toReal hq12,
        ereal_coe_ennreal_eq_coe_toReal hq₂, EReal.top_sub_coe, EReal.top_sub_coe,
        EReal.add_top_of_ne_bot h1_ne_bot]
    · rw [ereal_sub_ennreal_of_ne_top (ENNReal.add_ne_top.mpr ⟨hp₁, hp₂⟩)
          (ENNReal.add_ne_top.mpr ⟨hq₁, hq₂⟩),
        ereal_sub_ennreal_of_ne_top hp₁ hq₁, ereal_sub_ennreal_of_ne_top hp₂ hq₂,
        ← EReal.coe_add, ENNReal.toReal_add hp₁ hp₂, ENNReal.toReal_add hq₁ hq₂]
      congr 1
      ring

private lemma integralE_add_measure_convex {μ₁ μ₂ : Measure ℝ} (h₁ : InM μ₁) (h₂ : InM μ₂)
    {ϕ : ℝ → ℝ} (hϕ : ConvexOn ℝ Set.univ ϕ) :
    integralE (μ₁ + μ₂) ϕ = integralE μ₁ ϕ + integralE μ₂ ϕ := by
  rw [integralE_eq_sub_lintegral, integralE_eq_sub_lintegral, integralE_eq_sub_lintegral,
    lintegral_add_measure, lintegral_add_measure]
  exact ereal_add_sub_add_ennreal
    (lintegral_neg_convex_lt_top h₁ hϕ).ne
    (lintegral_neg_convex_lt_top h₂ hϕ).ne

private lemma convexLE_zero : ConvexLE (0 : Measure ℝ) 0 :=
  ⟨⟨inferInstance, integrable_zero_measure⟩, ⟨inferInstance, integrable_zero_measure⟩,
    fun _ _ => le_rfl⟩

private lemma convexLE_add {μ₁ μ₂ ν₁ ν₂ : Measure ℝ}
    (h₁ : ConvexLE μ₁ ν₁) (h₂ : ConvexLE μ₂ ν₂) :
    ConvexLE (μ₁ + μ₂) (ν₁ + ν₂) := by
  have := h₁.1.1; have := h₂.1.1; have := h₁.2.1.1; have := h₂.2.1.1
  refine ⟨⟨inferInstance, h₁.1.2.add_measure h₂.1.2⟩,
    ⟨inferInstance, h₁.2.1.2.add_measure h₂.2.1.2⟩, fun ϕ hϕ => ?_⟩
  rw [integralE_add_measure_convex h₁.1 h₂.1 hϕ,
    integralE_add_measure_convex h₁.2.1 h₂.2.1 hϕ]
  exact add_le_add (h₁.2.2 ϕ hϕ) (h₂.2.2 ϕ hϕ)

private lemma convexLE_finset_sum {ι : Type*} (s : Finset ι) (μ ν : ι → Measure ℝ)
    (h : ∀ i ∈ s, ConvexLE (μ i) (ν i)) :
    ConvexLE (∑ i ∈ s, μ i) (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexLE_zero
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact convexLE_add (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Part 2: Dyadic refining partitions and barycenter compression -/

private def M (n : ℕ) : ℤ := (n : ℤ) * 2 ^ n

private lemma M_nonneg (n : ℕ) : 0 ≤ M n := by
  unfold M
  positivity

private noncomputable def cellIdxSet (n : ℕ) : Finset ℤ := Finset.Icc (-M n - 1) (M n)

private noncomputable def idx (n : ℕ) (x : ℝ) : ℤ :=
  if x < -(n : ℝ) then -M n - 1
  else if (n : ℝ) ≤ x then M n
  else ⌊x * (2 : ℝ) ^ n⌋

private def proj (n : ℕ) (j : ℤ) : ℤ :=
  if j < -2 * M n then -M n - 1
  else if 2 * M n ≤ j then M n
  else j / 2

private def cell (n : ℕ) (k : ℤ) : Set ℝ := idx n ⁻¹' {k}

private noncomputable def bary (γ : Measure ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  if γ (cell n k) = 0 then (k : ℝ) / (2 : ℝ) ^ n
  else (γ (cell n k)).toReal⁻¹ * ∫ x in cell n k, x ∂γ

private noncomputable def approxMap (γ : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  bary γ n (idx n x)

private noncomputable def approxMeas (γ : Measure ℝ) (n : ℕ) : Measure ℝ :=
  γ.map (approxMap γ n)

private lemma idx_mem (n : ℕ) (x : ℝ) : idx n x ∈ cellIdxSet n := by
  unfold idx cellIdxSet
  have hM : 0 ≤ M n := M_nonneg n
  rw [Finset.mem_Icc]
  split_ifs with h1 h2
  · omega
  · omega
  · push Not at h1 h2
    have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hlow : (-(M n) : ℝ) ≤ x * (2 : ℝ) ^ n := by
      have : (-(M n) : ℝ) = -(n : ℝ) * (2 : ℝ) ^ n := by unfold M; push_cast; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h1 hpow.le
    have hhi : x * (2 : ℝ) ^ n < (M n : ℝ) := by
      have : (M n : ℝ) = (n : ℝ) * (2 : ℝ) ^ n := by unfold M; push_cast; ring
      rw [this]
      exact mul_lt_mul_of_pos_right h2 hpow
    have hfl1 : -M n ≤ ⌊x * (2 : ℝ) ^ n⌋ := Int.le_floor.mpr (by exact_mod_cast hlow)
    have hfl2 : ⌊x * (2 : ℝ) ^ n⌋ < M n := Int.floor_lt.mpr (by exact_mod_cast hhi)
    omega

private lemma proj_mem (n : ℕ) (j : ℤ) : proj n j ∈ cellIdxSet n := by
  unfold proj cellIdxSet
  have hM : 0 ≤ M n := M_nonneg n
  rw [Finset.mem_Icc]
  split_ifs with h1 h2 <;> omega

private lemma proj_idx (n : ℕ) (x : ℝ) : proj n (idx (n + 1) x) = idx n x := by
  unfold proj idx
  have hM_step : 2 * M n + 2 ^ (n + 1) = M (n + 1) := by
    unfold M; push_cast; ring
  have h2pow : (1 : ℤ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hM : 0 ≤ M n := M_nonneg n
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  by_cases hlt1 : x < -((n + 1 : ℕ) : ℝ)
  · have hltn : x < -(n : ℝ) := by push_cast at hlt1; linarith
    have hleft : -M (n + 1) - 1 < -2 * M n := by linarith
    rw [if_pos hlt1, if_pos hltn, if_pos hleft]
  · push Not at hlt1
    by_cases hge1 : ((n + 1 : ℕ) : ℝ) ≤ x
    · have hgen : (n : ℝ) ≤ x := by push_cast at hge1; linarith
      have hnot_lt_n : ¬ x < -(n : ℝ) := by push Not; linarith
      have hM_ge : 2 * M n ≤ M (n + 1) := by linarith
      have hM_not_lt : ¬ M (n + 1) < -2 * M n := by linarith
      rw [if_neg (not_lt.mpr hlt1), if_pos hge1, if_neg hM_not_lt, if_pos hM_ge,
        if_neg hnot_lt_n, if_pos hgen]
    · push Not at hge1
      rw [if_neg (not_lt.mpr hlt1), if_neg (not_le.mpr hge1)]
      by_cases hltn : x < -(n : ℝ)
      · have hmul : x * (2 : ℝ) ^ (n + 1) < ((-2 * M n : ℤ) : ℝ) := by
          have : ((-2 * M n : ℤ) : ℝ) = -(n : ℝ) * (2 : ℝ) ^ (n + 1) := by
            unfold M; push_cast; ring
          rw [this]
          exact mul_lt_mul_of_pos_right hltn hpow
        have hfl : ⌊x * (2 : ℝ) ^ (n + 1)⌋ < -2 * M n := Int.floor_lt.mpr hmul
        rw [if_pos hltn, if_pos hfl]
      · push Not at hltn
        by_cases hgen : (n : ℝ) ≤ x
        · have hmul : ((2 * M n : ℤ) : ℝ) ≤ x * (2 : ℝ) ^ (n + 1) := by
            have : ((2 * M n : ℤ) : ℝ) = (n : ℝ) * (2 : ℝ) ^ (n + 1) := by
              unfold M; push_cast; ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hgen hpow.le
          have hfl : 2 * M n ≤ ⌊x * (2 : ℝ) ^ (n + 1)⌋ := Int.le_floor.mpr hmul
          have hfl_not_lt : ¬ ⌊x * (2 : ℝ) ^ (n + 1)⌋ < -2 * M n := by linarith
          rw [if_neg (not_lt.mpr hltn), if_pos hgen, if_neg hfl_not_lt, if_pos hfl]
        · push Not at hgen
          have hlow : ((-2 * M n : ℤ) : ℝ) ≤ x * (2 : ℝ) ^ (n + 1) := by
            have : ((-2 * M n : ℤ) : ℝ) = -(n : ℝ) * (2 : ℝ) ^ (n + 1) := by
              unfold M; push_cast; ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hltn hpow.le
          have hhi : x * (2 : ℝ) ^ (n + 1) < ((2 * M n : ℤ) : ℝ) := by
            have : ((2 * M n : ℤ) : ℝ) = (n : ℝ) * (2 : ℝ) ^ (n + 1) := by
              unfold M; push_cast; ring
            rw [this]
            exact mul_lt_mul_of_pos_right hgen hpow
          have hfl1 : -2 * M n ≤ ⌊x * (2 : ℝ) ^ (n + 1)⌋ := Int.le_floor.mpr hlow
          have hfl2 : ⌊x * (2 : ℝ) ^ (n + 1)⌋ < 2 * M n := Int.floor_lt.mpr hhi
          rw [if_neg (not_lt.mpr hltn), if_neg (not_le.mpr hgen),
            if_neg (not_lt.mpr hfl1), if_neg (not_le.mpr hfl2)]
          set k := ⌊x * (2 : ℝ) ^ n⌋
          have hk1 : (k : ℝ) ≤ x * (2 : ℝ) ^ n := Int.floor_le _
          have hk2 : x * (2 : ℝ) ^ n < (k : ℝ) + 1 := Int.lt_floor_add_one _
          have h2k1 : ((2 * k : ℤ) : ℝ) ≤ x * (2 : ℝ) ^ (n + 1) := by
            push_cast; rw [pow_succ]; linarith
          have h2k2 : x * (2 : ℝ) ^ (n + 1) < ((2 * k + 2 : ℤ) : ℝ) := by
            push_cast; rw [pow_succ]; linarith
          have hfl_ge : 2 * k ≤ ⌊x * (2 : ℝ) ^ (n + 1)⌋ := Int.le_floor.mpr h2k1
          have hfl_lt : ⌊x * (2 : ℝ) ^ (n + 1)⌋ < 2 * k + 2 := Int.floor_lt.mpr h2k2
          omega

private lemma measurable_idx (n : ℕ) : Measurable (idx n) := by
  unfold idx
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  exact Int.measurable_floor.comp (measurable_id.mul_const ((2 : ℝ) ^ n))

private lemma measurableSet_cell (n : ℕ) (k : ℤ) : MeasurableSet (cell n k) :=
  measurable_idx n (MeasurableSet.singleton k)

private lemma measurable_approxMap (γ : Measure ℝ) (n : ℕ) : Measurable (approxMap γ n) :=
  (measurable_of_countable (bary γ n)).comp (measurable_idx n)

private lemma cell_pairwiseDisjoint (n : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set ℤ) (cell n) := by
  intro k₁ _ k₂ _ hne
  exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hne (hx₁.symm.trans hx₂)

private lemma biUnion_cell_eq_univ (n : ℕ) : (⋃ k ∈ cellIdxSet n, cell n k) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨idx n x, idx_mem n x, rfl⟩

private lemma cell_eq_biUnion_filter (n : ℕ) (k : ℤ) :
    cell n k = ⋃ j ∈ (cellIdxSet (n + 1)).filter (fun j => proj n j = k), cell (n + 1) j := by
  ext x
  simp only [cell, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Finset.mem_filter]
  constructor
  · intro hx
    exact ⟨idx (n + 1) x, ⟨idx_mem (n + 1) x, by rw [proj_idx, hx]⟩, rfl⟩
  · rintro ⟨j, ⟨_, hjk⟩, hxj⟩
    rw [← proj_idx n x, hxj, hjk]

private lemma idx_nonneg_iff (n : ℕ) (x : ℝ) : 0 ≤ idx n x ↔ 0 ≤ x := by
  unfold idx
  have hM : 0 ≤ M n := M_nonneg n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  split_ifs with h1 h2
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith
  · push Not at h1 h2
    rw [Int.floor_nonneg]
    exact mul_nonneg_iff_of_pos_right hpow

private lemma sum_restrict_eq_restrict_biUnion {ι : Type*} (μ : Measure ℝ) (T : Finset ι)
    (s : ι → Set ℝ) (hd : (T : Set ι).PairwiseDisjoint s)
    (hm : ∀ i ∈ T, MeasurableSet (s i)) :
    ∑ i ∈ T, μ.restrict (s i) = μ.restrict (⋃ i ∈ T, s i) := by
  ext E hE
  rw [Measure.finsetSum_apply, Measure.restrict_apply hE, Set.inter_iUnion₂,
    measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.restrict_apply hE]
  · intro i hi j hj hij
    exact (hd hi hj hij).mono Set.inter_subset_right Set.inter_subset_right
  · intro i hi
    exact hE.inter (hm i hi)

private lemma approxMeas_eq_sum (γ : Measure ℝ) (n : ℕ) :
    approxMeas γ n = ∑ k ∈ cellIdxSet n, γ (cell n k) • Measure.dirac (bary γ n k) := by
  ext E hE
  rw [approxMeas, Measure.map_apply (measurable_approxMap γ n) hE, Measure.finsetSum_apply]
  have hsplit : approxMap γ n ⁻¹' E = ⋃ k ∈ cellIdxSet n, (approxMap γ n ⁻¹' E ∩ cell n k) := by
    rw [← Set.inter_iUnion₂, biUnion_cell_eq_univ, Set.inter_univ]
  rw [hsplit, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hE]
    by_cases hmem : bary γ n k ∈ E
    · have hsub : approxMap γ n ⁻¹' E ∩ cell n k = cell n k := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, cell, Set.mem_singleton_iff,
          and_iff_right_iff_imp]
        intro hx
        show bary γ n (idx n x) ∈ E
        rw [hx]
        exact hmem
      rw [hsub, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    · have hemp : approxMap γ n ⁻¹' E ∩ cell n k = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, cell, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hidx
        apply hmem
        change bary γ n (idx n x) ∈ E at hx
        rwa [hidx] at hx
      rw [hemp, measure_empty, Set.indicator_of_notMem hmem, mul_zero]
  · intro k₁ _ k₂ _ hne
    exact (cell_pairwiseDisjoint n trivial trivial hne).mono
      Set.inter_subset_right Set.inter_subset_right
  · intro k _
    exact (measurable_approxMap γ n hE).inter (measurableSet_cell n k)

private lemma cell_mul_bary (γ : Measure ℝ) (hγ : InM γ) (n : ℕ) (k : ℤ) :
    (γ (cell n k)).toReal * bary γ n k = ∫ x in cell n k, x ∂γ := by
  have : IsFiniteMeasure γ := hγ.1
  unfold bary
  split_ifs with h0
  · rw [h0, ENNReal.toReal_zero, zero_mul, Measure.restrict_eq_zero.mpr h0, integral_zero_measure]
  · have hpos : (γ (cell n k)).toReal ≠ 0 :=
      (ENNReal.toReal_pos h0 (measure_ne_top γ _)).ne'
    rw [← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

private lemma middle_cell_bounds {n : ℕ} {k : ℤ} (hk1 : -M n ≤ k) (hk2 : k < M n)
    {y : ℝ} (hy : y ∈ cell n k) :
    (k : ℝ) / (2 : ℝ) ^ n ≤ y ∧ y ≤ ((k : ℝ) + 1) / (2 : ℝ) ^ n := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hidx : idx n y = k := hy
  unfold idx at hidx
  split_ifs at hidx with h1 h2
  · omega
  · omega
  · have hle : (k : ℝ) ≤ y * (2 : ℝ) ^ n := by rw [← hidx]; exact Int.floor_le _
    have hlt : y * (2 : ℝ) ^ n < (k : ℝ) + 1 := by rw [← hidx]; exact Int.lt_floor_add_one _
    exact ⟨(div_le_iff₀ hpow).mpr hle, (le_div_iff₀ hpow).mpr hlt.le⟩

private lemma bary_middle_bounds (γ : Measure ℝ) (hγ : InM γ) {n : ℕ} {k : ℤ}
    (hk1 : -M n ≤ k) (hk2 : k < M n) :
    (k : ℝ) / (2 : ℝ) ^ n ≤ bary γ n k ∧ bary γ n k ≤ ((k : ℝ) + 1) / (2 : ℝ) ^ n := by
  have : IsFiniteMeasure γ := hγ.1
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  unfold bary
  split_ifs with h0
  · refine ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hpow.le⟩
  · have hpos : 0 < (γ (cell n k)).toReal := ENNReal.toReal_pos h0 (measure_ne_top γ _)
    have hlow : (k : ℝ) / (2 : ℝ) ^ n * (γ (cell n k)).toReal ≤ ∫ x in cell n k, x ∂γ := by
      have hconst : ∫ _ in cell n k, ((k : ℝ) / (2 : ℝ) ^ n) ∂γ =
          (γ (cell n k)).toReal * ((k : ℝ) / (2 : ℝ) ^ n) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real]
      rw [mul_comm, ← hconst]
      exact setIntegral_mono_on (integrableOn_const (hs := measure_ne_top γ _))
        hγ.2.integrableOn (measurableSet_cell n k) fun y hy => (middle_cell_bounds hk1 hk2 hy).1
    have hhi : ∫ x in cell n k, x ∂γ ≤ ((k : ℝ) + 1) / (2 : ℝ) ^ n * (γ (cell n k)).toReal := by
      have hconst : ∫ _ in cell n k, (((k : ℝ) + 1) / (2 : ℝ) ^ n) ∂γ =
          (γ (cell n k)).toReal * (((k : ℝ) + 1) / (2 : ℝ) ^ n) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real]
      rw [mul_comm, ← hconst]
      exact setIntegral_mono_on hγ.2.integrableOn
        (integrableOn_const (hs := measure_ne_top γ _))
        (measurableSet_cell n k) fun y hy => (middle_cell_bounds hk1 hk2 hy).2
    constructor
    · rw [le_inv_mul_iff₀ hpos, mul_comm]; exact hlow
    · rw [inv_mul_le_iff₀ hpos, mul_comm]; exact hhi

private lemma tendsto_approxMap (γ : Measure ℝ) (hγ : InM γ) (x : ℝ) :
    Tendsto (fun n => approxMap γ n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt |x|
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hx_abs : |x| < (n : ℝ) := hN₁.trans_le (Nat.cast_le.mpr hn1)
  have hx_low : -(n : ℝ) ≤ x := by linarith [(abs_lt.mp hx_abs).1]
  have hx_hi : x < (n : ℝ) := (abs_lt.mp hx_abs).2
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hk_eq : idx n x = ⌊x * (2 : ℝ) ^ n⌋ := by
    unfold idx
    rw [if_neg (not_lt.mpr hx_low), if_neg (not_le.mpr hx_hi)]
  have hk1 : -M n ≤ idx n x := by
    rw [hk_eq]
    have : (-(M n) : ℝ) ≤ x * (2 : ℝ) ^ n := by
      have : (-(M n) : ℝ) = -(n : ℝ) * (2 : ℝ) ^ n := by unfold M; push_cast; ring
      rw [this]; exact mul_le_mul_of_nonneg_right hx_low hpow.le
    exact Int.le_floor.mpr (by exact_mod_cast this)
  have hk2 : idx n x < M n := by
    rw [hk_eq]
    have : x * (2 : ℝ) ^ n < (M n : ℝ) := by
      have : (M n : ℝ) = (n : ℝ) * (2 : ℝ) ^ n := by unfold M; push_cast; ring
      rw [this]; exact mul_lt_mul_of_pos_right hx_hi hpow
    exact Int.floor_lt.mpr (by exact_mod_cast this)
  have hx_mem : x ∈ cell n (idx n x) := rfl
  have hx_b := middle_cell_bounds hk1 hk2 hx_mem
  have hb_b := bary_middle_bounds γ hγ hk1 hk2
  rw [Real.dist_eq]
  have hdiff : |approxMap γ n x - x| ≤ 1 / (2 : ℝ) ^ n := by
    unfold approxMap
    rw [abs_le]
    have hstep : ((idx n x : ℝ) + 1) / (2 : ℝ) ^ n - (idx n x : ℝ) / (2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
      ring
    constructor <;> linarith
  have hpow_le : 1 / (2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N₂ := by
    rw [← one_div_pow]
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) hn2
  exact (hdiff.trans hpow_le).trans_lt hN₂

private lemma integral_abs_approxMeas (γ : Measure ℝ) (hγ : InM γ) (n : ℕ) :
    ∫ x, |x| ∂(approxMeas γ n) = ∫ x, |x| ∂γ := by
  have : IsFiniteMeasure γ := hγ.1
  have habs : Integrable (fun x : ℝ => |x|) γ := by
    simpa only [Real.norm_eq_abs] using hγ.2.norm
  rw [approxMeas_eq_sum γ n, integral_finsetSum_measure]
  · have hsum : ∫ x, |x| ∂γ = ∑ k ∈ cellIdxSet n, ∫ x in cell n k, |x| ∂γ := by
      rw [← integral_biUnion_finset (cellIdxSet n) (fun k _ => measurableSet_cell n k)
        (fun k₁ _ k₂ _ hne => cell_pairwiseDisjoint n trivial trivial hne)
        (fun k _ => habs.integrableOn), biUnion_cell_eq_univ, Measure.restrict_univ]
    rw [hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac, smul_eq_mul]
    have hmul : (γ (cell n k)).toReal * |bary γ n k| = |(γ (cell n k)).toReal * bary γ n k| := by
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [hmul, cell_mul_bary γ hγ n k]
    by_cases hk : 0 ≤ k
    · have hnonneg : ∀ x ∈ cell n k, 0 ≤ x := fun x hx =>
        (idx_nonneg_iff n x).mp (by rwa [show idx n x = k from hx])
      have hint_nn : 0 ≤ ∫ x in cell n k, x ∂γ :=
        setIntegral_nonneg (measurableSet_cell n k) hnonneg
      rw [abs_of_nonneg hint_nn]
      exact setIntegral_congr_fun (measurableSet_cell n k) fun x hx =>
        (abs_of_nonneg (hnonneg x hx)).symm
    · have hneg : ∀ x ∈ cell n k, x ≤ 0 := fun x hx => by
        by_contra hlt
        push Not at hlt
        exact hk ((idx_nonneg_iff n x).mpr hlt.le |>.trans_eq hx)
      have hint_np : ∫ x in cell n k, x ∂γ ≤ 0 :=
        setIntegral_nonpos (measurableSet_cell n k) hneg
      rw [abs_of_nonpos hint_np, ← integral_neg]
      exact setIntegral_congr_fun (measurableSet_cell n k) fun x hx =>
        (abs_of_nonpos (hneg x hx)).symm
  · intro k _
    exact (integrable_dirac (by simp)).smul_measure (measure_ne_top γ _)

private lemma convexLE_approxMeas_self (γ : Measure ℝ) (hγ : InM γ) (n : ℕ) :
    ConvexLE (approxMeas γ n) γ := by
  have : IsFiniteMeasure γ := hγ.1
  have hγ_sum : γ = ∑ k ∈ cellIdxSet n, γ.restrict (cell n k) := by
    rw [sum_restrict_eq_restrict_biUnion γ (cellIdxSet n) (cell n)
      (fun k₁ _ k₂ _ hne => cell_pairwiseDisjoint n trivial trivial hne)
      (fun k _ => measurableSet_cell n k), biUnion_cell_eq_univ, Measure.restrict_univ]
  rw [approxMeas_eq_sum γ n]
  conv_rhs => rw [hγ_sum]
  refine convexLE_finset_sum (cellIdxSet n) _ _ fun k _ => ?_
  have hμk : InM (γ.restrict (cell n k)) := ⟨inferInstance, hγ.2.integrableOn⟩
  have hmass : (γ.restrict (cell n k)) Set.univ = γ (cell n k) := by
    rw [Measure.restrict_apply_univ]
  rw [← hmass]
  refine convexLE_smul_dirac_of_barycenter hμk (bary γ n k) ?_
  rw [hmass]
  exact cell_mul_bary γ hγ n k

private lemma convexLE_approxMeas_succ (γ : Measure ℝ) (hγ : InM γ) (n : ℕ) :
    ConvexLE (approxMeas γ n) (approxMeas γ (n + 1)) := by
  have : IsFiniteMeasure γ := hγ.1
  rw [approxMeas_eq_sum γ n, approxMeas_eq_sum γ (n + 1)]
  have hgroup :
      ∑ j ∈ cellIdxSet (n + 1), γ (cell (n + 1) j) • Measure.dirac (bary γ (n + 1) j) =
        ∑ k ∈ cellIdxSet n,
          ∑ j ∈ (cellIdxSet (n + 1)).filter (fun j => proj n j = k),
            γ (cell (n + 1) j) • Measure.dirac (bary γ (n + 1) j) :=
    (Finset.sum_fiberwise_of_maps_to (fun j _ => proj_mem n j) _).symm
  rw [hgroup]
  refine convexLE_finset_sum (cellIdxSet n) _ _ fun k _ => ?_
  set J := (cellIdxSet (n + 1)).filter (fun j => proj n j = k)
  set νk : Measure ℝ := ∑ j ∈ J, γ (cell (n + 1) j) • Measure.dirac (bary γ (n + 1) j)
  have hνk_inM : InM νk := by
    have hfin : IsFiniteMeasure νk := by
      refine ⟨?_⟩
      rw [Measure.finsetSum_apply]
      exact ENNReal.sum_lt_top.mpr fun j _ => by
        simp [measure_lt_top γ _]
    have hint : Integrable (fun x : ℝ => x) νk :=
      integrable_finsetSum_measure.mpr fun j _ =>
        (integrable_dirac (by simp)).smul_measure (measure_ne_top γ _)
    exact ⟨hfin, hint⟩
  have hmass : νk Set.univ = γ (cell n k) := by
    rw [Measure.finsetSum_apply, cell_eq_biUnion_filter n k, measure_biUnion_finset]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp
    · intro j₁ _ j₂ _ hne
      exact cell_pairwiseDisjoint (n + 1) trivial trivial hne
    · intro j _
      exact measurableSet_cell (n + 1) j
  rw [← hmass]
  refine convexLE_smul_dirac_of_barycenter hνk_inM (bary γ n k) ?_
  rw [hmass, cell_mul_bary γ hγ n k, cell_eq_biUnion_filter n k,
    integral_biUnion_finset J (fun j _ => measurableSet_cell (n + 1) j)
      (fun j₁ _ j₂ _ hne => cell_pairwiseDisjoint (n + 1) trivial trivial hne)
      (fun j _ => hγ.2.integrableOn),
    integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_measure, integral_dirac, smul_eq_mul, cell_mul_bary γ hγ (n + 1) j]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure (measure_ne_top γ _)

theorem solution (γ : Measure ℝ) (hγ : MartOT.Var.InM γ) :
    ∃ γs : ℕ → Measure ℝ, (∀ n, ∃ S : Finset ℝ, γs n (↑S : Set ℝ)ᶜ = 0) ∧
      (∀ n, MartOT.Var.ConvexLE (γs n) (γs (n + 1))) ∧ ConvergesInM γs γ ∧
      ∀ n, MartOT.Var.ConvexLE (γs n) γ := by
  have : IsFiniteMeasure γ := hγ.1
  refine ⟨approxMeas γ, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(cellIdxSet n).image (bary γ n), ?_⟩
    rw [approxMeas_eq_sum γ n, Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (Finset.finite_toSet _).measurableSet.compl]
    have hmem : bary γ n k ∉ ((↑((cellIdxSet n).image (bary γ n)) : Set ℝ)ᶜ) := by
      simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_image, not_not]
      exact ⟨k, hk, rfl⟩
    rw [Set.indicator_of_notMem hmem, mul_zero]
  · exact convexLE_approxMeas_succ γ hγ
  · refine ⟨fun n => (convexLE_approxMeas_self γ hγ n).1, hγ, ?_, ?_⟩
    · intro f
      have hrew : (fun n => ∫ x, f x ∂(approxMeas γ n)) = fun n => ∫ x, f (approxMap γ n x) ∂γ := by
        ext n
        exact integral_map (measurable_approxMap γ n).aemeasurable f.continuous.aestronglyMeasurable
      rw [hrew]
      exact tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (measurable_approxMap γ n)).aestronglyMeasurable)
        (integrable_const ‖f‖)
        (fun n => Eventually.of_forall fun x => f.norm_coe_le_norm (approxMap γ n x))
        (Eventually.of_forall fun x => (f.continuous.tendsto x).comp (tendsto_approxMap γ hγ x))
    · simp_rw [integral_abs_approxMeas γ hγ]
      exact tendsto_const_nhds
  · exact convexLE_approxMeas_self γ hγ
