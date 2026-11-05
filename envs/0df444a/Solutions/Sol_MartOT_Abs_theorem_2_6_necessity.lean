-- Prove2me | solution 1 for MartOT.Abs.theorem_2_6_necessity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:05:12.734585+00:00
-- url     : https://prove2.me/submissions/fef860fc-fa70-4ba0-905e-ba5ec04cd34a

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory Set

lemma n26_toENNReal (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma n26_ofReal_max (a : ℝ) : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-- Tangent-line inequality for a convex function on `ℝ`, with the right derivative. -/
lemma n26_tangent {ϕ : ℝ → ℝ} (hϕ : ConvexOn ℝ univ ϕ) (x y : ℝ) :
    ϕ x + derivWithin ϕ (Ioi x) x * (y - x) ≤ ϕ y := by
  have hint : ∀ z : ℝ, z ∈ interior (univ : Set ℝ) := fun z => by simp
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hϕ.rightDeriv_le_slope_of_mem_interior (hint x) (mem_univ y) hxy
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
    linarith
  · simp
  · have h1 := hϕ.slope_le_leftDeriv_of_mem_interior (mem_univ y) (hint x) hxy
    have h2 := hϕ.leftDeriv_le_rightDeriv_of_mem_interior (hint x)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at h1
    nlinarith [mul_le_mul_of_nonneg_right h2 (sub_pos.mpr hxy).le]

lemma n26_rightDeriv_measurable {ϕ : ℝ → ℝ} (hϕ : ConvexOn ℝ univ ϕ) :
    Measurable (fun x => derivWithin ϕ (Ioi x) x) := by
  have h := hϕ.monotoneOn_rightDeriv
  rw [interior_univ] at h
  exact (monotoneOn_univ.mp h).measurable

/-- Decomposition of the `EReal` integral of `ψ + ℓ`, with `ψ ≥ 0` and `ℓ` integrable. -/
lemma n26_integralE_split {η : Measure ℝ} {ψ ℓ : ℝ → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hℓ : Integrable ℓ η) (hℓm : Measurable ℓ) :
    MartOT.Var.integralE η (fun x => ψ x + ℓ x) =
      ((∫⁻ x, ENNReal.ofReal (ψ x) ∂η : ENNReal) : EReal) + ((∫ x, ℓ x ∂η : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h2 : ∀ x, (-(((ψ x + ℓ x : ℝ)) : EReal)).toENNReal = ENNReal.ofReal (-(ψ x + ℓ x)) :=
    fun x => by rw [← EReal.coe_neg, n26_toENNReal]
  simp only [n26_toENNReal, h2]
  set P := ∫⁻ x, ENNReal.ofReal (ψ x + ℓ x) ∂η
  set N := ∫⁻ x, ENNReal.ofReal (-(ψ x + ℓ x)) ∂η
  set H := ∫⁻ x, ENNReal.ofReal (ψ x) ∂η
  set Gp := ∫⁻ x, ENNReal.ofReal (ℓ x) ∂η
  set Gn := ∫⁻ x, ENNReal.ofReal (-ℓ x) ∂η
  have hGp : Gp ≠ ⊤ := (lintegral_ofReal_le_lintegral_enorm ℓ).trans_lt hℓ.2 |>.ne
  have hGn : Gn ≠ ⊤ := (lintegral_ofReal_le_lintegral_enorm (fun x => -ℓ x)).trans_lt hℓ.neg.2 |>.ne
  have hN : N ≤ Gn := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (by linarith [hψ0 x]))
  have hNt : N ≠ ⊤ := ne_top_of_le_ne_top hGn hN
  -- pointwise identity
  have hpt : ∀ x, ENNReal.ofReal (ψ x + ℓ x) + ENNReal.ofReal (-ℓ x) =
      ENNReal.ofReal (-(ψ x + ℓ x)) + ENNReal.ofReal (ψ x) + ENNReal.ofReal (ℓ x) := by
    intro x
    rw [← n26_ofReal_max (ψ x + ℓ x), ← n26_ofReal_max (-ℓ x), ← n26_ofReal_max (-(ψ x + ℓ x)),
      ← n26_ofReal_max (ℓ x), ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      ← ENNReal.ofReal_add (le_max_right _ _) (hψ0 x),
      ← ENNReal.ofReal_add (add_nonneg (le_max_right _ _) (hψ0 x)) (le_max_right _ _)]
    congr 1
    have := hψ0 x
    rcases le_total (ψ x + ℓ x) 0 with h1 | h1 <;> rcases le_total (ℓ x) 0 with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2, neg_nonneg, neg_nonpos] <;> linarith
  have hint : P + Gn = N + H + Gp := by
    have hm1 : Measurable fun x => ENNReal.ofReal (ψ x + ℓ x) :=
      ENNReal.measurable_ofReal.comp (hψm.add hℓm)
    have hm2 : Measurable fun x => ENNReal.ofReal (-(ψ x + ℓ x)) :=
      ENNReal.measurable_ofReal.comp (hψm.add hℓm).neg
    have hm3 : Measurable fun x => ENNReal.ofReal (ψ x) := ENNReal.measurable_ofReal.comp hψm
    have hm23 : Measurable fun x => ENNReal.ofReal (-(ψ x + ℓ x)) + ENNReal.ofReal (ψ x) :=
      hm2.add hm3
    rw [← lintegral_add_left hm1, ← lintegral_add_left hm2, ← lintegral_add_left hm23]
    exact lintegral_congr hpt
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hℓ]
  by_cases hH : H = ⊤
  · have hP : P = ⊤ := by
      by_contra hP
      have : N + H + Gp ≠ ⊤ := hint ▸ ENNReal.add_ne_top.mpr ⟨hP, hGn⟩
      simp [hH] at this
    rw [hP, hH, EReal.coe_ennreal_top, EReal.top_add_coe]
    rw [← EReal.coe_ennreal_toReal hNt]
    exact EReal.top_sub_coe _
  · have hPt : P ≠ ⊤ := by
      intro hP
      have : N + H + Gp = ⊤ := by rw [← hint, hP, top_add]
      exact (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hNt, hH⟩, hGp⟩) this
    have hreal : P.toReal + Gn.toReal = N.toReal + H.toReal + Gp.toReal := by
      rw [← ENNReal.toReal_add hPt hGn, hint, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hNt, hH⟩) hGp,
        ENNReal.toReal_add hNt hH]
    rw [← EReal.coe_ennreal_toReal hPt, ← EReal.coe_ennreal_toReal hNt,
      ← EReal.coe_ennreal_toReal hH, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    linarith

theorem solution (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsMartingalePlan μ ν π) :
    MartOT.Var.ConvexLE μ ν := by
  refine ⟨hμ, hν, fun ϕ hϕ => ?_⟩
  obtain ⟨hμf, hμi⟩ := hμ
  obtain ⟨hνf, hνi⟩ := hν
  obtain ⟨⟨h1, h2⟩, hπi, hmart⟩ := hπ
  have hπf : IsFiniteMeasure π := by
    constructor
    have : π.map Prod.fst univ = π univ := Measure.map_apply measurable_fst MeasurableSet.univ
    rw [← this, h1]; exact measure_lt_top _ _
  set D : ℝ → ℝ := fun x => derivWithin ϕ (Ioi x) x with hD
  have hDm : Measurable D := n26_rightDeriv_measurable hϕ
  have htan : ∀ x y, ϕ x + D x * (y - x) ≤ ϕ y := n26_tangent hϕ
  have hϕc : Continuous ϕ := continuousOn_univ.mp (hϕ.continuousOn isOpen_univ)
  set ℓ : ℝ → ℝ := fun x => ϕ 0 + D 0 * x with hℓ
  set ψ : ℝ → ℝ := fun x => ϕ x - ℓ x with hψ
  have hψc : Continuous ψ := hϕc.sub (continuous_const.add (continuous_const.mul continuous_id))
  have hψm : Measurable ψ := hψc.measurable
  have hℓm : Measurable ℓ := (measurable_const.add (measurable_const.mul measurable_id))
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => by
    have := htan 0 x; simp only [hψ, hℓ]; linarith
  have hϕeq : ϕ = fun x => ψ x + ℓ x := by funext x; simp [hψ]
  have hℓi : ∀ η : Measure ℝ, IsFiniteMeasure η → Integrable (fun x : ℝ => x) η →
      Integrable ℓ η := fun η _ hη => (integrable_const _).add (hη.const_mul _)
  -- transfer of integrals to π
  have tμ : ∀ g : ℝ → ℝ, Measurable g → ∫ x, g x ∂μ = ∫ p, g p.1 ∂π := by
    intro g hg; rw [← h1, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
  have tν : ∀ g : ℝ → ℝ, Measurable g → ∫ x, g x ∂ν = ∫ p, g p.2 ∂π := by
    intro g hg; rw [← h2, integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable]
  have iμ : ∀ g : ℝ → ℝ, Measurable g → Integrable g μ → Integrable (fun p : ℝ × ℝ => g p.1) π := by
    intro g hg hgi; rw [← h1] at hgi
    exact (integrable_map_measure hg.aestronglyMeasurable measurable_fst.aemeasurable).mp hgi
  have iν : ∀ g : ℝ → ℝ, Measurable g → Integrable g ν → Integrable (fun p : ℝ × ℝ => g p.2) π := by
    intro g hg hgi; rw [← h2] at hgi
    exact (integrable_map_measure hg.aestronglyMeasurable measurable_snd.aemeasurable).mp hgi
  -- the affine part has the same integral
  have hL : ∫ x, ℓ x ∂μ = ∫ x, ℓ x ∂ν := by
    rw [tμ ℓ hℓm, tν ℓ hℓm]
    have hm := hmart (fun _ => D 0) measurable_const ⟨|D 0|, fun _ => le_rfl⟩
    have hi1 := iμ ℓ hℓm (hℓi μ hμf hμi)
    have hi2 := iν ℓ hℓm (hℓi ν hνf hνi)
    have : ∫ p, ℓ p.2 ∂π - ∫ p, ℓ p.1 ∂π = ∫ p, D 0 * (p.2 - p.1) ∂π := by
      rw [← integral_sub hi2 hi1]
      congr 1; funext p; simp only [hℓ]; ring
    linarith
  -- the key inequality for the nonnegative part
  have hkey : ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν := by
    by_cases htop : ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν = ⊤
    · rw [htop]; exact le_top
    have hψν : Integrable ψ ν := by
      refine ⟨hψm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hψ0)]
      exact lt_top_iff_ne_top.mpr htop
    set B : ℕ → Set ℝ := fun n => {x | |D x - D 0| ≤ n ∧ |x| ≤ n} with hB
    have hBm : ∀ n, MeasurableSet (B n) := fun n =>
      (measurableSet_le ((hDm.sub measurable_const).abs) measurable_const).inter
        (measurableSet_le measurable_id.abs measurable_const)
    have hstep : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal ((B n).indicator ψ x) ∂μ ≤
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν := by
      intro n
      -- `ψ` is bounded on `B n`
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := -(n : ℝ)) (b := n)).exists_bound_of_continuousOn
        hψc.continuousOn
      have hbd : ∀ x, ‖(B n).indicator ψ x‖ ≤ M := by
        intro x
        by_cases hx : x ∈ B n
        · rw [indicator_of_mem hx]
          exact hM x (abs_le.mp hx.2)
        · rw [indicator_of_notMem hx, norm_zero]
          exact (norm_nonneg _).trans (hM 0 ⟨by simp, by simp⟩)
      have hIm : Measurable ((B n).indicator ψ) := hψm.indicator (hBm n)
      have hIi : Integrable ((B n).indicator ψ) μ :=
        Integrable.of_bound hIm.aestronglyMeasurable M (Filter.Eventually.of_forall hbd)
      set r : ℝ → ℝ := (B n).indicator (fun x => D x - D 0) with hr
      have hrm : Measurable r := (hDm.sub measurable_const).indicator (hBm n)
      have hrb : ∀ x, |r x| ≤ n := by
        intro x
        by_cases hx : x ∈ B n
        · rw [hr, indicator_of_mem hx]; exact hx.1
        · rw [hr, indicator_of_notMem hx, abs_zero]; exact Nat.cast_nonneg n
      have hpt : ∀ p : ℝ × ℝ, (B n).indicator ψ p.1 + r p.1 * (p.2 - p.1) ≤ ψ p.2 := by
        intro p
        by_cases hx : p.1 ∈ B n
        · rw [indicator_of_mem hx, hr, indicator_of_mem hx]
          have := htan p.1 p.2
          simp only [hψ, hℓ]
          nlinarith
        · rw [indicator_of_notMem hx, hr, indicator_of_notMem hx]
          simpa using hψ0 p.2
      have hri : Integrable (fun p : ℝ × ℝ => r p.1 * (p.2 - p.1)) π := by
        refine hπi.bdd_mul (c := n) (hrm.comp measurable_fst).aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall (fun p => by simpa [Real.norm_eq_abs] using hrb p.1)
      have hIπ := iμ _ hIm hIi
      have hψπ := iν ψ hψm hψν
      have hle : ∫ p, ((B n).indicator ψ p.1 + r p.1 * (p.2 - p.1)) ∂π ≤ ∫ p, ψ p.2 ∂π :=
        integral_mono (hIπ.add hri) hψπ hpt
      rw [integral_add hIπ hri, hmart r hrm ⟨n, hrb⟩, add_zero, ← tμ _ hIm, ← tν ψ hψm] at hle
      have hI0 : ∀ x, 0 ≤ (B n).indicator ψ x := fun x =>
        indicator_nonneg (fun y _ => hψ0 y) x
      rw [← ofReal_integral_eq_lintegral_ofReal hIi (Filter.Eventually.of_forall hI0),
        ← ofReal_integral_eq_lintegral_ofReal hψν (Filter.Eventually.of_forall hψ0)]
      exact ENNReal.ofReal_le_ofReal hle
    -- monotone convergence
    have hmono : Monotone (fun n : ℕ => fun x => ENNReal.ofReal ((B n).indicator ψ x)) := by
      intro m k hmk x
      apply ENNReal.ofReal_le_ofReal
      apply indicator_le_indicator_of_subset _ (fun y => hψ0 y)
      intro y hy
      exact ⟨hy.1.trans (by exact_mod_cast hmk), hy.2.trans (by exact_mod_cast hmk)⟩
    have hsup : ∀ x, ⨆ n : ℕ, ENNReal.ofReal ((B n).indicator ψ x) = ENNReal.ofReal (ψ x) := by
      intro x
      apply le_antisymm
      · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal
          (indicator_le_self' (fun y _ => hψ0 y) x))
      · obtain ⟨N, hN⟩ := exists_nat_ge (max |D x - D 0| |x|)
        have hx : x ∈ B N := ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
        refine le_trans (le_of_eq ?_) (le_iSup _ N)
        rw [indicator_of_mem hx]
    calc ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ
        = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal ((B n).indicator ψ x) ∂μ := by simp_rw [hsup]
      _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal ((B n).indicator ψ x) ∂μ :=
          lintegral_iSup (fun n => ENNReal.measurable_ofReal.comp (hψm.indicator (hBm n))) hmono
      _ ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν := iSup_le hstep
  rw [hϕeq, n26_integralE_split hψm hψ0 (hℓi μ hμf hμi) hℓm,
    n26_integralE_split hψm hψ0 (hℓi ν hνf hνi) hℓm, hL]
  exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hkey) _
