-- Prove2me | solution 1 for LocalRademacher.StarHull.theorem_3_3_part_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T03:15:15.667977+00:00
-- url     : https://prove2.me/submissions/bf6a7d56-61c3-4f91-985f-dd045bf44a5c

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory ProbabilityTheory Filter Topology

namespace Bq857

/-- `ψ(u) = 1 + (u - 1) e^u = e^u φ(-u)`. -/
noncomputable def psiB (u : ℝ) : ℝ := 1 + (u - 1) * Real.exp u

lemma psiB_nonneg (u : ℝ) : 0 ≤ psiB u := by
  unfold psiB
  have h1 := Real.add_one_le_exp (-u)
  have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos u
  nlinarith

lemma psiB_le_sq_of_nonpos (u : ℝ) (hu : u ≤ 0) : psiB u ≤ u ^ 2 / 2 := by
  -- h(u) = u^2/2 - psiB u is antitone on (-∞, 0] with h 0 = 0
  have key : ∀ x ∈ Set.Iic (0:ℝ), ∀ y ∈ Set.Iic (0:ℝ), x ≤ y →
      y ^ 2 / 2 - psiB y ≤ x ^ 2 / 2 - psiB x := by
    have hd : ∀ x, HasDerivAt (fun x : ℝ => x ^ 2 / 2 - psiB x) (x - x * Real.exp x) x := by
      intro x
      unfold psiB
      have h1 := ((((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)).const_add 1)
      have h2 := ((hasDerivAt_pow 2 x).div_const 2).sub h1
      exact h2.congr_deriv (by norm_num <;> ring)
    have hanti : AntitoneOn (fun x : ℝ => x ^ 2 / 2 - psiB x) (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
      · exact (fun x _ => (hd x).continuousAt.continuousWithinAt)
      · intro x _; exact (hd x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Iic] at hx
        rw [(hd x).deriv]
        have hx' : x < 0 := hx
        have : Real.exp x < 1 := by
          have h := Real.exp_lt_exp.mpr hx'
          rwa [Real.exp_zero] at h
        nlinarith
    intro x hx y hy hxy
    exact hanti hx hy hxy
  have := key u hu 0 (Set.mem_Iic.mpr le_rfl) hu
  simp [psiB] at this
  simp [psiB]
  linarith

/-- The `y ≥ 0` case, in the variable `u = l y ∈ [0, l]`. -/
lemma p1_nonneg (l u : ℝ) (hu : 0 ≤ u) (hul : u ≤ l) :
    (4 + 4 * l - l ^ 2) * psiB u ≤ 2 * u ^ 2 + 4 * l * (u * (Real.exp u - 1)) := by
  have hE := Real.quadratic_le_exp_of_nonneg hu
  have hψ := psiB_nonneg u
  have hφ : 0 ≤ Real.exp u - u - 1 := by linarith [Real.add_one_le_exp u]
  unfold psiB at hψ ⊢
  set E := Real.exp u with hEdef
  -- g(u) = E (u^3 - u^2 + 4) - (u+2)^2 ≥ 0
  have hc : 0 ≤ u ^ 3 - u ^ 2 + 4 := by nlinarith [sq_nonneg (u - 1), sq_nonneg u]
  have hg : 0 ≤ E * (u ^ 3 - u ^ 2 + 4) - (u + 2) ^ 2 := by
    have : (1 + u + u ^ 2 / 2) * (u ^ 3 - u ^ 2 + 4) ≤ E * (u ^ 3 - u ^ 2 + 4) :=
      mul_le_mul_of_nonneg_right hE hc
    nlinarith [pow_nonneg hu 4, pow_nonneg hu 5]
  -- RHS - LHS = 2u^2 - 4ψ + 4 l φ + l^2 ψ ≥ g(u)
  have h1 : 4 * u * (E - u - 1) ≤ 4 * l * (E - u - 1) := by nlinarith
  have h2 : u ^ 2 * (1 + (u - 1) * E) ≤ l ^ 2 * (1 + (u - 1) * E) := by
    have : u ^ 2 ≤ l ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hψ
  nlinarith

/-- The `y < 0` case. -/
lemma p1_neg (l y : ℝ) (hl : 0 ≤ l) (hl2 : l ≤ 2) (hy1 : -1 ≤ y) (hy0 : y ≤ 0) :
    (4 + 4 * l - l ^ 2) * psiB (l * y) ≤ 2 * l ^ 2 * (y ^ 2 + 2 * y * (Real.exp (l * y) - 1)) := by
  have hD : 0 ≤ 4 + 4 * l - l ^ 2 := by nlinarith
  have hψ := psiB_le_sq_of_nonpos (l * y) (by nlinarith)
  -- convexity: e^{l y} ≤ (-y) e^{-l} + (1 + y)
  have hconv : Real.exp (l * y) ≤ (-y) * Real.exp (-l) + (1 + y) * 1 := by
    have h := convexOn_exp.2 (Set.mem_univ (-l)) (Set.mem_univ 0) (by linarith : (0:ℝ) ≤ -y)
      (by linarith : (0:ℝ) ≤ 1 + y) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero] at h
    have : -y * -l = l * y := by ring
    rw [this] at h
    linarith
  have hmul : y ^ 2 * (1 - Real.exp (-l)) ≤ y * (Real.exp (l * y) - 1) := by nlinarith
  -- 8 e^{-l} ≤ 8 - 4 l + l^2
  have hel : 8 * Real.exp (-l) ≤ 8 - 4 * l + l ^ 2 := by
    have hq := Real.quadratic_le_exp_of_nonneg hl
    have hpos : 0 < 8 - 4 * l + l ^ 2 := by nlinarith [sq_nonneg (l - 2)]
    have hprod : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
    have : 8 ≤ Real.exp l * (8 - 4 * l + l ^ 2) := by
      have : (1 + l + l ^ 2 / 2) * (8 - 4 * l + l ^ 2) ≤ Real.exp l * (8 - 4 * l + l ^ 2) :=
        mul_le_mul_of_nonneg_right hq hpos.le
      nlinarith [pow_nonneg hl 3, pow_nonneg hl 4, mul_nonneg hl (sq_nonneg (l - 1))]
    have he := Real.exp_pos (-l)
    nlinarith
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  calc (4 + 4 * l - l ^ 2) * psiB (l * y) ≤ (4 + 4 * l - l ^ 2) * ((l * y) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hψ hD
    _ ≤ 2 * l ^ 2 * (y ^ 2 + 2 * (y ^ 2 * (1 - Real.exp (-l)))) := by
        have hl2' : 0 ≤ l ^ 2 * y ^ 2 := by positivity
        nlinarith
    _ ≤ 2 * l ^ 2 * (y ^ 2 + 2 * y * (Real.exp (l * y) - 1)) := by
        have : 0 ≤ 2 * l ^ 2 := by positivity
        have h3 : y ^ 2 + 2 * (y ^ 2 * (1 - Real.exp (-l))) ≤ y ^ 2 + 2 * y * (Real.exp (l * y) - 1) := by
          nlinarith
        exact mul_le_mul_of_nonneg_left h3 this

/-- **P1** (pointwise inequality for the Bousquet-type entropy bound). -/
theorem p1 (l y y' : ℝ) (hl : 0 ≤ l) (hl2 : l ≤ 2) (hy'1 : -1 ≤ y') (hyy : y' ≤ y) (hy1 : y ≤ 1) :
    (4 + 4 * l - l ^ 2) * psiB (l * y) ≤
      2 * l ^ 2 * (2 * y * Real.exp (l * y) + y' ^ 2 - 2 * y') := by
  have base : (4 + 4 * l - l ^ 2) * psiB (l * y) ≤
      2 * l ^ 2 * (y ^ 2 + 2 * y * (Real.exp (l * y) - 1)) := by
    rcases le_or_gt y 0 with hy0 | hy0
    · exact p1_neg l y hl hl2 (by linarith) hy0
    · have h := p1_nonneg l (l * y) (by positivity) (by nlinarith)
      have : 2 * (l * y) ^ 2 + 4 * l * (l * y * (Real.exp (l * y) - 1)) =
          2 * l ^ 2 * (y ^ 2 + 2 * y * (Real.exp (l * y) - 1)) := by ring
      linarith
  have hq : y ^ 2 - 2 * y ≤ y' ^ 2 - 2 * y' := by nlinarith
  have : 0 ≤ 2 * l ^ 2 := by positivity
  calc _ ≤ 2 * l ^ 2 * (y ^ 2 + 2 * y * (Real.exp (l * y) - 1)) := base
    _ ≤ 2 * l ^ 2 * (2 * y * Real.exp (l * y) + y' ^ 2 - 2 * y') := by
        apply mul_le_mul_of_nonneg_left _ this; nlinarith


/-- Entropy `Ent_μ(g) = E[g log g] - E[g] log E[g]`. -/
noncomputable def ent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ) : ℝ :=
  ∫ ω, g ω * Real.log (g ω) ∂μ - (∫ ω, g ω ∂μ) * Real.log (∫ ω, g ω ∂μ)

section General

variable {Ω : Type*} [MeasurableSpace Ω]

lemma intOfBdd {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

lemma abs_le_of_mem {m M x : ℝ} (h1 : m ≤ x) (h2 : x ≤ M) : |x| ≤ |m| + |M| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have := neg_abs_le m; have := abs_nonneg M; linarith
  · have := le_abs_self M; have := abs_nonneg m; linarith

lemma abs_log_le {m M x : ℝ} (hm : 0 < m) (h1 : m ≤ x) (h2 : x ≤ M) :
    |Real.log x| ≤ |Real.log m| + |Real.log M| := by
  have hx : 0 < x := lt_of_lt_of_le hm h1
  exact abs_le_of_mem (Real.log_le_log hm h1) (Real.log_le_log hx h2)

lemma glog_bdd {m M x : ℝ} (hm : 0 < m) (h1 : m ≤ x) (h2 : x ≤ M) :
    |x * Real.log x| ≤ M * (|Real.log m| + |Real.log M|) := by
  have hx : 0 < x := lt_of_lt_of_le hm h1
  rw [abs_mul, abs_of_pos hx]
  exact mul_le_mul h2 (abs_log_le hm h1 h2) (abs_nonneg _) (by linarith)

lemma integral_mem_of {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {m M : ℝ} (hm : ∀ ω, m ≤ f ω) (hM : ∀ ω, f ω ≤ M) :
    m ≤ ∫ ω, f ω ∂μ ∧ ∫ ω, f ω ∂μ ≤ M := by
  have hI : Integrable f μ := intOfBdd hf (|m| + |M|) (fun ω => abs_le_of_mem (hm ω) (hM ω))
  constructor
  · have := integral_mono (integrable_const m) hI hm
    simpa using this
  · have := integral_mono hI (integrable_const M) hM
    simpa using this

lemma abs_integral_le_of {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) : |∫ ω, f ω ∂μ| ≤ C := by
  have h := integral_mem_of (μ := μ) hf (m := -C) (M := C) (fun ω => (abs_le.mp (hC ω)).1)
    (fun ω => (abs_le.mp (hC ω)).2)
  exact abs_le.mpr h

lemma young_pt {g h m0 : ℝ} (hg : 0 < g) (hm0 : 0 < m0) :
    g * h ≤ g * Real.log g - g * Real.log m0 - g + m0 * Real.exp h := by
  have h1 := Real.add_one_le_exp (h - Real.log g + Real.log m0)
  have h2 : Real.exp (h - Real.log g + Real.log m0) = Real.exp h * m0 / g := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log hg, Real.exp_log hm0]; ring
  rw [h2, le_div_iff₀ hg] at h1
  linear_combination h1

lemma ent_abs_le (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : Measurable g)
    {m M : ℝ} (hm : 0 < m) (hgm : ∀ ω, m ≤ g ω) (hgM : ∀ ω, g ω ≤ M) :
    |ent μ g| ≤ 2 * (M * (|Real.log m| + |Real.log M|)) := by
  have h1 := abs_integral_le_of (μ := μ) (f := fun ω => g ω * Real.log (g ω)) (hg.mul hg.log)
    (fun ω => glog_bdd hm (hgm ω) (hgM ω))
  obtain ⟨a, b⟩ := integral_mem_of (μ := μ) hg hgm hgM
  have h2 := glog_bdd hm a b
  unfold ent
  calc _ ≤ |∫ ω, g ω * Real.log (g ω) ∂μ| + |(∫ ω, g ω ∂μ) * Real.log (∫ ω, g ω ∂μ)| :=
        abs_sub _ _
    _ ≤ _ := by linarith

/-- Gibbs / duality inequality: `E[g h] ≤ Ent(g)` when `E[e^h] = 1`. -/
lemma gibbs (μ : Measure Ω) [IsProbabilityMeasure μ] {g h : Ω → ℝ} (hg : Measurable g)
    (hh : Measurable h) {m M K : ℝ} (hm : 0 < m) (hgm : ∀ ω, m ≤ g ω) (hgM : ∀ ω, g ω ≤ M)
    (hK : ∀ ω, |h ω| ≤ K) (hexp : ∫ ω, Real.exp (h ω) ∂μ = 1) :
    ∫ ω, g ω * h ω ∂μ ≤ ent μ g := by
  obtain ⟨hm0, -⟩ := integral_mem_of (μ := μ) hg hgm hgM
  set m0 := ∫ ω, g ω ∂μ with hm0def
  have hm0p : 0 < m0 := lt_of_lt_of_le hm hm0
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le hm (hgm ω)
  have gI : Integrable g μ := intOfBdd hg (|m| + |M|) (fun ω => abs_le_of_mem (hgm ω) (hgM ω))
  have glI : Integrable (fun ω => g ω * Real.log (g ω)) μ :=
    intOfBdd (hg.mul hg.log) _ (fun ω => glog_bdd hm (hgm ω) (hgM ω))
  have ghI : Integrable (fun ω => g ω * h ω) μ := intOfBdd (hg.mul hh) ((|m| + |M|) * K)
    (fun ω => by
      rw [abs_mul]
      exact mul_le_mul (abs_le_of_mem (hgm ω) (hgM ω)) (hK ω) (abs_nonneg _) (by positivity))
  have eI : Integrable (fun ω => Real.exp (h ω)) μ := intOfBdd hh.exp (Real.exp K) (fun ω => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hK ω)))
  have rI1 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log m0) μ :=
    glI.sub (gI.mul_const _)
  have rI2 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log m0 - g ω) μ := rI1.sub gI
  have rI : Integrable
      (fun ω => g ω * Real.log (g ω) - g ω * Real.log m0 - g ω + m0 * Real.exp (h ω)) μ :=
    rI2.add (eI.const_mul m0)
  have key := integral_mono ghI rI (fun ω => young_pt (h := h ω) (hgpos ω) hm0p)
  rw [integral_add rI2 (eI.const_mul m0), integral_sub rI1 gI, integral_sub glI (gI.mul_const _),
    integral_mul_const, integral_const_mul, hexp] at key
  unfold ent
  linarith

/-- Variational upper bound: `Ent(g) ≤ E[g log g - g log c - g + c]` for a constant `c > 0`. -/
lemma ent_le_var (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : Measurable g)
    {m M : ℝ} (hm : 0 < m) (hgm : ∀ ω, m ≤ g ω) (hgM : ∀ ω, g ω ≤ M) {c : ℝ} (hc : 0 < c) :
    ent μ g ≤ ∫ ω, (g ω * Real.log (g ω) - g ω * Real.log c - g ω + c) ∂μ := by
  obtain ⟨hm0, -⟩ := integral_mem_of (μ := μ) hg hgm hgM
  set m0 := ∫ ω, g ω ∂μ with hm0def
  have hm0p : 0 < m0 := lt_of_lt_of_le hm hm0
  have gI : Integrable g μ := intOfBdd hg (|m| + |M|) (fun ω => abs_le_of_mem (hgm ω) (hgM ω))
  have glI : Integrable (fun ω => g ω * Real.log (g ω)) μ :=
    intOfBdd (hg.mul hg.log) _ (fun ω => glog_bdd hm (hgm ω) (hgM ω))
  have rI1 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log c) μ :=
    glI.sub (gI.mul_const _)
  have rI2 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log c - g ω) μ := rI1.sub gI
  rw [integral_add rI2 (integrable_const c), integral_sub rI1 gI,
    integral_sub glI (gI.mul_const _), integral_mul_const]
  have hcI : ∫ _ω, c ∂μ = c := by simp
  rw [hcI]
  unfold ent
  have hl := Real.log_le_sub_one_of_pos (div_pos hc hm0p)
  rw [Real.log_div hc.ne' hm0p.ne'] at hl
  have hl2 : m0 * (Real.log c - Real.log m0) ≤ m0 * (c / m0 - 1) :=
    mul_le_mul_of_nonneg_left hl hm0p.le
  have e : m0 * (c / m0 - 1) = c - m0 := by field_simp
  rw [e] at hl2
  nlinarith

end General

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma ent_meas_right (ν : Measure β) [IsProbabilityMeasure ν] {F : α × β → ℝ}
    (hF : Measurable F) : Measurable (fun a => ent ν (fun b => F (a, b))) := by
  unfold ent
  have h1 : Measurable (fun a => ∫ b, F (a, b) * Real.log (F (a, b)) ∂ν) :=
    ((hF.mul hF.log).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have h2 : Measurable (fun a => ∫ b, F (a, b) ∂ν) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  exact h1.sub (h2.mul h2.log)

/-- Two-factor tensorization of entropy. -/
theorem ent_prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : α × β → ℝ} (hg : Measurable g)
    {m M : ℝ} (hm : 0 < m) (hgm : ∀ p, m ≤ g p) (hgM : ∀ p, g p ≤ M) :
    ent (μ.prod ν) g ≤ ∫ b, ent μ (fun a => g (a, b)) ∂ν + ∫ a, ent ν (fun b => g (a, b)) ∂μ := by
  set L := |Real.log m| + |Real.log M| with hL
  have hgl : Measurable (fun p => g p * Real.log (g p)) := hg.mul hg.log
  set G : β → ℝ := fun b => ∫ a, g (a, b) ∂μ with hGdef
  have hGmeas : Measurable G := (hg.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable
  have hGb : ∀ b, m ≤ G b ∧ G b ≤ M := fun b =>
    integral_mem_of (μ := μ) (hg.comp (measurable_id.prodMk measurable_const))
      (fun a => hgm _) (fun a => hgM _)
  have hGpos : ∀ b, 0 < G b := fun b => lt_of_lt_of_le hm (hGb b).1
  set Mt := ∫ b, G b ∂ν with hMtdef
  have hMt : m ≤ Mt ∧ Mt ≤ M :=
    integral_mem_of (μ := ν) hGmeas (fun b => (hGb b).1) (fun b => (hGb b).2)
  have hMtp : 0 < Mt := lt_of_lt_of_le hm hMt.1
  have gI : Integrable g (μ.prod ν) := intOfBdd hg _ (fun p => abs_le_of_mem (hgm p) (hgM p))
  have glI : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν) :=
    intOfBdd hgl _ (fun p => glog_bdd hm (hgm p) (hgM p))
  have e1 : ∫ p, g p ∂(μ.prod ν) = Mt := integral_prod_symm g gI
  have e2 : ∫ p, g p * Real.log (g p) ∂(μ.prod ν) =
      ∫ b, ∫ a, g (a, b) * Real.log (g (a, b)) ∂μ ∂ν := integral_prod_symm _ glI
  set h : β → ℝ := fun b => Real.log (G b) - Real.log Mt with hhdef
  have hmeas : Measurable h := hGmeas.log.sub measurable_const
  have hK : ∀ b, |h b| ≤ 2 * L := fun b => by
    have a1 := abs_log_le hm (hGb b).1 (hGb b).2
    have a2 := abs_log_le hm hMt.1 hMt.2
    calc |h b| ≤ |Real.log (G b)| + |Real.log Mt| := abs_sub _ _
      _ ≤ 2 * L := by linarith
  have hexpb : ∀ b, Real.exp (h b) = G b / Mt := fun b => by
    simp only [h, Real.exp_sub, Real.exp_log (hGpos b), Real.exp_log hMtp]
  have hexp : ∫ b, Real.exp (h b) ∂ν = 1 := by
    simp_rw [hexpb]
    rw [integral_div]
    exact div_self hMtp.ne'
  have GI : Integrable G ν := intOfBdd hGmeas _ (fun b => abs_le_of_mem (hGb b).1 (hGb b).2)
  have GlI : Integrable (fun b => G b * Real.log (G b)) ν :=
    intOfBdd (hGmeas.mul hGmeas.log) _ (fun b => glog_bdd hm (hGb b).1 (hGb b).2)
  have e3 : ∫ b, G b * h b ∂ν = ∫ b, G b * Real.log (G b) ∂ν - Mt * Real.log Mt := by
    simp only [h, mul_sub]
    rw [integral_sub GlI (GI.mul_const _), integral_mul_const]
  have e4 : ∫ b, G b * h b ∂ν = ∫ b, ∫ a, g (a, b) * h b ∂μ ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only [G]
    exact (integral_mul_const (h b) _).symm
  have swapI : Integrable (Function.uncurry fun (b : β) (a : α) => g (a, b) * h b) (ν.prod μ) := by
    refine intOfBdd ((hg.comp measurable_swap).mul (hmeas.comp measurable_fst)) ((|m| + |M|) * (2 * L))
      (fun p => ?_)
    simp only [Function.uncurry]
    rw [abs_mul]
    exact mul_le_mul (abs_le_of_mem (hgm _) (hgM _)) (hK _) (abs_nonneg _) (by positivity)
  have e5 : ∫ b, ∫ a, g (a, b) * h b ∂μ ∂ν = ∫ a, ∫ b, g (a, b) * h b ∂ν ∂μ :=
    integral_integral_swap swapI
  have I1 : Integrable (fun a => ∫ b, g (a, b) * h b ∂ν) μ := by
    refine intOfBdd ((hg.mul (hmeas.comp measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := ν)).measurable ((|m| + |M|) * (2 * L)) (fun a => ?_)
    refine abs_integral_le_of (μ := ν) ((hg.comp (measurable_const.prodMk measurable_id)).mul hmeas)
      (fun b => ?_)
    show |g (a, b) * h b| ≤ _
    rw [abs_mul]
    exact mul_le_mul (abs_le_of_mem (hgm _) (hgM _)) (hK _) (abs_nonneg _) (by positivity)
  have I2 : Integrable (fun a => ent ν (fun b => g (a, b))) μ :=
    intOfBdd (ent_meas_right ν hg) _ (fun a => ent_abs_le ν (hg.comp
      (measurable_const.prodMk measurable_id)) hm (fun b => hgm _) (fun b => hgM _))
  have e6 : ∫ a, ∫ b, g (a, b) * h b ∂ν ∂μ ≤ ∫ a, ent ν (fun b => g (a, b)) ∂μ :=
    integral_mono I1 I2 (fun a => gibbs ν (hg.comp (measurable_const.prodMk measurable_id)) hmeas
      hm (fun b => hgm _) (fun b => hgM _) hK hexp)
  have J1 : Integrable (fun b => ∫ a, g (a, b) * Real.log (g (a, b)) ∂μ) ν :=
    intOfBdd (hgl.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable _
      (fun b => abs_integral_le_of (μ := μ) (hgl.comp (measurable_id.prodMk measurable_const))
        (fun a => glog_bdd hm (hgm _) (hgM _)))
  have e7 : ∫ b, ent μ (fun a => g (a, b)) ∂ν =
      ∫ b, ∫ a, g (a, b) * Real.log (g (a, b)) ∂μ ∂ν - ∫ b, G b * Real.log (G b) ∂ν := by
    unfold ent
    exact integral_sub J1 GlI
  have hent : ent (μ.prod ν) g = ∫ p, g p * Real.log (g p) ∂(μ.prod ν) - Mt * Real.log Mt := by
    unfold ent; rw [e1]
  rw [hent, e2]
  linarith

end Prod

section Pi

variable {X : Type*} [MeasurableSpace X]

lemma esymm_update0 {n : ℕ} (p : X × (Fin n → X)) (y : X) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm p) 0 y =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm (y, p.2) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma esymm_update_succ {n : ℕ} (p : X × (Fin n → X)) (j : Fin n) (y : X) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm p) j.succ y =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm
        (p.1, Function.update p.2 j y) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma esymm_update_k {n : ℕ} (k : Fin (n + 1)) (p : X × (Fin n → X)) (y : X) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k).symm p) k y =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k).symm (y, p.2) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma esymm_update0' {n : ℕ} (e : (Fin (n + 1) → X) ≃ᵐ X × (Fin n → X))
    (he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0)
    (p : X × (Fin n → X)) (y : X) : Function.update (e.symm p) 0 y = e.symm (y, p.2) := by
  subst he; exact esymm_update0 p y

lemma esymm_update_succ' {n : ℕ} (e : (Fin (n + 1) → X) ≃ᵐ X × (Fin n → X))
    (he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0)
    (p : X × (Fin n → X)) (j : Fin n) (y : X) :
    Function.update (e.symm p) j.succ y = e.symm (p.1, Function.update p.2 j y) := by
  subst he; exact esymm_update_succ p j y

lemma esymm_update_k' {n : ℕ} (k : Fin (n + 1)) (e : (Fin (n + 1) → X) ≃ᵐ X × (Fin n → X))
    (he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k)
    (p : X × (Fin n → X)) (y : X) : Function.update (e.symm p) k y = e.symm (y, p.2) := by
  subst he; exact esymm_update_k k p y

/-- Resampling one coordinate leaves the product measure invariant. -/
theorem resample (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) (k : Fin n)
    {F : (Fin n → X) → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ s, |F s| ≤ C) :
    ∫ s, (∫ y, F (Function.update s k y) ∂P) ∂(Measure.pi fun _ : Fin n => P) =
      ∫ s, F s ∂(Measure.pi fun _ : Fin n => P) := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k with he
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => P)
      (P.prod (Measure.pi fun _ : Fin n => P)) := measurePreserving_piFinSuccAbove (fun _ => P) k
  have a1 := hmp.symm.integral_comp' (fun s => ∫ y, F (Function.update s k y) ∂P)
  have a2 := hmp.symm.integral_comp' F
  rw [← a1, ← a2]
  simp_rw [esymm_update_k' k e he]
  have hF' : Measurable (fun q : (X × (Fin n → X)) × X => F (e.symm (q.2, q.1.2))) :=
    hF.comp (e.symm.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have I1 : Integrable (fun p : X × (Fin n → X) => ∫ y, F (e.symm (y, p.2)) ∂P)
      (P.prod (Measure.pi fun _ : Fin n => P)) :=
    intOfBdd (hF'.stronglyMeasurable.integral_prod_right' (ν := P)).measurable C
      (fun p => abs_integral_le_of (μ := P)
        (hF.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))) (fun y => hC _))
  have I2 : Integrable (fun p : X × (Fin n → X) => F (e.symm p))
      (P.prod (Measure.pi fun _ : Fin n => P)) := intOfBdd (hF.comp e.symm.measurable) C (fun p => hC _)
  rw [integral_prod_symm _ I1, integral_prod_symm _ I2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [integral_const, probReal_univ, one_smul]

/-- Tensorization of entropy for `Pⁿ`. -/
theorem tens (P : Measure X) [IsProbabilityMeasure P] :
    ∀ (n : ℕ) (g : (Fin n → X) → ℝ), Measurable g → ∀ (m M : ℝ), 0 < m → (∀ s, m ≤ g s) →
      (∀ s, g s ≤ M) →
      ent (Measure.pi fun _ : Fin n => P) g ≤
        ∑ k : Fin n, ∫ s, ent P (fun x => g (Function.update s k x))
          ∂(Measure.pi fun _ : Fin n => P) := by
  intro n
  induction n with
  | zero =>
    intro g hg m M hm hgm hgM
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have hc : ∀ s : Fin 0 → X, g s = g (fun i => i.elim0) := fun s => by
      congr 1; funext i; exact i.elim0
    have hconst : ∀ (φ : ℝ → ℝ), ∫ s, φ (g s) ∂(Measure.pi fun _ : Fin 0 => P) =
        φ (g (fun i => i.elim0)) := by
      intro φ; simp_rw [hc]; simp
    have h1 := hconst (fun x => x * Real.log x)
    have h2 := hconst id
    simp only [id] at h2
    unfold ent
    rw [h1, h2]; simp
  | succ n ih =>
    intro g hg m M hm hgm hgM
    set L := |Real.log m| + |Real.log M| with hL
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => P)
        (P.prod (Measure.pi fun _ : Fin n => P)) :=
      measurePreserving_piFinSuccAbove (fun _ => P) 0
    set g' : X × (Fin n → X) → ℝ := fun p => g (e.symm p) with hg'def
    have hg' : Measurable g' := hg.comp e.symm.measurable
    have hent : ent (Measure.pi fun _ : Fin (n + 1) => P) g =
        ent (P.prod (Measure.pi fun _ : Fin n => P)) g' := by
      unfold ent
      have a1 := hmp.symm.integral_comp' (fun s => g s * Real.log (g s))
      have a2 := hmp.symm.integral_comp' g
      rw [← a1, ← a2]
    rw [hent]
    have step := ent_prod P (Measure.pi fun _ : Fin n => P) hg' hm (fun p => hgm _)
      (fun p => hgM _)
    refine le_trans step ?_
    rw [Fin.sum_univ_succ]
    -- coordinate 0
    have F0 : Measurable (fun q : (X × (Fin n → X)) × X => g' (q.2, q.1.2)) :=
      hg'.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have t0 : ∫ s, ent P (fun x => g (Function.update s 0 x)) ∂(Measure.pi fun _ => P) =
        ∫ b, ent P (fun a => g' (a, b)) ∂(Measure.pi fun _ : Fin n => P) := by
      have a := hmp.symm.integral_comp' (fun s => ent P (fun x => g (Function.update s 0 x)))
      rw [← a]
      simp_rw [esymm_update0' e he]
      have I : Integrable (fun p : X × (Fin n → X) => ent P (fun y => g' (y, p.2)))
          (P.prod (Measure.pi fun _ : Fin n => P)) :=
        intOfBdd (ent_meas_right P F0) _ (fun p => ent_abs_le P
          (hg'.comp (measurable_id.prodMk measurable_const)) hm (fun y => hgm _) (fun y => hgM _))
      rw [integral_prod_symm _ I]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [integral_const, probReal_univ, one_smul]
    -- coordinates succ j
    have ts : ∀ j : Fin n,
        ∫ s, ent P (fun x => g (Function.update s j.succ x)) ∂(Measure.pi fun _ => P) =
          ∫ a, ∫ t, ent P (fun y => g' (a, Function.update t j y))
            ∂(Measure.pi fun _ : Fin n => P) ∂P := by
      intro j
      have a := hmp.symm.integral_comp' (fun s => ent P (fun x => g (Function.update s j.succ x)))
      rw [← a]
      simp_rw [esymm_update_succ' e he]
      have Fj : Measurable (fun q : (X × (Fin n → X)) × X =>
          g' (q.1.1, Function.update q.1.2 j q.2)) :=
        hg'.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      have I : Integrable (fun p : X × (Fin n → X) => ent P (fun y => g' (p.1, Function.update p.2 j y)))
          (P.prod (Measure.pi fun _ : Fin n => P)) :=
        intOfBdd (ent_meas_right P Fj) _ (fun p => ent_abs_le P
          (Fj.comp (measurable_const.prodMk measurable_id)) hm (fun y => hgm _) (fun y => hgM _))
      rw [integral_prod _ I]
    rw [t0]
    simp_rw [ts]
    have Ij : ∀ j : Fin n, Integrable
        (fun a => ∫ t, ent P (fun y => g' (a, Function.update t j y))
          ∂(Measure.pi fun _ : Fin n => P)) P := by
      intro j
      have Fj : Measurable (fun q : (X × (Fin n → X)) × X =>
          g' (q.1.1, Function.update q.1.2 j q.2)) :=
        hg'.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      refine intOfBdd ((ent_meas_right P Fj).stronglyMeasurable.integral_prod_right'
        (ν := Measure.pi fun _ : Fin n => P)).measurable (2 * (M * L)) (fun a => ?_)
      exact abs_integral_le_of (ent_meas_right P Fj |>.comp (measurable_const.prodMk measurable_id))
        (fun t => ent_abs_le P (Fj.comp (measurable_const.prodMk measurable_id)) hm
          (fun y => hgm _) (fun y => hgM _))
    rw [← integral_finsetSum _ (fun j _ => Ij j)]
    apply add_le_add le_rfl
    apply integral_mono
      (intOfBdd (ent_meas_right _ hg') _ (fun a => ent_abs_le _
        (hg'.comp (measurable_const.prodMk measurable_id)) hm (fun y => hgm _) (fun y => hgM _)))
      (integrable_finset_sum _ (fun j _ => Ij j))
    intro a
    exact ih (fun t => g' (a, t)) (hg'.comp (measurable_const.prodMk measurable_id)) m M hm
      (fun t => hgm _) (fun t => hgM _)

end Pi


/-- **P5**: comparison for the differential inequality
`l(4 - l²) G' - (4 + 4l - l²) G ≤ 2 l² v` on `(0, 2)`, with `G 0 = 0`, `G' 0 = 0`. -/
theorem ode_bound (G G' : ℝ → ℝ) (v : ℝ) (hG0 : G 0 = 0)
    (hd : ∀ l, 0 ≤ l → l < 2 → HasDerivAt G (G' l) l) (hG'0 : G' 0 = 0)
    (hineq : ∀ l, 0 < l → l < 2 →
      l * (4 - l ^ 2) * G' l - (4 + 4 * l - l ^ 2) * G l ≤ 2 * l ^ 2 * v) :
    ∀ l, 0 ≤ l → l < 2 → G l ≤ v * l ^ 2 / (2 - l) := by
  intro l hl0 hl2
  rcases eq_or_lt_of_le hl0 with h | hpos
  · subst h; simp [hG0]
  set Q : ℝ → ℝ := fun x => (G x * (2 - x) - v * (x * x)) / (2 * x + x * x) with hQ
  have hRd : ∀ x, 0 ≤ x → x < 2 →
      HasDerivAt (fun x => G x * (2 - x) - v * (x * x))
        (G' x * (2 - x) - G x - 2 * v * x) x := by
    intro x hx0 hx2
    have h1 := ((hd x hx0 hx2).mul ((hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x))).sub
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul v)
    refine h1.congr_deriv ?_
    simp only [id, Pi.sub_apply]; ring
  have hSd : ∀ x, HasDerivAt (fun x : ℝ => 2 * x + x * x) (2 + 2 * x) x := by
    intro x
    have h1 := ((hasDerivAt_id x).const_mul (2:ℝ)).add ((hasDerivAt_id x).mul (hasDerivAt_id x))
    refine h1.congr_deriv ?_
    simp only [id]; ring
  have hQd : ∀ x, 0 < x → x < 2 → HasDerivAt Q
      (((G' x * (2 - x) - G x - 2 * v * x) * (2 * x + x * x) -
        (G x * (2 - x) - v * (x * x)) * (2 + 2 * x)) / (2 * x + x * x) ^ 2) x := by
    intro x hx0 hx2
    exact (hRd x hx0.le hx2).div (hSd x) (by positivity)
  have hanti : AntitoneOn Q (Set.Ioo 0 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 2)
    · intro x hx; exact (hQd x hx.1 hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (hQd x hx.1 hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hQd x hx.1 hx.2).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have := hineq x hx.1 hx.2
      nlinarith
  -- Q ε → 0 as ε → 0⁺
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (G (0 + t) - G 0)) (𝓝[>] 0) (𝓝 (G' 0)) :=
    (hd 0 le_rfl two_pos).tendsto_slope_zero_right
  simp only [zero_add, hG0, sub_zero, smul_eq_mul, hG'0] at hslope
  have hfac : Tendsto (fun t : ℝ => (2 - t) / (2 + t)) (𝓝[>] 0) (𝓝 ((2 - 0) / (2 + 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
      (by norm_num)).tendsto
  have hv : Tendsto (fun t : ℝ => v * t / (2 + t)) (𝓝[>] 0) (𝓝 (v * 0 / (2 + 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuousAt_const.mul continuousAt_id).div (continuousAt_const.add continuousAt_id)
      (by norm_num)).tendsto
  have hlim : Tendsto (fun t => (t⁻¹ * G t) * ((2 - t) / (2 + t)) - v * t / (2 + t)) (𝓝[>] 0)
      (𝓝 0) := by
    have := (hslope.mul hfac).sub hv
    simpa using this
  have hQeq : ∀ t, 0 < t → Q t = (t⁻¹ * G t) * ((2 - t) / (2 + t)) - v * t / (2 + t) := by
    intro t ht
    have h1 : t ≠ 0 := ht.ne'
    have h2 : 2 + t ≠ 0 := by positivity
    have h3 : 2 * t + t * t ≠ 0 := by positivity
    simp only [hQ]
    field_simp
  have hQlim : Tendsto Q (𝓝[>] 0) (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hQeq t ht).symm
  have hQl : Q l ≤ 0 := by
    refine ge_of_tendsto hQlim ?_
    filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
    exact hanti ⟨ht.1, lt_trans ht.2 hl2⟩ ⟨hpos, hl2⟩ ht.2.le
  have hS : 0 < 2 * l + l * l := by positivity
  have hRQ : G l * (2 - l) - v * (l * l) = Q l * (2 * l + l * l) := by
    simp only [hQ]; field_simp
  have hR : G l * (2 - l) - v * (l * l) ≤ 0 := by
    rw [hRQ]; exact mul_nonpos_of_nonpos_of_nonneg hQl hS.le
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 - l)]
  nlinarith

/-! ### P3/P4: the finite-class Bousquet entropy bound -/
section Bq

variable {X : Type*} [MeasurableSpace X] {n N : ℕ} (h : Fin (N + 1) → X → ℝ)

noncomputable def val (s : Fin n → X) (i : Fin (N + 1)) : ℝ := ∑ j, h i (s j)

noncomputable def valk (k : Fin n) (s : Fin n → X) (i : Fin (N + 1)) : ℝ :=
  ∑ j, h i (s j) - h i (s k)

noncomputable def Zf (s : Fin n → X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => val h s i)

noncomputable def Zk (k : Fin n) (s : Fin n → X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => valk h k s i)

lemma sum_update_eq (f : X → ℝ) (s : Fin n → X) (k : Fin n) (y : X) :
    ∑ j, f (Function.update s k y j) = ∑ j, f (s j) - f (s k) + f y := by
  have e1 := Finset.add_sum_erase Finset.univ (fun j => f (Function.update s k y j))
    (Finset.mem_univ k)
  have e2 := Finset.add_sum_erase Finset.univ (fun j => f (s j)) (Finset.mem_univ k)
  have e3 : ∑ j ∈ Finset.univ.erase k, f (Function.update s k y j) =
      ∑ j ∈ Finset.univ.erase k, f (s j) :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  simp only [Function.update_self] at e1
  linarith

lemma valk_update (k : Fin n) (s : Fin n → X) (y : X) (i : Fin (N + 1)) :
    valk h k (Function.update s k y) i = valk h k s i := by
  unfold valk
  rw [sum_update_eq (h i)]
  simp only [Function.update_self]
  ring

lemma Zk_update (k : Fin n) (s : Fin n → X) (y : X) :
    Zk h k (Function.update s k y) = Zk h k s := by
  unfold Zk; simp_rw [valk_update]

lemma val_eq (s : Fin n → X) (k : Fin n) (i : Fin (N + 1)) :
    val h s i = valk h k s i + h i (s k) := by
  unfold val valk; ring

lemma val_le_Zf (s : Fin n → X) (i : Fin (N + 1)) : val h s i ≤ Zf h s :=
  Finset.le_sup' (fun i => val h s i) (Finset.mem_univ i)

lemma valk_le_Zk (k : Fin n) (s : Fin n → X) (i : Fin (N + 1)) : valk h k s i ≤ Zk h k s :=
  Finset.le_sup' (fun i => valk h k s i) (Finset.mem_univ i)

lemma Zf_attained (s : Fin n → X) : ∃ i, Zf h s = val h s i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => val h s i)
  exact ⟨i, hi⟩

lemma Zk_attained (k : Fin n) (s : Fin n → X) : ∃ i, Zk h k s = valk h k s i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => valk h k s i)
  exact ⟨i, hi⟩

section Bounds
variable (hb : ∀ i x, |h i x| ≤ 1)
include hb

lemma abs_val_le (s : Fin n → X) (i : Fin (N + 1)) : |val h s i| ≤ n := by
  unfold val
  calc |∑ j, h i (s j)| ≤ ∑ j, |h i (s j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (1:ℝ) := Finset.sum_le_sum (fun j _ => hb i (s j))
    _ = n := by simp

lemma abs_valk_le (k : Fin n) (s : Fin n → X) (i : Fin (N + 1)) : |valk h k s i| ≤ n + 1 := by
  have h1 := abs_val_le h hb s i
  have h2 := hb i (s k)
  have : valk h k s i = val h s i - h i (s k) := by unfold val valk; ring
  rw [this]
  calc _ ≤ |val h s i| + |h i (s k)| := abs_sub _ _
    _ ≤ n + 1 := by linarith

lemma Zf_mem (s : Fin n → X) : -((n:ℝ) + 1) ≤ Zf h s ∧ Zf h s ≤ n + 1 := by
  constructor
  · have := (abs_le.mp (abs_val_le h hb s 0)).1
    have := val_le_Zf h s 0
    linarith
  · obtain ⟨i, hi⟩ := Zf_attained h s
    rw [hi]; have := (abs_le.mp (abs_val_le h hb s i)).2; linarith

lemma Zk_mem (k : Fin n) (s : Fin n → X) : -((n:ℝ) + 1) ≤ Zk h k s ∧ Zk h k s ≤ n + 1 := by
  constructor
  · have := (abs_le.mp (abs_valk_le h hb k s 0)).1
    have := valk_le_Zk h k s 0
    linarith
  · obtain ⟨i, hi⟩ := Zk_attained h k s
    rw [hi]; exact (abs_le.mp (abs_valk_le h hb k s i)).2

/-- `Z - Z_k ≤ 1`. -/
lemma Y_le_one (s : Fin n → X) (k : Fin n) : Zf h s - Zk h k s ≤ 1 := by
  obtain ⟨i, hi⟩ := Zf_attained h s
  have a := valk_le_Zk h k s i
  have b := val_eq h s k i
  have c := (abs_le.mp (hb i (s k))).2
  linarith

/-- `∑ₖ (Z - Z_k) ≤ Z`. -/
lemma sumY_le (s : Fin n → X) : ∑ k, (Zf h s - Zk h k s) ≤ Zf h s := by
  obtain ⟨i, hi⟩ := Zf_attained h s
  calc ∑ k, (Zf h s - Zk h k s) ≤ ∑ k, h i (s k) := Finset.sum_le_sum (fun k _ => by
        have a := valk_le_Zk h k s i
        have b := val_eq h s k i
        linarith)
    _ = Zf h s := by rw [hi]; rfl

end Bounds

/-- `Y' ≤ Y` for a maximizer of `Z_k`. -/
lemma Y_ge (s : Fin n → X) (k : Fin n) (i : Fin (N + 1)) (hi : valk h k s i = Zk h k s) :
    h i (s k) ≤ Zf h s - Zk h k s := by
  have a := val_le_Zf h s i
  have b := val_eq h s k i
  linarith

section Meas
variable (hm : ∀ i, Measurable (h i))
include hm

lemma val_meas (i : Fin (N + 1)) : Measurable (fun s : Fin n → X => val h s i) := by
  unfold val
  exact Finset.measurable_sum _ (fun j _ => (hm i).comp (measurable_pi_apply j))

lemma valk_meas (k : Fin n) (i : Fin (N + 1)) : Measurable (fun s : Fin n → X => valk h k s i) := by
  unfold valk
  exact (Finset.measurable_sum _ (fun j _ => (hm i).comp (measurable_pi_apply j))).sub
    ((hm i).comp (measurable_pi_apply k))

lemma Zf_meas : Measurable (fun s : Fin n → X => Zf h s) := by
  have := Finset.measurable_sup' (δ := Fin n → X) (s := Finset.univ) Finset.univ_nonempty
    (f := fun i s => val h s i) (fun i _ => val_meas h hm i)
  convert this using 1
  funext s
  simp [Zf, Finset.sup'_apply]

lemma Zk_meas (k : Fin n) : Measurable (fun s : Fin n → X => Zk h k s) := by
  have := Finset.measurable_sup' (δ := Fin n → X) (s := Finset.univ) Finset.univ_nonempty
    (f := fun i s => valk h k s i) (fun i _ => valk_meas h hm k i)
  convert this using 1
  funext s
  simp [Zk, Finset.sup'_apply]

end Meas

/-- First maximizer sets. -/
def Eset (k : Fin n) (i : Fin (N + 1)) : Set (Fin n → X) :=
  {s | valk h k s i = Zk h k s} ∩ ⋂ j, ⋂ (_ : j < i), {s | valk h k s j < Zk h k s}

lemma mem_Eset (k : Fin n) (i : Fin (N + 1)) (s : Fin n → X) :
    s ∈ Eset h k i ↔ valk h k s i = Zk h k s ∧ ∀ j < i, valk h k s j < Zk h k s := by
  simp [Eset]

lemma Eset_meas (hm : ∀ i, Measurable (h i)) (k : Fin n) (i : Fin (N + 1)) :
    MeasurableSet (Eset h k i) := by
  refine MeasurableSet.inter (measurableSet_eq_fun (valk_meas h hm k i) (Zk_meas h hm k)) ?_
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (valk_meas h hm k j) (Zk_meas h hm k)

lemma Eset_update (k : Fin n) (i : Fin (N + 1)) (s : Fin n → X) (y : X) :
    Function.update s k y ∈ Eset h k i ↔ s ∈ Eset h k i := by
  simp only [mem_Eset, valk_update, Zk_update]

lemma Eset_unique (k : Fin n) (s : Fin n → X) :
    ∃ i0, s ∈ Eset h k i0 ∧ ∀ i, s ∈ Eset h k i → i = i0 := by
  classical
  set S := Finset.univ.filter (fun i => valk h k s i = Zk h k s) with hS
  have hne : S.Nonempty := by
    obtain ⟨i, hi⟩ := Zk_attained h k s
    exact ⟨i, by simp [S, hi]⟩
  have hmin := S.min'_mem hne
  have hminS : valk h k s (S.min' hne) = Zk h k s := by simpa [S] using hmin
  have hlt : ∀ j < S.min' hne, valk h k s j < Zk h k s := by
    intro j hj
    have hjS : j ∉ S := fun hjS => absurd (S.min'_le j hjS) (not_le.mpr hj)
    have : valk h k s j ≠ Zk h k s := fun he => hjS (by simp [S, he])
    exact lt_of_le_of_ne (valk_le_Zk h k s j) this
  refine ⟨S.min' hne, (mem_Eset h k _ s).mpr ⟨hminS, hlt⟩, ?_⟩
  intro i hi
  rw [mem_Eset] at hi
  rcases lt_trichotomy i (S.min' hne) with h1 | h1 | h1
  · exact absurd hi.1 (ne_of_lt (hlt i h1))
  · exact h1
  · exact absurd hminS (ne_of_lt (hi.2 _ h1))

/-- The variance-term integrand. -/
noncomputable def Vf (l : ℝ) (k : Fin n) (i : Fin (N + 1)) (s : Fin n → X) : ℝ :=
  Real.exp (l * Zk h k s) * (h i (s k) ^ 2 - 2 * h i (s k))

/-- The modified-LSI summand. -/
noncomputable def Wf (l : ℝ) (k : Fin n) (s : Fin n → X) : ℝ :=
  Real.exp (l * Zf h s) * (l * Zf h s) - Real.exp (l * Zf h s) * (l * Zk h k s)
    - Real.exp (l * Zf h s) + Real.exp (l * Zk h k s)

lemma W_pointwise (hb : ∀ i x, |h i x| ≤ 1) (l : ℝ) (hl0 : 0 ≤ l) (hl2 : l ≤ 2)
    (k : Fin n) (s : Fin n → X) (i0 : Fin (N + 1)) (hi0 : s ∈ Eset h k i0) :
    (4 + 4 * l - l ^ 2) * Wf h l k s ≤
      2 * l ^ 2 * (2 * (Zf h s - Zk h k s) * Real.exp (l * Zf h s) + Vf h l k i0 s) := by
  set Y := Zf h s - Zk h k s with hY
  have hW : Wf h l k s = Real.exp (l * Zk h k s) * psiB (l * Y) := by
    unfold Wf psiB
    have : l * Zf h s = l * Zk h k s + l * Y := by rw [hY]; ring
    rw [this, Real.exp_add]; ring
  have hy'1 : -1 ≤ h i0 (s k) := (abs_le.mp (hb i0 (s k))).1
  have hyy := Y_ge h s k i0 ((mem_Eset h k i0 s).mp hi0).1
  have hy1 := Y_le_one h hb s k
  have hp := p1 l Y (h i0 (s k)) hl0 hl2 hy'1 hyy hy1
  have hE := Real.exp_pos (l * Zk h k s)
  have hexp : Real.exp (l * Zf h s) = Real.exp (l * Zk h k s) * Real.exp (l * Y) := by
    rw [← Real.exp_add]; congr 1; rw [hY]; ring
  rw [hW, hexp]
  unfold Vf
  have := mul_le_mul_of_nonneg_left hp hE.le
  nlinarith

end Bq

lemma Wexpr_abs {a b C : ℝ} (ha : |a| ≤ C) (hb' : |b| ≤ C) :
    |Real.exp a * a - Real.exp a * b - Real.exp a + Real.exp b| ≤ 4 * Real.exp C * (C + 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) ha
  have ea : Real.exp a ≤ Real.exp C := Real.exp_le_exp.mpr (le_trans (le_abs_self a) ha)
  have eb : Real.exp b ≤ Real.exp C := Real.exp_le_exp.mpr (le_trans (le_abs_self b) hb')
  have pa := Real.exp_pos a
  have pb := Real.exp_pos b
  have pC := Real.exp_pos C
  have e1 : |Real.exp a * a| ≤ Real.exp C * C := by
    rw [abs_mul, abs_of_pos pa]; exact mul_le_mul ea ha (abs_nonneg _) pC.le
  have e2 : |Real.exp a * b| ≤ Real.exp C * C := by
    rw [abs_mul, abs_of_pos pa]; exact mul_le_mul ea hb' (abs_nonneg _) pC.le
  have e3 : |Real.exp a| ≤ Real.exp C := by rw [abs_of_pos pa]; exact ea
  have e4 : |Real.exp b| ≤ Real.exp C := by rw [abs_of_pos pb]; exact eb
  have tri : |Real.exp a * a - Real.exp a * b - Real.exp a + Real.exp b| ≤
      |Real.exp a * a| + |Real.exp a * b| + |Real.exp a| + |Real.exp b| := by
    calc _ ≤ |Real.exp a * a - Real.exp a * b - Real.exp a| + |Real.exp b| := abs_add_le _ _
      _ ≤ |Real.exp a * a - Real.exp a * b| + |Real.exp a| + |Real.exp b| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_sub _ _
  nlinarith

lemma lZ_abs {l u B : ℝ} (hl0 : 0 ≤ l) (hl2 : l ≤ 2) (hu : -B ≤ u ∧ u ≤ B) :
    |l * u| ≤ 2 * B := by
  have hB : 0 ≤ B := by linarith [hu.1, hu.2]
  rw [abs_mul, abs_of_nonneg hl0]
  have : |u| ≤ B := abs_le.mpr hu
  nlinarith [abs_nonneg u]

section Integ

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
  {n N : ℕ} (h : Fin (N + 1) → X → ℝ) (hm : ∀ i, Measurable (h i)) (hb : ∀ i x, |h i x| ≤ 1)
include hm hb

lemma Wf_meas (l : ℝ) (k : Fin n) : Measurable (fun s => Wf h l k s) := by
  unfold Wf
  have a := (Zf_meas (n := n) h hm).const_mul l
  have b := (Zk_meas (n := n) h hm k).const_mul l
  exact (((a.exp.mul a).sub (a.exp.mul b)).sub a.exp).add b.exp

/-- **S1**: tensorization + variational bound + resampling. -/
theorem ent_le_sumW (l : ℝ) (hl0 : 0 ≤ l) (hl2 : l ≤ 2) :
    ent (Measure.pi fun _ : Fin n => P) (fun s => Real.exp (l * Zf h s)) ≤
      ∑ k, ∫ s, Wf h l k s ∂(Measure.pi fun _ : Fin n => P) := by
  set B : ℝ := (n : ℝ) + 1 with hB
  have hlZf : ∀ s, |l * Zf h s| ≤ 2 * B := fun s =>
    lZ_abs hl0 hl2 ⟨(Zf_mem h hb s).1, (Zf_mem h hb s).2⟩
  have hlZk : ∀ k s, |l * Zk h k s| ≤ 2 * B := fun k s =>
    lZ_abs hl0 hl2 ⟨(Zk_mem h hb k s).1, (Zk_mem h hb k s).2⟩
  have gmeas : Measurable (fun s => Real.exp (l * Zf h s)) := ((Zf_meas (n := n) h hm).const_mul l).exp
  have glo : ∀ s, Real.exp (-(2 * B)) ≤ Real.exp (l * Zf h s) := fun s =>
    Real.exp_le_exp.mpr (abs_le.mp (hlZf s)).1
  have ghi : ∀ s, Real.exp (l * Zf h s) ≤ Real.exp (2 * B) := fun s =>
    Real.exp_le_exp.mpr (abs_le.mp (hlZf s)).2
  have T := tens P n (fun s => Real.exp (l * Zf h s)) gmeas _ _ (Real.exp_pos _) glo ghi
  refine le_trans T (Finset.sum_le_sum fun k _ => ?_)
  have Wmeas := Wf_meas h hm hb l k
  have Wbd : ∀ s, |Wf h l k s| ≤ 4 * Real.exp (2 * B) * (2 * B + 1) := fun s =>
    Wexpr_abs (hlZf s) (hlZk k s)
  refine le_trans ?_ (le_of_eq (resample P n k Wmeas Wbd))
  have upd_meas : Measurable (fun q : (Fin n → X) × X => Function.update q.1 k q.2) :=
    measurable_update'
  have F1 : Measurable (fun q : (Fin n → X) × X => Real.exp (l * Zf h (Function.update q.1 k q.2))) :=
    (((Zf_meas (n := n) h hm).comp upd_meas).const_mul l).exp
  have I1 : Integrable (fun s => ent P (fun x => Real.exp (l * Zf h (Function.update s k x))))
      (Measure.pi fun _ : Fin n => P) :=
    intOfBdd (ent_meas_right P F1) _ (fun s => ent_abs_le P
      (F1.comp (measurable_const.prodMk measurable_id)) (Real.exp_pos _) (fun x => glo _)
      (fun x => ghi _))
  have I2 : Integrable (fun s => ∫ x, Wf h l k (Function.update s k x) ∂P)
      (Measure.pi fun _ : Fin n => P) :=
    intOfBdd ((Wmeas.comp upd_meas).stronglyMeasurable.integral_prod_right' (ν := P)).measurable _
      (fun s => abs_integral_le_of (Wmeas.comp (measurable_update s)) (fun x => Wbd _))
  apply integral_mono I1 I2
  intro s
  show ent P (fun x => Real.exp (l * Zf h (Function.update s k x))) ≤
    ∫ x, Wf h l k (Function.update s k x) ∂P
  have gm : Measurable (fun x => Real.exp (l * Zf h (Function.update s k x))) :=
    (((Zf_meas (n := n) h hm).comp (measurable_update s)).const_mul l).exp
  have glo' : ∀ x, Real.exp (-(2 * B)) ≤ Real.exp (l * Zf h (Function.update s k x)) :=
    fun x => glo (Function.update s k x)
  have ghi' : ∀ x, Real.exp (l * Zf h (Function.update s k x)) ≤ Real.exp (2 * B) :=
    fun x => ghi (Function.update s k x)
  have hv := ent_le_var P gm (Real.exp_pos (-(2 * B))) glo' ghi' (Real.exp_pos (l * Zk h k s))
  have heq : ∀ x, Real.exp (l * Zf h (Function.update s k x)) *
        Real.log (Real.exp (l * Zf h (Function.update s k x))) -
      Real.exp (l * Zf h (Function.update s k x)) * Real.log (Real.exp (l * Zk h k s)) -
      Real.exp (l * Zf h (Function.update s k x)) + Real.exp (l * Zk h k s) =
      Wf h l k (Function.update s k x) := by
    intro x
    rw [Real.log_exp, Real.log_exp]
    unfold Wf
    rw [Zk_update]
  simp only [heq] at hv
  exact hv

/-- **S3a**: the variance term, one maximizer set at a time. -/
lemma V_int (σ2 : ℝ) (hvar : ∀ i, ∫ x, h i x ^ 2 ∂P ≤ σ2) (hmean : ∀ i, ∫ x, h i x ∂P = 0)
    (l : ℝ) (hl0 : 0 ≤ l) (hl2 : l ≤ 2) (k : Fin n) (i : Fin (N + 1)) :
    ∫ s, (Eset h k i).indicator (Vf h l k i) s ∂(Measure.pi fun _ : Fin n => P) ≤
      σ2 * ∫ s, (Eset h k i).indicator (fun s => Real.exp (l * Zk h k s)) s
        ∂(Measure.pi fun _ : Fin n => P) := by
  set B : ℝ := (n : ℝ) + 1 with hB
  have hlZk : ∀ s, |l * Zk h k s| ≤ 2 * B := fun s =>
    lZ_abs hl0 hl2 ⟨(Zk_mem h hb k s).1, (Zk_mem h hb k s).2⟩
  have hk : Measurable (fun s : Fin n → X => h i (s k)) := (hm i).comp (measurable_pi_apply k)
  have Emeas := Eset_meas h hm k i
  have Vmeas : Measurable (Vf h l k i) := by
    unfold Vf
    exact (((Zk_meas h hm k).const_mul l).exp).mul ((hk.pow_const 2).sub (hk.const_mul 2))
  have hVbd : ∀ s, |Vf h l k i s| ≤ Real.exp (2 * B) * 3 := by
    intro s
    unfold Vf
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have e1 : Real.exp (l * Zk h k s) ≤ Real.exp (2 * B) :=
      Real.exp_le_exp.mpr (abs_le.mp (hlZk s)).2
    have hh := abs_le.mp (hb i (s k))
    have e2 : |h i (s k) ^ 2 - 2 * h i (s k)| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith
    exact mul_le_mul e1 e2 (abs_nonneg _) (Real.exp_pos _).le
  have Ibd : ∀ s, |(Eset h k i).indicator (Vf h l k i) s| ≤ Real.exp (2 * B) * 3 := by
    intro s
    by_cases hs : s ∈ Eset h k i
    · rw [Set.indicator_of_mem hs]; exact hVbd s
    · simp only [Set.indicator, hs, if_false, abs_zero]; positivity
  have Imeas : Measurable ((Eset h k i).indicator (Vf h l k i)) := Vmeas.indicator Emeas
  rw [← resample P n k Imeas Ibd]
  have Emeas2 : Measurable ((Eset h k i).indicator (fun s => Real.exp (l * Zk h k s))) :=
    (((Zk_meas h hm k).const_mul l).exp).indicator Emeas
  have E2bd : ∀ s, |(Eset h k i).indicator (fun s => Real.exp (l * Zk h k s)) s| ≤
      Real.exp (2 * B) := by
    intro s
    by_cases hs : s ∈ Eset h k i
    · rw [Set.indicator_of_mem hs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (abs_le.mp (hlZk s)).2
    · simp only [Set.indicator, hs, if_false, abs_zero]; positivity
  have upd_meas : Measurable (fun q : (Fin n → X) × X => Function.update q.1 k q.2) :=
    measurable_update'
  have I1 : Integrable (fun s => ∫ x, (Eset h k i).indicator (Vf h l k i) (Function.update s k x) ∂P)
      (Measure.pi fun _ : Fin n => P) :=
    intOfBdd ((Imeas.comp upd_meas).stronglyMeasurable.integral_prod_right' (ν := P)).measurable _
      (fun s => abs_integral_le_of (Imeas.comp (measurable_update s)) (fun x => Ibd _))
  have I2 : Integrable (fun s => σ2 * (Eset h k i).indicator (fun s => Real.exp (l * Zk h k s)) s)
      (Measure.pi fun _ : Fin n => P) :=
    (intOfBdd Emeas2 _ E2bd).const_mul σ2
  rw [← integral_const_mul]
  apply integral_mono I1 I2
  intro s
  have hxI : Integrable (fun x => h i x ^ 2) P :=
    intOfBdd ((hm i).pow_const 2) 1 (fun x => by
      have := abs_le.mp (hb i x); rw [abs_le]; constructor <;> nlinarith)
  have hxI2 : Integrable (fun x => 2 * h i x) P :=
    (intOfBdd (hm i) 1 (fun x => hb i x)).const_mul 2
  beta_reduce
  by_cases hs : s ∈ Eset h k i
  · have hfun : ∀ x, (Eset h k i).indicator (Vf h l k i) (Function.update s k x) =
        Real.exp (l * Zk h k s) * (h i x ^ 2 - 2 * h i x) := by
      intro x
      rw [Set.indicator_of_mem ((Eset_update h k i s x).mpr hs)]
      simp only [Vf, Zk_update, Function.update_self]
    simp only [hfun]
    rw [integral_const_mul, integral_sub hxI hxI2, integral_const_mul, hmean i,
      Set.indicator_of_mem hs]
    have := hvar i
    have hE := Real.exp_pos (l * Zk h k s)
    nlinarith
  · have hfun : ∀ x, (Eset h k i).indicator (Vf h l k i) (Function.update s k x) = 0 := by
      intro x
      have : Function.update s k x ∉ Eset h k i := fun h' => hs ((Eset_update h k i s x).mp h')
      simp only [Set.indicator, this, if_false]
    have hz : (fun x => (Eset h k i).indicator (Vf h l k i) (Function.update s k x)) =
        fun _ => (0:ℝ) := funext hfun
    rw [hz, integral_zero]
    simp only [Set.indicator, hs, if_false, mul_zero, le_refl]

end Integ


section Bq2

variable {X : Type*} [MeasurableSpace X] {n N : ℕ} (h : Fin (N + 1) → X → ℝ)

lemma sum_ind (k : Fin n) (s : Fin n → X) : ∃ i0, s ∈ Eset h k i0 ∧
    ∀ f : Fin (N + 1) → (Fin n → X) → ℝ, ∑ i, (Eset h k i).indicator (f i) s = f i0 s := by
  obtain ⟨i0, hi0, huniq⟩ := Eset_unique h k s
  refine ⟨i0, hi0, fun f => ?_⟩
  rw [Finset.sum_eq_single i0]
  · exact Set.indicator_of_mem hi0 _
  · intro i _ hne
    have : s ∉ Eset h k i := fun hs => hne (huniq i hs)
    simp only [Set.indicator, this, if_false]
  · intro h0; exact absurd (Finset.mem_univ i0) h0

end Bq2

section Integ2

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
  {n N : ℕ} (h : Fin (N + 1) → X → ℝ) (hm : ∀ i, Measurable (h i)) (hb : ∀ i x, |h i x| ≤ 1)
include hm hb

/-- **S3c**: `E e^{l Z_k} ≤ E e^{l Z}` (Jensen in coordinate `k`). -/
lemma expZk_le (hmean : ∀ i, ∫ x, h i x ∂P = 0) (l : ℝ) (hl0 : 0 ≤ l) (hl2 : l ≤ 2)
    (k : Fin n) :
    ∫ s, Real.exp (l * Zk h k s) ∂(Measure.pi fun _ : Fin n => P) ≤
      ∫ s, Real.exp (l * Zf h s) ∂(Measure.pi fun _ : Fin n => P) := by
  set B : ℝ := (n : ℝ) + 1 with hB
  have hlZf : ∀ s, |l * Zf h s| ≤ 2 * B := fun s =>
    lZ_abs hl0 hl2 ⟨(Zf_mem h hb s).1, (Zf_mem h hb s).2⟩
  have hlZk : ∀ s, |l * Zk h k s| ≤ 2 * B := fun s =>
    lZ_abs hl0 hl2 ⟨(Zk_mem h hb k s).1, (Zk_mem h hb k s).2⟩
  have mK : Measurable (fun s : Fin n → X => Real.exp (l * Zk h k s)) :=
    ((Zk_meas h hm k).const_mul l).exp
  have mF : Measurable (fun s : Fin n → X => Real.exp (l * Zf h s)) :=
    ((Zf_meas (n := n) h hm).const_mul l).exp
  have bK : ∀ s, |Real.exp (l * Zk h k s)| ≤ Real.exp (2 * B) := fun s => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (abs_le.mp (hlZk s)).2
  have bF : ∀ s, |Real.exp (l * Zf h s)| ≤ Real.exp (2 * B) := fun s => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (abs_le.mp (hlZf s)).2
  refine le_trans (le_of_eq (resample P n k mK bK).symm) (le_trans ?_ (le_of_eq (resample P n k mF bF)))
  have upd_meas : Measurable (fun q : (Fin n → X) × X => Function.update q.1 k q.2) :=
    measurable_update'
  have I1 : Integrable (fun s => ∫ x, Real.exp (l * Zk h k (Function.update s k x)) ∂P)
      (Measure.pi fun _ : Fin n => P) :=
    intOfBdd ((mK.comp upd_meas).stronglyMeasurable.integral_prod_right' (ν := P)).measurable _
      (fun s => abs_integral_le_of (mK.comp (measurable_update s)) (fun x => bK _))
  have I2 : Integrable (fun s => ∫ x, Real.exp (l * Zf h (Function.update s k x)) ∂P)
      (Measure.pi fun _ : Fin n => P) :=
    intOfBdd ((mF.comp upd_meas).stronglyMeasurable.integral_prod_right' (ν := P)).measurable _
      (fun s => abs_integral_le_of (mF.comp (measurable_update s)) (fun x => bF _))
  apply integral_mono I1 I2
  intro s
  simp only [Zk_update, integral_const, probReal_univ, one_smul]
  obtain ⟨i1, hi1⟩ := Zk_attained h k s
  have hx : ∀ x, Real.exp (l * Zk h k s) * (1 + l * h i1 x) ≤
      Real.exp (l * Zf h (Function.update s k x)) := by
    intro x
    have a := val_le_Zf h (Function.update s k x) i1
    have b := val_eq h (Function.update s k x) k i1
    rw [valk_update, Function.update_self, ← hi1] at b
    have c : l * Zk h k s + l * h i1 x ≤ l * Zf h (Function.update s k x) := by
      have : Zk h k s + h i1 x ≤ Zf h (Function.update s k x) := by linarith
      nlinarith
    calc Real.exp (l * Zk h k s) * (1 + l * h i1 x)
        ≤ Real.exp (l * Zk h k s) * Real.exp (l * h i1 x) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (l * h i1 x)])
            (Real.exp_pos _).le
      _ = Real.exp (l * Zk h k s + l * h i1 x) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr c
  have hI1 : Integrable (fun x => h i1 x) P := intOfBdd (hm i1) 1 (hb i1)
  have hL : Integrable (fun x => Real.exp (l * Zk h k s) * (1 + l * h i1 x)) P :=
    ((integrable_const 1).add (hI1.const_mul l)).const_mul _
  have hR : Integrable (fun x => Real.exp (l * Zf h (Function.update s k x))) P :=
    intOfBdd (mF.comp (measurable_update s)) _ (fun x => bF _)
  have := integral_mono hL hR hx
  rw [integral_const_mul, integral_add (integrable_const 1) (hI1.const_mul l), integral_const_mul,
    hmean i1] at this
  simpa using this

lemma Wf_bdd (l : ℝ) (hl0 : 0 ≤ l) (hl2 : l ≤ 2) (k : Fin n) (s : Fin n → X) :
    |Wf h l k s| ≤ 4 * Real.exp (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) + 1) :=
  Wexpr_abs (lZ_abs hl0 hl2 ⟨(Zf_mem h hb s).1, (Zf_mem h hb s).2⟩)
    (lZ_abs hl0 hl2 ⟨(Zk_mem h hb k s).1, (Zk_mem h hb k s).2⟩)

/-- **S4**: the finite-class Bousquet entropy inequality
`(4+4l-l²) Ent(e^{lZ}) ≤ 2 l² (2 E[Z e^{lZ}] + n σ² E[e^{lZ}])`, `0 ≤ l ≤ 2`. -/
theorem bousquet_ent (σ2 : ℝ) (hvar : ∀ i, ∫ x, h i x ^ 2 ∂P ≤ σ2)
    (hmean : ∀ i, ∫ x, h i x ∂P = 0) (l : ℝ) (hl0 : 0 ≤ l) (hl2 : l ≤ 2) :
    (4 + 4 * l - l ^ 2) * ent (Measure.pi fun _ : Fin n => P) (fun s => Real.exp (l * Zf h s)) ≤
      2 * l ^ 2 * (2 * ∫ s, Zf h s * Real.exp (l * Zf h s) ∂(Measure.pi fun _ : Fin n => P) +
        n * σ2 * ∫ s, Real.exp (l * Zf h s) ∂(Measure.pi fun _ : Fin n => P)) := by
  set μ := Measure.pi fun _ : Fin n => P with hμ
  set B : ℝ := (n : ℝ) + 1 with hB
  have hD : 0 ≤ 4 + 4 * l - l ^ 2 := by nlinarith
  have hσ : 0 ≤ σ2 := le_trans (integral_nonneg (fun x => sq_nonneg (h 0 x))) (hvar 0)
  have S1 := ent_le_sumW (n := n) P h hm hb l hl0 hl2
  have hlZf : ∀ s, |l * Zf h s| ≤ 2 * B := fun s =>
    lZ_abs hl0 hl2 ⟨(Zf_mem h hb s).1, (Zf_mem h hb s).2⟩
  have mZ := Zf_meas (n := n) h hm
  have mF : Measurable (fun s : Fin n → X => Real.exp (l * Zf h s)) := (mZ.const_mul l).exp
  have WI : ∀ k, Integrable (Wf h l k) μ := fun k =>
    intOfBdd (Wf_meas h hm hb l k) _ (Wf_bdd h hm hb l hl0 hl2 k)
  have EI : Integrable (fun s => Real.exp (l * Zf h s)) μ :=
    intOfBdd mF (Real.exp (2 * B)) (fun s => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (abs_le.mp (hlZf s)).2)
  have ZEI : Integrable (fun s => Zf h s * Real.exp (l * Zf h s)) μ :=
    intOfBdd (mZ.mul mF) (B * Real.exp (2 * B)) (fun s => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (abs_le.mpr (Zf_mem h hb s)) (Real.exp_le_exp.mpr (abs_le.mp (hlZf s)).2)
        (Real.exp_pos _).le (by positivity))
  have VI : ∀ k i, Integrable ((Eset h k i).indicator (Vf h l k i)) μ := by
    intro k i
    have hk : Measurable (fun s : Fin n → X => h i (s k)) := (hm i).comp (measurable_pi_apply k)
    have Vmeas : Measurable (Vf h l k i) := by
      unfold Vf
      exact (((Zk_meas h hm k).const_mul l).exp).mul ((hk.pow_const 2).sub (hk.const_mul 2))
    refine intOfBdd (Vmeas.indicator (Eset_meas h hm k i)) (Real.exp (2 * B) * 3) (fun s => ?_)
    by_cases hs : s ∈ Eset h k i
    · rw [Set.indicator_of_mem hs]
      unfold Vf
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have e1 : Real.exp (l * Zk h k s) ≤ Real.exp (2 * B) := Real.exp_le_exp.mpr
        (abs_le.mp (lZ_abs hl0 hl2 ⟨(Zk_mem h hb k s).1, (Zk_mem h hb k s).2⟩)).2
      have hh := abs_le.mp (hb i (s k))
      have e2 : |h i (s k) ^ 2 - 2 * h i (s k)| ≤ 3 := by
        rw [abs_le]; constructor <;> nlinarith
      exact mul_le_mul e1 e2 (abs_nonneg _) (Real.exp_pos _).le
    · simp only [Set.indicator, hs, if_false, abs_zero]; positivity
  have VsI : ∀ k, Integrable (fun s => ∑ i, (Eset h k i).indicator (Vf h l k i) s) μ := fun k =>
    integrable_finsetSum _ (fun i _ => VI k i)
  -- pointwise bound
  have hpt : ∀ s : Fin n → X, (4 + 4 * l - l ^ 2) * ∑ k, Wf h l k s ≤
      2 * l ^ 2 * (2 * (Zf h s * Real.exp (l * Zf h s)) +
        ∑ k, ∑ i, (Eset h k i).indicator (Vf h l k i) s) := by
    intro s
    have each : ∀ k, (4 + 4 * l - l ^ 2) * Wf h l k s ≤
        2 * l ^ 2 * (2 * (Zf h s - Zk h k s) * Real.exp (l * Zf h s) +
          ∑ i, (Eset h k i).indicator (Vf h l k i) s) := by
      intro k
      obtain ⟨i0, hi0, hsum⟩ := sum_ind h k s
      rw [hsum (fun i => Vf h l k i)]
      exact W_pointwise h hb l hl0 hl2 k s i0 hi0
    have hsY := sumY_le h hb s
    have hE := Real.exp_pos (l * Zf h s)
    have hl2' : 0 ≤ 2 * l ^ 2 := by positivity
    calc (4 + 4 * l - l ^ 2) * ∑ k, Wf h l k s = ∑ k, (4 + 4 * l - l ^ 2) * Wf h l k s :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ k, 2 * l ^ 2 * (2 * (Zf h s - Zk h k s) * Real.exp (l * Zf h s) +
            ∑ i, (Eset h k i).indicator (Vf h l k i) s) := Finset.sum_le_sum (fun k _ => each k)
      _ = 2 * l ^ 2 * (2 * (∑ k, (Zf h s - Zk h k s)) * Real.exp (l * Zf h s) +
            ∑ k, ∑ i, (Eset h k i).indicator (Vf h l k i) s) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hl2'
          have : (∑ k, (Zf h s - Zk h k s)) * Real.exp (l * Zf h s) ≤
              Zf h s * Real.exp (l * Zf h s) := mul_le_mul_of_nonneg_right hsY hE.le
          linarith
  -- variance terms
  have hV : ∀ k, ∑ i, ∫ s, (Eset h k i).indicator (Vf h l k i) s ∂μ ≤
      σ2 * ∫ s, Real.exp (l * Zf h s) ∂μ := by
    intro k
    have mK : Measurable (fun s : Fin n → X => Real.exp (l * Zk h k s)) :=
      ((Zk_meas h hm k).const_mul l).exp
    have KI : ∀ i, Integrable ((Eset h k i).indicator (fun s => Real.exp (l * Zk h k s))) μ := by
      intro i
      refine intOfBdd (mK.indicator (Eset_meas h hm k i)) (Real.exp (2 * B)) (fun s => ?_)
      by_cases hs : s ∈ Eset h k i
      · rw [Set.indicator_of_mem hs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr
          (abs_le.mp (lZ_abs hl0 hl2 ⟨(Zk_mem h hb k s).1, (Zk_mem h hb k s).2⟩)).2
      · simp only [Set.indicator, hs, if_false, abs_zero]; positivity
    calc ∑ i, ∫ s, (Eset h k i).indicator (Vf h l k i) s ∂μ
        ≤ ∑ i, σ2 * ∫ s, (Eset h k i).indicator (fun s => Real.exp (l * Zk h k s)) s ∂μ :=
          Finset.sum_le_sum (fun i _ => V_int P h hm hb σ2 hvar hmean l hl0 hl2 k i)
      _ = σ2 * ∫ s, ∑ i, (Eset h k i).indicator (fun s => Real.exp (l * Zk h k s)) s ∂μ := by
          rw [← Finset.mul_sum, integral_finsetSum _ (fun i _ => KI i)]
      _ = σ2 * ∫ s, Real.exp (l * Zk h k s) ∂μ := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          obtain ⟨i0, -, hsum⟩ := sum_ind h k s
          exact hsum (fun _ s => Real.exp (l * Zk h k s))
      _ ≤ σ2 * ∫ s, Real.exp (l * Zf h s) ∂μ :=
          mul_le_mul_of_nonneg_left (expZk_le P h hm hb hmean l hl0 hl2 k) hσ
  calc (4 + 4 * l - l ^ 2) * ent μ (fun s => Real.exp (l * Zf h s))
      ≤ (4 + 4 * l - l ^ 2) * ∑ k, ∫ s, Wf h l k s ∂μ := mul_le_mul_of_nonneg_left S1 hD
    _ = ∫ s, (4 + 4 * l - l ^ 2) * ∑ k, Wf h l k s ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ (fun k _ => WI k)]
    _ ≤ ∫ s, 2 * l ^ 2 * (2 * (Zf h s * Real.exp (l * Zf h s)) +
          ∑ k, ∑ i, (Eset h k i).indicator (Vf h l k i) s) ∂μ :=
        integral_mono ((integrable_finsetSum _ (fun k _ => WI k)).const_mul _)
          (((ZEI.const_mul 2).add (integrable_finsetSum _ (fun k _ => VsI k))).const_mul _) hpt
    _ = 2 * l ^ 2 * (2 * ∫ s, Zf h s * Real.exp (l * Zf h s) ∂μ +
          ∑ k, ∑ i, ∫ s, (Eset h k i).indicator (Vf h l k i) s ∂μ) := by
        rw [integral_const_mul, integral_add (ZEI.const_mul 2)
          (integrable_finsetSum _ (fun k _ => VsI k)), integral_const_mul,
          integral_finsetSum _ (fun k _ => VsI k)]
        congr 2
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact integral_finsetSum _ (fun i _ => VI k i)
    _ ≤ 2 * l ^ 2 * (2 * ∫ s, Zf h s * Real.exp (l * Zf h s) ∂μ +
          ∑ _k : Fin n, σ2 * ∫ s, Real.exp (l * Zf h s) ∂μ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hV k)
        linarith
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Integ2

/-! ### P6: cgf bound and the Bernstein-type tail -/
section P6

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
  {n N : ℕ} (h : Fin (N + 1) → X → ℝ) (hm : ∀ i, Measurable (h i)) (hb : ∀ i x, |h i x| ≤ 1)
include hm hb

theorem tail_finite (σ2 : ℝ) (hvar : ∀ i, ∫ x, h i x ^ 2 ∂P ≤ σ2)
    (hmean : ∀ i, ∫ x, h i x ∂P = 0) (t : ℝ) (ht : 0 < t)
    (hv : 0 < n * σ2 + 2 * ∫ s, Zf h s ∂(Measure.pi fun _ : Fin n => P)) :
    (Measure.pi fun _ : Fin n => P).real
      {s | (∫ s, Zf h s ∂(Measure.pi fun _ : Fin n => P)) +
          Real.sqrt (2 * (n * σ2 + 2 * ∫ s, Zf h s ∂(Measure.pi fun _ : Fin n => P)) * t) + t / 2
        ≤ Zf h s} ≤ Real.exp (-t) := by
  set μ := Measure.pi fun _ : Fin n => P with hμ
  set m := ∫ s, Zf h s ∂μ with hmdef
  set v := n * σ2 + 2 * m with hvdef
  set B : ℝ := (n : ℝ) + 1 with hB
  have mZ : Measurable (fun s : Fin n → X => Zf h s) := Zf_meas h hm
  have hZb : ∀ s, |Zf h s| ≤ B := fun s => abs_le.mpr (Zf_mem h hb s)
  have hB0 : 0 ≤ B := by positivity
  have hint : ∀ l : ℝ, Integrable (fun s => Real.exp (l * Zf h s)) μ := by
    intro l
    refine intOfBdd (mZ.const_mul l).exp (Real.exp (|l| * B)) (fun s => ?_)
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc l * Zf h s ≤ |l * Zf h s| := le_abs_self _
      _ = |l| * |Zf h s| := abs_mul _ _
      _ ≤ |l| * B := mul_le_mul_of_nonneg_left (hZb s) (abs_nonneg _)
  have hset : integrableExpSet (fun s => Zf h s) μ = Set.univ := by
    ext l; simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hint l
  set F : ℝ → ℝ := fun l => mgf (fun s => Zf h s) μ l with hFdef
  set F1 : ℝ → ℝ := fun l => ∫ s, Zf h s * Real.exp (l * Zf h s) ∂μ with hF1def
  have hFd : ∀ l, HasDerivAt F (F1 l) l := by
    intro l
    have := hasDerivAt_mgf (X := fun s => Zf h s) (μ := μ) (t := l) (by rw [hset]; simp)
    exact this
  have hFpos : ∀ l, 0 < F l := fun l => mgf_pos (hint l)
  have hF0 : F 0 = 1 := by simp [hFdef, mgf_zero]
  have hF10 : F1 0 = m := by simp [hF1def, hmdef]
  set G : ℝ → ℝ := fun l => Real.log (F l) - l * m with hGdef
  set G' : ℝ → ℝ := fun l => F1 l / F l - m with hG'def
  have hd : ∀ l, 0 ≤ l → l < 2 → HasDerivAt G (G' l) l := by
    intro l _ _
    have := ((hFd l).log (hFpos l).ne').sub ((hasDerivAt_id l).mul_const m)
    refine this.congr_deriv ?_
    simp [hG'def]
  have hG0 : G 0 = 0 := by simp [hGdef, hF0]
  have hG'0 : G' 0 = 0 := by simp [hG'def, hF0, hF10]
  have hineq : ∀ l, 0 < l → l < 2 →
      l * (4 - l ^ 2) * G' l - (4 + 4 * l - l ^ 2) * G l ≤ 2 * l ^ 2 * v := by
    intro l hl0 hl2
    have key := bousquet_ent (n := n) P h hm hb σ2 hvar hmean l hl0.le hl2.le
    have hent : ent μ (fun s => Real.exp (l * Zf h s)) = l * F1 l - F l * Real.log (F l) := by
      unfold ent
      simp only [Real.log_exp, hF1def, hFdef, mgf]
      rw [← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only; ring
    rw [hent] at key
    have r1 : ∫ s, Zf h s * Real.exp (l * Zf h s) ∂μ = F1 l := rfl
    have r2 : ∫ s, Real.exp (l * Zf h s) ∂μ = F l := rfl
    rw [r1, r2] at key
    have hFp := hFpos l
    set D := 4 + 4 * l - l ^ 2 with hD
    have e : l * (4 - l ^ 2) * G' l - D * G l =
        (D * (l * F1 l - F l * Real.log (F l)) - 4 * l ^ 2 * F1 l) / F l + 4 * l ^ 2 * m := by
      simp only [hG'def, hGdef, hD]
      field_simp
      ring
    have h1 : (D * (l * F1 l - F l * Real.log (F l)) - 4 * l ^ 2 * F1 l) / F l ≤
        (2 * l ^ 2 * (2 * F1 l + n * σ2 * F l) - 4 * l ^ 2 * F1 l) / F l :=
      div_le_div_of_nonneg_right (by linarith) hFp.le
    have h2 : (2 * l ^ 2 * (2 * F1 l + n * σ2 * F l) - 4 * l ^ 2 * F1 l) / F l =
        2 * l ^ 2 * (n * σ2) := by
      field_simp; ring
    rw [e]
    simp only [hvdef]
    nlinarith
  have hode := ode_bound G G' v hG0 hd hG'0 hineq
  -- Chernoff at l = w / (v + w/2)
  set w := Real.sqrt (2 * v * t) with hw
  have hw0 : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w ^ 2 = 2 * v * t := Real.sq_sqrt (by positivity)
  set l := w / (v + w / 2) with hl
  have hl0 : 0 < l := by positivity
  have hl2 : l < 2 := by
    rw [hl, div_lt_iff₀ (by positivity)]; linarith
  have hch := measure_ge_le_exp_mul_mgf (X := fun s => Zf h s) (μ := μ)
    (m + w + t / 2) hl0.le (hint l)
  have hGl := hode l hl0.le hl2
  have hFl : F l = Real.exp (G l + l * m) := by
    simp only [hGdef]; rw [sub_add_cancel, Real.exp_log (hFpos l)]
  calc μ.real {s | m + w + t / 2 ≤ Zf h s}
      ≤ Real.exp (-l * (m + w + t / 2)) * F l := hch
    _ = Real.exp (G l - l * (w + t / 2)) := by
        rw [hFl, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (v * l ^ 2 / (2 - l) - l * (w + t / 2)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = Real.exp (-t) := by
        congr 1
        have h2l : 2 - l = 2 * v / (v + w / 2) := by
          rw [hl]; field_simp; ring
        rw [h2l, hl]
        field_simp
        nlinarith [hw2]

end P6

end Bq857

namespace P82cd

lemma int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma abs_integral_le_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : |∫ x, F x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Real.norm_eq_abs] using this

/-- Hoeffding step: a measurable function with oscillation at most `c`. -/
lemma hoeff_step {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (G : Ω → ℝ) (hG : Measurable G) (c B : ℝ) (hc : 0 ≤ c) (hB : ∀ z, |G z| ≤ B)
    (hosc : ∀ z z', G z' - G z ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 8 * t ^ 2) := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  have hbdd : BddBelow (Set.range G) := ⟨-B, by
    rintro _ ⟨z, rfl⟩; have := hB z; rw [abs_le] at this; linarith⟩
  set A := ⨅ z, G z with hA
  have hmem : ∀ z, G z ∈ Set.Icc A (A + c) := by
    intro z
    refine ⟨ciInf_le hbdd z, ?_⟩
    have : G z - c ≤ A := le_ciInf fun z' => by have := hosc z' z; linarith
    linarith
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := G) (a := A) (b := A + c)
    hG.aemeasurable (Filter.Eventually.of_forall hmem)
  have h1 := hs.mgf_le t
  have hcoe : (((‖(A + c) - A‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 / 4 := by
    have : (A + c) - A = c := by ring
    rw [this]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rw [hcoe] at h1
  unfold mgf at h1
  calc ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 4 * t ^ 2 / 2) := h1
    _ = Real.exp (c ^ 2 / 8 * t ^ 2) := by ring_nf


end P82cd

namespace F198

open P82cd

lemma bdd_of_abs {T : Type*} (f : T → ℝ) (B : ℝ) (hf : ∀ τ, |f τ| ≤ B) :
    BddAbove (Set.range f) :=
  ⟨B, by rintro _ ⟨τ, rfl⟩; exact (le_abs_self _).trans (hf τ)⟩

lemma abs_iSup_le {T : Type*} [Nonempty T] (f : T → ℝ) (B : ℝ) (hf : ∀ τ, |f τ| ≤ B) :
    |⨆ τ, f τ| ≤ B := by
  obtain ⟨τ0⟩ := ‹Nonempty T›
  rw [abs_le]; constructor
  · have h1 := le_ciSup (bdd_of_abs f B hf) τ0
    have h2 := (abs_le.mp (hf τ0)).1
    linarith
  · exact ciSup_le fun τ => (le_abs_self _).trans (hf τ)

lemma iSup_le_iSup_add {T : Type*} [Nonempty T] (f g : T → ℝ) (B c : ℝ)
    (hg : ∀ τ, |g τ| ≤ B) (hfg : ∀ τ, f τ ≤ g τ + c) : ⨆ τ, f τ ≤ (⨆ τ, g τ) + c :=
  ciSup_le fun τ => (hfg τ).trans (by have := le_ciSup (bdd_of_abs g B hg) τ; linarith)

lemma abs_iSup_sub_le {T : Type*} [Nonempty T] (f g : T → ℝ) (B c : ℝ)
    (hf : ∀ τ, |f τ| ≤ B) (hg : ∀ τ, |g τ| ≤ B) (hfg : ∀ τ, |f τ - g τ| ≤ c) :
    |(⨆ τ, f τ) - ⨆ τ, g τ| ≤ c := by
  have h1 := iSup_le_iSup_add f g B c hg fun τ => by have := (abs_le.mp (hfg τ)).2; linarith
  have h2 := iSup_le_iSup_add g f B c hf fun τ => by have := (abs_le.mp (hfg τ)).1; linarith
  rw [abs_le]; constructor <;> linarith

lemma avg_abs_le {n : ℕ} (a : Fin n → ℝ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, |a i| ≤ K) :
    |(n : ℝ)⁻¹ * ∑ i, a i| ≤ K := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [hK]
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  rw [abs_mul, abs_inv, abs_of_pos hn]
  have : |∑ i, a i| ≤ n * K := by
    calc |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, K := Finset.sum_le_sum fun i _ => ha i
      _ = n * K := by simp
  calc (n : ℝ)⁻¹ * |∑ i, a i| ≤ (n : ℝ)⁻¹ * (n * K) := by gcongr
    _ = K := by field_simp

lemma signVec_abs {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : |UnderstandingML.signVec σ i| = 1 := by
  unfold UnderstandingML.signVec; split_ifs <;> simp

lemma signVec_not {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    UnderstandingML.signVec (fun j => !σ j) i = -UnderstandingML.signVec σ i := by
  unfold UnderstandingML.signVec; cases h : σ i <;> simp [h]

lemma sum_sign_abs {n : ℕ} (σ : Fin n → Bool) (a : Fin n → ℝ) (K : ℝ) (ha : ∀ i, |a i| ≤ K) :
    |∑ i, UnderstandingML.signVec σ i * a i| ≤ n * K := by
  calc |∑ i, UnderstandingML.signVec σ i * a i| ≤ ∑ i, |UnderstandingML.signVec σ i * a i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, K := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, signVec_abs, one_mul]; exact ha i
    _ = n * K := by simp


section Sym

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
  {T : Type*} [Countable T] [Nonempty T]

theorem mean_eq (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ x, |g x| ≤ M) (n : ℕ)
    (hn : 0 < n) :
    ∫ x, g x ∂P = ∫ s, (n : ℝ)⁻¹ * ∑ i, g (s i) ∂(Measure.pi fun _ : Fin n => P) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [integral_const_mul, integral_finset_sum]
  · have : ∀ i : Fin n, ∫ s, g (s i) ∂(Measure.pi fun _ : Fin n => P) = ∫ x, g x ∂P := by
      intro i
      have h := (measurePreserving_eval (fun _ : Fin n => P) i)
      have := integral_map (μ := Measure.pi fun _ : Fin n => P) h.measurable.aemeasurable
        hg.aestronglyMeasurable
      rw [h.map_eq] at this
      exact this.symm
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro i _
    exact int_of_bdd _ _ (hg.comp (measurable_pi_apply i)) M fun s => hM (s i)

theorem sym (g : T → X → ℝ) (hg : ∀ τ, Measurable (g τ)) (M : ℝ) (hM : ∀ τ x, |g τ x| ≤ M)
    (n : ℕ) (hn : 0 < n) :
    ∫ s, (⨆ τ, (∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i))) ∂(Measure.pi fun _ : Fin n => P)
      ≤ 2 * ∫ s, (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ : Fin n → Bool,
          ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)) ∂(Measure.pi fun _ : Fin n => P) := by
  classical
  set π := Measure.pi fun _ : Fin n => P with hπ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : 0 ≤ M := by
    obtain ⟨τ⟩ := ‹Nonempty T›
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (abs_nonneg _).trans (hM τ x)
  have hem : ∀ τ (s : Fin n → X), |(n : ℝ)⁻¹ * ∑ i, g τ (s i)| ≤ M :=
    fun τ s => avg_abs_le _ M hM0 fun i => hM τ (s i)
  have hemm : ∀ τ, Measurable fun s : Fin n → X => (n : ℝ)⁻¹ * ∑ i, g τ (s i) := fun τ =>
    measurable_const.mul (Finset.measurable_sum _ fun i _ => (hg τ).comp (measurable_pi_apply i))
  have hmu : ∀ τ, |∫ x, g τ x ∂P| ≤ M := fun τ => abs_integral_le_of_bdd P _ M (hM τ)
  -- the supremum Z
  set Z : (Fin n → X) → ℝ := fun s => ⨆ τ, (∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i))
    with hZ
  have hZm : Measurable Z := Measurable.iSup fun τ => measurable_const.sub (hemm τ)
  have hZb : ∀ s, |Z s| ≤ 2 * M := fun s => abs_iSup_le _ _ fun τ => by
    have h1 := hmu τ; have h2 := hem τ s
    rw [abs_le] at *; constructor <;> linarith
  -- the symmetrized supremum W
  set W : (Fin n → X) × (Fin n → X) → ℝ :=
    fun p => ⨆ τ, ((n : ℝ)⁻¹ * ∑ i, g τ (p.2 i) - (n : ℝ)⁻¹ * ∑ i, g τ (p.1 i)) with hW
  have hWt : ∀ τ (p : (Fin n → X) × (Fin n → X)),
      |(n : ℝ)⁻¹ * ∑ i, g τ (p.2 i) - (n : ℝ)⁻¹ * ∑ i, g τ (p.1 i)| ≤ 2 * M := by
    intro τ p
    have h1 := hem τ p.2; have h2 := hem τ p.1
    rw [abs_le] at *; constructor <;> linarith
  have hWm : Measurable W :=
    Measurable.iSup fun τ => ((hemm τ).comp measurable_snd).sub ((hemm τ).comp measurable_fst)
  have hWb : ∀ p, |W p| ≤ 2 * M := fun p => abs_iSup_le _ _ fun τ => hWt τ p
  have hWint : Integrable W (π.prod π) := int_of_bdd _ _ hWm _ hWb
  -- Step 1
  have hstep1 : ∀ s, Z s ≤ ∫ s', W (s, s') ∂π := by
    intro s
    apply ciSup_le
    intro τ
    calc ∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i)
        = ∫ s', ((n : ℝ)⁻¹ * ∑ i, g τ (s' i) - (n : ℝ)⁻¹ * ∑ i, g τ (s i)) ∂π := by
          rw [mean_eq P (g τ) (hg τ) M (hM τ) n hn, integral_sub
            (int_of_bdd _ _ (hemm τ) M (hem τ)) (integrable_const _), integral_const]
          simp [hπ]
      _ ≤ ∫ s', W (s, s') ∂π := by
          refine integral_mono (int_of_bdd _ _ ((hemm τ).sub measurable_const) (2 * M)
            fun s' => hWt τ (s, s')) (int_of_bdd _ _ (hWm.comp (measurable_const.prodMk
              measurable_id)) (2 * M) fun s' => hWb (s, s')) fun s' => ?_
          exact le_ciSup (bdd_of_abs _ _ fun τ => hWt τ (s, s')) τ
  have hstep2 : ∫ s, Z s ∂π ≤ ∫ p, W p ∂(π.prod π) := by
    rw [integral_prod W hWint]
    exact integral_mono (int_of_bdd _ _ hZm _ hZb) hWint.integral_prod_left hstep1
  -- Step 3: sign swaps
  set e := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n) with he
  have hE : MeasurePreserving e (Measure.pi fun _ : Fin n => P.prod P) (π.prod π) :=
    measurePreserving_arrowProdEquivProdArrow X X (Fin n) (fun _ => P) (fun _ => P)
  set Φ : (Fin n → Bool) → (Fin n → X) × (Fin n → X) → (Fin n → X) × (Fin n → X) :=
    fun σ p => (fun i => if σ i then p.1 i else p.2 i, fun i => if σ i then p.2 i else p.1 i)
    with hΦ
  have hΦmp : ∀ σ, MeasurePreserving (Φ σ) (π.prod π) (π.prod π) := by
    intro σ
    have hpi : MeasurePreserving (fun (w : Fin n → X × X) i => if σ i then w i else (w i).swap)
        (Measure.pi fun _ : Fin n => P.prod P) (Measure.pi fun _ : Fin n => P.prod P) := by
      refine measurePreserving_pi (fun _ => P.prod P) (fun _ => P.prod P)
        (f := fun i (q : X × X) => if σ i then q else q.swap) fun i => ?_
      by_cases h : σ i = true
      · simp only [h, if_true]; exact MeasurePreserving.id _
      · simp only [h]; exact Measure.measurePreserving_swap
    have hcomp := hE.comp (hpi.comp (hE.symm e))
    have heq : Φ σ = e ∘ (fun (w : Fin n → X × X) i => if σ i then w i else (w i).swap) ∘ e.symm := by
      funext p
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        by_cases h : σ i = true <;>
        simp [Φ, h, e, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    rw [heq]; exact hcomp
  have hWΦ : ∀ σ p, W (Φ σ p) = ⨆ τ, ((n : ℝ)⁻¹ *
      ∑ i, UnderstandingML.signVec σ i * (g τ (p.2 i) - g τ (p.1 i))) := by
    intro σ p
    simp only [W, Φ]
    congr 1; funext τ
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold UnderstandingML.signVec
    by_cases h : σ i = true <;> simp [h]
  have hstep3 : ∫ p, W p ∂(π.prod π) =
      ∫ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ∂(π.prod π) := by
    have hint : ∀ σ, Integrable (fun p => W (Φ σ p)) (π.prod π) := fun σ =>
      int_of_bdd _ _ (hWm.comp (hΦmp σ).measurable) _ fun p => hWb _
    rw [integral_const_mul, integral_finset_sum _ fun σ _ => hint σ]
    have : ∀ σ, ∫ p, W (Φ σ p) ∂(π.prod π) = ∫ p, W p ∂(π.prod π) := by
      intro σ
      have h := integral_map (μ := π.prod π) (hΦmp σ).measurable.aemeasurable
        hWm.aestronglyMeasurable
      rw [(hΦmp σ).map_eq] at h
      exact h.symm
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  -- Step 4: pointwise bound
  set U : (Fin n → Bool) → (Fin n → X) → ℝ :=
    fun σ s => ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i) with hU
  have hUt : ∀ σ τ (s : Fin n → X), |∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M :=
    fun σ τ s => sum_sign_abs σ _ M fun i => hM τ (s i)
  set R : (Fin n → X) → ℝ := fun s => (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ, U σ s) with hR
  have hRm : Measurable R := by
    refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun σ _ => ?_))
    exact Measurable.iSup fun τ => Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((hg τ).comp (measurable_pi_apply i))
  have hUb : ∀ σ s, |U σ s| ≤ n * M := fun σ s => abs_iSup_le _ _ fun τ => hUt σ τ s
  have hRb : ∀ s, |R s| ≤ M := by
    intro s
    simp only [R]
    have h2 : |(1 / 2 ^ n : ℝ) * ∑ σ, U σ s| ≤ n * M := by
      rw [abs_mul, abs_of_pos (by positivity)]
      calc (1 / 2 ^ n : ℝ) * |∑ σ, U σ s| ≤ (1 / 2 ^ n) * ∑ σ : Fin n → Bool, |U σ s| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (1 / 2 ^ n) * ∑ _σ : Fin n → Bool, (n * M) := by
            gcongr with σ; exact hUb σ s
        _ = n * M := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; field_simp
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (n : ℝ) * |(1 / 2 ^ n : ℝ) * ∑ σ, U σ s| ≤ 1 / n * (n * M) := by gcongr
      _ = M := by field_simp
  have hnot : ∀ s, ∑ σ : Fin n → Bool, U (fun j => !σ j) s = ∑ σ, U σ s := by
    intro s
    refine Fintype.sum_equiv ⟨fun σ j => !σ j, fun σ j => !σ j, fun σ => by funext j; simp,
      fun σ => by funext j; simp⟩ _ _ fun σ => rfl
  have hstep4 : ∀ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ≤ R p.2 + R p.1 := by
    intro p
    have hb : ∀ σ, W (Φ σ p) ≤ (n : ℝ)⁻¹ * U σ p.2 + (n : ℝ)⁻¹ * U (fun j => !σ j) p.1 := by
      intro σ
      rw [hWΦ]
      refine ciSup_le fun τ => ?_
      have hsplit : (n : ℝ)⁻¹ * ∑ i, UnderstandingML.signVec σ i * (g τ (p.2 i) - g τ (p.1 i)) =
          (n : ℝ)⁻¹ * ∑ i, UnderstandingML.signVec σ i * g τ (p.2 i) +
          (n : ℝ)⁻¹ * ∑ i, UnderstandingML.signVec (fun j => !σ j) i * g τ (p.1 i) := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [signVec_not]; ring
      rw [hsplit]
      have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnpos.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_ciSup (bdd_of_abs _ _ fun τ => hUt σ τ p.2) τ) hinv)
        (mul_le_mul_of_nonneg_left
          (le_ciSup (bdd_of_abs _ _ fun τ => hUt (fun j => !σ j) τ p.1) τ) hinv)
    calc (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p)
        ≤ (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
            ((n : ℝ)⁻¹ * U σ p.2 + (n : ℝ)⁻¹ * U (fun j => !σ j) p.1) := by
          gcongr with σ; exact hb σ
      _ = R p.2 + R p.1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnot]
          simp only [R]; ring
  -- Step 5
  have hRint : Integrable R π := int_of_bdd _ _ hRm M hRb
  have hfst : ∫ p, R p.1 ∂(π.prod π) = ∫ s, R s ∂π := by
    have h := integral_map (μ := π.prod π) (measurePreserving_fst (μ := π) (ν := π)).measurable.aemeasurable
      hRm.aestronglyMeasurable
    rw [(measurePreserving_fst (μ := π) (ν := π)).map_eq] at h
    exact h.symm
  have hsnd : ∫ p, R p.2 ∂(π.prod π) = ∫ s, R s ∂π := by
    have h := integral_map (μ := π.prod π) (measurePreserving_snd (μ := π) (ν := π)).measurable.aemeasurable
      hRm.aestronglyMeasurable
    rw [(measurePreserving_snd (μ := π) (ν := π)).map_eq] at h
    exact h.symm
  have hstep5 : ∫ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ∂(π.prod π) ≤
      2 * ∫ s, R s ∂π := by
    have hi1 : Integrable (fun p : (Fin n → X) × (Fin n → X) => R p.2) (π.prod π) :=
      int_of_bdd _ _ (hRm.comp measurable_snd) M fun p => hRb _
    have hi2 : Integrable (fun p : (Fin n → X) × (Fin n → X) => R p.1) (π.prod π) :=
      int_of_bdd _ _ (hRm.comp measurable_fst) M fun p => hRb _
    calc ∫ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ∂(π.prod π)
        ≤ ∫ p, (R p.2 + R p.1) ∂(π.prod π) := by
          refine integral_mono ?_ (hi1.add hi2) hstep4
          refine Integrable.const_mul ?_ _
          exact integrable_finset_sum _ fun σ _ =>
            int_of_bdd _ _ (hWm.comp (hΦmp σ).measurable) _ fun p => hWb _
      _ = 2 * ∫ s, R s ∂π := by
          rw [integral_add hi1 hi2, hfst, hsnd]; ring
  calc ∫ s, Z s ∂π ≤ ∫ p, W p ∂(π.prod π) := hstep2
    _ = _ := hstep3
    _ ≤ 2 * ∫ s, R s ∂π := hstep5

end Sym

end F198

namespace F198

open P82cd

theorem rad_int {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {T : Type*} [Countable T] [Nonempty T]
    (g : T → X → ℝ) (hg : ∀ τ, Measurable (g τ)) (M : ℝ) (hM : ∀ τ x, |g τ x| ≤ M)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun s : Fin n → X => (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ : Fin n → Bool,
          ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i))) (Measure.pi fun _ : Fin n => P) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hUt : ∀ σ τ (s : Fin n → X), |∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M :=
    fun σ τ s => sum_sign_abs σ _ M fun i => hM τ (s i)
  have hUb : ∀ σ (s : Fin n → X), |⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M :=
    fun σ s => abs_iSup_le _ _ fun τ => hUt σ τ s
  refine int_of_bdd _ _ ?_ M fun s => ?_
  · refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun σ _ => ?_))
    exact Measurable.iSup fun τ => Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((hg τ).comp (measurable_pi_apply i))
  · have h2 : |(1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M := by
      rw [abs_mul, abs_of_pos (by positivity)]
      calc (1 / 2 ^ n : ℝ) * |∑ σ : Fin n → Bool,
            ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)|
          ≤ (1 / 2 ^ n) * ∑ σ : Fin n → Bool,
            |⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (1 / 2 ^ n) * ∑ _σ : Fin n → Bool, (n * M) := by
            gcongr with σ; exact hUb σ s
        _ = n * M := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; field_simp
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (n : ℝ) * |(1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
          ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ 1 / n * (n * M) := by gcongr
      _ = M := by field_simp

end F198

namespace Bq857

/-! ### P7: countable class, both tails (C1') -/
section P7

open VarianceRegularization.Localized

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]

lemma sqrt_split (A m t α : ℝ) (hA : 0 ≤ A) (hm : 0 ≤ m) (ht : 0 < t) (hα : 0 < α) :
    Real.sqrt (A ^ 2 + 4 * m * t) ≤ A + α * m + t / α := by
  have hw : 4 * m * t ≤ (α * m + t / α) ^ 2 := by
    have h1 : α * m * (t / α) = m * t := by field_simp
    nlinarith [sq_nonneg (α * m - t / α)]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have : 0 ≤ A * (α * m + t / α) := by positivity
  nlinarith

theorem core_tail (n : ℕ) (hn : 0 < n) (e : ℕ → X → ℝ) (hme : ∀ i, Measurable (e i))
    (M : ℝ) (hM : ∀ i x, |e i x| ≤ M)
    (U r t α R : ℝ) (hU : 0 < U) (hr : 0 < r) (ht : 0 < t) (hα : 0 < α)
    (hosc : ∀ i x, |e i x - ∫ y, e i y ∂P| ≤ U)
    (hvar : ∀ i, ∫ x, (e i x - ∫ y, e i y ∂P) ^ 2 ∂P ≤ r)
    (hR : ∀ N : ℕ, ∫ s, (⨆ i : Fin (N + 1), (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j)))
        ∂(Measure.pi fun _ : Fin n => P) ≤ 2 * R) :
    (Measure.pi fun _ : Fin n => P)
        {s | ∃ i, 2 * (1 + α) * R + Real.sqrt (2 * r * t / n) + t / n * U * (1 / 2 + 1 / α)
            < (∫ x, e i x ∂P) - (n : ℝ)⁻¹ * ∑ j, e i (s j)}
        ≤ ENNReal.ofReal (Real.exp (-t)) := by
  set μ := Measure.pi fun _ : Fin n => P with hμ
  set thr := 2 * (1 + α) * R + Real.sqrt (2 * r * t / n) + t / n * U * (1 / 2 + 1 / α)
    with hthr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : 0 ≤ M := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (abs_nonneg _).trans (hM 0 x)
  set E : ℕ → Set (Fin n → X) := fun N =>
    {s | ∃ i : Fin (N + 1), thr < (∫ x, e i x ∂P) - (n : ℝ)⁻¹ * ∑ j, e i (s j)} with hE
  have hmono : Monotone E := by
    intro N N' hNN s hs
    obtain ⟨i, hi⟩ := hs
    exact ⟨⟨i.1, by omega⟩, hi⟩
  have hU' : {s | ∃ i, thr < (∫ x, e i x ∂P) - (n : ℝ)⁻¹ * ∑ j, e i (s j)} = ⋃ N, E N := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hE]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, ⟨i, by omega⟩, hi⟩
    · rintro ⟨N, i, hi⟩
      exact ⟨i, hi⟩
  have key : ∀ N, μ (E N) ≤ ENNReal.ofReal (Real.exp (-t)) := by
    intro N
    set h : Fin (N + 1) → X → ℝ := fun i x => ((∫ y, e i y ∂P) - e i x) / U with hh
    have hm : ∀ i, Measurable (h i) := fun i => (measurable_const.sub (hme i)).div_const U
    have hb : ∀ i x, |h i x| ≤ 1 := by
      intro i x
      simp only [hh]
      rw [abs_div, abs_of_pos hU, div_le_one hU, abs_sub_comm]
      exact hosc i x
    have hie : ∀ i, Integrable (e i) P := fun i => P82cd.int_of_bdd P _ (hme i) M (hM i)
    have hmean : ∀ i, ∫ x, h i x ∂P = 0 := by
      intro i
      simp only [hh]
      rw [integral_div, integral_sub (integrable_const _) (hie i)]
      simp
    have hvar' : ∀ i, ∫ x, h i x ^ 2 ∂P ≤ r / U ^ 2 := by
      intro i
      have : ∀ x, h i x ^ 2 = (e i x - ∫ y, e i y ∂P) ^ 2 / U ^ 2 := by
        intro x; simp only [hh]; rw [div_pow]; ring
      simp_rw [this]
      rw [integral_div]
      exact div_le_div_of_nonneg_right (hvar i) (by positivity)
    set D : (Fin n → X) → ℝ := fun s =>
      ⨆ i : Fin (N + 1), (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j)) with hD
    have hval : ∀ (s : Fin n → X) i, val h s i = (n / U) * (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j)) := by
      intro s i
      simp only [val, hh]
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hZD : ∀ s, Zf h s = (n / U) * D s := by
      intro s
      obtain ⟨i0, hi0⟩ := Zf_attained h s
      apply le_antisymm
      · rw [hi0, hval]
        gcongr
        exact le_ciSup (f := fun i : Fin (N + 1) =>
          (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j))) (Set.finite_range _).bddAbove i0
      · have h1 : D s ≤ U / n * Zf h s := by
          apply ciSup_le
          intro i
          have := val_le_Zf h s i
          rw [hval] at this
          calc (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j))
              = U / n * ((n / U) * (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j))) := by
                field_simp
            _ ≤ U / n * Zf h s := by gcongr
        calc (n / U) * D s ≤ (n / U) * (U / n * Zf h s) := by gcongr
          _ = Zf h s := by field_simp
    have hZm : Measurable (fun s : Fin n → X => Zf h s) := Zf_meas h hm
    have hZi : Integrable (fun s : Fin n → X => Zf h s) μ :=
      P82cd.int_of_bdd μ _ hZm ((n : ℝ) + 1) fun s => abs_le.mpr (Zf_mem h hb s)
    set m := ∫ s, Zf h s ∂μ with hmdef
    have hmD : m = (n / U) * ∫ s, D s ∂μ := by
      rw [hmdef, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hZD)
    have hm_le : m ≤ (n / U) * (2 * R) := by
      rw [hmD]; gcongr; exact hR N
    have hm0 : 0 ≤ m := by
      have hAm : Measurable (fun s : Fin n → X => (n : ℝ)⁻¹ * ∑ j, e 0 (s j)) :=
        (Finset.measurable_sum _ fun j _ => (hme 0).comp (measurable_pi_apply j)).const_mul _
      have hAi : Integrable (fun s : Fin n → X => (n : ℝ)⁻¹ * ∑ j, e 0 (s j)) μ :=
        P82cd.int_of_bdd μ _ hAm M fun s => F198.avg_abs_le _ M hM0 fun j => hM 0 (s j)
      have h0 : ∫ s, (n / U) * (∫ x, e 0 x ∂P - (n : ℝ)⁻¹ * ∑ j, e 0 (s j)) ∂μ = 0 := by
        rw [integral_const_mul, integral_sub (integrable_const _) hAi,
          ← F198.mean_eq P (e 0) (hme 0) M (hM 0) n hn]
        simp
      rw [← h0]
      refine integral_mono (((integrable_const _).sub hAi).const_mul _) hZi fun s => ?_
      have := val_le_Zf h s 0
      rw [hval] at this
      exact this
    have hv : 0 < (n : ℝ) * (r / U ^ 2) + 2 * m := by
      have : 0 < (n : ℝ) * (r / U ^ 2) := by positivity
      linarith
    have htail := tail_finite P h hm hb (n := n) (r / U ^ 2) hvar' hmean t ht hv
    rw [← hmdef] at htail
    -- the event inclusion
    have hsub : E N ⊆ {s | m + Real.sqrt (2 * ((n : ℝ) * (r / U ^ 2) + 2 * m) * t) + t / 2
        ≤ Zf h s} := by
      intro s hs
      obtain ⟨i, hi⟩ := hs
      have hiD : thr < D s := lt_of_lt_of_le hi (le_ciSup (f := fun i : Fin (N + 1) =>
          (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j))) (Set.finite_range _).bddAbove i)
      rw [Set.mem_setOf_eq, hZD]
      set A := (n / U) * Real.sqrt (2 * r * t / n) with hA
      have hA0 : 0 ≤ A := by positivity
      have hA2 : A ^ 2 = 2 * ((n : ℝ) * (r / U ^ 2)) * t := by
        rw [hA, mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      have hsq : Real.sqrt (2 * ((n : ℝ) * (r / U ^ 2) + 2 * m) * t) ≤ A + α * m + t / α := by
        have := sqrt_split A m t α hA0 hm0 ht hα
        have e1 : 2 * ((n : ℝ) * (r / U ^ 2) + 2 * m) * t = A ^ 2 + 4 * m * t := by
          rw [hA2]; ring
        rw [e1]; exact this
      have hthr' : (n / U) * thr = 2 * (1 + α) * ((n / U) * R) + A + (t / 2 + t / α) := by
        rw [hthr, hA]
        field_simp
      have hmR : m ≤ 2 * ((n / U) * R) := by linarith [hm_le]
      have hpos : 0 < (n : ℝ) / U := by positivity
      have := mul_lt_mul_of_pos_left hiD hpos
      nlinarith
    have hfin : μ {s | m + Real.sqrt (2 * ((n : ℝ) * (r / U ^ 2) + 2 * m) * t) + t / 2
        ≤ Zf h s} = ENNReal.ofReal (μ.real {s | m + Real.sqrt (2 * ((n : ℝ) * (r / U ^ 2)
          + 2 * m) * t) + t / 2 ≤ Zf h s}) := (ofReal_measureReal).symm
    calc μ (E N) ≤ _ := measure_mono hsub
      _ = _ := hfin
      _ ≤ ENNReal.ofReal (Real.exp (-t)) := ENNReal.ofReal_le_ofReal htail
  rw [hU', hmono.measure_iUnion]
  exact iSup_le key

end P7

end Bq857

namespace BB227DF6

lemma sum_bound {n : ℕ} (σ : Fin n → Bool) (v : Fin n → ℝ) (M : ℝ)
    (hv : ∀ i, |v i| ≤ M) :
    |∑ i, UnderstandingML.signVec σ i * v i| ≤ n * M := by
  calc |∑ i, UnderstandingML.signVec σ i * v i|
      ≤ ∑ i, |UnderstandingML.signVec σ i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, M := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have h1 : |UnderstandingML.signVec σ i| = 1 := by
          unfold UnderstandingML.signVec; split_ifs <;> simp
        rw [h1, one_mul]; exact hv i
    _ = n * M := by simp

lemma iSup_abs_bound {ι : Sort*} (f : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, |f i| ≤ C) :
    |⨆ i, f i| ≤ C := by
  rw [abs_le]
  constructor
  · rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Real.iSup_of_isEmpty]; linarith
    · obtain ⟨i⟩ := hι
      have hb : BddAbove (Set.range f) := ⟨C, by
        rintro _ ⟨j, rfl⟩; exact (abs_le.mp (hf j)).2⟩
      exact le_ciSup_of_le hb i (abs_le.mp (hf i)).1
  · exact Real.iSup_le (fun i => (abs_le.mp (hf i)).2) hC

lemma iSup_subset_mono {n : ℕ} (A A' : Set (Fin n → ℝ)) (hAA : A ⊆ A') (hA : A.Nonempty)
    (φ : (Fin n → ℝ) → ℝ) (hb : BddAbove (Set.range fun a : A' => φ a)) :
    (⨆ a : A, φ a) ≤ ⨆ a : A', φ a := by
  have : Nonempty A := hA.to_subtype
  apply ciSup_le
  intro a
  exact le_ciSup_of_le hb ⟨a.1, hAA a.2⟩ le_rfl

lemma iSup_evalSet {X : Type*} {n : ℕ} (G : Set (X → ℝ)) (s : Fin n → X)
    (φ : (Fin n → ℝ) → ℝ) :
    (⨆ a : UnderstandingML.evalSet G s, φ a) = ⨆ g : G, φ (fun i => (g : X → ℝ) (s i)) := by
  show sSup (Set.range _) = sSup (Set.range _)
  congr 1
  ext y
  constructor
  · rintro ⟨⟨v, f, hf, rfl⟩, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact ⟨⟨_, f, hf, rfl⟩, rfl⟩

end BB227DF6

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized LocalRademacher.StarHull in
theorem sib_tgRad {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFc : F.Countable)
    (hmeas : ∀ f ∈ F, Measurable f) (a b : ℝ) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a b)
    (T : (X → ℝ) → ℝ) (B : ℝ) (hB : 0 < B) (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f)
    (ψ : ℝ → ℝ) (r : ℝ) (hr : 0 < r)
    (hint : Integrable (fun s : Fin n → X => empRademacher (localClass F T r) s)
      (Measure.pi fun _ : Fin n => P))
    (hloc : B * expRademacher P n (localClass F T r) ≤ ψ r) :
    Integrable (fun s : Fin n → X => empRademacher (tildeG F T r) s)
        (Measure.pi fun _ : Fin n => P) ∧
      expRademacher P n (tildeG F T r) ≤ ψ r / B := by
  set M : ℝ := |a| + |b| with hM
  have hM0 : 0 ≤ M := by positivity
  have hfM : ∀ f ∈ F, ∀ x, |f x| ≤ M := by
    intro f hf x
    have h := hrange f hf x
    rw [abs_le]
    constructor
    · have := neg_abs_le a; have := abs_nonneg b; linarith [h.1]
    · have := le_abs_self b; have := abs_nonneg a; linarith [h.2]
  -- coefficient facts
  have hc : ∀ f ∈ F, r / max (T f) r ∈ Set.Icc (0 : ℝ) 1 := by
    intro f _
    have hpos : 0 < max (T f) r := lt_of_lt_of_le hr (le_max_right _ _)
    refine ⟨div_nonneg hr.le hpos.le, ?_⟩
    rw [div_le_one hpos]; exact le_max_right _ _
  -- tildeG ⊆ localClass
  have hsub : tildeG F T r ⊆ localClass F T r := by
    rintro g ⟨f, hf, rfl⟩
    refine ⟨⟨f, hf, r / max (T f) r, hc f hf, ?_⟩, ?_⟩
    · funext x; simp
    · have h1 := hTsq f hf _ (hc f hf)
      refine le_trans h1 ?_
      have hT := hT0 f hf
      rcases le_total (T f) r with h | h
      · rw [max_eq_right h, div_self hr.ne']; simpa using h
      · rw [max_eq_left h]
        have hTpos : 0 < T f := lt_of_lt_of_le hr h
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hr.le hT) (sub_nonneg.mpr h)]
  -- bounds on localClass members
  have hlocM : ∀ g ∈ localClass F T r, ∀ x, |g x| ≤ M := by
    rintro g ⟨⟨f, hf, α, hα, rfl⟩, -⟩ x
    simp only [Pi.zero_apply, sub_zero, zero_add]
    rw [abs_mul, abs_of_nonneg hα.1]
    calc α * |f x| ≤ 1 * M := mul_le_mul hα.2 (hfM f hf x) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have htilM : ∀ g ∈ tildeG F T r, ∀ x, |g x| ≤ M := fun g hg => hlocM g (hsub hg)
  -- empRademacher bounded for tildeG
  have hbound : ∀ s : Fin n → X, |empRademacher (tildeG F T r) s| ≤ n * M := by
    intro s
    unfold empRademacher UnderstandingML.rademacher
    have hsup : ∀ σ : Fin n → Bool,
        |⨆ v : UnderstandingML.evalSet (tildeG F T r) s,
          ∑ i, UnderstandingML.signVec σ i * (v : Fin n → ℝ) i| ≤ n * M := by
      intro σ
      apply BB227DF6.iSup_abs_bound _ _ (by positivity)
      rintro ⟨v, g, hg, rfl⟩
      exact BB227DF6.sum_bound σ _ M (fun i => htilM g hg (s i))
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n),
      abs_of_pos (by positivity : (0:ℝ) < 1 / 2 ^ n)]
    calc 1 / (n:ℝ) * (1 / 2 ^ n * |∑ σ : Fin n → Bool,
            ⨆ v : UnderstandingML.evalSet (tildeG F T r) s,
              ∑ i, UnderstandingML.signVec σ i * (v : Fin n → ℝ) i|)
        ≤ 1 / (n:ℝ) * (1 / 2 ^ n * ∑ _σ : Fin n → Bool, (n * M)) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => hsup σ)
      _ ≤ n * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          have h2 : (0:ℝ) < 2 ^ n := by positivity
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
          field_simp
          push_cast
          nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (mul_nonneg h2.le hM0)]
  -- measurability
  have hGc : (tildeG F T r).Countable := by
    refine (hFc.image (fun f => fun x => (r / max (T f) r) * f x)).mono ?_
    rintro g ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  have hmeasG : Measurable (fun s : Fin n → X => empRademacher (tildeG F T r) s) := by
    unfold empRademacher UnderstandingML.rademacher
    apply Measurable.const_mul
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro σ _
    have key : (fun s : Fin n → X => ⨆ v : UnderstandingML.evalSet (tildeG F T r) s,
          ∑ i, UnderstandingML.signVec σ i * (v : Fin n → ℝ) i) =
        fun s => ⨆ g : tildeG F T r,
          ∑ i, UnderstandingML.signVec σ i * (g : X → ℝ) (s i) :=
      funext fun s => BB227DF6.iSup_evalSet _ s (fun v => ∑ i, UnderstandingML.signVec σ i * v i)
    have : Countable (tildeG F T r) := hGc.to_subtype
    have hm : Measurable (fun s : Fin n → X => ⨆ g : tildeG F T r,
          ∑ i, UnderstandingML.signVec σ i * (g : X → ℝ) (s i)) := by
      apply Measurable.iSup
      rintro ⟨g, f, hf, rfl⟩
      apply Finset.measurable_sum
      intro i _
      exact measurable_const.mul
        (((hmeas f hf).const_mul _).comp (measurable_pi_apply i))
    rw [← key] at hm
    exact hm
  have hintG : Integrable (fun s : Fin n → X => empRademacher (tildeG F T r) s)
      (Measure.pi fun _ : Fin n => P) := by
    refine Integrable.mono' (integrable_const ((n:ℝ) * M)) hmeasG.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs]; exact hbound s)
  refine ⟨hintG, ?_⟩
  -- pointwise monotonicity
  have hpt : ∀ s : Fin n → X,
      empRademacher (tildeG F T r) s ≤ empRademacher (localClass F T r) s := by
    intro s
    rcases (tildeG F T r).eq_empty_or_nonempty with hE | hNE
    · -- F is empty
      have hF : F = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro f hf
        have : (fun x => (r / max (T f) r) * f x) ∈ tildeG F T r := ⟨f, hf, rfl⟩
        rw [hE] at this; exact this
      have hL : localClass F T r = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro g ⟨⟨f, hf, -⟩, -⟩
        rw [hF] at hf; exact hf
      rw [hE, hL]
    · unfold empRademacher UnderstandingML.rademacher
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      gcongr with σ _
      refine BB227DF6.iSup_subset_mono _ _ ?_ ?_ (fun v => ∑ i, UnderstandingML.signVec σ i * v i) ?_
      · rintro v ⟨g, hg, rfl⟩; exact ⟨g, hsub hg, rfl⟩
      · obtain ⟨g, hg⟩ := hNE; exact ⟨_, g, hg, rfl⟩
      · refine ⟨n * M, ?_⟩
        rintro _ ⟨⟨v, g, hg, rfl⟩, rfl⟩
        exact (abs_le.mp (BB227DF6.sum_bound σ _ M (fun i => hlocM g hg (s i)))).2
  have hmono : expRademacher P n (tildeG F T r) ≤ expRademacher P n (localClass F T r) :=
    integral_mono hintG hint hpt
  rw [le_div_iff₀ hB]
  nlinarith


open MeasureTheory ProbabilityTheory VarianceRegularization.Localized LocalRademacher.StarHull in
theorem sib_lem38 {X : Type*} [MeasurableSpace X] (P : Measure X) {n : ℕ} (s : Fin n → X)
    (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (B K r : ℝ) (hB : 0 < B) (hK : 1 < K) (hr : 0 < r)
    (hT0 : ∀ f ∈ F, 0 ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ y, f y ∂P) :
    ((∀ g ∈ tildeG F T r, (∫ y, g y ∂P) - empMean s g ≤ r / (B * K)) →
        ∀ f ∈ F, ∫ y, f y ∂P ≤ max (empMean s f) (K / (K - 1) * empMean s f) + r / (B * K)) ∧
      ((∀ g ∈ tildeG F T r, empMean s g - ∫ y, g y ∂P ≤ r / (B * K)) →
        ∀ f ∈ F, empMean s f ≤ (K + 1) / K * ∫ y, f y ∂P + r / (B * K)) := by
  have hK0 : 0 < K := by linarith
  have hBK : 0 < B * K := mul_pos hB hK0
  have he : 0 < r / (B * K) := div_pos hr hBK
  -- linearity facts for the rescaled function
  have hint : ∀ (c : ℝ) (f : X → ℝ), ∫ y, (fun x => c * f x) y ∂P = c * ∫ y, f y ∂P := by
    intro c f
    exact integral_const_mul c f
  have hemp : ∀ (c : ℝ) (f : X → ℝ), empMean s (fun x => c * f x) = c * empMean s f := by
    intro c f
    unfold empMean
    rw [← Finset.mul_sum]
    ring
  have hmem : ∀ f ∈ F, (fun x => (r / max (T f) r) * f x) ∈ tildeG F T r :=
    fun f hf => ⟨f, hf, rfl⟩
  -- key cancellation in the case T f > r
  have key : ∀ f ∈ F, ∀ D : ℝ, r < T f → r / T f * D ≤ r / (B * K) →
      K * D ≤ ∫ y, f y ∂P := by
    intro f hf D hTr h
    have hT : 0 < T f := lt_trans hr hTr
    have h1 : r * D / T f ≤ r / (B * K) := by
      rw [div_mul_eq_mul_div] at h; exact h
    rw [div_le_div_iff₀ hT hBK] at h1
    have h2 : D * (B * K) ≤ T f := by
      have : r * (D * (B * K)) ≤ r * T f := by nlinarith
      exact le_of_mul_le_mul_left this hr
    have h3 := hTB f hf
    have h4 : B * (K * D) ≤ B * ∫ y, f y ∂P := by nlinarith
    exact le_of_mul_le_mul_left h4 hB
  refine ⟨?_, ?_⟩
  · intro hV f hf
    have h := hV _ (hmem f hf)
    rw [hint, hemp, ← mul_sub] at h
    set Pf := ∫ y, f y ∂P
    set Pn := empMean s f
    rcases le_or_gt (T f) r with hTr | hTr
    · rw [max_eq_right hTr, div_self (ne_of_gt hr), one_mul] at h
      have : Pn ≤ max Pn (K / (K - 1) * Pn) := le_max_left _ _
      linarith
    · rw [max_eq_left hTr.le] at h
      have hk := key f hf (Pf - Pn) hTr h
      have hK1 : 0 < K - 1 := by linarith
      have hle : Pf ≤ K / (K - 1) * Pn := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hK1]
        nlinarith
      have : K / (K - 1) * Pn ≤ max Pn (K / (K - 1) * Pn) := le_max_right _ _
      linarith
  · intro hV f hf
    have h := hV _ (hmem f hf)
    rw [hint, hemp, ← mul_sub] at h
    have hPf : 0 ≤ ∫ y, f y ∂P := by
      have h0 := hT0 f hf
      have h3 := hTB f hf
      have : 0 ≤ B * ∫ y, f y ∂P := le_trans h0 h3
      exact nonneg_of_mul_nonneg_right (by linarith) hB
    set Pf := ∫ y, f y ∂P
    set Pn := empMean s f
    have hgoal : (K + 1) / K * Pf = Pf + Pf / K := by
      field_simp
    rcases le_or_gt (T f) r with hTr | hTr
    · rw [max_eq_right hTr, div_self (ne_of_gt hr), one_mul] at h
      have : 0 ≤ Pf / K := div_nonneg hPf hK0.le
      rw [hgoal]
      linarith
    · rw [max_eq_left hTr.le] at h
      have hk := key f hf (Pn - Pf) hTr h
      have hle : Pn ≤ (K + 1) / K * Pf := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hK0]
        nlinarith
      linarith


/-! ### P7b: the countable class, rademacher comparison and both tails -/
namespace Bq857

section P7b

open VarianceRegularization.Localized

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]

lemma sup_le_rad {n : ℕ} (G : Set (X → ℝ)) (e : ℕ → X → ℝ) (he : ∀ i, e i ∈ G) (M : ℝ)
    (hM : ∀ g ∈ G, ∀ x, |g x| ≤ M) (N : ℕ) (s : Fin n → X) (σ : Fin n → Bool) :
    (⨆ τ : Fin (N + 1), ∑ i, UnderstandingML.signVec σ i * e τ (s i))
      ≤ ⨆ a : UnderstandingML.evalSet G s,
          ∑ i, UnderstandingML.signVec σ i * (a : Fin n → ℝ) i := by
  have hev := BB227DF6.iSup_evalSet G s (fun a => ∑ i, UnderstandingML.signVec σ i * a i)
  simp only at hev
  rw [hev]
  apply ciSup_le
  intro τ
  refine le_ciSup_of_le ?_ ⟨e τ, he τ⟩ le_rfl
  exact F198.bdd_of_abs _ (n * M) fun g => F198.sum_sign_abs σ _ M fun i => hM g g.2 (s i)

theorem rad_le_up (n : ℕ) (hn : 0 < n) (G : Set (X → ℝ)) (e : ℕ → X → ℝ) (he : ∀ i, e i ∈ G)
    (hme : ∀ i, Measurable (e i)) (M : ℝ) (hM : ∀ g ∈ G, ∀ x, |g x| ≤ M)
    (hint : Integrable (fun s : Fin n → X => empRademacher G s) (Measure.pi fun _ : Fin n => P))
    (N : ℕ) :
    ∫ s, (⨆ i : Fin (N + 1), (∫ x, e i x ∂P - (n : ℝ)⁻¹ * ∑ j, e i (s j)))
        ∂(Measure.pi fun _ : Fin n => P) ≤ 2 * expRademacher P n G := by
  have hsym := F198.sym P (T := Fin (N + 1)) (fun i => e i) (fun i => hme i) M
    (fun i x => hM _ (he i) x) n hn
  refine hsym.trans ?_
  unfold expRademacher
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine integral_mono (F198.rad_int P (fun i : Fin (N + 1) => e i) (fun i => hme i) M
    (fun i x => hM _ (he i) x) n hn) hint fun s => ?_
  unfold empRademacher UnderstandingML.rademacher
  gcongr with σ
  exact sup_le_rad G e he M hM N s σ

/-- negating all signs is a bijection of sign vectors -/
def flipEquiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ j := !σ j
  invFun σ j := !σ j
  left_inv σ := by funext j; simp
  right_inv σ := by funext j; simp

theorem rad_le_dn (n : ℕ) (hn : 0 < n) (G : Set (X → ℝ)) (e : ℕ → X → ℝ) (he : ∀ i, e i ∈ G)
    (hme : ∀ i, Measurable (e i)) (M : ℝ) (hM : ∀ g ∈ G, ∀ x, |g x| ≤ M)
    (hint : Integrable (fun s : Fin n → X => empRademacher G s) (Measure.pi fun _ : Fin n => P))
    (N : ℕ) :
    ∫ s, (⨆ i : Fin (N + 1), (∫ x, -e i x ∂P - (n : ℝ)⁻¹ * ∑ j, -e i (s j)))
        ∂(Measure.pi fun _ : Fin n => P) ≤ 2 * expRademacher P n G := by
  have hsym := F198.sym P (T := Fin (N + 1)) (fun i x => -e i x)
    (fun i => (hme i).neg) M (fun i x => by rw [abs_neg]; exact hM _ (he i) x) n hn
  refine hsym.trans ?_
  unfold expRademacher
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hneg : ∀ i : Fin (N + 1), ∀ x, |-e i x| ≤ M := fun i x => by
    rw [abs_neg]; exact hM _ (he i) x
  refine integral_mono (F198.rad_int P (fun (i : Fin (N + 1)) x => -e i x)
    (fun i => (hme i).neg) M hneg n hn) hint fun s => ?_
  unfold empRademacher UnderstandingML.rademacher
  have hflip : ∀ σ : Fin n → Bool,
      (⨆ τ : Fin (N + 1), ∑ i, UnderstandingML.signVec σ i * -e τ (s i))
        = ⨆ τ : Fin (N + 1), ∑ i, UnderstandingML.signVec (flipEquiv n σ) i * e τ (s i) := by
    intro σ
    congr 1
    funext τ
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = UnderstandingML.signVec (fun j => !σ j) i * _
    rw [F198.signVec_not]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hflip σ]
  have hsum : ∑ σ : Fin n → Bool, (⨆ a : UnderstandingML.evalSet G s,
        ∑ i, UnderstandingML.signVec (flipEquiv n σ) i * (a : Fin n → ℝ) i)
      = ∑ σ : Fin n → Bool, (⨆ a : UnderstandingML.evalSet G s,
        ∑ i, UnderstandingML.signVec σ i * (a : Fin n → ℝ) i) :=
    Fintype.sum_equiv (flipEquiv n) _ _ fun σ => rfl
  rw [← hsum]
  gcongr with σ
  exact sup_le_rad G e he M hM N s (flipEquiv n σ)

theorem C1G (n : ℕ) (hn : 0 < n) (G : Set (X → ℝ)) (hGc : G.Countable)
    (hmeas : ∀ g ∈ G, Measurable g) (M : ℝ) (hM : ∀ g ∈ G, ∀ x, |g x| ≤ M)
    (U r t α : ℝ) (hU : 0 < U) (hr : 0 < r) (ht : 0 < t) (hα : 0 < α)
    (hosc : ∀ g ∈ G, ∀ x, |g x - ∫ y, g y ∂P| ≤ U)
    (hvar : ∀ g ∈ G, ∫ x, (g x - ∫ y, g y ∂P) ^ 2 ∂P ≤ r)
    (hint : Integrable (fun s : Fin n → X => empRademacher G s) (Measure.pi fun _ : Fin n => P)) :
    (Measure.pi fun _ : Fin n => P)
        {s | ∃ g ∈ G, 2 * (1 + α) * expRademacher P n G + Real.sqrt (2 * r * t / n)
              + t / n * U * (1 / 2 + 1 / α) < (∫ x, g x ∂P) - empMean s g}
        ≤ ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi fun _ : Fin n => P)
        {s | ∃ g ∈ G, 2 * (1 + α) * expRademacher P n G + Real.sqrt (2 * r * t / n)
              + t / n * U * (1 / 2 + 1 / α) < empMean s g - ∫ x, g x ∂P}
        ≤ ENNReal.ofReal (Real.exp (-t)) := by
  rcases G.eq_empty_or_nonempty with hG | hG
  · subst hG
    simp
  obtain ⟨e, he⟩ := hGc.exists_eq_range hG
  have he' : ∀ i, e i ∈ G := fun i => by rw [he]; exact ⟨i, rfl⟩
  have hme : ∀ i, Measurable (e i) := fun i => hmeas _ (he' i)
  constructor
  · refine le_trans (measure_mono ?_) (core_tail P n hn e hme M (fun i => hM _ (he' i)) U r t α
      (expRademacher P n G) hU hr ht hα (fun i => hosc _ (he' i)) (fun i => hvar _ (he' i))
      (rad_le_up P n hn G e he' hme M hM hint))
    rintro s ⟨g, hg, hlt⟩
    rw [he] at hg
    obtain ⟨i, rfl⟩ := hg
    refine ⟨i, ?_⟩
    simpa only [empMean, one_div] using hlt
  · have hosc' : ∀ (i : ℕ) (x : X), |-e i x - ∫ y, -e i y ∂P| ≤ U := by
      intro i x
      simp only [integral_neg]
      rw [show -e i x - -∫ y, e i y ∂P = -(e i x - ∫ y, e i y ∂P) by ring, abs_neg]
      exact hosc _ (he' i) x
    have hvar' : ∀ i : ℕ, ∫ x, (-e i x - ∫ y, -e i y ∂P) ^ 2 ∂P ≤ r := by
      intro i
      simp only [integral_neg]
      have : ∀ x, (-e i x - -∫ y, e i y ∂P) ^ 2 = (e i x - ∫ y, e i y ∂P) ^ 2 := fun x => by ring
      simp_rw [this]
      exact hvar _ (he' i)
    refine le_trans (measure_mono ?_) (core_tail P n hn (fun i x => -e i x)
      (fun i => (hme i).neg) M (fun i x => by rw [abs_neg]; exact hM _ (he' i) x) U r t α
      (expRademacher P n G) hU hr ht hα hosc' hvar'
      (rad_le_dn P n hn G e he' hme M hM hint))
    rintro s ⟨g, hg, hlt⟩
    rw [he] at hg
    obtain ⟨i, rfl⟩ := hg
    refine ⟨i, ?_⟩
    simp only [empMean, one_div, integral_neg, Finset.sum_neg_distrib] at hlt ⊢
    linarith

lemma sq_bound {q A C : ℝ} (hq : 0 ≤ q) (hA : 0 ≤ A) (hC : 0 ≤ C) (h : q ^ 2 ≤ 4 * A * C) :
    q ≤ A + C := by
  nlinarith [sq_nonneg (A - C)]

end P7b

end Bq857

set_option maxHeartbeats 1000000 in
open MeasureTheory ProbabilityTheory VarianceRegularization.Localized LocalRademacher.StarHull in
theorem parent_main {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (F : Set (X → ℝ)) (hFc : F.Countable) (hmeas : ∀ f ∈ F, Measurable f)
    (a b : ℝ) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a b)
    (T : (X → ℝ) → ℝ) (B : ℝ) (hB : 0 < B) (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hvar : ∀ f ∈ F, variance f P ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ x, f x ∂P)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f)
    (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar)
    (hloc : ∀ r, rstar ≤ r →
      Integrable (fun s : Fin n → X => empRademacher (localClass F T r) s)
          (Measure.pi fun _ : Fin n => P) ∧
        B * expRademacher P n (localClass F T r) ≤ ψ r)
    (K x : ℝ) (hK : 1 < K) (hx : 0 < x) :
    (Measure.pi fun _ : Fin n => P)
        {s | ∃ f ∈ F, max (empMean s f) (K / (K - 1) * empMean s f)
            + (7.04 : ℝ) * K / B * rstar + x * (21 * (b - a) + (6.4 : ℝ) * B * K) / n
            < ∫ y, f y ∂P}
        ≤ ENNReal.ofReal (Real.exp (-x)) ∧
      (Measure.pi fun _ : Fin n => P)
        {s | ∃ f ∈ F, (K + 1) / K * (∫ y, f y ∂P)
            + (7.04 : ℝ) * K / B * rstar + x * (21 * (b - a) + (6.4 : ℝ) * B * K) / n
            < empMean s f}
        ≤ ENNReal.ofReal (Real.exp (-x)) := by
  have hK0 : 0 < K := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases F.eq_empty_or_nonempty with hF | ⟨f0, hf0⟩
  · subst hF
    simp
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hab : a ≤ b := (hrange f0 hf0 x0).1.trans (hrange f0 hf0 x0).2
  have hBK : 0 < B * K := mul_pos hB hK0
  obtain ⟨A1, hA1⟩ : ∃ A1 : ℝ, A1 = K * rstar / B := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℝ, A2 = x / n := ⟨_, rfl⟩
  have hA1p : 0 < A1 := by rw [hA1]; positivity
  have hA2p : 0 < A2 := by rw [hA2]; positivity
  set u : ℝ := (7.04 : ℝ) * K / B * rstar + x * (21 * (b - a) + (6.4 : ℝ) * B * K) / n with hu
  have hu' : u = 176 / 25 * A1 + 21 * (b - a) * A2 + 32 / 5 * (B * K) * A2 := by
    rw [hu, hA1, hA2, show (7.04 : ℝ) = 176 / 25 by norm_num, show (6.4 : ℝ) = 32 / 5 by norm_num]
    field_simp
    ring
  have hba : 0 ≤ (b - a) * A2 := mul_nonneg (by linarith) hA2p.le
  have hBKA : 0 < (B * K) * A2 := mul_pos hBK hA2p
  have hu0 : 0 < u := by rw [hu']; nlinarith
  set r : ℝ := B * K * u with hr
  have hr0 : 0 < r := mul_pos hBK hu0
  have hrBK : r / (B * K) = u := by rw [hr]; field_simp
  have hr_ge : rstar ≤ r := by
    have hBA1 : B * K * A1 = K ^ 2 * rstar := by rw [hA1]; field_simp
    have hK2 : rstar ≤ K ^ 2 * rstar := by
      have h1K : 1 ≤ K ^ 2 := by nlinarith
      exact le_mul_of_one_le_left hrstar.le h1K
    have : r = 176 / 25 * (K ^ 2 * rstar) + B * K * (21 * (b - a) * A2 + 32 / 5 * (B * K) * A2) := by
      rw [hr, hu', ← hBA1]; ring
    rw [this]
    have h1 : 0 ≤ B * K * (21 * (b - a) * A2 + 32 / 5 * (B * K) * A2) := by
      apply mul_nonneg hBK.le; nlinarith
    nlinarith
  obtain ⟨hintL, hlocr⟩ := hloc r hr_ge
  obtain ⟨hintG, hER⟩ := sib_tgRad P n hn F hFc hmeas a b hrange T B hB hT0 hTsq ψ r hr0
    hintL hlocr
  have hψr : ψ r ≤ Real.sqrt (r * rstar) := by
    have h := hψ.2.2 (show rstar ∈ Set.Ioi 0 from hrstar) (show r ∈ Set.Ioi 0 from hr0) hr_ge
    simp only at h
    rw [hfix, Real.div_sqrt, div_le_iff₀ (Real.sqrt_pos.2 hr0)] at h
    rw [Real.sqrt_mul hr0.le]
    linarith
  -- the rescaled class
  set G := tildeG F T r with hG
  set M : ℝ := |a| + |b| with hM
  have hcoef : ∀ f ∈ F, 0 < r / max (T f) r ∧ r / max (T f) r ≤ 1 ∧
      (r / max (T f) r) ^ 2 * T f ≤ r := by
    intro f hf
    have hmx : 0 < max (T f) r := lt_of_lt_of_le hr0 (le_max_right _ _)
    have hc0 : 0 < r / max (T f) r := div_pos hr0 hmx
    have hc1 : r / max (T f) r ≤ 1 := (div_le_one hmx).2 (le_max_right _ _)
    have hcm : r / max (T f) r * max (T f) r = r := div_mul_cancel₀ r hmx.ne'
    refine ⟨hc0, hc1, ?_⟩
    calc (r / max (T f) r) ^ 2 * T f ≤ (r / max (T f) r) ^ 2 * max (T f) r :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
      _ = r / max (T f) r * r := by rw [sq, mul_assoc, hcm]
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right hc1 hr0.le
      _ = r := one_mul r
  have hGc : G.Countable := by
    refine (hFc.image (fun f => fun x => (r / max (T f) r) * f x)).mono ?_
    rintro g ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  have hGm : ∀ g ∈ G, Measurable g := by
    rintro g ⟨f, hf, rfl⟩
    exact (hmeas f hf).const_mul _
  have hGM : ∀ g ∈ G, ∀ y, |g y| ≤ M := by
    rintro g ⟨f, hf, rfl⟩ y
    obtain ⟨c0, c1, -⟩ := hcoef f hf
    have hfy := hrange f hf y
    have hfa : |f y| ≤ |a| + |b| := Bq857.abs_le_of_mem hfy.1 hfy.2
    show |r / max (T f) r * f y| ≤ M
    rw [abs_mul, abs_of_pos c0]
    calc r / max (T f) r * |f y| ≤ 1 * |f y| :=
          mul_le_mul_of_nonneg_right c1 (abs_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hfa
  have hfint : ∀ f ∈ F, a ≤ ∫ y, f y ∂P ∧ ∫ y, f y ∂P ≤ b := fun f hf =>
    Bq857.integral_mem_of (μ := P) (hmeas f hf) (fun y => (hrange f hf y).1)
      (fun y => (hrange f hf y).2)
  have hGosc : ∀ g ∈ G, ∀ y, |g y - ∫ z, g z ∂P| ≤ b - a := by
    rintro g ⟨f, hf, rfl⟩ y
    obtain ⟨c0, c1, -⟩ := hcoef f hf
    show |r / max (T f) r * f y - ∫ z, r / max (T f) r * f z ∂P| ≤ b - a
    rw [integral_const_mul, ← mul_sub, abs_mul, abs_of_pos c0]
    have h1 : |f y - ∫ z, f z ∂P| ≤ b - a := by
      rw [abs_le]
      constructor <;> linarith [(hrange f hf y).1, (hrange f hf y).2, (hfint f hf).1,
        (hfint f hf).2]
    calc r / max (T f) r * |f y - ∫ z, f z ∂P| ≤ 1 * (b - a) :=
          mul_le_mul c1 h1 (abs_nonneg _) zero_le_one
      _ = b - a := one_mul _
  have hGvar : ∀ g ∈ G, ∫ y, (g y - ∫ z, g z ∂P) ^ 2 ∂P ≤ r := by
    rintro g ⟨f, hf, rfl⟩
    obtain ⟨-, -, c2⟩ := hcoef f hf
    show ∫ y, (r / max (T f) r * f y - ∫ z, r / max (T f) r * f z ∂P) ^ 2 ∂P ≤ r
    rw [integral_const_mul]
    have hsq : ∀ y, (r / max (T f) r * f y - r / max (T f) r * ∫ z, f z ∂P) ^ 2
        = (r / max (T f) r) ^ 2 * (f y - ∫ z, f z ∂P) ^ 2 := fun y => by ring
    simp_rw [hsq]
    rw [integral_const_mul, ← variance_eq_integral (hmeas f hf).aemeasurable]
    calc (r / max (T f) r) ^ 2 * variance f P ≤ (r / max (T f) r) ^ 2 * T f :=
          mul_le_mul_of_nonneg_left (hvar f hf) (sq_nonneg _)
      _ ≤ r := c2
  -- the deviation threshold at alpha = 1/10 is at most u
  have hthr : 2 * (1 + 1 / 10) * expRademacher P n G + Real.sqrt (2 * r * x / n)
      + x / n * (b - a) * (1 / 2 + 1 / (1 / 10)) ≤ u := by
    set Q := Real.sqrt (r * rstar) with hQ
    have hE1 : expRademacher P n G ≤ Q / B :=
      hER.trans (div_le_div_of_nonneg_right hψr hB.le)
    have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
    have hQ2 : Q ^ 2 = r * rstar := Real.sq_sqrt (by positivity)
    have hb1 : 11 / 5 * Q ≤ 11 / 32 * u * B + 88 / 25 * K * rstar := by
      apply Bq857.sq_bound (by positivity) (by positivity) (by positivity)
      rw [mul_pow, hQ2, hr]
      apply le_of_eq
      ring
    have hb1' : 11 / 5 * (Q / B) ≤ 11 / 32 * u + 88 / 25 * A1 := by
      have h := div_le_div_of_nonneg_right hb1 hB.le
      have e1 : 11 / 5 * Q / B = 11 / 5 * (Q / B) := by ring
      have e2 : (11 / 32 * u * B + 88 / 25 * K * rstar) / B = 11 / 32 * u + 88 / 25 * A1 := by
        rw [hA1]; field_simp
      rw [e1, e2] at h
      exact h
    set p := Real.sqrt (2 * r * x / n) with hp
    have hp2 : p ^ 2 = 2 * r * x / n := Real.sq_sqrt (by positivity)
    have hb2 : p ≤ 5 / 32 * u + 16 / 5 * (B * K) * A2 := by
      apply Bq857.sq_bound (Real.sqrt_nonneg _) (by positivity) (by positivity)
      rw [hp2, hr, hA2]
      apply le_of_eq
      ring
    have e3 : x / n * (b - a) * (1 / 2 + 1 / (1 / 10)) = 21 / 2 * ((b - a) * A2) := by
      rw [hA2]; ring
    rw [e3]
    have hE2 : 2 * (1 + 1 / 10) * expRademacher P n G ≤ 11 / 5 * (Q / B) := by
      linarith
    rw [hu'] at hb1' hb2 ⊢
    nlinarith
  -- the two bad events of the rescaled class
  have hbad : (Measure.pi fun _ : Fin n => P) {s | ∃ g ∈ G, u < (∫ y, g y ∂P) - empMean s g}
        ≤ ENNReal.ofReal (Real.exp (-x)) ∧
      (Measure.pi fun _ : Fin n => P) {s | ∃ g ∈ G, u < empMean s g - ∫ y, g y ∂P}
        ≤ ENNReal.ofReal (Real.exp (-x)) := by
    rcases hab.lt_or_eq with hlt | heq
    · obtain ⟨h1, h2⟩ := Bq857.C1G P n hn G hGc hGm M hGM (b - a) r x (1 / 10)
        (sub_pos.2 hlt) hr0 hx (by norm_num) hGosc hGvar hintG
      constructor
      · refine le_trans (measure_mono ?_) h1
        rintro s ⟨g, hg, hs⟩
        exact ⟨g, hg, lt_of_le_of_lt hthr hs⟩
      · refine le_trans (measure_mono ?_) h2
        rintro s ⟨g, hg, hs⟩
        exact ⟨g, hg, lt_of_le_of_lt hthr hs⟩
    · have hz : ∀ s : Fin n → X, ∀ g ∈ G, (∫ y, g y ∂P) - empMean s g = 0 := by
        rintro s g ⟨f, hf, rfl⟩
        have hfc : f = fun _ => a := by
          funext y
          have := hrange f hf y
          rw [← heq] at this
          exact le_antisymm this.2 this.1
        subst hfc
        simp [empMean]
        field_simp
        ring
      constructor
      · have e1 : {s : Fin n → X | ∃ g ∈ G, u < (∫ y, g y ∂P) - empMean s g} = ∅ := by
          ext s
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨g, hg, hs⟩
          rw [hz s g hg] at hs
          linarith
        rw [e1, measure_empty]
        exact zero_le
      · have e1 : {s : Fin n → X | ∃ g ∈ G, u < empMean s g - ∫ y, g y ∂P} = ∅ := by
          ext s
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨g, hg, hs⟩
          have := hz s g hg
          linarith
        rw [e1, measure_empty]
        exact zero_le
  have L38 := fun s : Fin n → X => sib_lem38 P s F T B K r hB hK hr0 hT0 hTB
  constructor
  · refine le_trans (measure_mono ?_) hbad.1
    intro s hs
    obtain ⟨f, hf, hlt⟩ := hs
    by_contra hns
    have hgood : ∀ g ∈ tildeG F T r, (∫ y, g y ∂P) - empMean s g ≤ r / (B * K) := by
      intro g hg
      rw [hrBK]
      by_contra h
      exact hns ⟨g, hg, not_le.1 h⟩
    have := (L38 s).1 hgood f hf
    rw [hrBK] at this
    linarith
  · refine le_trans (measure_mono ?_) hbad.2
    intro s hs
    obtain ⟨f, hf, hlt⟩ := hs
    by_contra hns
    have hgood : ∀ g ∈ tildeG F T r, empMean s g - ∫ y, g y ∂P ≤ r / (B * K) := by
      intro g hg
      rw [hrBK]
      by_contra h
      exact hns ⟨g, hg, not_le.1 h⟩
    have := (L38 s).2 hgood f hf
    rw [hrBK] at this
    linarith

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized LocalRademacher.StarHull in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (F : Set (X → ℝ)) (hFc : F.Countable) (hmeas : ∀ f ∈ F, Measurable f)
    (a b : ℝ) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a b)
    (T : (X → ℝ) → ℝ) (B : ℝ) (hB : 0 < B) (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hvar : ∀ f ∈ F, variance f P ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ x, f x ∂P)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f)
    (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar)
    (hloc : ∀ r, rstar ≤ r →
      Integrable (fun s : Fin n → X => empRademacher (localClass F T r) s)
          (Measure.pi fun _ : Fin n => P) ∧
        B * expRademacher P n (localClass F T r) ≤ ψ r)
    (K x : ℝ) (hK : 1 < K) (hx : 0 < x) :
    (Measure.pi fun _ : Fin n => P)
        {s | ∃ f ∈ F, max (empMean s f) (K / (K - 1) * empMean s f)
            + (7.04 : ℝ) * K / B * rstar + x * (21 * (b - a) + (6.4 : ℝ) * B * K) / n
            < ∫ y, f y ∂P}
        ≤ ENNReal.ofReal (Real.exp (-x)) ∧
      (Measure.pi fun _ : Fin n => P)
        {s | ∃ f ∈ F, (K + 1) / K * (∫ y, f y ∂P)
            + (7.04 : ℝ) * K / B * rstar + x * (21 * (b - a) + (6.4 : ℝ) * B * K) / n
            < empMean s f}
        ≤ ENNReal.ofReal (Real.exp (-x)) := by
  exact parent_main P n hn F hFc hmeas a b hrange T B hB hT0 hvar hTB hTsq ψ hψ rstar hrstar hfix
    hloc K x hK hx
