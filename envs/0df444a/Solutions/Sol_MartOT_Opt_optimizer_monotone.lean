-- Prove2me | solution 1 for MartOT.Opt.optimizer_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T08:28:32.751012+00:00
-- url     : https://prove2.me/submissions/3cc189b8-cafa-4623-93ff-2a3d0d6c8fdb

import Mathlib
import Definitions.Def_MartOT_Var_Setting


set_option autoImplicit false

namespace MartOT.Mono

/-- Four-point strict convexity: `a < b, c < d`, `b + c = a + d` gives `f b + f c < f a + f d`. -/
lemma sc_pair {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {a b c d : ℝ} (hab : a < b)
    (hbd : b < d) (hac : a < c) (hcd : c < d) (hs : b + c = a + d) :
    f b + f c < f a + f d := by
  have hda : 0 < d - a := by linarith
  have key : ∀ y, a < y → y < d →
      f y < (d - y) / (d - a) * f a + (y - a) / (d - a) * f d := by
    intro y hy1 hy2
    have h1 : 0 < (d - y) / (d - a) := div_pos (by linarith) hda
    have h2 : 0 < (y - a) / (d - a) := div_pos (by linarith) hda
    have h3 : (d - y) / (d - a) + (y - a) / (d - a) = 1 := by
      field_simp; ring
    have := hf.2 (Set.mem_univ a) (Set.mem_univ d) (ne_of_lt (by linarith : a < d)) h1 h2 h3
    simp only [smul_eq_mul] at this
    have e : (d - y) / (d - a) * a + (y - a) / (d - a) * d = y := by
      field_simp; ring
    rw [e] at this
    exact this
  have kb := key b hab hbd
  have kc := key c hac hcd
  have e1 : (d - b) / (d - a) + (d - c) / (d - a) = 1 := by
    field_simp; linarith
  have e2 : (b - a) / (d - a) + (c - a) / (d - a) = 1 := by
    field_simp; linarith
  have : (d - b) / (d - a) * f a + (b - a) / (d - a) * f d +
      ((d - c) / (d - a) * f a + (c - a) / (d - a) * f d) = f a + f d := by
    have : (d - b) / (d - a) * f a + (b - a) / (d - a) * f d +
      ((d - c) / (d - a) * f a + (c - a) / (d - a) * f d) =
      ((d - b) / (d - a) + (d - c) / (d - a)) * f a +
        ((b - a) / (d - a) + (c - a) / (d - a)) * f d := by ring
    rw [this, e1, e2]; ring
  linarith

/-- With `h'` strictly convex and `x < x'`, `g y = h (y - x) - h (y - x')` is strictly convex. -/
lemma g_strictConvex {h : ℝ → ℝ} (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h)) {x x' : ℝ} (hxx : x < x') :
    StrictConvexOn ℝ Set.univ (fun y => h (y - x) - h (y - x')) := by
  have hderiv : ∀ y, HasDerivAt (fun y => h (y - x) - h (y - x'))
      (deriv h (y - x) - deriv h (y - x')) y := by
    intro y
    have a1 : HasDerivAt (fun y => h (y - x)) (deriv h (y - x)) y := by
      exact ((hd (y - x)).hasDerivAt).comp_sub_const y x
    have a2 : HasDerivAt (fun y => h (y - x')) (deriv h (y - x')) y := by
      exact ((hd (y - x')).hasDerivAt).comp_sub_const y x'
    exact a1.sub a2
  have hcont : Continuous (fun y => h (y - x) - h (y - x')) :=
    (hd.continuous.comp (continuous_id.sub continuous_const)).sub
      (hd.continuous.comp (continuous_id.sub continuous_const))
  apply StrictMono.strictConvexOn_univ_of_deriv hcont
  intro y1 y2 hy
  rw [(hderiv y1).deriv, (hderiv y2).deriv]
  -- s = y1 - x', t = y2 - x', δ = x' - x
  have := sc_pair hconv (a := y1 - x') (b := y2 - x') (c := y1 - x) (d := y2 - x)
    (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  linarith

/-- The three-point rerouting inequality (Beiglböck–Juillet §6): for `x < x'`, `u < w < v`,
`p = (v-w)/(v-u)`, `q = (w-u)/(v-u)`, rerouting strictly lowers the cost `h (y - x)`. -/
lemma reroute_lt {h : ℝ → ℝ} (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h)) {x x' u w v : ℝ} (hxx : x < x')
    (huw : u < w) (hwv : w < v) :
    h (w - x) + (v - w) / (v - u) * h (u - x') + (w - u) / (v - u) * h (v - x') <
      (v - w) / (v - u) * h (u - x) + (w - u) / (v - u) * h (v - x) + h (w - x') := by
  have hg := g_strictConvex hd hconv hxx
  have hvu : 0 < v - u := by linarith
  have h1 : 0 < (v - w) / (v - u) := div_pos (by linarith) hvu
  have h2 : 0 < (w - u) / (v - u) := div_pos (by linarith) hvu
  have h3 : (v - w) / (v - u) + (w - u) / (v - u) = 1 := by field_simp; ring
  have := hg.2 (Set.mem_univ u) (Set.mem_univ v) (ne_of_lt (by linarith : u < v)) h1 h2 h3
  simp only [smul_eq_mul] at this
  have e : (v - w) / (v - u) * u + (w - u) / (v - u) * v = w := by field_simp; ring
  rw [e] at this
  linarith

end MartOT.Mono


set_option autoImplicit false

open MeasureTheory

namespace MartOT.Mono

lemma integralE_eq_coe {X : Type*} [MeasurableSpace X] (m : Measure X) (f : X → ℝ)
    (hf : Integrable f m) : MartOT.Var.integralE m f = ((∫ x, f x ∂m : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have e1 : ∀ x, ((f x : ℝ) : EReal).toENNReal = ENNReal.ofReal (max (f x) 0) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have e2 : ∀ x, (-((f x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (max (-f x) 0) := fun x => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (-f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  simp_rw [e1, e2]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.pos_part (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    ← ofReal_integral_eq_lintegral_ofReal (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part) (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg (fun x => le_max_right (f x) 0)),
    max_eq_left (integral_nonneg (fun x => le_max_right (-f x) 0)), ← EReal.coe_sub]
  congr 1
  rw [← integral_sub hf.pos_part (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part)]
  congr 1
  ext x
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma toENNReal_coe (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma toENNReal_neg_coe (r : ℝ) : (-(r : EReal)).toENNReal = ENNReal.ofReal (-r) := by
  rw [← EReal.coe_neg, toENNReal_coe]

/-- Finite cost plus the sufficient integrability condition make the cost integrable. -/
lemma cost_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] (π : Measure (ℝ × ℝ))
    (hplan : MartOT.Var.IsPlan μ ν π) (c : ℝ → ℝ → ℝ)
    (hc : Measurable (fun p : ℝ × ℝ => c p.1 p.2))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hfin : MartOT.Var.cost c π < ⊤) :
    Integrable (fun p : ℝ × ℝ => c p.1 p.2) π := by
  obtain ⟨a, b, ha, hb, hab⟩ := hint
  have hπa : Integrable (fun p : ℝ × ℝ => a p.1) π := by
    have h1 : Integrable a (π.map Prod.fst) := by rw [hplan.1]; exact ha
    exact (integrable_map_measure (hplan.1 ▸ ha.aestronglyMeasurable)
      measurable_fst.aemeasurable).1 h1
  have hπb : Integrable (fun p : ℝ × ℝ => b p.2) π := by
    have h1 : Integrable b (π.map Prod.snd) := by rw [hplan.2]; exact hb
    exact (integrable_map_measure (hplan.2 ▸ hb.aestronglyMeasurable)
      measurable_snd.aemeasurable).1 h1
  have hg := hπa.add hπb
  set f : ℝ × ℝ → ℝ := fun p => c p.1 p.2 with hf
  -- negative part finite
  have hneg : ∫⁻ p, ENNReal.ofReal (-f p) ∂π ≠ ⊤ := by
    have hle : ∀ p, ENNReal.ofReal (-f p) ≤ ‖a p.1 + b p.2‖ₑ := by
      intro p
      rw [← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      have := hab p.1 p.2
      rw [Real.norm_eq_abs]
      have := neg_abs_le (a p.1 + b p.2)
      simp only [hf]; linarith
    exact ne_top_of_le_ne_top hg.2.ne (lintegral_mono hle)
  have hpos : ∫⁻ p, ENNReal.ofReal (f p) ∂π ≠ ⊤ := by
    intro htop
    have : MartOT.Var.cost c π = ⊤ := by
      unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
      simp_rw [toENNReal_coe, toENNReal_neg_coe]
      change ((∫⁻ p, ENNReal.ofReal (f p) ∂π : ENNReal) : EReal) -
        ((∫⁻ p, ENNReal.ofReal (-f p) ∂π : ENNReal) : EReal) = ⊤
      rw [htop, EReal.coe_ennreal_top]
      apply EReal.top_sub
      exact fun h => hneg (EReal.coe_ennreal_eq_top_iff.1 h)
    rw [this] at hfin
    exact lt_irrefl _ hfin
  have i1 := integrable_toReal_of_lintegral_ne_top
    (hc.ennreal_ofReal.aemeasurable) hpos
  have i2 := integrable_toReal_of_lintegral_ne_top
    (hc.neg.ennreal_ofReal.aemeasurable) hneg
  refine (i1.sub i2).congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Pi.sub_apply, ENNReal.toReal_ofReal', Pi.neg_apply]
  rcases le_total 0 (f p) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

end MartOT.Mono


set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace MartOT.Mono

/-- Configuration space `ω = ((x, (u, v)), (x', w))`. -/
abbrev Ω := (ℝ × (ℝ × ℝ)) × (ℝ × ℝ)

noncomputable def pR (ω : Ω) : ℝ := (ω.1.2.2 - ω.2.2) / (ω.1.2.2 - ω.1.2.1)
noncomputable def qR (ω : Ω) : ℝ := (ω.2.2 - ω.1.2.1) / (ω.1.2.2 - ω.1.2.1)
noncomputable def pw (ω : Ω) : ℝ≥0 := Real.toNNReal (pR ω)
noncomputable def qw (ω : Ω) : ℝ≥0 := Real.toNNReal (qR ω)

def fXU (ω : Ω) : ℝ × ℝ := (ω.1.1, ω.1.2.1)
def fXV (ω : Ω) : ℝ × ℝ := (ω.1.1, ω.1.2.2)
def fXW (ω : Ω) : ℝ × ℝ := (ω.1.1, ω.2.2)
def fYU (ω : Ω) : ℝ × ℝ := (ω.2.1, ω.1.2.1)
def fYV (ω : Ω) : ℝ × ℝ := (ω.2.1, ω.1.2.2)
def fYW (ω : Ω) : ℝ × ℝ := (ω.2.1, ω.2.2)

lemma m_fXU : Measurable fXU := by unfold fXU; fun_prop
lemma m_fXV : Measurable fXV := by unfold fXV; fun_prop
lemma m_fXW : Measurable fXW := by unfold fXW; fun_prop
lemma m_fYU : Measurable fYU := by unfold fYU; fun_prop
lemma m_fYV : Measurable fYV := by unfold fYV; fun_prop
lemma m_fYW : Measurable fYW := by unfold fYW; fun_prop
lemma m_pw : Measurable pw := by unfold pw pR; fun_prop
lemma m_qw : Measurable qw := by unfold qw qR; fun_prop

/-- Mass removed from the plan. -/
noncomputable def Rm (θ : Measure Ω) : Measure (ℝ × ℝ) :=
  (θ.withDensity (fun ω => (pw ω : ℝ≥0∞))).map fXU +
    (θ.withDensity (fun ω => (qw ω : ℝ≥0∞))).map fXV + θ.map fYW

/-- Mass added to the plan. -/
noncomputable def Am (θ : Measure Ω) : Measure (ℝ × ℝ) :=
  θ.map fXW + (θ.withDensity (fun ω => (pw ω : ℝ≥0∞))).map fYU +
    (θ.withDensity (fun ω => (qw ω : ℝ≥0∞))).map fYV

def Good (K : ℝ) (ω : Ω) : Prop :=
  ω.1.1 < ω.2.1 ∧ ω.1.2.1 < ω.2.2 ∧ ω.2.2 < ω.1.2.2 ∧ |ω.1.1| ≤ K ∧ |ω.2.1| ≤ K ∧
    |ω.1.2.1| ≤ K ∧ |ω.1.2.2| ≤ K ∧ |ω.2.2| ≤ K

lemma good_pq {K : ℝ} {ω : Ω} (hω : Good K ω) :
    0 ≤ pR ω ∧ pR ω ≤ 1 ∧ 0 ≤ qR ω ∧ qR ω ≤ 1 ∧ pR ω + qR ω = 1 ∧
      pR ω * ω.1.2.1 + qR ω * ω.1.2.2 = ω.2.2 := by
  obtain ⟨_, h1, h2, -⟩ := hω
  have hvu : 0 < ω.1.2.2 - ω.1.2.1 := by linarith
  unfold pR qR
  refine ⟨div_nonneg (by linarith) hvu.le, (div_le_one hvu).2 (by linarith),
    div_nonneg (by linarith) hvu.le, (div_le_one hvu).2 (by linarith), ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring

lemma pw_coe {K : ℝ} {ω : Ω} (hω : Good K ω) : (pw ω : ℝ) = pR ω :=
  Real.coe_toNNReal _ (good_pq hω).1

lemma qw_coe {K : ℝ} {ω : Ω} (hω : Good K ω) : (qw ω : ℝ) = qR ω :=
  Real.coe_toNNReal _ (good_pq hω).2.2.1

/-- One weighted piece of `Rm`/`Am`: integrability and the change of variables. -/
lemma piece (θ : Measure Ω) [IsFiniteMeasure θ] {K C : ℝ} (hG : ∀ᵐ ω ∂θ, Good K ω)
    (w : Ω → ℝ≥0) (hw : Measurable w) (hw1 : ∀ ω, Good K ω → (w ω : ℝ) ≤ 1)
    (f : Ω → ℝ × ℝ) (hf : Measurable f)
    (hfK : ∀ ω, Good K ω → |(f ω).1| ≤ K ∧ |(f ω).2| ≤ K)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (hgC : ∀ z : ℝ × ℝ, |z.1| ≤ K → |z.2| ≤ K → |g z| ≤ C) :
    Integrable (fun ω => (w ω : ℝ) * g (f ω)) θ ∧
    Integrable g ((θ.withDensity (fun ω => (w ω : ℝ≥0∞))).map f) ∧
    ∫ z, g z ∂((θ.withDensity (fun ω => (w ω : ℝ≥0∞))).map f) =
      ∫ ω, (w ω : ℝ) * g (f ω) ∂θ := by
  have hint : Integrable (fun ω => (w ω : ℝ) * g (f ω)) θ := by
    refine Integrable.of_bound
      ((hw.coe_nnreal_real).mul (hg.comp hf)).aestronglyMeasurable C ?_
    filter_upwards [hG] with ω hω
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, NNReal.abs_eq]
    have h1 := hw1 ω hω
    have h2 := hgC (f ω) (hfK ω hω).1 (hfK ω hω).2
    calc (w ω : ℝ) * |g (f ω)| ≤ 1 * |g (f ω)| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ C := by linarith
  refine ⟨hint, ?_, ?_⟩
  · rw [integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable]
    refine (integrable_withDensity_iff_integrable_smul hw).2 ?_
    simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul]
    exact hint
  · rw [integral_map hf.aemeasurable hg.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hw]
    simp only [NNReal.smul_def, smul_eq_mul]

lemma piece1 (θ : Measure Ω) [IsFiniteMeasure θ] {K C : ℝ} (hG : ∀ᵐ ω ∂θ, Good K ω)
    (f : Ω → ℝ × ℝ) (hf : Measurable f)
    (hfK : ∀ ω, Good K ω → |(f ω).1| ≤ K ∧ |(f ω).2| ≤ K)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (hgC : ∀ z : ℝ × ℝ, |z.1| ≤ K → |z.2| ≤ K → |g z| ≤ C) :
    Integrable (fun ω => g (f ω)) θ ∧ Integrable g (θ.map f) ∧
    ∫ z, g z ∂(θ.map f) = ∫ ω, g (f ω) ∂θ := by
  have hint : Integrable (fun ω => g (f ω)) θ := by
    refine Integrable.of_bound (hg.comp hf).aestronglyMeasurable C ?_
    filter_upwards [hG] with ω hω
    rw [Real.norm_eq_abs]
    exact hgC (f ω) (hfK ω hω).1 (hfK ω hω).2
  refine ⟨hint, ?_, ?_⟩
  · rw [integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable]
    exact hint
  · rw [integral_map hf.aemeasurable hg.aestronglyMeasurable]

/-- The cost/test-function change between the added and removed masses. -/
noncomputable def Δf (g : ℝ × ℝ → ℝ) (ω : Ω) : ℝ :=
  (g (fXW ω) + (pw ω : ℝ) * g (fYU ω) + (qw ω : ℝ) * g (fYV ω)) -
    ((pw ω : ℝ) * g (fXU ω) + (qw ω : ℝ) * g (fXV ω) + g (fYW ω))

lemma AR (θ : Measure Ω) [IsFiniteMeasure θ] {K C : ℝ} (hG : ∀ᵐ ω ∂θ, Good K ω)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (hgC : ∀ z : ℝ × ℝ, |z.1| ≤ K → |z.2| ≤ K → |g z| ≤ C) :
    Integrable g (Am θ) ∧ Integrable g (Rm θ) ∧
      ∫ z, g z ∂(Am θ) = ∫ z, g z ∂(Rm θ) + ∫ ω, Δf g ω ∂θ := by
  have hp1 : ∀ ω, Good K ω → (pw ω : ℝ) ≤ 1 := fun ω hω => (pw_coe hω) ▸ (good_pq hω).2.1
  have hq1 : ∀ ω, Good K ω → (qw ω : ℝ) ≤ 1 := fun ω hω => (qw_coe hω) ▸ (good_pq hω).2.2.2.1
  obtain ⟨i1, j1, e1⟩ := piece θ hG pw m_pw hp1 fXU m_fXU
    (fun ω hω => ⟨hω.2.2.2.1, hω.2.2.2.2.2.1⟩) g hg hgC
  obtain ⟨i2, j2, e2⟩ := piece θ hG qw m_qw hq1 fXV m_fXV
    (fun ω hω => ⟨hω.2.2.2.1, hω.2.2.2.2.2.2.1⟩) g hg hgC
  obtain ⟨i3, j3, e3⟩ := piece1 θ hG fYW m_fYW
    (fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.2.2⟩) g hg hgC
  obtain ⟨i4, j4, e4⟩ := piece1 θ hG fXW m_fXW
    (fun ω hω => ⟨hω.2.2.2.1, hω.2.2.2.2.2.2.2⟩) g hg hgC
  obtain ⟨i5, j5, e5⟩ := piece θ hG pw m_pw hp1 fYU m_fYU
    (fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.1⟩) g hg hgC
  obtain ⟨i6, j6, e6⟩ := piece θ hG qw m_qw hq1 fYV m_fYV
    (fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.2.1⟩) g hg hgC
  refine ⟨(j4.add_measure j5).add_measure j6, (j1.add_measure j2).add_measure j3, ?_⟩
  unfold Am Rm
  rw [integral_add_measure (j4.add_measure j5) j6, integral_add_measure j4 j5,
    integral_add_measure (j1.add_measure j2) j3, integral_add_measure j1 j2,
    e1, e2, e3, e4, e5, e6]
  unfold Δf
  have I45 : Integrable (fun ω => g (fXW ω) + (pw ω : ℝ) * g (fYU ω)) θ := i4.add i5
  have I456 : Integrable (fun ω => g (fXW ω) + (pw ω : ℝ) * g (fYU ω) +
      (qw ω : ℝ) * g (fYV ω)) θ := I45.add i6
  have I12 : Integrable (fun ω => (pw ω : ℝ) * g (fXU ω) + (qw ω : ℝ) * g (fXV ω)) θ :=
    i1.add i2
  have I123 : Integrable (fun ω => (pw ω : ℝ) * g (fXU ω) + (qw ω : ℝ) * g (fXV ω) +
      g (fYW ω)) θ := I12.add i3
  rw [integral_sub I456 I123, integral_add I45 i6, integral_add i4 i5, integral_add I12 i3,
    integral_add i1 i2]
  ring

lemma split (θ : Measure Ω) {K : ℝ} (hG : ∀ᵐ ω ∂θ, Good K ω) :
    θ.withDensity (fun ω => (pw ω : ℝ≥0∞)) + θ.withDensity (fun ω => (qw ω : ℝ≥0∞)) = θ := by
  rw [← withDensity_add_left m_pw.coe_nnreal_ennreal]
  conv_rhs => rw [← withDensity_one (μ := θ)]
  apply withDensity_congr_ae
  filter_upwards [hG] with ω hω
  have : pw ω + qw ω = 1 := by
    apply NNReal.eq
    push_cast
    rw [pw_coe hω, qw_coe hω]
    exact (good_pq hω).2.2.2.2.1
  simp only [Pi.add_apply, Pi.one_apply]
  rw [← ENNReal.coe_add, this, ENNReal.coe_one]

lemma marg_fst (θ : Measure Ω) {K : ℝ} (hG : ∀ᵐ ω ∂θ, Good K ω) :
    (Rm θ).map Prod.fst = (Am θ).map Prod.fst := by
  have hs := split θ hG
  set θp := θ.withDensity (fun ω => (pw ω : ℝ≥0∞))
  set θq := θ.withDensity (fun ω => (qw ω : ℝ≥0∞))
  have mX : Measurable (fun ω : Ω => ω.1.1) := by fun_prop
  have mY : Measurable (fun ω : Ω => ω.2.1) := by fun_prop
  unfold Rm Am
  simp only [Measure.map_add _ _ measurable_fst]
  rw [Measure.map_map measurable_fst m_fXU, Measure.map_map measurable_fst m_fXV,
    Measure.map_map measurable_fst m_fYW, Measure.map_map measurable_fst m_fXW,
    Measure.map_map measurable_fst m_fYU, Measure.map_map measurable_fst m_fYV]
  have c1 : Prod.fst ∘ fXU = fun ω : Ω => ω.1.1 := rfl
  have c2 : Prod.fst ∘ fXV = fun ω : Ω => ω.1.1 := rfl
  have c3 : Prod.fst ∘ fXW = fun ω : Ω => ω.1.1 := rfl
  have c4 : Prod.fst ∘ fYU = fun ω : Ω => ω.2.1 := rfl
  have c5 : Prod.fst ∘ fYV = fun ω : Ω => ω.2.1 := rfl
  have c6 : Prod.fst ∘ fYW = fun ω : Ω => ω.2.1 := rfl
  rw [c1, c2, c3, c4, c5, c6]
  have hX : θ.map (fun ω : Ω => ω.1.1) =
      θp.map (fun ω : Ω => ω.1.1) + θq.map (fun ω : Ω => ω.1.1) := by
    rw [← Measure.map_add _ _ mX, hs]
  have hY : θ.map (fun ω : Ω => ω.2.1) =
      θp.map (fun ω : Ω => ω.2.1) + θq.map (fun ω : Ω => ω.2.1) := by
    rw [← Measure.map_add _ _ mY, hs]
  rw [hX, hY]
  abel

lemma marg_snd (θ : Measure Ω) :
    (Rm θ).map Prod.snd = (Am θ).map Prod.snd := by
  unfold Rm Am
  simp only [Measure.map_add _ _ measurable_snd]
  rw [Measure.map_map measurable_snd m_fXU, Measure.map_map measurable_snd m_fXV,
    Measure.map_map measurable_snd m_fYW, Measure.map_map measurable_snd m_fXW,
    Measure.map_map measurable_snd m_fYU, Measure.map_map measurable_snd m_fYV]
  have c1 : Prod.snd ∘ fXU = Prod.snd ∘ fYU := rfl
  have c2 : Prod.snd ∘ fXV = Prod.snd ∘ fYV := rfl
  have c3 : Prod.snd ∘ fYW = Prod.snd ∘ fXW := rfl
  rw [c1, c2, c3]
  abel

end MartOT.Mono


set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace MartOT.Mono

/-- If a nonzero finite configuration measure `θ` (supported on good configurations) has its removed
mass `Rm θ` below `π`, rerouting gives a martingale plan of strictly smaller cost. -/
lemma improve (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) {h : ℝ → ℝ} (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h))
    (hcI : Integrable (fun p : ℝ × ℝ => h (p.2 - p.1)) π)
    (θ : Measure Ω) [IsFiniteMeasure θ] {K : ℝ} (hG : ∀ᵐ ω ∂θ, Good K ω) (hθ : θ ≠ 0)
    (hR : Rm θ ≤ π) :
    ∃ π', MartOT.Var.IsMartingalePlan μ ν π' ∧
      MartOT.Var.cost (fun x y => h (y - x)) π' < MartOT.Var.cost (fun x y => h (y - x)) π := by
  haveI : IsFiniteMeasure (Rm θ) := isFiniteMeasure_of_le π hR
  have hcancel : π - Rm θ + Rm θ = π := Measure.sub_add_cancel_of_le hR
  have hle : π - Rm θ ≤ π := Measure.sub_le
  have hK : 0 ≤ K := by
    by_contra hneg
    apply hθ
    rw [← Measure.measure_univ_eq_zero]
    have : ∀ᵐ ω ∂θ, False := by
      filter_upwards [hG] with ω hω
      have := hω.2.2.2.1
      have := abs_nonneg ω.1.1
      linarith
    simpa [ae_iff] using this
  refine ⟨π - Rm θ + Am θ, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, ← marg_fst θ hG, ← Measure.map_add _ _ measurable_fst,
      hcancel]
    exact hπ.1.1
  · rw [Measure.map_add _ _ measurable_snd, ← marg_snd θ, ← Measure.map_add _ _ measurable_snd,
      hcancel]
    exact hπ.1.2
  · obtain ⟨hA, -, -⟩ := AR θ hG (fun z : ℝ × ℝ => z.2 - z.1) (by fun_prop) (C := 2 * K)
      (fun z h1 h2 => by
        have := abs_sub z.2 z.1
        linarith)
    exact (hπ.2.1.mono_measure hle).add_measure hA
  · intro ρ hρ hρb
    obtain ⟨Cρ, hCρ⟩ := hρb
    have hC0 : 0 ≤ Cρ := (abs_nonneg _).trans (hCρ 0)
    have hgm : Measurable (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) :=
      (hρ.comp measurable_fst).mul (by fun_prop)
    obtain ⟨hA, hRg, hΔ⟩ := AR θ hG (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) hgm (C := Cρ * (2 * K))
      (fun z h1 h2 => by
        rw [abs_mul]
        have := abs_sub z.2 z.1
        exact mul_le_mul (hCρ _) (by linarith) (abs_nonneg _) hC0)
    have hπg : Integrable (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) π := by
      refine Integrable.mono' (hπ.2.1.norm.const_mul Cρ) hgm.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => ?_))
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hCρ _) (abs_nonneg _)
    have hΔ0 : ∫ ω, Δf (fun z : ℝ × ℝ => ρ z.1 * (z.2 - z.1)) ω ∂θ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hG] with ω hω
      obtain ⟨-, -, -, -, hs, hb⟩ := good_pq hω
      unfold Δf
      simp only [fXW, fYU, fYV, fXU, fXV, fYW, Pi.zero_apply]
      rw [pw_coe hω, qw_coe hω]
      have e1 : pR ω = 1 - qR ω := by linarith
      rw [e1] at hb ⊢
      linear_combination (ρ ω.2.1 - ρ ω.1.1) * hb
    rw [integral_add_measure (hπg.mono_measure hle) hA, hΔ, hΔ0, add_zero,
      ← integral_add_measure (hπg.mono_measure hle) hRg, hcancel]
    exact hπ.2.2 ρ hρ ⟨Cρ, hCρ⟩
  · -- the cost strictly decreases
    obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := -(2 * K)) (b := 2 * K)).exists_bound_of_continuousOn
      hd.continuous.continuousOn
    have hgm : Measurable (fun z : ℝ × ℝ => h (z.2 - z.1)) :=
      hd.continuous.measurable.comp (by fun_prop)
    obtain ⟨hA, hRg, hΔ⟩ := AR θ hG (fun z : ℝ × ℝ => h (z.2 - z.1)) hgm (C := Ch)
      (fun z h1 h2 => by
        have := abs_sub z.2 z.1
        have hz : z.2 - z.1 ∈ Set.Icc (-(2 * K)) (2 * K) := by
          rw [Set.mem_Icc, ← abs_le]; linarith
        simpa [Real.norm_eq_abs] using hCh _ hz)
    have hc' : Integrable (fun z : ℝ × ℝ => h (z.2 - z.1)) (π - Rm θ + Am θ) :=
      (hcI.mono_measure hle).add_measure hA
    have e1 : MartOT.Var.cost (fun x y => h (y - x)) (π - Rm θ + Am θ) =
        ((∫ z, h (z.2 - z.1) ∂(π - Rm θ + Am θ) : ℝ) : EReal) :=
      integralE_eq_coe _ _ hc'
    have e2 : MartOT.Var.cost (fun x y => h (y - x)) π =
        ((∫ z, h (z.2 - z.1) ∂π : ℝ) : EReal) := integralE_eq_coe _ _ hcI
    rw [e1, e2, EReal.coe_lt_coe_iff]
    -- Δ < 0 almost everywhere
    have hneg : ∀ᵐ ω ∂θ, Δf (fun z : ℝ × ℝ => h (z.2 - z.1)) ω < 0 := by
      filter_upwards [hG] with ω hω
      unfold Δf
      simp only [fXW, fYU, fYV, fXU, fXV, fYW]
      rw [pw_coe hω, qw_coe hω]
      unfold pR qR
      have := reroute_lt hd hconv hω.1 hω.2.1 hω.2.2.1
      linarith
    have hb : ∀ z : ℝ × ℝ, |z.1| ≤ K → |z.2| ≤ K → |h (z.2 - z.1)| ≤ Ch := fun z h1 h2 => by
      have := abs_sub z.2 z.1
      have hz : z.2 - z.1 ∈ Set.Icc (-(2 * K)) (2 * K) := by
        rw [Set.mem_Icc, ← abs_le]; linarith
      simpa [Real.norm_eq_abs] using hCh _ hz
    have hΔi : Integrable (Δf (fun z : ℝ × ℝ => h (z.2 - z.1))) θ := by
      have hp1 : ∀ ω, Good K ω → (pw ω : ℝ) ≤ 1 :=
        fun ω hω => (pw_coe hω) ▸ (good_pq hω).2.1
      have hq1 : ∀ ω, Good K ω → (qw ω : ℝ) ≤ 1 :=
        fun ω hω => (qw_coe hω) ▸ (good_pq hω).2.2.2.1
      obtain ⟨i1, -, -⟩ := piece θ hG pw m_pw hp1 fXU m_fXU
        (fun ω hω => ⟨hω.2.2.2.1, hω.2.2.2.2.2.1⟩) _ hgm hb
      obtain ⟨i2, -, -⟩ := piece θ hG qw m_qw hq1 fXV m_fXV
        (fun ω hω => ⟨hω.2.2.2.1, hω.2.2.2.2.2.2.1⟩) _ hgm hb
      obtain ⟨i3, -, -⟩ := piece1 θ hG fYW m_fYW
        (fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.2.2⟩) _ hgm hb
      obtain ⟨i4, -, -⟩ := piece1 θ hG fXW m_fXW
        (fun ω hω => ⟨hω.2.2.2.1, hω.2.2.2.2.2.2.2⟩) _ hgm hb
      obtain ⟨i5, -, -⟩ := piece θ hG pw m_pw hp1 fYU m_fYU
        (fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.1⟩) _ hgm hb
      obtain ⟨i6, -, -⟩ := piece θ hG qw m_qw hq1 fYV m_fYV
        (fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.2.1⟩) _ hgm hb
      exact ((i4.add i5).add i6).sub ((i1.add i2).add i3)
    have hpos : 0 < ∫ ω, -Δf (fun z : ℝ × ℝ => h (z.2 - z.1)) ω ∂θ := by
      have hI : Integrable (fun ω => -Δf (fun z : ℝ × ℝ => h (z.2 - z.1)) ω) θ := hΔi.neg
      refine (integral_pos_iff_support_of_nonneg_ae ?_ hI).2 ?_
      · filter_upwards [hneg] with ω hω
        simp only [Pi.zero_apply]
        linarith
      rw [pos_iff_ne_zero]
      intro h0
      apply hθ
      rw [← Measure.measure_univ_eq_zero]
      set S := Function.support (fun ω => -Δf (fun z : ℝ × ℝ => h (z.2 - z.1)) ω)
      have hsupp : ∀ᵐ ω ∂θ, ω ∈ S := by
        filter_upwards [hneg] with ω hω
        simp only [S, Function.mem_support]
        linarith
      have hc : θ Sᶜ = 0 := by
        have := (ae_iff).1 hsupp
        simpa [Set.compl_def] using this
      refine le_antisymm ?_ zero_le
      calc θ Set.univ = θ (S ∪ Sᶜ) := by rw [Set.union_compl_self]
        _ ≤ θ S + θ Sᶜ := measure_union_le _ _
        _ = 0 := by rw [hc, add_zero]; exact h0
    rw [integral_neg] at hpos
    rw [integral_add_measure (hcI.mono_measure hle) hA, hΔ]
    have := integral_add_measure (hcI.mono_measure hle) hRg
    rw [hcancel] at this
    linarith

end MartOT.Mono


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MartOT.Mono

lemma lint_pos (μ : Measure ℝ) {s : Set ℝ} (hμs : 0 < μ s) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hpos : ∀ x ∈ s, 0 < f x) : 0 < ∫⁻ x in s, f x ∂μ := by
  rw [lintegral_pos_iff_support hf, Measure.restrict_apply (measurableSet_support hf)]
  exact lt_of_lt_of_le hμs (measure_mono (fun x hx => ⟨(hpos x hx).ne', hx⟩))

/-- Construction of the rerouting measure from two positive-measure blocks of first coordinates. -/
lemma build (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    {K : ℝ} {S1 S2 T1 T2 T3 : Set ℝ} (hm1 : MeasurableSet S1) (hm2 : MeasurableSet S2)
    (hm3 : MeasurableSet T1) (hm4 : MeasurableSet T2) (hm5 : MeasurableSet T3)
    (hS1 : 0 < μ S1) (hS2 : 0 < μ S2)
    (hS1T : ∀ x ∈ S1, 0 < κ x T1 ∧ 0 < κ x T2) (hS2T : ∀ x ∈ S2, 0 < κ x T3)
    (hord : ∀ x ∈ S1, ∀ x' ∈ S2, x < x') (hUW : ∀ u ∈ T1, ∀ w ∈ T3, u < w)
    (hWV : ∀ w ∈ T3, ∀ v ∈ T2, w < v)
    (hK1 : ∀ x ∈ S1, |x| ≤ K) (hK2 : ∀ x ∈ S2, |x| ≤ K) (hK3 : ∀ x ∈ T1, |x| ≤ K)
    (hK4 : ∀ x ∈ T2, |x| ≤ K) (hK5 : ∀ x ∈ T3, |x| ≤ K) :
    ∃ θ : Measure Ω, IsFiniteMeasure θ ∧ (∀ᵐ ω ∂θ, Good K ω) ∧ θ ≠ 0 ∧ Rm θ ≤ μ ⊗ₘ κ := by
  set P1 : Measure (ℝ × (ℝ × ℝ)) := μ ⊗ₘ (κ ×ₖ κ) with hP1
  set A1 : Set (ℝ × (ℝ × ℝ)) := S1 ×ˢ (T1 ×ˢ T2) with hA1
  set A2 : Set (ℝ × ℝ) := S2 ×ˢ T3 with hA2
  have mA1 : MeasurableSet A1 := hm1.prod (hm3.prod hm4)
  have mA2 : MeasurableSet A2 := hm2.prod hm5
  set base : Measure Ω := (P1.restrict A1).prod ((μ ⊗ₘ κ).restrict A2) with hbase
  set θ : Measure Ω := (3 : ℝ≥0∞)⁻¹ • base with hθ
  haveI : IsFiniteMeasure θ := ⟨by
    rw [hθ, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩
  have hG : ∀ᵐ ω ∂θ, Good K ω := by
    have hA : ∀ᵐ ω ∂base, ω ∈ A1 ×ˢ A2 := by
      rw [hbase, Measure.prod_restrict A1 A2]
      exact ae_restrict_mem (mA1.prod mA2)
    filter_upwards [Measure.ae_smul_measure hA _] with ω hω
    simp only [hA1, hA2, Set.mem_prod] at hω
    obtain ⟨⟨hx, hu, hv⟩, hx', hw⟩ := hω
    exact ⟨hord _ hx _ hx', hUW _ hu _ hw, hWV _ hw _ hv, hK1 _ hx, hK2 _ hx', hK3 _ hu,
      hK4 _ hv, hK5 _ hw⟩
  refine ⟨θ, inferInstance, hG, ?_, ?_⟩
  · -- θ ≠ 0
    intro h0
    have h1 : θ Set.univ = 0 := by rw [h0]; rfl
    rw [hθ, Measure.smul_apply, smul_eq_mul, ← Set.univ_prod_univ, hbase, Measure.prod_prod,
      Measure.restrict_apply_univ, Measure.restrict_apply_univ] at h1
    have p1 : 0 < P1 A1 := by
      rw [hP1, hA1, Measure.compProd_apply_prod hm1 (hm3.prod hm4)]
      simp_rw [Kernel.prod_apply_prod]
      exact lint_pos μ hS1 ((κ.measurable_coe hm3).mul (κ.measurable_coe hm4))
        (fun x hx => ENNReal.mul_pos (hS1T x hx).1.ne' (hS1T x hx).2.ne')
    have p2 : 0 < (μ ⊗ₘ κ) A2 := by
      rw [hA2, Measure.compProd_apply_prod hm2 hm5]
      exact lint_pos μ hS2 (κ.measurable_coe hm5) hS2T
    rcases mul_eq_zero.1 h1 with h | h
    · simp at h
    · rcases mul_eq_zero.1 h with h | h
      · exact p1.ne' h
      · exact p2.ne' h
  · -- Rm θ ≤ π
    rw [Measure.le_iff]
    intro S hS
    have hp1 : ∀ᵐ ω ∂θ, (pw ω : ℝ≥0∞) ≤ 1 := by
      filter_upwards [hG] with ω hω
      have : pw ω ≤ 1 := by
        rw [← NNReal.coe_le_coe, NNReal.coe_one, pw_coe hω]; exact (good_pq hω).2.1
      exact_mod_cast this
    have hq1 : ∀ᵐ ω ∂θ, (qw ω : ℝ≥0∞) ≤ 1 := by
      filter_upwards [hG] with ω hω
      have : qw ω ≤ 1 := by
        rw [← NNReal.coe_le_coe, NNReal.coe_one, qw_coe hω]; exact (good_pq hω).2.2.2.1
      exact_mod_cast this
    have hP1prob : IsProbabilityMeasure P1 := by rw [hP1]; infer_instance
    have hA2le : (μ ⊗ₘ κ).restrict A2 Set.univ ≤ 1 := by
      rw [Measure.restrict_apply_univ]; exact prob_le_one
    have hA1le : P1.restrict A1 Set.univ ≤ 1 := by
      rw [Measure.restrict_apply_univ]; exact prob_le_one
    have mfst : Measurable (Prod.map (id : ℝ → ℝ) (Prod.fst : ℝ × ℝ → ℝ)) :=
      measurable_id.prodMap measurable_fst
    have msnd : Measurable (Prod.map (id : ℝ → ℝ) (Prod.snd : ℝ × ℝ → ℝ)) :=
      measurable_id.prodMap measurable_snd
    have hPf : P1 (Prod.map id Prod.fst ⁻¹' S) = (μ ⊗ₘ κ) S := by
      rw [← Measure.map_apply mfst hS, hP1, ← Measure.compProd_map measurable_fst]
      congr 2
      simpa [Kernel.fst] using Kernel.fst_prod κ κ
    have hPs : P1 (Prod.map id Prod.snd ⁻¹' S) = (μ ⊗ₘ κ) S := by
      rw [← Measure.map_apply msnd hS, hP1, ← Measure.compProd_map measurable_snd]
      congr 2
      simpa [Kernel.snd] using Kernel.snd_prod κ κ
    have e1 : fXU ⁻¹' S = (Prod.map id Prod.fst ⁻¹' S) ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
      ext ω; simp only [fXU, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]; rfl
    have e2 : fXV ⁻¹' S = (Prod.map id Prod.snd ⁻¹' S) ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
      ext ω; simp only [fXV, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]; rfl
    have e3 : fYW ⁻¹' S = (Set.univ : Set (ℝ × (ℝ × ℝ))) ×ˢ S := by
      ext ω; simp [fYW]
    have b1 : (θ.withDensity (fun ω => (pw ω : ℝ≥0∞))) (fXU ⁻¹' S) ≤ (μ ⊗ₘ κ) S / 3 := by
      rw [withDensity_apply _ (m_fXU hS)]
      calc ∫⁻ ω in fXU ⁻¹' S, (pw ω : ℝ≥0∞) ∂θ ≤ ∫⁻ ω in fXU ⁻¹' S, 1 ∂θ :=
            lintegral_mono_ae (ae_restrict_of_ae hp1)
        _ = θ (fXU ⁻¹' S) := setLIntegral_one _
        _ ≤ (μ ⊗ₘ κ) S / 3 := by
          rw [hθ, Measure.smul_apply, smul_eq_mul, e1, hbase, Measure.prod_prod,
            ENNReal.div_eq_inv_mul]
          gcongr
          calc P1.restrict A1 (Prod.map id Prod.fst ⁻¹' S) * (μ ⊗ₘ κ).restrict A2 Set.univ
              ≤ P1 (Prod.map id Prod.fst ⁻¹' S) * 1 :=
                mul_le_mul' (Measure.restrict_apply_le _ _) hA2le
            _ = (μ ⊗ₘ κ) S := by rw [mul_one, hPf]
    have b2 : (θ.withDensity (fun ω => (qw ω : ℝ≥0∞))) (fXV ⁻¹' S) ≤ (μ ⊗ₘ κ) S / 3 := by
      rw [withDensity_apply _ (m_fXV hS)]
      calc ∫⁻ ω in fXV ⁻¹' S, (qw ω : ℝ≥0∞) ∂θ ≤ ∫⁻ ω in fXV ⁻¹' S, 1 ∂θ :=
            lintegral_mono_ae (ae_restrict_of_ae hq1)
        _ = θ (fXV ⁻¹' S) := setLIntegral_one _
        _ ≤ (μ ⊗ₘ κ) S / 3 := by
          rw [hθ, Measure.smul_apply, smul_eq_mul, e2, hbase, Measure.prod_prod,
            ENNReal.div_eq_inv_mul]
          gcongr
          calc P1.restrict A1 (Prod.map id Prod.snd ⁻¹' S) * (μ ⊗ₘ κ).restrict A2 Set.univ
              ≤ P1 (Prod.map id Prod.snd ⁻¹' S) * 1 :=
                mul_le_mul' (Measure.restrict_apply_le _ _) hA2le
            _ = (μ ⊗ₘ κ) S := by rw [mul_one, hPs]
    have b3 : θ (fYW ⁻¹' S) ≤ (μ ⊗ₘ κ) S / 3 := by
      rw [hθ, Measure.smul_apply, smul_eq_mul, e3, hbase, Measure.prod_prod,
        ENNReal.div_eq_inv_mul]
      gcongr
      calc P1.restrict A1 Set.univ * (μ ⊗ₘ κ).restrict A2 S ≤ 1 * (μ ⊗ₘ κ) S :=
            mul_le_mul' hA1le (Measure.restrict_apply_le _ _)
        _ = (μ ⊗ₘ κ) S := one_mul _
    unfold Rm
    rw [Measure.add_apply, Measure.add_apply, Measure.map_apply m_fXU hS,
      Measure.map_apply m_fXV hS, Measure.map_apply m_fYW hS]
    calc _ ≤ (μ ⊗ₘ κ) S / 3 + (μ ⊗ₘ κ) S / 3 + (μ ⊗ₘ κ) S / 3 := add_le_add (add_le_add b1 b2) b3
      _ = (μ ⊗ₘ κ) S := ENNReal.add_thirds _

end MartOT.Mono


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MartOT.Mono

def Eset (κ : Kernel ℝ ℝ) (M : ℕ) (a0 a d d0 : ℚ) : Set ℝ :=
  {x | |x| < M ∧ 0 < κ x (Set.Ioo (a0 : ℝ) a) ∧ 0 < κ x (Set.Ioo (d : ℝ) d0)}

def Fset (κ : Kernel ℝ ℝ) (M : ℕ) (b c : ℚ) : Set ℝ :=
  {x | |x| < M ∧ 0 < κ x (Set.Ioo (b : ℝ) c)}

open Classical in
noncomputable def Nset (μ : Measure ℝ) (κ : Kernel ℝ ℝ) (M : ℕ) (a0 a b c d d0 q : ℚ) :
    Set ℝ :=
  if μ (Eset κ M a0 a d d0 ∩ Set.Iio (q : ℝ)) = 0 then Eset κ M a0 a d d0 ∩ Set.Iio (q : ℝ)
  else if μ (Fset κ M b c ∩ Set.Ioi (q : ℝ)) = 0 then Fset κ M b c ∩ Set.Ioi (q : ℝ) else ∅

lemma mE (κ : Kernel ℝ ℝ) (M : ℕ) (a0 a d d0 : ℚ) : MeasurableSet (Eset κ M a0 a d d0) := by
  unfold Eset
  rw [Set.setOf_and, Set.setOf_and]
  exact (measurableSet_lt continuous_abs.measurable measurable_const).inter
    ((measurableSet_lt measurable_const (κ.measurable_coe measurableSet_Ioo)).inter
      (measurableSet_lt measurable_const (κ.measurable_coe measurableSet_Ioo)))

lemma mF (κ : Kernel ℝ ℝ) (M : ℕ) (b c : ℚ) : MeasurableSet (Fset κ M b c) := by
  unfold Fset
  rw [Set.setOf_and]
  exact (measurableSet_lt continuous_abs.measurable measurable_const).inter
    (measurableSet_lt measurable_const (κ.measurable_coe measurableSet_Ioo))

lemma Nset_null (μ : Measure ℝ) (κ : Kernel ℝ ℝ) (M : ℕ) (a0 a b c d d0 q : ℚ) :
    μ (Nset μ κ M a0 a b c d d0 q) = 0 := by
  unfold Nset
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact measure_empty

/-- The key claim: no rational split point separates positive masses of `E` (left) and `F`
(right), otherwise `build` + `improve` would produce a cheaper plan. -/
lemma claim (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hno : ∀ (θ : Measure Ω) (K : ℝ), IsFiniteMeasure θ → (∀ᵐ ω ∂θ, Good K ω) → θ ≠ 0 →
      Rm θ ≤ μ ⊗ₘ κ → False)
    (M : ℕ) {a0 a b c d d0 : ℚ} (q : ℚ) (h1 : a0 < a) (h2 : a < b) (h3 : b < c) (h4 : c < d)
    (h5 : d < d0) :
    μ (Eset κ M a0 a d d0 ∩ Set.Iio (q : ℝ)) = 0 ∨ μ (Fset κ M b c ∩ Set.Ioi (q : ℝ)) = 0 := by
  by_contra hcon
  push_neg at hcon
  have r1 : (a0 : ℝ) < a := by exact_mod_cast h1
  have r2 : (a : ℝ) < b := by exact_mod_cast h2
  have r3 : (b : ℝ) < c := by exact_mod_cast h3
  have r4 : (c : ℝ) < d := by exact_mod_cast h4
  have r5 : (d : ℝ) < d0 := by exact_mod_cast h5
  have hT : ∀ y : ℝ, (a0 : ℝ) < y → y < d0 → |y| ≤ (M : ℝ) + |(a0 : ℝ)| + |(d0 : ℝ)| := by
    intro y hy1 hy2
    have := le_abs_self (d0 : ℝ)
    have := neg_abs_le (a0 : ℝ)
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have := abs_nonneg (a0 : ℝ)
    have := abs_nonneg (d0 : ℝ)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨θ, hfin, hG, hθ, hR⟩ := build μ κ (K := (M : ℝ) + |(a0 : ℝ)| + |(d0 : ℝ)|)
    (S1 := Eset κ M a0 a d d0 ∩ Set.Iio (q : ℝ)) (S2 := Fset κ M b c ∩ Set.Ioi (q : ℝ))
    (T1 := Set.Ioo (a0 : ℝ) a) (T2 := Set.Ioo (d : ℝ) d0) (T3 := Set.Ioo (b : ℝ) c)
    ((mE κ M a0 a d d0).inter measurableSet_Iio) ((mF κ M b c).inter measurableSet_Ioi)
    measurableSet_Ioo measurableSet_Ioo measurableSet_Ioo
    (pos_iff_ne_zero.2 hcon.1) (pos_iff_ne_zero.2 hcon.2)
    (fun x hx => ⟨hx.1.2.1, hx.1.2.2⟩) (fun x hx => hx.1.2)
    (fun x hx x' hx' => lt_trans (Set.mem_Iio.1 hx.2) (Set.mem_Ioi.1 hx'.2))
    (fun u hu w hw => by linarith [hu.2, hw.1])
    (fun w hw v hv => by linarith [hw.2, hv.1])
    (fun x hx => by
      have := hx.1.1
      have := abs_nonneg (a0 : ℝ)
      have := abs_nonneg (d0 : ℝ)
      linarith)
    (fun x hx => by
      have := hx.1.1
      have := abs_nonneg (a0 : ℝ)
      have := abs_nonneg (d0 : ℝ)
      linarith)
    (fun x hx => hT x hx.1 (by linarith [hx.2]))
    (fun x hx => hT x (by linarith [hx.1]) hx.2)
    (fun x hx => hT x (by linarith [hx.1]) (by linarith [hx.2]))
  exact hno θ _ hfin hG hθ hR

/-- The support-like set: every rational interval around `y` has positive `κ x`-mass. -/
def Gset (κ : Kernel ℝ ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ u v : ℚ, (u : ℝ) < p.2 → p.2 < v → 0 < κ p.1 (Set.Ioo (u : ℝ) v)}

lemma mG (κ : Kernel ℝ ℝ) : MeasurableSet (Gset κ) := by
  have : Gset κ = ⋂ u : ℚ, ⋂ v : ℚ, ({p : ℝ × ℝ | p.2 ≤ u} ∪ {p | (v : ℝ) ≤ p.2} ∪
      Prod.fst ⁻¹' {x | 0 < κ x (Set.Ioo (u : ℝ) v)}) := by
    ext p
    simp only [Gset, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_preimage]
    constructor
    · intro h u v
      by_cases hu : (u : ℝ) < p.2
      · by_cases hv : p.2 < v
        · exact Or.inr (h u v hu hv)
        · exact Or.inl (Or.inr (not_lt.1 hv))
      · exact Or.inl (Or.inl (not_lt.1 hu))
    · intro h u v hu hv
      rcases h u v with (h | h) | h
      · exact absurd hu (not_lt.2 h)
      · exact absurd hv (not_lt.2 h)
      · exact h
  rw [this]
  refine MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun v => ?_))
  refine (((measurableSet_le measurable_snd measurable_const)).union
    (measurableSet_le measurable_const measurable_snd)).union
    (measurable_fst (measurableSet_lt measurable_const (κ.measurable_coe measurableSet_Ioo)))

lemma G_full (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ) (Gset κ)ᶜ = 0 := by
  have hsub : (Gset κ)ᶜ ⊆ ⋃ u : ℚ, ⋃ v : ℚ,
      {x | κ x (Set.Ioo (u : ℝ) v) = 0} ×ˢ Set.Ioo (u : ℝ) v := by
    intro p hp
    simp only [Gset, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hp
    obtain ⟨u, v, hu, hv, h0⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq, Set.mem_Ioo]
    exact ⟨u, v, le_antisymm h0 zero_le, hu, hv⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null (fun u => measure_iUnion_null (fun v => ?_))
  have hm : MeasurableSet {x | κ x (Set.Ioo (u : ℝ) v) = 0} :=
    measurableSet_eq_fun (κ.measurable_coe measurableSet_Ioo) measurable_const
  rw [Measure.compProd_apply_prod hm measurableSet_Ioo]
  rw [setLIntegral_congr_fun hm (fun x hx => hx)]
  simp

/-- Absent any improving rerouting, `μ ⊗ₘ κ` is left-monotone. -/
lemma mono_of (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hno : ∀ (θ : Measure Ω) (K : ℝ), IsFiniteMeasure θ → (∀ᵐ ω ∂θ, Good K ω) → θ ≠ 0 →
      Rm θ ≤ μ ⊗ₘ κ → False) :
    MartOT.Var.IsLeftMonotone (μ ⊗ₘ κ) := by
  set N : Set ℝ := ⋃ (M : ℕ) (a0 : ℚ) (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) (d0 : ℚ) (q : ℚ),
    Nset μ κ M a0 a b c d d0 q with hN
  have hNnull : μ N = 0 := by
    rw [hN]
    simp only [measure_iUnion_null_iff]
    intro M a0 a b c d d0 q
    exact Nset_null μ κ M a0 a b c d d0 q
  have hNm : MeasurableSet N := by
    rw [hN]
    refine MeasurableSet.iUnion (fun M => MeasurableSet.iUnion (fun a0 => MeasurableSet.iUnion
      (fun a => MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun c =>
      MeasurableSet.iUnion (fun d => MeasurableSet.iUnion (fun d0 =>
      MeasurableSet.iUnion (fun q => ?_))))))))
    unfold Nset
    split_ifs
    · exact (mE κ M a0 a d d0).inter measurableSet_Iio
    · exact (mF κ M b c).inter measurableSet_Ioi
    · exact MeasurableSet.empty
  refine ⟨(Nᶜ ×ˢ Set.univ) ∩ Gset κ, (hNm.compl.prod MeasurableSet.univ).inter (mG κ), ?_, ?_⟩
  · rw [Set.compl_inter]
    refine measure_union_null ?_ (G_full μ κ)
    have : (Nᶜ ×ˢ (Set.univ : Set ℝ))ᶜ = N ×ˢ Set.univ := by
      ext p; simp
    rw [this, Measure.compProd_apply_prod hNm MeasurableSet.univ]
    exact setLIntegral_measure_zero _ _ hNnull
  · rintro x x' ym yp y' ⟨⟨hxN, -⟩, hGm⟩ ⟨-, hGp⟩ ⟨⟨hxN', -⟩, hG'⟩ ⟨hxx, hm, hp⟩
    simp only [Set.mem_compl_iff] at hxN hxN'
    -- rationals around the configuration
    obtain ⟨a0, ha0, ha0'⟩ := exists_rat_btwn (show ym - 1 < ym by linarith)
    obtain ⟨a, ha, ha'⟩ := exists_rat_btwn hm
    obtain ⟨b, hb, hb'⟩ := exists_rat_btwn ha'
    obtain ⟨c, hc, hc'⟩ := exists_rat_btwn hp
    obtain ⟨d, hd, hd'⟩ := exists_rat_btwn hc'
    obtain ⟨d0, hd0, hd0'⟩ := exists_rat_btwn (show yp < yp + 1 by linarith)
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hxx
    obtain ⟨M, hM⟩ := exists_nat_gt (max |x| |x'|)
    have hxE : x ∈ Eset κ M a0 a d d0 :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hM, hGm a0 a ha0' ha, hGp d d0 hd' hd0⟩
    have hxF : x' ∈ Fset κ M b c :=
      ⟨lt_of_le_of_lt (le_max_right _ _) hM, hG' b c hb' hc⟩
    have hcl := claim μ κ hno M q (a0 := a0) (a := a) (b := b) (c := c) (d := d) (d0 := d0)
      (by exact_mod_cast (ha0'.trans ha)) (by exact_mod_cast hb) (by exact_mod_cast (hb'.trans hc))
      (by exact_mod_cast hd) (by exact_mod_cast (hd'.trans hd0))
    have hNs : Nset μ κ M a0 a b c d d0 q ⊆ N := by
      intro z hz
      rw [hN]
      simp only [Set.mem_iUnion]
      exact ⟨M, a0, a, b, c, d, d0, q, hz⟩
    unfold Nset at hNs
    split_ifs at hNs with h1 h2
    · exact hxN (hNs ⟨hxE, hq⟩)
    · exact hxN' (hNs ⟨hxF, hq'⟩)
    · rcases hcl with h | h
      · exact h1 h
      · exact h2 h

end MartOT.Mono


set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MartOT.Mono

theorem main (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h))
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x))) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π)
    (hfin : MartOT.Var.cost (fun x y => h (y - x)) π < ⊤) :
    MartOT.Var.IsLeftMonotone π := by
  have hplan := hπ.1
  have : IsProbabilityMeasure π := by
    constructor
    have h1 := congrArg (fun m : Measure ℝ => m Set.univ) hplan.1.1
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h1
    rw [h1]; exact measure_univ
  have hfst : π.fst = μ := hplan.1.1
  have hdis : μ ⊗ₘ π.condKernel = π := by
    have := Measure.disintegrate π π.condKernel
    rw [hfst] at this
    exact this
  have hcI : Integrable (fun p : ℝ × ℝ => h (p.2 - p.1)) π :=
    cost_integrable μ ν π hplan.1 (fun x y => h (y - x))
      (hd.continuous.measurable.comp (by fun_prop)) hint hfin
  rw [← hdis]
  apply mono_of μ π.condKernel
  intro θ K hfinθ hG hθ hR
  rw [hdis] at hR
  obtain ⟨π', hπ', hlt⟩ := improve μ ν π hplan hd hconv hcI θ hG hθ hR
  exact absurd (hπ.2 π' hπ') (not_le.2 hlt)

end MartOT.Mono

open MeasureTheory in
theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h))
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x))) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π) (hfin : MartOT.Var.cost (fun x y => h (y - x)) π < ⊤) :
    MartOT.Var.IsLeftMonotone π := by
  exact MartOT.Mono.main μ ν hμν h hd hconv hint π hπ hfin
