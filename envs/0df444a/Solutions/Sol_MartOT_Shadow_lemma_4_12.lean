-- Prove2me | solution 1 for MartOT.Shadow.lemma_4_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:00:41.124254+00:00
-- url     : https://prove2.me/submissions/ce47c45a-e7fa-4949-99fa-31cabd673875
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MartOT_Shadow_lemma_4_6
import Theorems.Thm_MartOT_Shadow_lemma_4_11
import Theorems.Thm_MartOT_Shadow_lemma_4_12_ext

namespace MartOT.Shadow.T412Aux

open MeasureTheory MartOT.Var Filter Topology

lemma inM_of_le {μ ν : Measure ℝ} (h : μ ≤ ν) (hν : InM ν) : InM μ := by
  haveI := hν.1
  exact ⟨isFiniteMeasure_of_le ν h, hν.2.mono_measure h⟩

lemma inM_add {μ ν : Measure ℝ} (hμ : InM μ) (hν : InM ν) : InM (μ + ν) := by
  haveI := hμ.1; haveI := hν.1
  exact ⟨inferInstance, hμ.2.add_measure hν.2⟩

lemma inM_zero : InM (0 : Measure ℝ) := ⟨inferInstance, integrable_zero_measure⟩

lemma inM_atom (α : NNReal) (x : ℝ) : InM ((α : ENNReal) • Measure.dirac x) := by
  haveI : IsFiniteMeasure ((α : ENNReal) • Measure.dirac x) := by
    constructor; simp
  refine ⟨inferInstance, ?_⟩
  exact (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top

lemma integralE_of_nonneg (μ : Measure ℝ) (φ : ℝ → ℝ) (h : ∀ x, 0 ≤ φ x) :
    integralE μ φ = ((∫⁻ x, ENNReal.ofReal (φ x) ∂μ : ENNReal) : EReal) := by
  unfold integralE ModelRiskOT.Duality.extIntegral
  have h2 : ∀ x, (-(φ x : EReal)).toENNReal = 0 := fun x => by
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal, ENNReal.ofReal_eq_zero]; linarith [h x]
  simp only [EReal.real_coe_toENNReal, h2, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

lemma extLE_of_convexLE {μ η : Measure ℝ} (h : ConvexLE μ η) : ExtConvexLE μ η := by
  refine ⟨h.1, h.2.1, fun φ hφ h0 => ?_⟩
  have := h.2.2 φ hφ
  rwa [integralE_of_nonneg _ _ h0, integralE_of_nonneg _ _ h0,
    EReal.coe_ennreal_le_coe_ennreal_iff] at this

lemma extLE_mono {μ η η' : Measure ℝ} (h : ExtConvexLE μ η) (hle : η ≤ η') (hη' : InM η') :
    ExtConvexLE μ η' :=
  ⟨h.1, hη', fun φ hφ h0 => (h.2.2 φ hφ h0).trans (lintegral_mono' hle le_rfl)⟩

lemma extLE_left {μ μ' ν : Measure ℝ} (hle : μ ≤ μ') (hμ : InM μ) (h : ExtConvexLE μ' ν) :
    ExtConvexLE μ ν :=
  ⟨hμ, h.2.1, fun φ hφ h0 => (lintegral_mono' hle le_rfl).trans (h.2.2 φ hφ h0)⟩

lemma extLE_trans {μ η ν : Measure ℝ} (h1 : ExtConvexLE μ η) (h2 : ExtConvexLE η ν) :
    ExtConvexLE μ ν :=
  ⟨h1.1, h2.2.1, fun φ hφ h0 => (h1.2.2 φ hφ h0).trans (h2.2.2 φ hφ h0)⟩

lemma convexLE_refl {μ : Measure ℝ} (h : InM μ) : ConvexLE μ μ :=
  ⟨h, h, fun _ _ => le_rfl⟩

lemma affine_minorant {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∃ a b : ℝ, ∀ x, a * x + b ≤ φ x := by
  set d := derivWithin φ (Set.Ioi 0) 0
  have hint : (0 : ℝ) ∈ interior (Set.univ : Set ℝ) := by simp
  refine ⟨d, φ 0, fun x => ?_⟩
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h1 := hφ.slope_le_leftDeriv_of_mem_interior (Set.mem_univ x) hint hx
    have h2 := hφ.leftDeriv_le_rightDeriv_of_mem_interior hint
    have h3 : slope φ x 0 ≤ d := h1.trans h2
    rw [slope_def_field] at h3
    have hpos : 0 < 0 - x := by linarith
    rw [div_le_iff₀ hpos] at h3
    nlinarith
  · subst hx; simp
  · have h1 := hφ.rightDeriv_le_slope_of_mem_interior hint (Set.mem_univ x) hx
    rw [slope_def_field] at h1
    have hpos : 0 < x - 0 := by linarith
    rw [le_div_iff₀ hpos] at h1
    nlinarith

lemma neg_lintegral_lt_top {μ : Measure ℝ} (hμ : InM μ) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) : ∫⁻ x, (-(φ x : EReal)).toENNReal ∂μ < ⊤ := by
  haveI := hμ.1
  obtain ⟨a, b, hab⟩ := affine_minorant hφ
  have hg : Integrable (fun x : ℝ => |a| * |x| + |b|) μ :=
    (hμ.2.abs.const_mul |a|).add (integrable_const |b|)
  refine lt_of_le_of_lt ?_ hg.lintegral_lt_top
  refine lintegral_mono fun x => ?_
  rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
  apply ENNReal.ofReal_le_ofReal
  have := hab x
  have h1 : -(a * x) ≤ |a| * |x| := by rw [← abs_mul]; exact neg_le_abs _
  have h2 : -b ≤ |b| := neg_le_abs _
  linarith

lemma ereal_aux (Pa Pc : ENNReal) (Na Nc : ENNReal) (ha : Na ≠ ⊤) (hc : Nc ≠ ⊤) :
    (((Pa + Pc : ENNReal) : EReal) - ((Na + Nc : ENNReal) : EReal)) =
      ((Pa : EReal) - (Na : EReal)) + ((Pc : EReal) - (Nc : EReal)) := by
  lift Na to NNReal using ha
  lift Nc to NNReal using hc
  simp only [EReal.coe_ennreal_add, EReal.coe_nnreal_eq_coe_real]
  rw [← EReal.coe_add]
  rcases eq_or_ne Pa ⊤ with rfl | hPa
  · rcases eq_or_ne Pc ⊤ with rfl | hPc
    · simp only [EReal.coe_ennreal_top, EReal.top_add_top, EReal.top_sub_coe]
    · lift Pc to NNReal using hPc
      simp only [EReal.coe_ennreal_top, EReal.coe_nnreal_eq_coe_real, EReal.top_add_coe,
        EReal.top_sub_coe]
      rw [← EReal.coe_sub, EReal.top_add_coe]
  · lift Pa to NNReal using hPa
    rcases eq_or_ne Pc ⊤ with rfl | hPc
    · simp only [EReal.coe_ennreal_top, EReal.coe_nnreal_eq_coe_real, EReal.coe_add_top,
        EReal.top_sub_coe]
      rw [← EReal.coe_sub, EReal.coe_add_top]
    · lift Pc to NNReal using hPc
      simp only [EReal.coe_nnreal_eq_coe_real]
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
      congr 1
      ring

lemma integralE_add {a c : Measure ℝ} (ha : InM a) (hc : InM c) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) :
    integralE (a + c) φ = integralE a φ + integralE c φ := by
  have h1 := neg_lintegral_lt_top ha hφ
  have h2 := neg_lintegral_lt_top hc hφ
  unfold integralE ModelRiskOT.Duality.extIntegral at *
  rw [lintegral_add_measure, lintegral_add_measure]
  exact ereal_aux _ _ _ _ h1.ne h2.ne

lemma convexLE_add {a b c d : Measure ℝ} (h1 : ConvexLE a b) (h2 : ConvexLE c d) :
    ConvexLE (a + c) (b + d) := by
  refine ⟨inM_add h1.1 h2.1, inM_add h1.2.1 h2.2.1, fun φ hφ => ?_⟩
  rw [integralE_add h1.1 h2.1 hφ, integralE_add h1.2.1 h2.2.1 hφ]
  exact add_le_add (h1.2.2 φ hφ) (h2.2.2 φ hφ)


lemma sub_sub_eq {ν a b : Measure ℝ} [IsFiniteMeasure ν] (ha : a ≤ ν) (hb : b ≤ ν - a) :
    ν - a - b = ν - (a + b) := by
  haveI : IsFiniteMeasure a := isFiniteMeasure_of_le ν ha
  haveI : IsFiniteMeasure (ν - a) := isFiniteMeasure_of_le ν Measure.sub_le
  haveI : IsFiniteMeasure b := isFiniteMeasure_of_le (ν - a) hb
  have hab : a + b ≤ ν := by
    rw [Measure.le_iff] at hb ⊢
    intro s hs
    have := hb s hs
    rw [Measure.sub_apply hs ha] at this
    rw [Measure.add_apply]
    calc a s + b s ≤ a s + (ν s - a s) := add_le_add le_rfl this
      _ = ν s := add_tsub_cancel_of_le (ha s)
  ext s hs
  rw [Measure.sub_apply hs hb, Measure.sub_apply hs ha, Measure.sub_apply hs hab,
    Measure.add_apply, tsub_tsub]

lemma le_sub_of_add_le' {ν a b : Measure ℝ} [IsFiniteMeasure ν] (h : a + b ≤ ν) :
    b ≤ ν - a := by
  have ha : a ≤ ν := le_trans (Measure.le_add_right le_rfl) h
  haveI : IsFiniteMeasure a := isFiniteMeasure_of_le ν ha
  rw [Measure.le_iff] at h ⊢
  intro s hs
  rw [Measure.sub_apply hs ha]
  have := h s hs
  rw [Measure.add_apply] at this
  exact ENNReal.le_sub_of_add_le_left (measure_ne_top a s) this

lemma sub_mono_left' {η ν c : Measure ℝ} [IsFiniteMeasure ν] (hην : η ≤ ν) (hc : c ≤ η) :
    η - c ≤ ν - c := by
  haveI : IsFiniteMeasure c := isFiniteMeasure_of_le ν (hc.trans hην)
  apply Measure.sub_le_of_le_add
  rw [Measure.sub_add_cancel_of_le (hc.trans hην)]
  exact hην

lemma shadow_exists {μ ν : Measure ℝ} (hμ : InM μ) (hν : InM ν) (h : ExtConvexLE μ ν) :
    ∃ η, IsShadow ν μ η :=
  (lemma_4_6 μ ν hμ hν h).1.exists

lemma shadow_unique {μ ν a b : Measure ℝ} (hμ : InM μ) (hν : InM ν) (h : ExtConvexLE μ ν)
    (ha : IsShadow ν μ a) (hb : IsShadow ν μ b) : a = b :=
  (lemma_4_6 μ ν hμ hν h).1.unique ha hb

lemma isShadow_zero {ν : Measure ℝ} : IsShadow ν 0 0 :=
  ⟨Measure.zero_le _, convexLE_refl inM_zero, fun _ _ h => h⟩


lemma mass_eq {μ η : Measure ℝ} (h : ConvexLE μ η) : μ Set.univ = η Set.univ := by
  have h1 := h.2.2 (fun _ => 1) (convexOn_const 1 convex_univ)
  rw [integralE_of_nonneg _ _ (fun _ => zero_le_one),
    integralE_of_nonneg _ _ (fun _ => zero_le_one)] at h1
  simp only [ENNReal.ofReal_one, lintegral_const, one_mul,
    EReal.coe_ennreal_le_coe_ennreal_iff] at h1
  have h2 := h.2.2 (fun _ => -1) (convexOn_const (-1) convex_univ)
  unfold integralE ModelRiskOT.Duality.extIntegral at h2
  have e1 : (1 : EReal).toENNReal = 1 := by
    rw [← EReal.coe_one, EReal.real_coe_toENNReal, ENNReal.ofReal_one]
  simp only [EReal.coe_neg, EReal.coe_one, neg_neg, e1] at h2
  have e : ∀ m : Measure ℝ, ∫⁻ (_ : ℝ), (-1 : EReal).toENNReal ∂m = 0 := fun m => by
    rw [EReal.toENNReal_of_nonpos (by norm_num)]; simp
  rw [e, e] at h2
  simp only [lintegral_const, one_mul, EReal.coe_ennreal_zero, zero_sub] at h2
  rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff] at h2
  exact le_antisymm h1 h2

lemma eq_of_le_of_mass {a b : Measure ℝ} [IsFiniteMeasure b] (hab : a ≤ b)
    (hm : a Set.univ = b Set.univ) : a = b := by
  haveI : IsFiniteMeasure a := isFiniteMeasure_of_le b hab
  have hc : (b - a) Set.univ = 0 := by
    rw [Measure.sub_apply MeasurableSet.univ hab, hm, tsub_self]
  have h0 : b - a = 0 := Measure.measure_univ_eq_zero.mp hc
  have := Measure.sub_add_cancel_of_le hab
  rw [h0, zero_add] at this
  exact this

end MartOT.Shadow.T412Aux

open MeasureTheory NNReal MartOT.Var MartOT.Shadow MartOT.Shadow.T412Aux in
theorem solution (α : ℝ≥0) (x : ℝ) (γ ν : Measure ℝ) (hγ : MartOT.Var.InM γ) (hν : MartOT.Var.InM ν)
    (h : MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x + γ) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x) η1 →
      MartOT.Var.ExtConvexLE γ (ν - η1) ∧
      ∀ η2 : Measure ℝ, MartOT.Var.IsShadow (ν - η1) γ η2 →
        MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x + γ) (η1 + η2) := by
  intro η1 hη1
  haveI := hν.1
  set δ : Measure ℝ := (α : ENNReal) • Measure.dirac x with hδ
  have hδM : InM δ := inM_atom α x
  refine ⟨lemma_4_12_ext α x γ ν hγ hν h η1 hη1, fun η2 hη2 => ?_⟩
  haveI : IsFiniteMeasure η1 := isFiniteMeasure_of_le ν hη1.1
  refine ⟨?_, convexLE_add hη1.2.1 hη2.2.1, fun η' hη'ν hC => ?_⟩
  · calc η1 + η2 ≤ η1 + (ν - η1) := add_le_add le_rfl hη2.1
      _ = ν := by rw [add_comm]; exact Measure.sub_add_cancel_of_le hη1.1
  · have hη'M : InM η' := hC.2.1
    haveI := hη'M.1
    have hE' : ExtConvexLE (δ + γ) η' := extLE_of_convexLE hC
    have hδE : ExtConvexLE δ η' := extLE_left (Measure.le_add_right le_rfl) hδM hE'
    obtain ⟨a, ha⟩ := shadow_exists hδM hη'M hδE
    haveI : IsFiniteMeasure a := isFiniteMeasure_of_le η' ha.1
    have hγE : ExtConvexLE γ (η' - a) := lemma_4_12_ext α x γ η' hγ hη'M hE' a ha
    obtain ⟨b, hb⟩ := shadow_exists hγ (inM_of_le Measure.sub_le hη'M) hγE
    -- `η' = a + b`
    have hab : a + b ≤ η' := by
      calc a + b ≤ a + (η' - a) := add_le_add le_rfl hb.1
        _ = η' := by rw [add_comm]; exact Measure.sub_add_cancel_of_le ha.1
    have hCab : ConvexLE (δ + γ) (a + b) := convexLE_add ha.2.1 hb.2.1
    have hη'eq : a + b = η' := eq_of_le_of_mass hab ((mass_eq hCab).symm.trans (mass_eq hC))
    -- monotonicity of the shadow in the target, and Lemma 4.11
    have h411 : η' - a ≤ ν - η1 := lemma_4_11 α x η' ν hν hη'ν hδE a η1 ha hη1
    have h1 : ConvexLE η1 a := hη1.2.2 a (ha.1.trans hη'ν) ha.2.1
    have h2 : ConvexLE η2 b := hη2.2.2 b (hb.1.trans h411) hb.2.1
    rw [← hη'eq]
    exact convexLE_add h1 h2
