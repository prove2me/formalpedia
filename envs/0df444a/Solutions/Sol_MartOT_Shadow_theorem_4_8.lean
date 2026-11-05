-- Prove2me | solution 1 for MartOT.Shadow.theorem_4_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:50:00.22547+00:00
-- url     : https://prove2.me/submissions/90b3639b-06da-475b-92b3-c468da2c59a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MartOT_Shadow_lemma_4_6
import Theorems.Thm_MartOT_Shadow_lemma_4_16
import Theorems.Thm_MartOT_Shadow_proposition_4_15
import Theorems.Thm_MartOT_Shadow_lemma_2_9

namespace MartOT.Shadow.T48Aux

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

lemma decomp {p : Measure ℝ} [IsFiniteMeasure p] {a : ℝ} {S : Finset ℝ} (ha : a ∉ S)
    (hS : p (↑(insert a S) : Set ℝ)ᶜ = 0) :
    p = p.restrict (↑S : Set ℝ) + (((p {a}).toNNReal : NNReal) : ENNReal) • Measure.dirac a := by
  rw [ENNReal.coe_toNNReal (measure_ne_top p {a})]
  ext A hA
  rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hA, Measure.dirac_apply' _ hA,
    smul_eq_mul]
  set T : Set ℝ := ↑(insert a S)
  have hT : MeasurableSet T := (Finset.measurableSet _)
  have h1 : p A = p (A ∩ T) := by
    have := measure_inter_add_sdiff A hT (μ := p)
    have h0 : p (A \ T) = 0 := measure_mono_null (fun x hx => hx.2) hS
    rw [h0, add_zero] at this
    exact this.symm
  have hAT : A ∩ T = (A ∩ ↑S) ∪ (A ∩ {a}) := by
    ext x; simp [T, Finset.coe_insert]; tauto
  have hdisj : Disjoint (A ∩ (↑S : Set ℝ)) (A ∩ {a}) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hx⟩ ⟨_, hx'⟩
    rw [Set.mem_singleton_iff] at hx'
    subst hx'; exact ha hx
  rw [h1, hAT, measure_union hdisj (hA.inter (measurableSet_singleton a))]
  congr 1
  by_cases haA : a ∈ A
  · rw [Set.indicator_of_mem haA, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr haA)]
    simp
  · rw [Set.indicator_of_notMem haA]
    have : A ∩ {a} = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro hx rfl; exact haA hx
    rw [this]; simp

lemma finite_case (γ1 ν η1 : Measure ℝ) (h1 : InM γ1) (hν : InM ν) (hη1 : IsShadow ν γ1 η1)
    (S : Finset ℝ) : ∀ p : Measure ℝ, InM p → p (↑S : Set ℝ)ᶜ = 0 → ExtConvexLE (γ1 + p) ν →
      ∃ σ, IsShadow (ν - η1) p σ ∧ IsShadow ν (γ1 + p) (η1 + σ) := by
  haveI := hν.1
  induction S using Finset.induction_on with
  | empty =>
    intro p hp hS _
    have : p = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa using hS
    subst this
    exact ⟨0, isShadow_zero, by simpa using hη1⟩
  | insert a S' ha ih =>
    intro p hp hS hE
    haveI := hp.1
    set α : NNReal := (p {a}).toNNReal with hα
    set δ : Measure ℝ := (α : ENNReal) • Measure.dirac a with hδ
    set q : Measure ℝ := p.restrict (↑S' : Set ℝ) with hq
    have hpq : p = q + δ := decomp ha hS
    have hqM : InM q := inM_of_le Measure.restrict_le_self hp
    have hqS : q (↑S' : Set ℝ)ᶜ = 0 := by
      rw [hq, Measure.restrict_apply' (Finset.measurableSet S')]; simp
    have hδM : InM δ := inM_atom α a
    have hEq : ExtConvexLE (γ1 + q) ν := by
      refine extLE_left ?_ (inM_add h1 hqM) hE
      rw [hpq, ← add_assoc]
      exact Measure.le_add_right le_rfl
    obtain ⟨σ', hσ'1, hσ'2⟩ := ih q hqM hqS hEq
    have hγq : InM (γ1 + q) := inM_add h1 hqM
    have hE' : ExtConvexLE (γ1 + q + δ) ν := by rw [add_assoc, ← hpq]; exact hE
    obtain ⟨η, hη⟩ := shadow_exists (inM_add hγq hδM) hν hE'
    obtain ⟨hle, hδE, hdecomp⟩ := lemma_4_16 α a (γ1 + q) ν hγq hν hE' (η1 + σ') hσ'2 η hη
    have hην : η ≤ ν := hη.1
    have hsubM : InM (ν - (η1 + σ')) := inM_of_le Measure.sub_le hν
    have hδE' : ExtConvexLE δ (ν - (η1 + σ')) :=
      extLE_mono hδE (sub_mono_left' hην hle) hsubM
    obtain ⟨τ, hτ⟩ := shadow_exists hδM hsubM hδE'
    have hητ : η = η1 + σ' + τ := hdecomp τ hτ
    have hστ : σ' + τ ≤ ν - η1 := le_sub_of_add_le' (by rw [← add_assoc, ← hητ]; exact hην)
    have hC : ConvexLE (q + δ) (σ' + τ) := convexLE_add hσ'1.2.1 hτ.2.1
    have hνη : InM (ν - η1) := inM_of_le Measure.sub_le hν
    have hE2 : ExtConvexLE (q + δ) (ν - η1) := extLE_mono (extLE_of_convexLE hC) hστ hνη
    obtain ⟨ρ, hρ⟩ := shadow_exists (inM_add hqM hδM) hνη hE2
    obtain ⟨-, -, hdec2⟩ := lemma_4_16 α a q (ν - η1) hqM hνη hE2 σ' hσ'1 ρ hρ
    have hτ' : IsShadow (ν - η1 - σ') δ τ := by
      rw [sub_sub_eq hη1.1 hσ'1.1]; exact hτ
    have hρeq : ρ = σ' + τ := hdec2 τ hτ'
    refine ⟨ρ, hpq ▸ hρ, ?_⟩
    rw [hpq, ← add_assoc, hρeq, ← add_assoc, ← hητ]
    exact hη


lemma limit_unique {s : ℕ → Measure ℝ} {a b : Measure ℝ} (ha : ConvergesInM s a)
    (hb : ConvergesInM s b) : a = b := by
  haveI := ha.2.1.1; haveI := hb.2.1.1
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact tendsto_nhds_unique (ha.2.2.1 f) (hb.2.2.1 f)

lemma conv_add_left {c : Measure ℝ} (hc : InM c) {s : ℕ → Measure ℝ} {a : Measure ℝ}
    (h : ConvergesInM s a) : ConvergesInM (fun n => c + s n) (c + a) := by
  haveI := hc.1
  refine ⟨fun n => inM_add hc (h.1 n), inM_add hc h.2.1, fun f => ?_, ?_⟩
  · have hint : ∀ μ : Measure ℝ, InM μ → Integrable (fun x => f x) μ := fun μ hμ => by
      haveI := hμ.1; exact f.integrable μ
    have e : (fun n => ∫ x, f x ∂(c + s n)) = fun n => (∫ x, f x ∂c) + ∫ x, f x ∂(s n) :=
      funext fun n => integral_add_measure (hint c hc) (hint _ (h.1 n))
    rw [e, integral_add_measure (hint c hc) (hint a h.2.1)]
    exact (h.2.2.1 f).const_add _
  · have hint : ∀ μ : Measure ℝ, InM μ → Integrable (fun x : ℝ => |x|) μ := fun μ hμ => hμ.2.abs
    have e : (fun n => ∫ x, |x| ∂(c + s n)) = fun n => (∫ x, |x| ∂c) + ∫ x, |x| ∂(s n) :=
      funext fun n => integral_add_measure (hint c hc) (hint _ (h.1 n))
    rw [e, integral_add_measure (hint c hc) (hint a h.2.1)]
    exact h.2.2.2.const_add _

lemma extLE_of_limit {s : ℕ → Measure ℝ} {μ ν : Measure ℝ} (hs : ConvergesInM s μ) (hν : InM ν)
    (h : ∀ n, ExtConvexLE (s n) ν) : ExtConvexLE μ ν := by
  refine ⟨hs.2.1, hν, fun φ hφ h0 => ?_⟩
  set R := ∫⁻ x, ENNReal.ofReal (φ x) ∂ν with hRdef
  rcases eq_or_ne R ⊤ with hR | hR
  · rw [hR]; exact le_top
  have hφc : Continuous φ := hφ.locallyLipschitz.continuous
  have key : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (min (φ x) k) ∂μ ≤ R := by
    intro k
    let f : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound
      ⟨fun x => min (φ x) k, hφc.min continuous_const⟩ k (fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have a1 := min_le_right (φ x) (k : ℝ)
        have a2 := min_le_right (φ y) (k : ℝ)
        have a3 : 0 ≤ min (φ x) (k : ℝ) := le_min (h0 x) (Nat.cast_nonneg k)
        have a4 : 0 ≤ min (φ y) (k : ℝ) := le_min (h0 y) (Nat.cast_nonneg k)
        rw [abs_sub_le_iff]; constructor <;> linarith)
    have hf0 : ∀ x, 0 ≤ f x := fun x => le_min (h0 x) (Nat.cast_nonneg k)
    have hint : ∀ m : Measure ℝ, InM m →
        ∫⁻ x, ENNReal.ofReal (f x) ∂m = ENNReal.ofReal (∫ x, f x ∂m) := fun m hm => by
      haveI := hm.1
      rw [ofReal_integral_eq_lintegral_ofReal (f.integrable m) (Eventually.of_forall hf0)]
    have hn : ∀ n, ∫ x, f x ∂(s n) ≤ R.toReal := by
      intro n
      have h1 : ENNReal.ofReal (∫ x, f x ∂(s n)) ≤ R := by
        rw [← hint _ (hs.1 n)]
        exact le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _))
          ((h n).2.2 φ hφ h0)
      exact (ENNReal.ofReal_le_iff_le_toReal hR).mp h1
    have hlim : ∫ x, f x ∂μ ≤ R.toReal := le_of_tendsto' (hs.2.2.1 f) hn
    have e : ∫⁻ x, ENNReal.ofReal (min (φ x) k) ∂μ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := rfl
    rw [e, hint μ hs.2.1]
    exact (ENNReal.ofReal_le_iff_le_toReal hR).mpr hlim
  have hsup : ∀ x, ENNReal.ofReal (φ x) = ⨆ k : ℕ, ENNReal.ofReal (min (φ x) k) := by
    intro x
    apply le_antisymm
    · obtain ⟨k, hk⟩ := exists_nat_ge (φ x)
      exact le_iSup_of_le k (by rw [min_eq_left hk])
    · exact iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  calc ∫⁻ x, ENNReal.ofReal (φ x) ∂μ = ∫⁻ x, ⨆ k : ℕ, ENNReal.ofReal (min (φ x) k) ∂μ := by
        congr 1; funext x; exact hsup x
    _ = ⨆ k : ℕ, ∫⁻ x, ENNReal.ofReal (min (φ x) k) ∂μ :=
        lintegral_iSup (fun k => (hφc.min continuous_const).measurable.ennreal_ofReal)
          (fun i j hij x => ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.mpr hij)))
    _ ≤ R := iSup_le key

end MartOT.Shadow.T48Aux

open MeasureTheory MartOT.Var MartOT.Shadow MartOT.Shadow.T48Aux in
theorem solution (γ1 γ2 ν : Measure ℝ) (h1 : MartOT.Var.InM γ1) (h2 : MartOT.Var.InM γ2)
    (hν : MartOT.Var.InM ν) (h : MartOT.Var.ExtConvexLE (γ1 + γ2) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν γ1 η1 →
      MartOT.Var.ExtConvexLE γ2 (ν - η1) ∧
      ∀ η2 : Measure ℝ, MartOT.Var.IsShadow (ν - η1) γ2 η2 →
        MartOT.Var.IsShadow ν (γ1 + γ2) (η1 + η2) := by
  intro η1 hη1
  obtain ⟨γs, hfin, hmono, hconv, hleγ⟩ := lemma_2_9 γ2 h2
  have hγsM : ∀ n, InM (γs n) := hconv.1
  have hνη : InM (ν - η1) := inM_of_le Measure.sub_le hν
  have hη1M : InM η1 := inM_of_le hη1.1 hν
  have hEn : ∀ n, ExtConvexLE (γ1 + γs n) ν := fun n =>
    extLE_trans (extLE_of_convexLE (convexLE_add (convexLE_refl h1) (hleγ n))) h
  have hfc : ∀ n, ∃ σ, IsShadow (ν - η1) (γs n) σ ∧ IsShadow ν (γ1 + γs n) (η1 + σ) := by
    intro n
    obtain ⟨S, hS⟩ := hfin n
    exact finite_case γ1 ν η1 h1 hν hη1 S (γs n) (hγsM n) hS (hEn n)
  choose T hT1 hT2 using hfc
  have hA : ExtConvexLE γ2 (ν - η1) := by
    refine extLE_of_limit hconv hνη fun n => ?_
    exact extLE_mono (extLE_of_convexLE (hT1 n).2.1) (hT1 n).1 hνη
  refine ⟨hA, fun η2 hη2 => ?_⟩
  obtain ⟨μI, TI, hμI, hTI, hshI⟩ := proposition_4_15 γs γ2 (ν - η1) hmono hleγ hA T hT1
  have e1 : μI = γ2 := limit_unique hμI hconv
  subst e1
  have hTIeq : TI = η2 := shadow_unique h2 hνη hA hshI hη2
  subst hTIeq
  obtain ⟨μJ, SJ, hμJ, hSJ, hshJ⟩ := proposition_4_15 (fun n => γ1 + γs n) (γ1 + μI) ν
    (fun n => convexLE_add (convexLE_refl h1) (hmono n))
    (fun n => convexLE_add (convexLE_refl h1) (hleγ n)) h (fun n => η1 + T n) hT2
  have e2 : μJ = γ1 + μI := limit_unique hμJ (conv_add_left h1 hconv)
  have e3 : SJ = η1 + TI := limit_unique hSJ (conv_add_left hη1M hTI)
  rw [e2, e3] at hshJ
  exact hshJ
