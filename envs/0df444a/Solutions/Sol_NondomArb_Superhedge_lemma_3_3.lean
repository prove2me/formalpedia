-- Prove2me | solution 1 for NondomArb.Superhedge.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:11:39.342187+00:00
-- url     : https://prove2.me/submissions/fa2739b6-22ff-43c2-8aca-f840dfe269a1

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod
open NondomArb.Superhedge

namespace L33Aux

/-! ### A criterion for `0 ∈ ri C` -/

lemma lin_eq_dot {d : ℕ} (L : (Fin d → ℝ) →ₗ[ℝ] ℝ) (v : Fin d → ℝ) :
    L v = (fun i => L (fun j => if i = j then 1 else 0)) ⬝ᵥ v := by
  rw [L.pi_apply_eq_sum_univ v, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]

/-- If every linear functional that is nonnegative on the convex set `C` vanishes on `C`, then
the origin lies in the relative interior of `C`. -/
lemma zero_mem_ri {d : ℕ} (C : Set (Fin d → ℝ)) (hC : Convex ℝ C) (hne : C.Nonempty)
    (hP : ∀ y : Fin d → ℝ, (∀ c ∈ C, 0 ≤ y ⬝ᵥ c) → ∀ c ∈ C, y ⬝ᵥ c = 0) :
    (0 : Fin d → ℝ) ∈ intrinsicInterior ℝ C := by
  -- (a) the origin is in the closure of `C`
  have h0cl : (0 : Fin d → ℝ) ∈ closure C := by
    by_contra h
    obtain ⟨L, u, hLu, hLb⟩ := geometric_hahn_banach_point_closed hC.closure isClosed_closure h
    rw [map_zero] at hLu
    set y : Fin d → ℝ := fun i => L (fun j => if i = j then 1 else 0)
    have hy : ∀ c, L c = y ⬝ᵥ c := fun c => lin_eq_dot (L : (Fin d → ℝ) →ₗ[ℝ] ℝ) c
    obtain ⟨c0, hc0⟩ := hne
    have h1 := hP y (fun c hc => by rw [← hy]; exact (hLu.trans (hLb c (subset_closure hc))).le)
      c0 hc0
    have h2 := hLb c0 (subset_closure hc0)
    rw [hy, h1] at h2; linarith
  -- (b) hence it is in the affine span, which then equals its direction
  have h0A : (0 : Fin d → ℝ) ∈ affineSpan ℝ C :=
    closure_minimal (subset_affineSpan ℝ C) (AffineSubspace.closed_of_finiteDimensional _) h0cl
  set D := (affineSpan ℝ C).direction with hD
  have hcar : ((affineSpan ℝ C : Set (Fin d → ℝ))) = (D : Set (Fin d → ℝ)) := by
    rw [hD, AffineSubspace.coe_direction_eq_vsub_set_right h0A]
    ext x; simp
  let φ : (affineSpan ℝ C) ≃ₜ D := Homeomorph.setCongr hcar
  let CD : Set D := {v | (v : Fin d → ℝ) ∈ C}
  have hCD : Convex ℝ CD := hC.linear_preimage D.subtype
  have hpre : ((↑) ⁻¹' C : Set (affineSpan ℝ C)) = φ ⁻¹' CD := by ext p; rfl
  have hint_eq : interior ((↑) ⁻¹' C : Set (affineSpan ℝ C)) = φ ⁻¹' interior CD := by
    rw [hpre, φ.preimage_interior]
  -- (c) `CD` has nonempty interior
  have hintne : (interior CD).Nonempty := by
    obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hC hne
    obtain ⟨p, hp, _⟩ := mem_intrinsicInterior.mp hx
    rw [hint_eq] at hp
    exact ⟨φ p, hp⟩
  -- (d) the origin is an interior point of `CD`
  have hmain : (0 : D) ∈ interior CD := by
    by_contra h
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hCD.interior isOpen_interior h
    rw [map_zero] at hf
    have hle : ∀ a ∈ CD, f a ≤ 0 := by
      intro a ha
      have : a ∈ closure (interior CD) := by
        rw [hCD.closure_interior_eq_closure_of_nonempty_interior hintne]
        exact subset_closure ha
      have hcl : closure (interior CD) ⊆ {a | f a ≤ 0} :=
        closure_minimal (fun a ha => (hf a ha).le) (isClosed_le f.continuous continuous_const)
      exact hcl this
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (f : D →ₗ[ℝ] ℝ)
    have hgD : ∀ v : D, g v = f v := fun v => by
      have := congrArg (fun F : D →ₗ[ℝ] ℝ => F v) hg
      simpa using this
    have hCsub : ∀ c ∈ C, c ∈ D := fun c hc => by
      rw [← SetLike.mem_coe, ← hcar]; exact subset_affineSpan ℝ C hc
    set y : Fin d → ℝ := -(fun i => g (fun j => if i = j then 1 else 0))
    have hy : ∀ c, y ⬝ᵥ c = - g c := fun c => by
      rw [lin_eq_dot g c, neg_dotProduct]
    have hzero := hP y (fun c hc => by
      rw [hy, hgD ⟨c, hCsub c hc⟩]; linarith [hle ⟨c, hCsub c hc⟩ hc])
    have hgC : ∀ c ∈ C, g c = 0 := fun c hc => by
      have := hzero c hc; rw [hy] at this; linarith
    have hspan : D ≤ LinearMap.ker g := by
      rw [hD, direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      simp [vsub_eq_sub, hgC a ha, hgC b hb]
    obtain ⟨a, ha⟩ := hintne
    have h1 := hf a ha
    rw [← hgD a, LinearMap.mem_ker.mp (hspan a.2)] at h1
    exact lt_irrefl _ h1
  -- (e) conclude
  refine mem_intrinsicInterior.mpr ⟨⟨0, h0A⟩, ?_, rfl⟩
  rw [hint_eq]
  exact hmain

/-! ### Measures in `Θ` -/

section Theta
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma qs_mono {Pset : Set (Measure Ω)} {p q : Ω → Prop} (hp : QS Pset p)
    (h : ∀ ω, p ω → q ω) : QS Pset q := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  exact ⟨A, hA, fun ω hω => hsub (fun hp => hω (h ω hp)), h0⟩

lemma theta_integrable {Pset : Set (Measure Ω)} {ΔS : Ω → (Fin d → ℝ)} {f : Ω → ℝ}
    {R : Measure Ω} (hR : R ∈ Theta Pset ΔS f) (hΔS : Measurable ΔS) :
    Integrable ΔS R := by
  obtain ⟨_, _, hfin⟩ := hR
  refine ⟨hΔS.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg (f ω)])

lemma dot_integral {R : Measure Ω} {ΔS : Ω → (Fin d → ℝ)} (hi : Integrable ΔS R)
    (y : Fin d → ℝ) :
    Integrable (fun ω => y ⬝ᵥ ΔS ω) R ∧ ∫ ω, y ⬝ᵥ ΔS ω ∂ R = y ⬝ᵥ ∫ ω, ΔS ω ∂ R := by
  have hcomp : ∀ i, Integrable (fun ω => ΔS ω i) R := fun i => hi.eval i
  refine ⟨?_, ?_⟩
  · show Integrable (fun ω => ∑ i, y i * ΔS ω i) R
    exact integrable_finsetSum _ fun i _ => (hcomp i).const_mul (y i)
  · show ∫ ω, ∑ i, y i * ΔS ω i ∂ R = ∑ i, y i * (∫ ω, ΔS ω ∂ R) i
    rw [integral_finsetSum _ fun i _ => (hcomp i).const_mul (y i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, eval_integral hcomp i]

/-- Mixtures of elements of `Θ` stay in `Θ`, with mixed expectations. -/
lemma mix_theta {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset)
    {ΔS : Ω → (Fin d → ℝ)} {f : Ω → ℝ} {R1 R2 : Measure Ω}
    (hR1 : R1 ∈ Theta Pset ΔS f) (hR2 : R2 ∈ Theta Pset ΔS f) (a : NNReal) (ha1 : a ≤ 1) :
    a • R1 + (1 - a) • R2 ∈ Theta Pset ΔS f := by
  obtain ⟨hp1, ⟨P1, hP1, hac1⟩, hfin1⟩ := hR1
  obtain ⟨hp2, ⟨P2, hP2, hac2⟩, hfin2⟩ := hR2
  refine ⟨⟨?_⟩, ⟨a • P1 + (1 - a) • P2, hP.2.2 P1 hP1 P2 hP2 a ha1, ?_⟩, ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def,
      smul_eq_mul, mul_one]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le ha1, ENNReal.coe_one]
  · intro s hs
    simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      add_eq_zero, mul_eq_zero] at hs ⊢
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (hac1 h1)
    · rcases h2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (hac2 h2)
  · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hfin1,
      ENNReal.mul_lt_top ENNReal.coe_lt_top hfin2⟩

lemma mix_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {R1 R2 : Measure Ω} {X : Ω → F} (h1 : Integrable X R1) (h2 : Integrable X R2) (a : NNReal) :
    ∫ ω, X ω ∂ (a • R1 + (1 - a) • R2) = a • ∫ ω, X ω ∂ R1 + (1 - a) • ∫ ω, X ω ∂ R2 := by
  rw [integral_add_measure h1.smul_measure_nnreal h2.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]

lemma mix_ac {L R1 R2 : Measure Ω} (h1 : L ≪ R1) (h2 : L ≪ R2) (a : NNReal) :
    L ≪ a • R1 + (1 - a) • R2 := by
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    add_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hs
  obtain ⟨hs1, hs2⟩ := hs
  rcases hs1 with ha | hs1
  · rcases hs2 with hb | hs2
    · rw [ha, tsub_zero] at hb; exact absurd hb one_ne_zero
    · exact h2 hs2
  · exact h1 hs1

/-- Lemma 3.2-type construction: the normalised measure with density
`1_B / (1 + |ΔS| + |f|)` with respect to `M`. -/
lemma mkR {Pset : Set (Measure Ω)} {ΔS : Ω → (Fin d → ℝ)} (hΔS : Measurable ΔS) {f : Ω → ℝ}
    (hf : Measurable f) (M : Measure Ω) (hM : M ∈ Pset) [IsProbabilityMeasure M]
    (B : Set Ω) (hBm : MeasurableSet B) (hMB : M B ≠ 0) :
    ∃ R ∈ Theta Pset ΔS f, R ≪ M ∧ R Bᶜ = 0 ∧ (B = Set.univ → M ≪ R) := by
  let g : Ω → ℝ := fun ω => 1 + ‖ΔS ω‖ + |f ω|
  have hg1 : ∀ ω, 1 ≤ g ω := fun ω => by
    simp only [g]; linarith [norm_nonneg (ΔS ω), abs_nonneg (f ω)]
  have hgm : Measurable g := (measurable_const.add hΔS.norm).add hf.abs
  let w : Ω → ENNReal := B.indicator fun ω => ENNReal.ofReal (g ω)⁻¹
  have hwm : Measurable w := (ENNReal.measurable_ofReal.comp hgm.inv).indicator hBm
  have hwpos : ∀ ω ∈ B, w ω ≠ 0 := fun ω hω => by
    simp only [w, Set.indicator_of_mem hω]
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (by linarith [hg1 ω]))).ne'
  let R0 := M.withDensity w
  set c := R0 Set.univ with hc
  have hc_eq : c = ∫⁻ ω, w ω ∂M := by simp [c, R0, withDensity_apply _ MeasurableSet.univ]
  have hw1 : ∀ ω, w ω ≤ 1 := by
    intro ω
    simp only [w]
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (hg1 ω))
    · rw [Set.indicator_of_notMem hω]; exact zero_le_one
  have hctop : c ≠ ⊤ := by
    rw [hc_eq]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ENNReal) ∂M) ?_ (lintegral_mono hw1)
    simp
  have hc0 : c ≠ 0 := by
    rw [hc_eq]
    intro h0
    rw [lintegral_eq_zero_iff hwm] at h0
    apply hMB
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp h0)
    show ¬ (w ω = (0 : Ω → ENNReal) ω)
    exact hwpos ω hω
  let R : Measure Ω := c⁻¹ • R0
  have hRprob : IsProbabilityMeasure R := by
    constructor
    simp only [R, Measure.smul_apply, smul_eq_mul]
    rw [← hc]; exact ENNReal.inv_mul_cancel hc0 hctop
  have hRP : R ≪ M := fun s hs => by
    simp only [R, Measure.smul_apply, smul_eq_mul]
    rw [withDensity_absolutelyContinuous M w hs, mul_zero]
  have hFm : Measurable fun ω => ENNReal.ofReal (‖ΔS ω‖ + |f ω|) :=
    ENNReal.measurable_ofReal.comp (hΔS.norm.add hf.abs)
  refine ⟨R, ⟨hRprob, ⟨M, hM, hRP⟩, ?_⟩, hRP, ?_, ?_⟩
  · simp only [R, lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hFm]
    have hle : ∫⁻ ω, (w * fun ω => ENNReal.ofReal (‖ΔS ω‖ + |f ω|)) ω ∂M ≤ 1 := by
      calc ∫⁻ ω, (w * fun ω => ENNReal.ofReal (‖ΔS ω‖ + |f ω|)) ω ∂M
          ≤ ∫⁻ _, (1 : ENNReal) ∂M := by
            refine lintegral_mono fun ω => ?_
            simp only [Pi.mul_apply, w]
            by_cases hω : ω ∈ B
            · rw [Set.indicator_of_mem hω, ← ENNReal.ofReal_mul (inv_nonneg.mpr
                (by linarith [hg1 ω])), ← ENNReal.ofReal_one]
              refine ENNReal.ofReal_le_ofReal ?_
              have hgpos : 0 < g ω := by linarith [hg1 ω]
              rw [inv_mul_le_iff₀ hgpos, mul_one]
              simp only [g]; linarith
            · rw [Set.indicator_of_notMem hω, zero_mul]; exact zero_le_one
        _ = 1 := by simp
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc0))
      (lt_of_le_of_lt hle ENNReal.one_lt_top)
  · simp only [R, Measure.smul_apply, smul_eq_mul]
    have : R0 Bᶜ = 0 := by
      simp only [R0]
      rw [withDensity_apply _ hBm.compl]
      have : ∫⁻ ω in Bᶜ, w ω ∂M = ∫⁻ ω in Bᶜ, (0 : ENNReal) ∂M :=
        setLIntegral_congr_fun hBm.compl (fun ω hω => Set.indicator_of_notMem hω _)
      rw [this, lintegral_zero]
    rw [this, mul_zero]
  · intro hB s hs
    simp only [R, Measure.smul_apply, smul_eq_mul, mul_eq_zero, ENNReal.inv_eq_zero] at hs
    rcases hs with hs | hs
    · exact absurd hs hctop
    · simp only [R0] at hs
      rw [withDensity_apply' _ s, lintegral_eq_zero_iff hwm] at hs
      have h2 := ae_iff.mp hs
      have hsub : (Set.univ : Set Ω) ⊆ {a | ¬ w a = (0 : Ω → ENNReal) a} := fun ω _ =>
        hwpos ω (hB ▸ Set.mem_univ ω)
      have := measure_mono_null hsub h2
      rwa [Measure.restrict_apply_univ] at this

lemma neg_integral {R : Measure Ω} [IsProbabilityMeasure R] {B : Set Ω} (hBm : MeasurableSet B)
    (hRB : R Bᶜ = 0) {X : Ω → ℝ} (hX : Integrable X R) (hneg : ∀ ω ∈ B, X ω < 0) :
    ∫ ω, X ω ∂ R < 0 := by
  have hRB1 : R B = 1 := by
    have := measure_add_measure_compl (μ := R) hBm
    rw [hRB, add_zero, measure_univ] at this; exact this
  have hY : 0 ≤ᵐ[R] fun ω => -X ω := by
    have : ∀ᵐ ω ∂ R, ω ∈ B := by
      rw [ae_iff]
      have hs : {a | ¬ a ∈ B} = Bᶜ := rfl
      rw [hs, hRB]
    filter_upwards [this] with ω hω
    simp only [Pi.zero_apply]; linarith [hneg ω hω]
  have hpos : 0 < ∫ ω, -X ω ∂ R := by
    rw [integral_pos_iff_support_of_nonneg_ae hY hX.neg]
    refine lt_of_lt_of_le (by rw [hRB1]; exact one_pos) (measure_mono fun ω hω => ?_)
    simp only [Function.mem_support]; linarith [hneg ω hω]
  rw [integral_neg] at hpos
  linarith

/-- The argument preceding (3.1), with a lower bound `L ≪ R`. -/
lemma qs_transfer {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset)
    {ΔS : Ω → (Fin d → ℝ)} (hΔS : Measurable ΔS) {f : Ω → ℝ} (hf : Measurable f)
    (L : Measure Ω) (hL : ∀ P' ∈ Pset, ∃ M ∈ Pset, P' ≪ M ∧ L ≪ M)
    (X : Ω → ℝ) (hX : Measurable X) (hXi : ∀ R ∈ Theta Pset ΔS f, Integrable X R)
    (h : ∀ R ∈ Theta Pset ΔS f, L ≪ R → 0 ≤ ∫ ω, X ω ∂ R) :
    QS Pset (fun ω => 0 ≤ X ω) := by
  set B := {ω | X ω < 0} with hBdef
  have hBm : MeasurableSet B := measurableSet_lt hX measurable_const
  refine ⟨B, hBm, fun ω hω => by simpa [B] using hω, fun P' hP' => ?_⟩
  by_contra hPB
  obtain ⟨M, hM, hP'M, hLM⟩ := hL P' hP'
  haveI := hP.2.1 M hM
  have hMB : M B ≠ 0 := fun h0 => hPB (hP'M h0)
  obtain ⟨RB, hRB, _, hRBc, _⟩ := mkR hΔS hf M hM B hBm hMB
  obtain ⟨RM, hRM, _, _, hMRM⟩ := mkR hΔS hf M hM Set.univ MeasurableSet.univ
    (by rw [measure_univ]; exact one_ne_zero)
  have hMRM' := hMRM rfl
  haveI := hRB.1
  set a := ∫ ω, X ω ∂ RB with ha
  set b := ∫ ω, X ω ∂ RM with hb
  have ha0 : a < 0 := neg_integral hBm hRBc (hXi RB hRB) fun ω hω => hω
  set t : ℝ := (-a) / (2 * (|b| - a + 1)) with ht
  have hden : 0 < 2 * (|b| - a + 1) := by linarith [abs_nonneg b]
  have ht0 : 0 < t := div_pos (by linarith) hden
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hden]; linarith [abs_nonneg b]
  let t' : NNReal := ⟨t, ht0.le⟩
  have ht'1 : t' ≤ 1 := ht1
  have hR' := mix_theta hP hRM hRB t' ht'1
  have hLR' : L ≪ t' • RM + (1 - t') • RB := by
    intro s hs
    simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      add_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hs
    rcases hs.1 with h0 | h0
    · exact absurd (congrArg NNReal.toReal h0) (by simp [t']; exact ht0.ne')
    · exact hLM (hMRM' h0)
  have hint := h _ hR' hLR'
  rw [mix_integral (hXi RM hRM) (hXi RB hRB) t'] at hint
  have hc : ((1 - t' : NNReal) : ℝ) = 1 - t := by
    rw [NNReal.coe_sub ht'1]; rfl
  simp only [NNReal.smul_def, smul_eq_mul, hc] at hint
  change 0 ≤ t * b + (1 - t) * a at hint
  have key : t * (|b| - a) < -a / 2 := by
    have hd1 : (|b| - a + 1) ≠ 0 := by linarith [abs_nonneg b]
    have : t * (2 * (|b| - a + 1)) = -a := by rw [ht]; field_simp
    nlinarith [abs_nonneg b]
  have hbb : t * b ≤ t * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) ht0.le
  nlinarith

end Theta

end L33Aux

namespace L33Aux

lemma generic {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) (L : Measure Ω)
    (hL : ∀ P' ∈ Pset, ∃ M ∈ Pset, P' ≪ M ∧ L ≪ M) :
    (0 : Fin d → ℝ) ∈
      intrinsicInterior ℝ {v | ∃ R ∈ Theta Pset ΔS f, L ≪ R ∧ v = ∫ ω, ΔS ω ∂ R} := by
  apply zero_mem_ri
  · rintro _ ⟨R1, hR1, hL1, rfl⟩ _ ⟨R2, hR2, hL2, rfl⟩ a b ha hb hab
    let a' : NNReal := ⟨a, ha⟩
    have ha1 : a' ≤ 1 := by show a ≤ 1; linarith
    have hb' : ((1 - a' : NNReal) : ℝ) = b := by
      rw [NNReal.coe_sub ha1]; show 1 - a = b; linarith
    refine ⟨a' • R1 + (1 - a') • R2, mix_theta hP hR1 hR2 a' ha1, mix_ac hL1 hL2 a', ?_⟩
    rw [mix_integral (theta_integrable hR1 hΔS) (theta_integrable hR2 hΔS) a']
    simp only [NNReal.smul_def, hb']
    rfl
  · obtain ⟨P0, hP0⟩ := hP.1
    obtain ⟨M, hM, _, hLM⟩ := hL P0 hP0
    haveI := hP.2.1 M hM
    obtain ⟨R, hR, _, _, hMR⟩ := mkR hΔS hf M hM Set.univ MeasurableSet.univ
      (by rw [measure_univ]; exact one_ne_zero)
    exact ⟨_, R, hR, hLM.trans (hMR rfl), rfl⟩
  · intro y hy
    have hym : Measurable fun ω => y ⬝ᵥ ΔS ω := by
      show Measurable fun ω => ∑ i, y i * ΔS ω i
      exact Finset.measurable_sum _ fun i _ =>
        measurable_const.mul ((measurable_pi_apply i).comp hΔS)
    have hqs : QS Pset (fun ω => 0 ≤ y ⬝ᵥ ΔS ω) := by
      refine qs_transfer hP hΔS hf L hL _ hym
        (fun R hR => (dot_integral (theta_integrable hR hΔS) y).1) fun R hR hLR => ?_
      rw [(dot_integral (theta_integrable hR hΔS) y).2]
      exact hy _ ⟨R, hR, hLR, rfl⟩
    have hz := hNA y hqs
    rintro _ ⟨R, hR, hLR, rfl⟩
    rw [← (dot_integral (theta_integrable hR hΔS) y).2]
    obtain ⟨_, ⟨P'', hP'', hRP''⟩, _⟩ := hR
    obtain ⟨A, _, hsub, h0⟩ := hz
    have hae : ∀ᵐ ω ∂ R, y ⬝ᵥ ΔS ω = 0 :=
      measure_mono_null (fun ω hω => hsub hω) (hRP'' (h0 P'' hP''))
    rw [integral_congr_ae hae]; simp

end L33Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) :
    (0 : Fin d → ℝ) ∈ intrinsicInterior ℝ {v | ∃ R ∈ Theta Pset ΔS f, v = ∫ ω, ΔS ω ∂ R} ∧
      ∀ P ∈ Pset, (0 : Fin d → ℝ) ∈
        intrinsicInterior ℝ {v | ∃ R ∈ Theta Pset ΔS f, P ≪ R ∧ v = ∫ ω, ΔS ω ∂ R} := by
  refine ⟨?_, fun P hP0 => ?_⟩
  · have h := L33Aux.generic Pset hP ΔS hΔS hNA f hf 0
      (fun P' hP' => ⟨P', hP', Measure.AbsolutelyContinuous.rfl, fun s _ => rfl⟩)
    have e : {v | ∃ R ∈ Theta Pset ΔS f, v = ∫ ω, ΔS ω ∂ R} =
        {v | ∃ R ∈ Theta Pset ΔS f, (0 : Measure Ω) ≪ R ∧ v = ∫ ω, ΔS ω ∂ R} := by
      ext v
      constructor
      · rintro ⟨R, hR, rfl⟩; exact ⟨R, hR, fun s _ => rfl, rfl⟩
      · rintro ⟨R, hR, _, rfl⟩; exact ⟨R, hR, rfl⟩
    rw [e]; exact h
  · refine L33Aux.generic Pset hP ΔS hΔS hNA f hf P fun P' hP' => ?_
    have h12 : (1/2 : NNReal) ≤ 1 := by norm_num
    refine ⟨(1/2 : NNReal) • P' + (1 - 1/2 : NNReal) • P, hP.2.2 P' hP' P hP0 _ h12, ?_, ?_⟩
    · intro s hs
      simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
        add_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hs
      rcases hs.1 with h0 | h0
      · norm_num at h0
      · exact h0
    · intro s hs
      simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
        add_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hs
      rcases hs.2 with h0 | h0
      · have hne : (1 - 1/2 : NNReal) ≠ 0 := by
          rw [ne_eq, tsub_eq_zero_iff_le, not_le]; norm_num
        exact absurd h0 hne
      · exact h0
