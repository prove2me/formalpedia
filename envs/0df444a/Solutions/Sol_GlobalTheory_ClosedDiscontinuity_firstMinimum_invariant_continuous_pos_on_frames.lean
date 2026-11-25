-- Prove2me | solution 1 for GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:56:42.495931+00:00
-- url     : https://prove2.me/submissions/1317e990-a7b3-4b42-9486-a2a00c4063c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Theorems.Thm_GlobalTheory_MajorantContinuity_compact_bounds
import Theorems.Thm_GlobalTheory_MajorantContinuity_majorant_continuity
import Theorems.Thm_GlobalTheory_maj_lact_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_minimumSq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_minimumSq_two_sided_bounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_c_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.ClosedDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_integral_denominator (x : E) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ IsIntegral ℤ ((b : E) * x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  have hb' : (b : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have : (b : E) * (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) = a := by
    simp [mul_div_cancel₀ _ hb']
  rw [this]
  exact RingOfIntegers.isIntegral_coe a
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_common_denominator_lattice {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    ∃ y : 𝓞 E, y ≠ 0 ∧ ∀ v ∈ X.Λ, ∀ i, IsIntegral ℤ ((y : E) * v i) := by
  classical
  obtain ⟨S, hS⟩ := X.Λ_fg
  choose d hd0 hd using fun x : E => exists_integral_denominator x
  let T : Finset E := S.biUnion fun s => Finset.univ.image s
  refine ⟨∏ t ∈ T, d t, Finset.prod_ne_zero_iff.2 (fun t _ => hd0 t), fun v hv => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem s hs =>
    intro i
    have ht : s i ∈ T :=
      Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩
    rw [← Finset.mul_prod_erase T d ht]
    push_cast
    rw [mul_comm (d (s i) : E), mul_assoc]
    have h1 := (RingOfIntegers.isIntegral_coe (∏ t ∈ T.erase (s i), d t)).mul (hd (s i))
    simpa using h1
  | zero => intro i; simpa using isIntegral_zero
  | add u w _ _ hu hw => intro i; simpa [mul_add] using (hu i).add (hw i)
  | smul a u _ hu =>
    intro i
    have : ((∏ t ∈ T, d t : 𝓞 E) : E) * (a • u) i =
        (a : E) * (((∏ t ∈ T, d t : 𝓞 E) : E) * u i) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact (RingOfIntegers.isIntegral_coe a).mul (hu i)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma finite_denominator_norm_le (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (y : 𝓞 E) (hy : y ≠ 0) (R : ℝ) :
    {a : E | IsIntegral ℤ ((y : E) * a) ∧ ∀ τ ∈ Ψ, ‖τ a‖ ≤ R}.Finite := by
  have hy' : (y : E) ≠ 0 := by simpa using hy
  refine ((Embeddings.finite_of_norm_le E ℂ ((∑ ψ : E →+* ℂ, ‖ψ (y : E)‖) * R)).image
    (fun b => b / (y : E))).subset ?_
  intro a ⟨ha, hR⟩
  refine ⟨(y : E) * a, ⟨ha, fun φ => ?_⟩, by simp [hy']⟩
  have hφ : ‖φ a‖ ≤ R := by
    rcases hΨ φ with h | h
    · exact hR φ h
    · simpa using hR _ h
  rw [map_mul, norm_mul]
  exact mul_le_mul (Finset.single_le_sum (f := fun ψ : E →+* ℂ => ‖ψ (y : E)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)) hφ (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mem_Ψ_or_conjugate_mem {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : E →+* ℂ) :
    τ ∈ X.Ψ ∨ ComplexEmbedding.conjugate τ ∈ X.Ψ := by
  by_cases h : τ ∈ X.Ψ
  · exact Or.inl h
  · right
    rw [X.cmType]
    simpa [ComplexEmbedding.conjugate, star_star] using h
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma finite_lattice_norm_emb_le {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (R : ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ R}.Finite := by
  obtain ⟨y, hy0, hy⟩ := exists_common_denominator_lattice X
  refine (Set.Finite.pi (t := fun _ : Fin r => {a : E | IsIntegral ℤ ((y : E) * a) ∧
      ∀ τ ∈ X.Ψ, ‖τ a‖ ≤ R})
    (fun _ => finite_denominator_norm_le X.Ψ (mem_Ψ_or_conjugate_mem X) y hy0 R)).subset ?_
  intro v ⟨hv, hR⟩ i _
  refine ⟨hy v hv i, fun τ hτ => ?_⟩
  have := hR ⟨τ, hτ⟩
  exact le_trans (by simpa [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb] using norm_le_pi_norm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) i) this
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma emb_mulVec_torus_haar_measure {r : ℕ} (τ : E →+* ℂ) (g : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (g.mulVec v) = (g.map τ).mulVec (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
  ext i
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma la1_lact_rmul_eq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.la1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) = X.la1 x := by
  have hs := X.Γ_stab γ hγ
  obtain ⟨-, hmaj⟩ := _root_.GlobalTheory.maj_lact_rmul r X γ hs x hx b hb
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1 _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  apply congrArg Real.sqrt
  apply congrArg sInf
  ext t
  constructor
  · rintro ⟨v, hv, hv0, rfl⟩
    refine ⟨(↑γ⁻¹ : Matrix (Fin r) (Fin r) E).mulVec v, ?_, ?_, ?_⟩
    · rw [hs.2]; simpa [Matrix.mulVec_mulVec] using hv
    · intro h; apply hv0
      have := congrArg (fun w => (↑γ : Matrix (Fin r) (Fin r) E).mulVec w) h
      simpa [Matrix.mulVec_mulVec] using this
    · refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← hmaj τ, ← emb_mulVec_torus_haar_measure]
      simp [Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, hv0, rfl⟩
    refine ⟨(↑γ : Matrix (Fin r) (Fin r) E).mulVec v, (hs.2 v).1 hv, ?_, ?_⟩
    · intro h; apply hv0
      have := congrArg (fun w => (↑γ⁻¹ : Matrix (Fin r) (Fin r) E).mulVec w) h
      simpa [Matrix.mulVec_mulVec] using this
    · refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← hmaj τ, ← emb_mulVec_torus_haar_measure]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma la1_eq_sqrt_la1sq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    X.la1 = fun x => Real.sqrt (X.firstMinimumSq x) := by
  funext x
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  rfl
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma abs_sub_lt_of_ratio_bounds {L y e ε : ℝ} (hL : 0 ≤ L) (he : 0 < e) (he1 : e ≤ 1)
    (heL : 2 * e * L < ε) (h1 : L ≤ (1 + e) * y) (h2 : y ≤ (1 + e) * L) : |y - L| < ε := by
  have ha : e * y ≤ e * ((1 + e) * L) := mul_le_mul_of_nonneg_left h2 he.le
  have hb : e * ((1 + e) * L) ≤ 2 * e * L := by
    have : 0 ≤ e * L := mul_nonneg he.le hL
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma continuousOn_la1sq_dom {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ContinuousOn X.firstMinimumSq X.dom := by
  intro x hx
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hL0 : 0 ≤ X.firstMinimumSq x := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx
  obtain ⟨e, he0, he1, heL⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ 2 * e * X.firstMinimumSq x < ε := by
    refine ⟨min 1 (ε / (4 * (X.firstMinimumSq x + 1))), by positivity, min_le_left _ _, ?_⟩
    have hm : min 1 (ε / (4 * (X.firstMinimumSq x + 1))) ≤ ε / (4 * (X.firstMinimumSq x + 1)) := min_le_right _ _
    have h4 : ε / (4 * (X.firstMinimumSq x + 1)) * (X.firstMinimumSq x + 1) = ε / 4 := by
      field_simp
    have : min 1 (ε / (4 * (X.firstMinimumSq x + 1))) * X.firstMinimumSq x ≤ ε / 4 := by
      calc _ ≤ ε / (4 * (X.firstMinimumSq x + 1)) * X.firstMinimumSq x := mul_le_mul_of_nonneg_right hm hL0
        _ ≤ ε / (4 * (X.firstMinimumSq x + 1)) * (X.firstMinimumSq x + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = ε / 4 := h4
    linarith
  have hev := (_root_.GlobalTheory.MajorantContinuity.majorant_continuity (E := E)).1 r X x hx e he0
  filter_upwards [nhdsWithin_le_nhds hev] with y hyy
  obtain ⟨hy, hxy⟩ := hyy
  have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hy (k1 := 1 / (1 + e)) (k2 := 1 + e) (by positivity) (by positivity)
    (fun τ w => by
      have := (hxy τ w).1
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith)
    (fun τ w => (hxy τ w).2)
  obtain ⟨h1, h2⟩ := hb
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h1
  rw [Real.dist_eq]
  exact abs_sub_lt_of_ratio_bounds hL0 he0 he1 heL (by linarith) h2
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_pos_lower_bound_of_finite {α : Type} {s : Set α} (hs : s.Finite)
    (f : α → ℝ) (hpos : ∀ v ∈ s, 0 < f v) : ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ s, δ ≤ f v := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨v0, hv0, hmin⟩ := Set.exists_min_image s f hs hne
    exact ⟨f v0, hpos v0 hv0, hmin⟩
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma la1sq_pos_of_mem_dom {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hr : 0 < r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) : 0 < X.firstMinimumSq x := by
  classical
  obtain ⟨c0, C0, hc0, hb⟩ :=
    _root_.GlobalTheory.MajorantContinuity.compact_bounds X (isCompact_singleton (x := x)) (by simpa using hx)
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ0, hτ0⟩ : ∃ τ0 : E →+* ℂ, τ0 ∈ X.Ψ := by
    rcases mem_Ψ_or_conjugate_mem X σ with h | h
    · exact ⟨σ, h⟩
    · exact ⟨_, h⟩
  have hne : (Finset.univ : Finset X.Ψ).Nonempty := ⟨⟨τ0, hτ0⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne X.c
  have hm : 0 < m := (Finset.lt_inf'_iff hne).2 (fun τ _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ)
  let f : (Fin r → E) → ℝ := fun v => ∑ τ : X.Ψ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)
  have hterm : ∀ v (τ : X.Ψ), 0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v) :=
    fun v τ => mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ).le (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ _)
  have hfpos : ∀ v, v ≠ 0 → 0 < f v := by
    intro v hv
    have hemb : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0 v ≠ 0 := by
      intro h; apply hv; ext i
      have := congrFun h i
      simpa [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb] using this
    have h1 : 0 < X.c ⟨τ0, hτ0⟩ * X.maj x ⟨τ0, hτ0⟩ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0 v) :=
      mul_pos (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.maj_pos X hx _ hemb)
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun τ : X.Ψ =>
      X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)) (fun τ _ => hterm v τ)
      (Finset.mem_univ _))
  obtain ⟨δ, hδ, hδf⟩ := exists_pos_lower_bound_of_finite
    ((finite_lattice_norm_emb_le X 1).inter_of_left {v | v ≠ 0}) f (fun v hv => hfpos v hv.2)
  have hlow : ∀ v ∈ X.Λ, v ≠ 0 → min δ (m * c0) ≤ f v := by
    intro v hvΛ hv0
    by_cases hsmall : ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ 1
    · exact le_trans (min_le_left _ _) (hδf v ⟨⟨hvΛ, hsmall⟩, hv0⟩)
    · push_neg at hsmall
      obtain ⟨τ, hτ⟩ := hsmall
      refine le_trans (min_le_right _ _) ?_
      have h1 : m * c0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v) := by
        have hmτ : m ≤ X.c τ := Finset.inf'_le _ (Finset.mem_univ τ)
        have h2 := (hb x rfl τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)).1
        have h3 : c0 ≤ c0 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ^ 2 := by
          have : 1 ≤ ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ^ 2 := by nlinarith
          nlinarith
        calc m * c0 ≤ X.c τ * c0 := mul_le_mul_of_nonneg_right hmτ hc0.le
          _ ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v) :=
            mul_le_mul_of_nonneg_left (by linarith) (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ).le
      exact le_trans h1 (Finset.single_le_sum (f := fun τ : X.Ψ =>
        X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)) (fun τ _ => hterm v τ)
        (Finset.mem_univ _))
  obtain ⟨v0, hv0Λ, hv00⟩ : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : (X.Λ : Set (Fin r → E)) ⊆ {0} := fun v hv => hcon v hv
    have := X.Λ_span
    rw [eq_top_iff] at this
    have h1 := this (Submodule.mem_top (x := fun _ : Fin r => (1 : E)))
    have h2 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ := by
      rw [Submodule.span_le]; intro v hv; simpa using hbot hv
    have h3 := h2 h1
    rw [Submodule.mem_bot] at h3
    exact one_ne_zero (congrFun h3 ⟨0, hr⟩)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  refine lt_of_lt_of_le (lt_min hδ (mul_pos hm hc0)) (le_csInf ⟨f v0, v0, hv0Λ, hv00, rfl⟩ ?_)
  rintro t ⟨v, hv, hv0, rfl⟩
  exact hlow v hv hv0
end GlobalTheory.ClosedDiscontinuity
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ClosedDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ClosedDiscontinuity
namespace _root_.GlobalTheory.ClosedDiscontinuity
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration
  intro r X hr
  refine ⟨fun γ hγ x hx b hb => la1_lact_rmul_eq X hγ hx hb, ?_, fun x hx => ?_⟩
  · rw [la1_eq_sqrt_la1sq]
    exact Real.continuous_sqrt.comp_continuousOn (continuousOn_la1sq_dom X)
  · rw [la1_eq_sqrt_la1sq]
    exact Real.sqrt_pos.2 (la1sq_pos_of_mem_dom X hr hx)
end _root_.GlobalTheory.ClosedDiscontinuity
end GlobalTheory.ClosedDiscontinuity
