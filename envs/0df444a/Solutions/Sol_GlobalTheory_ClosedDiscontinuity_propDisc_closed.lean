-- Prove2me | solution 1 for GlobalTheory.ClosedDiscontinuity.propDisc_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:34.395222+00:00
-- url     : https://prove2.me/submissions/f7ed2071-06b9-491c-a78c-384e708f1199

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Theorems.Thm_GlobalTheory_MajInv_maj_lact
import Theorems.Thm_GlobalTheory_MajInv_maj_rmul
import Theorems.Thm_GlobalTheory_MajorantContinuity_compact_bounds
import Theorems.Thm_GlobalTheory_MajorantContinuity_majorant_continuity
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
private lemma exists_nhds_maj_two_sided_norm_sq_bound {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ U ∈ nhds x, ∃ c C : ℝ, 0 < c ∧ ∀ y ∈ U, y ∈ X.dom ∧
      ∀ (τ : X.Ψ) (w : Fin r → ℂ), c * ‖w‖ ^ 2 ≤ X.maj y τ w ∧ X.maj y τ w ≤ C * ‖w‖ ^ 2 := by
  obtain ⟨c, C, hc, hb⟩ :=
    _root_.GlobalTheory.MajorantContinuity.compact_bounds X (isCompact_singleton (x := x)) (by simpa using hx)
  have hev := (_root_.GlobalTheory.MajorantContinuity.majorant_continuity (E := E)).1 r X x hx 1 one_pos
  refine ⟨_, hev, c / 2, 2 * C, by positivity, fun y hy => ⟨hy.1, fun τ w => ?_⟩⟩
  obtain ⟨h1, h2⟩ := hy.2 τ w
  obtain ⟨h3, h4⟩ := hb x rfl τ w
  constructor <;> nlinarith
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
private lemma matrix_eq_of_mulVec_eq_on_span_generators {r : ℕ} {Λ : Submodule (𝓞 E) (Fin r → E)}
    {S : Finset (Fin r → E)} (hS : Submodule.span (𝓞 E) ↑S = Λ)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) {g g' : Matrix (Fin r) (Fin r) E}
    (h : ∀ s ∈ S, g.mulVec s = g'.mulVec s) : g = g' := by
  have htop : Submodule.span E (S : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro v hv
    rw [← hS] at hv
    exact Submodule.span_le_restrictScalars (𝓞 E) E _ hv
  apply Matrix.toLin'.injective
  exact LinearMap.ext_on htop (fun s hs => by simpa using h s hs)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma le_sqrt_mul_of_sq_le_mul_sq {a b k : ℝ} (hk : 0 ≤ k) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (h : a ^ 2 ≤ k * b ^ 2) : a ≤ Real.sqrt k * b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, ← Real.sqrt_mul hk]
  exact Real.sqrt_le_sqrt h
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
private lemma propDisc_arithmetic_group_frames (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X := by
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc
  intro x hx x' hx'
  obtain ⟨U, hU, c, C, hc, hUb⟩ := exists_nhds_maj_two_sided_norm_sq_bound X hx
  obtain ⟨U', hU', c', C', hc', hUb'⟩ := exists_nhds_maj_two_sided_norm_sq_bound X hx'
  refine ⟨U, hU, U', hU', ?_⟩
  obtain ⟨S, hS⟩ := X.Λ_fg
  have hSΛ : ∀ s ∈ S, s ∈ X.Λ := fun s hs => hS ▸ Submodule.subset_span hs
  set K := Real.sqrt (|C| / c')
  set R := K * ∑ s ∈ S, ∑ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) s‖
  have hF := finite_lattice_norm_emb_le X R
  have hpi : (Set.pi Set.univ (fun _ : S =>
      {v : Fin r → E | v ∈ X.Λ ∧ ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ R})).Finite :=
    Set.Finite.pi (fun _ => hF)
  refine (hpi.preimage
    (f := fun γ : GL (Fin r) E => fun s : S => (γ : Matrix (Fin r) (Fin r) E).mulVec s.1)
    ?_).subset ?_
  · intro γ _ γ' _ h
    apply Units.ext
    exact matrix_eq_of_mulVec_eq_on_span_generators hS X.Λ_span (fun s hs => congrFun h ⟨s, hs⟩)
  · rintro γ ⟨hγ, u, hu, u', hu', b, hb, he⟩ s _
    have hs := X.Γ_stab γ hγ
    obtain ⟨hud, hUu⟩ := hUb u hu
    obtain ⟨hud', hUu'⟩ := hUb' u' hu'
    refine ⟨(hs.2 s).1 (hSΛ s s.2), fun τ => ?_⟩
    have hmaj : ∀ w, X.maj u' τ (((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w) =
        X.maj u τ w := fun w => by
      rw [← _root_.GlobalTheory.MajInv.maj_rmul X hud' hb, ← he,
        _root_.GlobalTheory.MajInv.maj_lact X hs]
    have hbound : ∀ w, ‖((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w‖ ≤
        K * ‖w‖ := fun w => by
      apply le_sqrt_mul_of_sq_le_mul_sq (by positivity) (norm_nonneg _) (norm_nonneg _)
      have h1 := (hUu' τ (((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w)).1
      have h2 := (hUu τ w).2
      rw [hmaj] at h1
      have h3 : C * ‖w‖ ^ 2 ≤ |C| * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      rw [div_mul_eq_mul_div, le_div_iff₀ hc']
      nlinarith
    rw [emb_mulVec_torus_haar_measure]
    refine le_trans (hbound _) (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun s => ∑ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) s‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) s.2)
    exact Finset.single_le_sum
      (f := fun τ : X.Ψ => ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) (s : Fin r → E)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
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
theorem _root_.solution :
    ∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X :=
  fun r X => propDisc_arithmetic_group_frames r X
end _root_.GlobalTheory.ClosedDiscontinuity
end GlobalTheory.ClosedDiscontinuity
