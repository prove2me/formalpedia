-- Prove2me | solution 1 for GlobalTheory.pnorm_le_exp_neg_tt_near_cusp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:04.105633+00:00
-- url     : https://prove2.me/submissions/593dc4b2-45c4-414a-9a4b-1830ce67eea2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OneAddInvFirstMinimumLeOfMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_minimumSq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_minimumSq_two_sided_bounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_c_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
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
namespace GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace CuspDecay
end CuspDecay
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma isUStab_one' {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (L : Submodule (𝓞 E) (Fin r → E)) : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L (1 : GL (Fin r) E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab
  simp
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma lact_one_eq_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
  funext τ
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.mat]
  rfl
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma one_div_la1_nonneg {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    0 ≤ 1 / X.la1 x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma one_div_mul_le_one_div_of_ratio_bounds {k c m0 m1 : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hp : 0 < 1 / (c * m0)) (h1 : m0 ≤ k * m1) (h2 : m1 ≤ k * m0) :
    1 / k * (1 / (c * m0)) ≤ 1 / (c * m1) := by
  have hp' : 0 < c * m0 := one_div_pos.mp hp
  have hm0 : 0 < m0 := by
    by_contra h
    push_neg at h
    nlinarith
  have hm1 : 0 < m1 := by nlinarith
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (mul_pos hc hm1)
  nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mul_iInf_le_iInf_of_mul_le {ι : Type*} [Finite ι] {f g : ι → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i, k * g i ≤ f i) : k * ⨅ i, g i ≤ ⨅ i, f i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp [Real.iInf_of_isEmpty]
  | inr _ =>
    exact le_ciInf fun i =>
      (mul_le_mul_of_nonneg_left (ciInf_le (Set.finite_range g).bddBelow i) hk).trans (h i)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma one_add_one_div_sqrt_le_two_mul {s0 s1 k : ℝ} (hk : 0 < k) (hk2 : k ≤ 2) (hs0 : 0 ≤ s0)
    (h1 : s0 ≤ k * s1) (h2 : s1 ≤ k * s0) : 1 + 1 / √s1 ≤ 2 * (1 + 1 / √s0) := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    have hs1 : s1 ≤ 0 := by simpa using h2
    simp [Real.sqrt_eq_zero'.mpr hs1]
  · have hs1 : 0 < s1 := by nlinarith
    have hu := Real.sqrt_pos.mpr h
    have hv := Real.sqrt_pos.mpr hs1
    have h4 : s0 ≤ 4 * s1 := by nlinarith
    have hle : √s0 ≤ 2 * √s1 := by
      rw [show (2 : ℝ) * √s1 = √(4 * s1) by
        rw [Real.sqrt_mul' _ hs1.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h4
    have h3 : 1 / √s1 ≤ 2 / √s0 := by
      rw [div_le_div_iff₀ hv hu]
      linarith
    have h5 : 2 / √s0 = 2 * (1 / √s0) := by ring
    have h6 : 0 ≤ 1 / √s0 := by positivity
    linarith
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exp_half_le_of_comparable_lemma_4 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ps : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ)
    {a θ C A' : ℝ} (ha : 0 ≤ a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hps : ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, 1 ≤ X.tt ξ x τ) →
      ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * ((1 - θ) / 4)) * a * ⨅ τ, X.tt ξ x τ)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (htt : ∀ τ, 2 ≤ X.tt ξ x τ)
    (hcmp : ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + (1 - θ) / 2) * X.maj y τ v ∧
      X.maj y τ v ≤ (1 + (1 - θ) / 2) * X.maj x τ v) :
    Real.exp (ps y / 2) ≤ Real.exp ((C + |A'| * Real.log 2) / 2) *
      (1 + 1 / X.la1 x) ^ (|A'| / 2) * Real.exp (-4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ) := by
  have hT0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => by linarith only [htt τ]
  have hla0 : 0 ≤ 1 / X.la1 x := one_div_la1_nonneg X x
  have htty : ∀ τ, 1 / (1 + (1 - θ) / 2) * X.tt ξ x τ ≤ X.tt ξ y τ := by
    intro τ
    have hpos := htt τ
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt] at hpos ⊢
    exact one_div_mul_le_one_div_of_ratio_bounds (by linarith only [hθ1]) (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ) (by linarith only [hpos])
      (hcmp τ _).1 (hcmp τ _).2
  have hty1 : ∀ τ, 1 ≤ X.tt ξ y τ := by
    intro τ
    have h1 := htty τ
    have h2 := htt τ
    have h3 : 1 ≤ 1 / (1 + (1 - θ) / 2) * X.tt ξ x τ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith only [hθ1])]
      linarith only [h2, hθ0]
    linarith only [h1, h3]
  have hTy : 1 / (1 + (1 - θ) / 2) * ⨅ τ, X.tt ξ x τ ≤ ⨅ τ, X.tt ξ y τ :=
    mul_iInf_le_iInf_of_mul_le (by positivity) htty
  have hsq := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hy (k1 := 1 / (1 + (1 - θ) / 2)) (k2 := 1 + (1 - θ) / 2)
    (by positivity) (by linarith only [hθ1])
    (fun τ w => by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith only [hθ1])]
      linarith only [(hcmp τ w).1])
    (fun τ w => (hcmp τ w).2)
  have hL : 1 + 1 / X.la1 y ≤ 2 * (1 + 1 / X.la1 x) := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1]
    refine one_add_one_div_sqrt_le_two_mul (k := 1 + (1 - θ) / 2) (by linarith only [hθ1]) (by linarith only [hθ0])
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx) ?_ hsq.2
    have h := hsq.1
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith only [hθ1])] at h
    linarith only [h]
  have hly0 : 0 ≤ 1 / X.la1 y := one_div_la1_nonneg X y
  have hLy0 : 0 ≤ Real.log (1 + 1 / X.la1 y) := Real.log_nonneg (le_add_of_nonneg_right hly0)
  have hLyle : Real.log (1 + 1 / X.la1 y) ≤ Real.log 2 + Real.log (1 + 1 / X.la1 x) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt (by linarith only [hla0]))]
    exact Real.log_le_log (by linarith only [hly0]) hL
  have hpsy := hps y hy ξ hξ hty1
  have hA : A' * Real.log (1 + 1 / X.la1 y) ≤
      |A'| * (Real.log 2 + Real.log (1 + 1 / X.la1 x)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self A') hLy0).trans
      (mul_le_mul_of_nonneg_left hLyle (abs_nonneg _))
  have hθε : θ * (1 + (1 - θ) / 2) ≤ 1 - 2 * ((1 - θ) / 4) := by nlinarith [sq_nonneg (θ - 1)]
  have hkey : θ * ⨅ τ, X.tt ξ x τ ≤ (1 - 2 * ((1 - θ) / 4)) * ⨅ τ, X.tt ξ y τ := by
    have h1 : θ * ⨅ τ, X.tt ξ x τ ≤
        (1 - 2 * ((1 - θ) / 4)) * (1 / (1 + (1 - θ) / 2) * ⨅ τ, X.tt ξ x τ) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hT0
      rw [mul_one_div, le_div_iff₀ (by linarith only [hθ1])]
      exact hθε
    exact h1.trans (mul_le_mul_of_nonneg_left hTy (by linarith only [hθ0]))
  have hexp : ps y / 2 ≤ (C + |A'| * Real.log 2) / 2 +
      Real.log (1 + 1 / X.la1 x) * (|A'| / 2) + -4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ := by
    have h8 := mul_le_mul_of_nonneg_left hkey (by positivity : 0 ≤ 8 * Real.pi * a)
    linarith only [hpsy, hA, h8]
  calc Real.exp (ps y / 2)
      ≤ Real.exp ((C + |A'| * Real.log 2) / 2 +
          Real.log (1 + 1 / X.la1 x) * (|A'| / 2) + -4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ) :=
        Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by linarith only [hla0])]
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ v ∧ X.maj (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) → (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (ps : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ) (a : ℝ), X.IsSec la F → _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.cfwM X ps a → 0 ≤ a → (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (X.pnorm la F x) ≤ ENNReal.ofReal C * ⨆ (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (_ : ‖z‖ < ρ) (_ : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom), ENNReal.ofReal (Real.exp (ps (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) / 2))) → ∀ θ a' : ℝ, 0 < θ → θ < 1 → a' = θ * a → ∃ C A : ℝ, 0 ≤ A ∧ ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, 2 ≤ X.tt ξ x τ) → X.pnorm la F x ≤ C * (1 + 1 / X.la1 x) ^ A * Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ)) := by
  intro hcpt hinv hstat r X la F ps a hsec hcf ha hbound θ a' hθ0 hθ1 ha'
  obtain ⟨-, -, hpinv⟩ := hstat
  obtain ⟨ρ, hρ0, hρ1, hnear⟩ := hcpt r X ((1 - θ) / 2) (by linarith)
  obtain ⟨C₀, hC₀⟩ := hbound ρ hρ0 hρ1
  obtain ⟨C, A', hps⟩ := hcf.2 ((1 - θ) / 4) (by linarith) (by linarith)
  refine ⟨max C₀ 0 * Real.exp ((C + |A'| * Real.log 2) / 2), |A'| / 2, by positivity, ?_⟩
  intro x hx ξ hξ htt
  have hb : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
  obtain ⟨hx₀, hmaj₀⟩ := hinv r X 1 (isUStab_one' _ _) x hx _ hb
  have hpn := hpinv r X la F hsec 1 (one_mem _) x hx _ hb
  rw [lact_one_eq_self] at hx₀ hmaj₀ hpn
  have horth : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
  generalize _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) = x₀ at hx₀ hmaj₀ hpn horth
  have hmaj : ∀ τ v, X.maj x₀ τ v = X.maj x τ v := by
    intro τ v
    simpa using hmaj₀ τ v
  have htt₀ : ∀ τ, X.tt ξ x₀ τ = X.tt ξ x τ := by
    intro τ
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt, hmaj]
  have hla : X.la1 x₀ = X.la1 x := by
    have h := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hx₀ (k1 := 1) (k2 := 1) zero_le_one one_pos
      (fun τ w => by rw [hmaj, one_mul]) (fun τ w => by rw [hmaj, one_mul])
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1]
    exact congrArg Real.sqrt (by linarith [h.1, h.2])
  have hT0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => by linarith only [htt τ]
  have hla0 : 0 ≤ 1 / X.la1 x := one_div_la1_nonneg X x
  have hsup : ⨆ (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (_ : ‖z‖ < ρ) (_ : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x₀ z ∈ X.dom),
      ENNReal.ofReal (Real.exp (ps (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x₀ z) / 2)) ≤
        ENNReal.ofReal (Real.exp ((C + |A'| * Real.log 2) / 2) * (1 + 1 / X.la1 x) ^ (|A'| / 2) *
          Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ)) := by
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun _ => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hy, hcmp⟩ := hnear x₀ horth z hz
    have h := exp_half_le_of_comparable_lemma_4 X ps ha hθ0 hθ1 hps hx₀ hy hξ
      (fun τ => by rw [htt₀]; exact htt τ) hcmp
    rwa [hla, ← ha', iInf_congr htt₀] at h
  have hB0 : 0 ≤ Real.exp ((C + |A'| * Real.log 2) / 2) * (1 + 1 / X.la1 x) ^ (|A'| / 2) *
      Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith only [hla0]) _))
      (Real.exp_pos _).le
  have hfin := (hC₀ x₀ hx₀ horth).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0)) hsup)
  rw [← ENNReal.ofReal_mul (le_max_right _ _), hpn,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_max_right _ _) hB0)] at hfin
  calc X.pnorm la F x ≤ _ := hfin
    _ = _ := by ring
end _root_.GlobalTheory
end GlobalTheory
