-- Prove2me | solution 1 for GlobalTheory.LeadIndep.leadM_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:03:42.445166+00:00
-- url     : https://prove2.me/submissions/cbcbcddf-558e-4499-9ded-29d93a8e54df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadMCoeffEqZero
import Theorems.Thm_GlobalTheory_LeadIndep_mem_multiLt
import Theorems.Thm_GlobalTheory_LeadIndep_lowest_degree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_nmat_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_cd_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_isOpen_dom
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app


section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.LeadIndep
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem coeff_eq_zero_of_monomial_sum_eq_zero {n : ℕ} (M : Finset (Fin n → ℕ)) (B : (Fin n → ℕ) → ℂ)
    (h : ∀ y : V n, ∑ α ∈ M, B α * ∏ q, y q ^ α q = 0) : ∀ α ∈ M, B α = 0 := by
  classical
  let P : MvPolynomial (Fin n) ℂ :=
    ∑ α ∈ M, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (B α)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro y
    have hy := h (WithLp.toLp 2 y)
    simp only at hy
    simp only [P, map_zero, map_sum, MvPolynomial.eval_monomial]
    rw [← hy]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  intro α hα
  have hc := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α)) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero,
    (Finsupp.equivFunOnFinite).symm.injective.eq_iff] at hc
  rwa [Finset.sum_ite_eq' M α B, if_pos hα] at hc
end GlobalTheory.LeadIndep
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeadIndep
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LeadIndep
theorem _root_.solution : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ),
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsSec G (t k)) →
    (∀ u : Fin δ → ℂ, (∀ j, ∑ k, u k * t k (Fl.xs j) = 0) → u = 0) →
    ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      (∀ j, (fun z : V (nd X) => leadM X Fl.s Fl.w0 t T a cc (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a) →
      ∀ α ∈ multiLt (nd X) a, ∀ k, cc α k = 0 := by
  classical
  intro r X Xa Fl G T a δ t ht hind cc hO
  by_contra hne
  push Not at hne
  obtain ⟨α1, hα1, k1, hk1⟩ := hne
  set S := (multiLt (nd X) a).filter (fun α => ∃ k, cc α k ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨α1, Finset.mem_filter.2 ⟨hα1, k1, hk1⟩⟩
  obtain ⟨α0, hα0S, hα0d⟩ := Finset.exists_mem_eq_inf' hS (fun α => ∑ q, α q)
  set d := S.inf' hS (fun α => ∑ q, α q) with hd
  have hα0M := (Finset.mem_filter.1 hα0S).1
  have hlow : ∀ α ∈ multiLt (nd X) a, ∀ k, cc α k ≠ 0 → d ≤ ∑ q, α q := fun α hα k hk =>
    Finset.inf'_le _ (Finset.mem_filter.2 ⟨hα, k, hk⟩)
  have hda : d < a := hα0d ▸ mem_multiLt.1 hα0M
  have key : ∀ j, ∀ α ∈ multiLt (nd X) a, ∑ q, α q = d → ∑ k, cc α k * t k (Fl.xs j) = 0 := by
    intro j
    have hdomo := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X
    have hcd : Differentiable ℂ (cpt X (Fl.xs j)) :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.cd_cpt X (Fl.xs j)).differentiable (by simp)
    have hc0 : cpt X (Fl.xs j) 0 = Fl.xs j := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X (Fl.xs j)
    have hUo : IsOpen (cpt X (Fl.xs j) ⁻¹' X.dom) := hdomo.preimage hcd.continuous
    have h0U : (0 : V (nd X)) ∈ cpt X (Fl.xs j) ⁻¹' X.dom := by
      simp only [Set.mem_preimage, hc0]
      exact Fl.xs_mem j
    have hcomp : ∀ P : Frame X.Ψ r → ℂ, DifferentiableOn ℂ P X.dom →
        DifferentiableOn ℂ (fun z => P (cpt X (Fl.xs j) z)) (cpt X (Fl.xs j) ⁻¹' X.dom) :=
      fun P hP z hz => ((hP.differentiableAt (hdomo.mem_nhds hz)).comp z
        (hcd z)).differentiableWithinAt
    have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 := by
      refine (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, nmat X 0, ?_, ?_⟩
      · intro τ
        have hm := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.nmat_zero X τ
        refine ⟨by rw [hm]; simp, fun p c hpc => ?_⟩
        have := congrFun (congrFun hm p) c
        simp only [mat, Matrix.of_apply] at this
        rw [this, Matrix.one_apply_ne (ne_of_gt hpc)]
      · have hr : rmul (Fl.xs j) (nmat X 0) = Fl.xs j := hc0
        rw [hr]
        funext τ
        simp [lact, mat, Matrix.map_one]
        rfl
    have main := fun h0 => lowest_degree (cpt X (Fl.xs j) ⁻¹' X.dom) hUo 0 h0U
      (fun q z => Fl.s q (cpt X (Fl.xs j) z)) (fun z => Fl.w0 (cpt X (Fl.xs j) z))
      (fun k z => t k (cpt X (Fl.xs j) z)) (multiLt (nd X) a) T a d cc
      (fun q => hcomp _ (Fl.s_van q).1.1.1.1) (hcomp _ Fl.weightForm_vanishes.1.1.1.1)
      (fun k => hcomp _ (ht k).1) (fun q => by simp only [hc0, hs0])
      (by simp only [hc0]; exact Fl.w0_ne j) hlow hda
      (by
        obtain ⟨C, hC⟩ := (hO j).bound
        refine ⟨C, hC.mono fun z hz => ?_⟩
        simpa [leadM, monoM, norm_pow] using hz) h0
    simp only [hc0] at main
    have hsurj := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (Fl.coord j)))).2
    have hB := coeff_eq_zero_of_monomial_sum_eq_zero (multiLt (nd X) a)
      (fun α => (∑ k, cc α k * t k (Fl.xs j)) * 0 ^ (∑ q, α q - d) *
        Fl.w0 (Fl.xs j) ^ (∑ q, α q + (T - ∑ q, α q))) (fun y => by
          obtain ⟨h0, hh0⟩ := hsurj y
          have := main h0
          rw [← hh0]
          exact this)
    intro α hα hαd
    have := hB α hα
    rw [hαd, Nat.sub_self, pow_zero, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (Fl.w0_ne j))
  have hu : cc α0 = 0 := hind (cc α0) (fun j => key j α0 hα0M hα0d.symm)
  obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hα0S).2
  exact hk (congrFun hu k)
end GlobalTheory.LeadIndep
