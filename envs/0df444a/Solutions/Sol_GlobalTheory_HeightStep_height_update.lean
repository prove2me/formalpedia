-- Prove2me | solution 1 for GlobalTheory.HeightStep.height_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:46.667811+00:00
-- url     : https://prove2.me/submissions/6e30c4fb-5091-409b-baab-7bb39e02cd42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsMaximalMinorNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightUpdateFrameComponent
import Theorems.Thm_GlobalTheory_LatBasis_exists_basis_mem
import Theorems.Thm_GlobalTheory_exists_maximal_minor_ne_zero_of_linearIndependent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightStep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HeightStep
namespace _root_.GlobalTheory.HeightStep
theorem _root_.solution : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (d : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (τ0 : X.Ψ) (W : Submodule E (Fin r → E)), ∃ M : Matrix (Fin r) (Fin (Module.finrank E W)) ℂ, 0 < (((M)ᴴ * (M)).det.re) ∧ ∀ a : Matrix (Fin r) (Fin r) ℂ, a.det ≠ 0 → d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W = d x W * ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  classical
  intro r X d hd x hx τ0 W
  obtain ⟨w, hli, hmem, hspan⟩ := _root_.GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, -, hdet⟩ := _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hli
  set N : X.Ψ → Matrix (Fin r) (Fin (Module.finrank E W)) ℂ :=
    fun τ => Matrix.of fun k a => τ.1 (w a k) with hN
  set M := (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0)⁻¹ * N τ0 with hM
  have hA : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0).det := isUnit_iff_ne_zero.mpr (hx τ0)
  have hminor : (Matrix.of fun k a => N τ0 (e k) a).det ≠ 0 := by
    have hmap : (Matrix.of fun k a => N τ0 (e k) a) =
        τ0.1.mapMatrix (Matrix.of fun k a => w a (e k)) := by
      ext k a
      rfl
    rw [hmap, ← RingHom.map_det]
    exact (map_ne_zero τ0.1).mpr hdet
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    rw [← sub_eq_zero]
    have h0 : M *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have h1 : N τ0 *ᵥ (u - v) = 0 := by
      have : N τ0 = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * M := by
        rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
      rw [this, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hminor
    funext k
    have := congrFun h1 (e k)
    simpa [Matrix.mulVec, dotProduct] using this
  have hpos : 0 < ((Mᴴ * M).det.re) := by
    have := (Matrix.PosDef.conjTranspose_mul_self M hinj).det_pos
    exact (Complex.pos_iff.mp this).1
  refine ⟨M, hpos, fun a ha => ?_⟩
  set x' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := @Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _)
    x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ) with hx'
  have haU : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hupd : ∀ τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ = if τ = τ0 then _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ else _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := by
    intro τ
    by_cases h : τ = τ0
    · subst h
      rw [if_pos rfl, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_self _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ _
    · rw [if_neg h, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_of_ne _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ h _ _
  have hx'det : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det ≠ 0 := by
    intro τ
    rw [hupd]
    split_ifs
    · rw [Matrix.det_mul]
      exact mul_ne_zero (hx τ0) (Matrix.isUnit_nonsing_inv_det a haU).ne_zero
    · exact hx τ
  set F : X.Ψ → ℝ := fun τ => (((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)).det.re with hF
  have h1 := hd x' hx'det _ w hli hmem
  have h2 := hd x hx _ w hli hmem
  rw [hspan] at h1 h2
  rw [h1, h2]
  have hprod' : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      (((a * M)ᴴ * (a * M)).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Function.update_apply, hupd]
    split_ifs with h
    · subst h
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a haU, Matrix.mul_assoc]
    · rfl
  have hprod : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      ((Mᴴ * M).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0), Function.update_eq_self]
  rw [hprod', hprod]
  have hne : (Mᴴ * M).det.re ≠ 0 := hpos.ne'
  field_simp
end _root_.GlobalTheory.HeightStep
end GlobalTheory.HeightStep
