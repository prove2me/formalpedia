-- Prove2me | solution 1 for ModularCurve.periodHomPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1a914f92-0a3a-5021-a397-b848aa716f75

import Definitions.Def_ModularCurve_PeriodHomPair
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_periodMap_eq_periodHom
import Theorems.Thm_ModularCurve_existsPeriodMapLinear
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodHomPair_injective

set_option Elab.async false
set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ExistsPeriodMapLinear periodHomPair periodHomPair_def periodMap Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom existsPeriodMapLinear"
namespace SolESINJ
namespace Period
p2m_open "ModularCurve"

open UpperHalfPlane Filter Topology Complex Function ModularForm Metric
open scoped MatrixGroups Real CongruenceSubgroup ModularForm Manifold

section Constancy

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

theorem sub_eq_const_of_forall_hasDerivAt {F G : ℂ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt F (f τ) ↑τ) (hG : ∀ τ : ℍ, HasDerivAt G (f τ) ↑τ) :
    ∃ c : ℂ, ∀ τ : ℍ, F ↑τ - G ↑τ = c := by
  refine ⟨F ↑UpperHalfPlane.I - G ↑UpperHalfPlane.I, fun τ => ?_⟩
  exact apply_eq_apply_of_hasDerivAt_zero
    (D := fun z => F z - G z) (fun σ => by have h__af := (hF σ).sub (hG σ); simp at h__af; exact h__af) τ UpperHalfPlane.I

end Constancy

section ChainRule

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z)) ((g ∣[(2:ℤ)] γ) τ) ↑τ := by

  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]

  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rw [← hfun] at hcomp
  convert hcomp using 1 <;> try rfl
  exact SL_slash_apply (g : ℍ → ℂ) γ τ

end ChainRule

end ModularCurve.SolESINJ.Period

namespace ModularCurve
p2m_export "ModularCurve" "ExistsPeriodMapLinear periodHomPair periodHomPair_def periodMap Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom existsPeriodMapLinear"
namespace SolESINJ
p2m_open "ModularCurve"

open UpperHalfPlane Complex

def reflect (τ : ℍ) : ℍ :=
  ⟨-(starRingEnd ℂ) (τ : ℂ), by simpa using τ.2⟩

@[scoped simp] theorem coe_reflect (τ : ℍ) : (reflect τ : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl

@[scoped simp] theorem reflect_re (τ : ℍ) : (reflect τ).re = -τ.re := by
  show (-(starRingEnd ℂ) (τ : ℂ)).re = -(τ : ℂ).re
  simp

@[scoped simp] theorem reflect_im (τ : ℍ) : (reflect τ).im = τ.im := by
  show (-(starRingEnd ℂ) (τ : ℂ)).im = (τ : ℂ).im
  simp

@[scoped simp] theorem reflect_reflect (τ : ℍ) : reflect (reflect τ) = τ := by
  ext : 1
  simp

end ModularCurve.SolESINJ
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve"

open UpperHalfPlane Filter Topology CongruenceSubgroup Set
open scoped MatrixGroups ComplexConjugate Modular Interval ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "ExistsPeriodMapLinear periodHomPair periodHomPair_def periodMap Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom existsPeriodMapLinear"
namespace SolESINJ
p2m_open "ModularCurve"

open Period

section ImaginaryConstant

theorem deriv_eq_zero_of_re_eq_zero {B : ℂ → ℂ} {b : ℂ}
    {τ : ℍ} (hB : HasDerivAt B b ↑τ)
    (hre : ∀ σ : ℍ, (B ↑σ).re = 0) : b = 0 := by
  classical
  have hUopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ {w : ℂ | 0 < w.im} := τ.im_pos

  have hzero : ∀ w ∈ {w : ℂ | 0 < w.im}, (Complex.reCLM ∘ B) w = (fun _ : ℂ => (0:ℝ)) w := by
    intro w hw
    have : (B ↑(⟨w, hw⟩ : ℍ)).re = 0 := hre ⟨w, hw⟩
    simpa using this
  have hev : (Complex.reCLM ∘ B) =ᶠ[𝓝 (τ : ℂ)] (fun _ : ℂ => (0:ℝ)) :=
    Filter.eventuallyEq_of_mem (hUopen.mem_nhds hτU) hzero

  have h1 : HasFDerivAt (Complex.reCLM ∘ B)
      (Complex.reCLM.comp (((1 : ℂ →L[ℂ] ℂ).smulRight b).restrictScalars ℝ)) (τ : ℂ) :=
    (Complex.reCLM.hasFDerivAt).comp (τ : ℂ) (hB.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (Complex.reCLM ∘ B) (0 : ℂ →L[ℝ] ℝ) (τ : ℂ) :=
    (hasFDerivAt_const (0:ℝ) (τ : ℂ)).congr_of_eventuallyEq hev
  have hD := h1.unique h2

  have e1 : b.re = 0 := by
    have := DFunLike.congr_fun hD (1 : ℂ)
    simpa using this
  have e2 : b.im = 0 := by
    have := DFunLike.congr_fun hD (Complex.I)
    simpa using this
  exact Complex.ext e1 e2

theorem apply_eq_apply_of_re_eq_zero {B : ℂ → ℂ} {b : ℍ → ℂ}
    (hB : ∀ τ : ℍ, HasDerivAt B (b τ) ↑τ)
    (hre : ∀ σ : ℍ, (B ↑σ).re = 0) (z w : ℍ) : B ↑z = B ↑w := by
  refine apply_eq_apply_of_hasDerivAt_zero (fun τ => ?_) z w
  have hb0 : b τ = 0 := deriv_eq_zero_of_re_eq_zero (hB τ) hre
  simpa [hb0] using hB τ

end ImaginaryConstant
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section StripIdentity

variable {Φ : ℂ → ℂ} {Φ' : ℍ → ℂ} {p : ℝ} {A : ℂ}

theorem continuous_horizontal (hΦ : ∀ τ : ℍ, HasDerivAt Φ (Φ' τ) ↑τ) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => Φ (↑x + ↑y * Complex.I) := by
  have hmap : Continuous fun x : ℝ => (↑x + ↑y * Complex.I : ℂ) :=
    Complex.continuous_ofReal.add continuous_const
  rw [continuous_iff_continuousAt]
  intro x₀
  have hpt : ((↑x₀ + ↑y * Complex.I : ℂ)).im = y := by simp
  have hmem : (0:ℝ) < ((↑x₀ + ↑y * Complex.I : ℂ)).im := by rw [hpt]; exact hy
  have hΦc : ContinuousAt Φ (↑x₀ + ↑y * Complex.I) := by
    have := (hΦ ⟨_, hmem⟩).differentiableAt.continuousAt
    simpa using this
  have hcomp : ContinuousAt (Φ ∘ fun x : ℝ => (↑x + ↑y * Complex.I : ℂ)) x₀ :=
    ContinuousAt.comp (f := fun x : ℝ => (↑x + ↑y * Complex.I : ℂ)) hΦc hmap.continuousAt
  exact hcomp

theorem continuousOn_vertical (hΦ : ∀ τ : ℍ, HasDerivAt Φ (Φ' τ) ↑τ) {c : ℝ}
    {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (h12 : y₁ ≤ y₂) :
    ContinuousOn (fun s : ℝ => Φ (↑c + ↑s * Complex.I)) (Set.uIcc y₁ y₂) := by
  have hmap : Continuous fun s : ℝ => (↑c + ↑s * Complex.I : ℂ) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  intro s hs
  rw [Set.uIcc_of_le h12] at hs
  have hspos : 0 < s := lt_of_lt_of_le hy₁ hs.1
  have hpt : ((↑c + ↑s * Complex.I : ℂ)).im = s := by simp
  have hmem : (0:ℝ) < ((↑c + ↑s * Complex.I : ℂ)).im := by rw [hpt]; exact hspos
  have hΦc : ContinuousAt Φ (↑c + ↑s * Complex.I) := by
    have := (hΦ ⟨_, hmem⟩).differentiableAt.continuousAt
    simpa using this
  have hcomp : ContinuousAt (Φ ∘ fun s : ℝ => (↑c + ↑s * Complex.I : ℂ)) s :=
    ContinuousAt.comp (f := fun s : ℝ => (↑c + ↑s * Complex.I : ℂ)) hΦc hmap.continuousAt
  exact hcomp.continuousWithinAt

theorem horizontal_integral_eq_of_re_periodic_of_tendsto
    (hΦ : ∀ τ : ℍ, HasDerivAt Φ (Φ' τ) ↑τ) (hp : 0 < p)
    (hper : ∀ τ : ℍ, (Φ (↑τ + ↑p) - Φ ↑τ).re = 0)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ w : ℂ, Y ≤ w.im → ‖Φ w - A‖ ≤ ε)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in (0:ℝ)..p, Φ (↑x + ↑y * Complex.I)) = ↑p * A := by
  classical
  have hp' : p ≠ 0 := ne_of_gt hp

  set B : ℂ → ℂ := fun w => Φ (w + ↑p) - Φ w with hBdef
  have hBderiv : ∀ τ : ℍ, HasDerivAt B (Φ' ((p : ℝ) +ᵥ τ) - Φ' τ) ↑τ := by
    intro τ
    have him : (0:ℝ) < ((τ : ℂ) + ↑p).im := by simpa using τ.im_pos
    have hcoe : ((((p : ℝ) +ᵥ τ) : ℍ) : ℂ) = (τ : ℂ) + ↑p := by
      rw [UpperHalfPlane.coe_vadd]
      ring
    have h1 : HasDerivAt Φ (Φ' ((p : ℝ) +ᵥ τ)) ((τ : ℂ) + ↑p) := by
      have := hΦ ((p : ℝ) +ᵥ τ)
      rwa [hcoe] at this
    have h2 : HasDerivAt (fun w : ℂ => Φ (w + ↑p)) (Φ' ((p : ℝ) +ᵥ τ)) ↑τ := by
      have hshift : HasDerivAt (fun w : ℂ => w + ↑p) 1 ↑τ := by
        simpa using (hasDerivAt_id (τ : ℂ)).add_const (↑p : ℂ)
      have := h1.comp (τ : ℂ) hshift
      simp at this
      exact this
    exact h2.sub (hΦ τ)
  have hBre : ∀ σ : ℍ, (B ↑σ).re = 0 := fun σ => hper σ

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ σ : ℍ, B ↑σ = c := by
    refine ⟨B ↑(UpperHalfPlane.I), fun σ => ?_⟩
    exact apply_eq_apply_of_re_eq_zero hBderiv hBre σ UpperHalfPlane.I
  have hcre : c.re = 0 := by
    have := hBre UpperHalfPlane.I
    rw [hc UpperHalfPlane.I] at this
    exact this

  have key : ∀ t : ℝ, y ≤ t →
      (∫ x in (0:ℝ)..p, Φ (↑x + ↑y * Complex.I))
        = (∫ x in (0:ℝ)..p, Φ (↑x + ↑t * Complex.I)) - ((t : ℂ) - (y : ℂ)) * (Complex.I * c) := by
    intro t hyt

    set zc : ℂ := ↑y * Complex.I with hzc
    set wc : ℂ := ↑p + ↑t * Complex.I with hwc
    have hzre : zc.re = 0 := by simp [hzc]
    have hzim : zc.im = y := by simp [hzc]
    have hwre : wc.re = p := by simp [hwc]
    have hwim : wc.im = t := by simp [hwc]

    have hrect : DifferentiableOn ℂ Φ ([[zc.re, wc.re]] ×ℂ [[zc.im, wc.im]]) := by
      intro ζ hζ
      have hζim : ζ.im ∈ [[zc.im, wc.im]] := hζ.2
      rw [hzim, hwim, Set.uIcc_of_le hyt] at hζim
      have hζpos : (0:ℝ) < ζ.im := lt_of_lt_of_le hy hζim.1
      exact ((hΦ ⟨ζ, hζpos⟩).differentiableAt).differentiableWithinAt
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn Φ zc wc hrect
    rw [hzre, hzim, hwre, hwim] at hcauchy
    simp only [smul_eq_mul] at hcauchy

    have hleft : ContinuousOn (fun s : ℝ => Φ (↑(0:ℝ) + ↑s * Complex.I)) (Set.uIcc y t) :=
      continuousOn_vertical hΦ hy hyt
    have hright : ContinuousOn (fun s : ℝ => Φ (↑p + ↑s * Complex.I)) (Set.uIcc y t) :=
      continuousOn_vertical hΦ hy hyt
    have hBconst : ∀ s : ℝ, s ∈ Set.uIcc y t →
        Φ (↑p + ↑s * Complex.I) - Φ (↑(0:ℝ) + ↑s * Complex.I) = c := by
      intro s hs
      rw [Set.uIcc_of_le hyt] at hs
      have hspos : 0 < s := lt_of_lt_of_le hy hs.1
      have hmem : (0:ℝ) < ((↑(0:ℝ) + ↑s * Complex.I : ℂ)).im := by simpa using hspos
      have hpoint : ((⟨↑(0:ℝ) + ↑s * Complex.I, hmem⟩ : ℍ) : ℂ) + ↑p
          = ↑p + ↑s * Complex.I := by
        push_cast
        ring
      have := hc ⟨↑(0:ℝ) + ↑s * Complex.I, hmem⟩
      rw [hBdef] at this
      simpa [hpoint, add_comm] using this
    have hsub : (∫ s in y..t, Φ (↑p + ↑s * Complex.I))
        - (∫ s in y..t, Φ (↑(0:ℝ) + ↑s * Complex.I)) = ((t : ℂ) - (y : ℂ)) * c := by
      rw [← intervalIntegral.integral_sub (hright.intervalIntegrable)
        (hleft.intervalIntegrable), intervalIntegral.integral_congr hBconst,
        intervalIntegral.integral_const, Complex.real_smul]
      push_cast
      ring

    have hIsub : Complex.I * (∫ s in y..t, Φ (↑p + ↑s * Complex.I))
        - Complex.I * (∫ s in y..t, Φ (↑(0:ℝ) + ↑s * Complex.I))
        = ((t : ℂ) - (y : ℂ)) * (Complex.I * c) := by
      rw [← mul_sub, hsub]
      ring
    linear_combination hcauchy - hIsub

  have hJlim : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, y ≤ T ∧ ∀ t : ℝ, T ≤ t →
      ‖(∫ x in (0:ℝ)..p, Φ (↑x + ↑t * Complex.I)) - ↑p * A‖ ≤ ε * p := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hlim ε hε
    refine ⟨max Y y, le_max_right _ _, fun t ht => ?_⟩
    have htY : Y ≤ t := le_trans (le_max_left _ _) ht
    have hty : y ≤ t := le_trans (le_max_right _ _) ht
    have htpos : 0 < t := lt_of_lt_of_le hy hty
    have hint : IntervalIntegrable (fun x : ℝ => Φ (↑x + ↑t * Complex.I)) MeasureTheory.volume 0 p :=
      (continuous_horizontal hΦ htpos).intervalIntegrable _ _
    have hconst : (∫ _ in (0:ℝ)..p, A) = ↑p * A := by
      rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    rw [← hconst, ← intervalIntegral.integral_sub hint (intervalIntegrable_const)]
    have hbound : ∀ x ∈ Set.uIoc (0:ℝ) p, ‖Φ (↑x + ↑t * Complex.I) - A‖ ≤ ε := by
      intro x _
      apply hY
      simpa using htY
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa [abs_of_pos hp, mul_comm] using this

  have hczero : c = 0 := by
    by_contra hcne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
    obtain ⟨T, hTy, hT⟩ := hJlim (‖c‖ / (4 * p)) (by positivity)
    have h1 := key T hTy
    have h2 := key (T + 1) (le_trans hTy (by linarith))

    have hdiff : (∫ x in (0:ℝ)..p, Φ (↑x + ↑(T+1) * Complex.I))
        - (∫ x in (0:ℝ)..p, Φ (↑x + ↑T * Complex.I)) = Complex.I * c := by
      push_cast at h1 h2 ⊢
      linear_combination h1 - h2
    have hb1 := hT T (le_refl T)
    have hb2 := hT (T+1) (by linarith)
    have htri : ‖Complex.I * c‖ ≤ ‖(∫ x in (0:ℝ)..p, Φ (↑x + ↑(T+1) * Complex.I)) - ↑p * A‖
        + ‖(∫ x in (0:ℝ)..p, Φ (↑x + ↑T * Complex.I)) - ↑p * A‖ := by
      rw [← hdiff]
      have hsplit : (∫ x in (0:ℝ)..p, Φ (↑x + ↑(T+1) * Complex.I))
          - (∫ x in (0:ℝ)..p, Φ (↑x + ↑T * Complex.I))
          = ((∫ x in (0:ℝ)..p, Φ (↑x + ↑(T+1) * Complex.I)) - ↑p * A)
            - ((∫ x in (0:ℝ)..p, Φ (↑x + ↑T * Complex.I)) - ↑p * A) := by ring
      rw [hsplit]
      exact norm_sub_le _ _
    have hIc : ‖Complex.I * c‖ = ‖c‖ := by
      rw [norm_mul]
      simp
    have hfinal : ‖c‖ ≤ 2 * (‖c‖ / (4 * p) * p) := by
      calc ‖c‖ = ‖Complex.I * c‖ := hIc.symm
        _ ≤ _ + _ := htri
        _ ≤ ‖c‖ / (4 * p) * p + ‖c‖ / (4 * p) * p := add_le_add hb2 hb1
        _ = 2 * (‖c‖ / (4 * p) * p) := by ring
    have hsimp : 2 * (‖c‖ / (4 * p) * p) = ‖c‖ / 2 := by
      field_simp
      ring
    rw [hsimp] at hfinal
    linarith

  have hconst_height : ∀ t : ℝ, y ≤ t →
      (∫ x in (0:ℝ)..p, Φ (↑x + ↑y * Complex.I))
        = (∫ x in (0:ℝ)..p, Φ (↑x + ↑t * Complex.I)) := by
    intro t hyt
    have := key t hyt
    rw [hczero] at this
    simpa using this
  have hfar : ∀ d : ℝ, 0 < d →
      ‖(∫ x in (0:ℝ)..p, Φ (↑x + ↑y * Complex.I)) - ↑p * A‖ ≤ d := by
    intro d hd
    obtain ⟨T, hTy, hT⟩ := hJlim (d / (2 * p)) (by positivity)
    have h1 := hT T (le_refl T)
    rw [← hconst_height T hTy] at h1
    have h2 : d / (2 * p) * p = d / 2 := by
      field_simp
    rw [h2] at h1
    linarith
  have h0 : (∫ x in (0:ℝ)..p, Φ (↑x + ↑y * Complex.I)) - ↑p * A = 0 := by
    rw [← norm_le_zero_iff]
    by_contra hpos
    push Not at hpos
    have := hfar (‖(∫ x in (0:ℝ)..p, Φ (↑x + ↑y * Complex.I)) - ↑p * A‖ / 2) (by linarith)
    linarith
  exact sub_eq_zero.mp h0

end StripIdentity
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section InteriorMax

theorem re_eq_const_of_isMaxOn {φ : ℍ → ℂ} {φ' : ℍ → ℂ}
    (hφ : ∀ τ : ℍ, HasDerivAt (φ ∘ ofComplex) (φ' τ) ↑τ)
    {z₀ : ℍ} (hmax : ∀ z : ℍ, (φ z).re ≤ (φ z₀).re) (z : ℍ) : (φ z).re = (φ z₀).re := by
  classical
  set U : Set ℂ := {w : ℂ | 0 < w.im} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUpre : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  set E : ℂ → ℂ := fun w => Complex.exp ((φ ∘ ofComplex) w) with hEdef
  have hEdiff : DifferentiableOn ℂ E U := by
    intro w hw
    have : DifferentiableAt ℂ (φ ∘ ofComplex) w := by
      have := (hφ ⟨w, hw⟩).differentiableAt
      simpa using this
    exact (Complex.differentiable_exp.differentiableAt.comp w this).differentiableWithinAt
  have hnorm : ∀ w : ℂ, ‖E w‖ = Real.exp ((φ (ofComplex w)).re) := by
    intro w
    rw [hEdef]
    simpa using Complex.norm_exp ((φ ∘ ofComplex) w)
  have hz₀U : (z₀ : ℂ) ∈ U := z₀.im_pos
  have hzU : (z : ℂ) ∈ U := z.im_pos
  have hmaxOn : IsMaxOn (norm ∘ E) U ↑z₀ := by
    intro w hw
    have h1 : ‖E w‖ = Real.exp ((φ (ofComplex w)).re) := hnorm w
    have h2 : ‖E ↑z₀‖ = Real.exp ((φ z₀).re) := by
      rw [hnorm ↑z₀, ofComplex_apply]
    simp only [Function.comp_apply, Set.mem_setOf_eq]
    rw [h1, h2]
    exact Real.exp_le_exp.mpr (hmax (ofComplex w))
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hUpre hUopen hEdiff hz₀U hmaxOn
  have hzeq := heq hzU
  have h1 : ‖E ↑z‖ = Real.exp ((φ z).re) := by rw [hnorm ↑z, ofComplex_apply]
  have h2 : ‖E ↑z₀‖ = Real.exp ((φ z₀).re) := by rw [hnorm ↑z₀, ofComplex_apply]
  have : Real.exp ((φ z).re) = Real.exp ((φ z₀).re) := by
    rw [← h1, ← h2]
    simpa using hzeq
  exact Real.exp_injective this

end InteriorMax
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section Engine

variable {N : ℕ} [NeZero N]

omit [NeZero N] in

theorem conj_T_pow_mem_Gamma0 (δ : SL(2, ℤ)) :
    δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma0 N := by
  have hTN : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
    simpa using this
  have hconj : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem _ hTN δ

  have hle : Gamma N ≤ Gamma0 N := by
    intro γ hγ
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    rw [CongruenceSubgroup.Gamma0_mem]
    exact hγ.2.2.1
  exact hle hconj

omit [NeZero N] in

theorem exists_tile_translate (z : ℍ) :
    ∃ (q : SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ))) (v : ℍ) (γ : SL(2, ℤ)),
      v ∈ ModularGroup.fd ∧ γ ∈ Gamma0 N ∧ z = γ • ((Quotient.out q)⁻¹ • v) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  set q : SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ)) := QuotientGroup.mk g with hq
  set s : SL(2, ℤ) := Quotient.out q with hs
  have hcoset : s⁻¹ * g ∈ (Gamma0 N : Subgroup SL(2, ℤ)) := by
    have hout : (QuotientGroup.mk s : SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ)))
        = QuotientGroup.mk g := by
      rw [hs, hq]
      exact Quotient.out_eq _
    exact (QuotientGroup.eq).mp hout
  refine ⟨q, g • z, (s⁻¹ * g)⁻¹, hg, (Gamma0 N).inv_mem hcoset, ?_⟩
  have hcollapse : ((s⁻¹ * g)⁻¹ • ((Quotient.out q)⁻¹ • (g • z)) : ℍ) = z := by
    rw [← hs, smul_smul, smul_smul]
    have h1 : (s⁻¹ * g)⁻¹ * s⁻¹ * g = 1 := by group
    rw [h1, one_smul]
  exact hcollapse.symm

theorem continuous_smul_upperHalfPlane (g : SL(2, ℤ)) :
    Continuous fun z : ℍ => g • z := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  have hF : Continuous ((fun w : ℂ => ((g • ofComplex w : ℍ) : ℂ)) ∘ (fun z : ℍ => (z : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact ((Period.hasDerivAt_smul_ofComplex g z).differentiableAt.continuousAt).comp
      continuous_coe.continuousAt
  refine hF.congr (fun z => ?_)
  simp [Function.comp_apply, ofComplex_apply]

set_option maxHeartbeats 3200000 in

theorem re_eq_const_of_invariant_of_tendsto {φ φ' : ℍ → ℂ}
    (hφ : ∀ τ : ℍ, HasDerivAt (φ ∘ ofComplex) (φ' τ) ↑τ)
    (hinv : ∀ γ ∈ Gamma0 N, ∀ z : ℍ, (φ (γ • z)).re = (φ z).re)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => φ (δ • w)) atImInfty (𝓝 L))
    (z w : ℍ) : (φ z).re = (φ w).re := by
  classical

  set A : SL(2, ℤ) → ℂ := fun δ => (hlim δ).choose with hAdef
  have hA : ∀ δ : SL(2, ℤ), Tendsto (fun w : ℍ => φ (δ • w)) atImInfty (𝓝 (A δ)) :=
    fun δ => (hlim δ).choose_spec
  clear_value A

  have hthresh : ∀ (δ : SL(2, ℤ)) (ε : ℝ), 0 < ε →
      ∃ Y : ℝ, ∀ v : ℍ, Y ≤ v.im → ‖φ (δ • v) - A δ‖ ≤ ε := by
    intro δ ε hε
    have := (Metric.tendsto_nhds.mp (hA δ)) ε hε
    rw [Filter.eventually_iff, atImInfty_mem] at this
    obtain ⟨Y, hY⟩ := this
    refine ⟨Y, fun v hv => le_of_lt ?_⟩
    have := hY v hv
    simpa [dist_eq_norm] using this

  haveI : Nonempty (SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ))) :=
    ⟨QuotientGroup.mk (1 : SL(2, ℤ))⟩

  set r : (SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ))) → ℝ :=
    fun q => (A (Quotient.out q)⁻¹).re with hrdef
  obtain ⟨q₀, hq₀⟩ := Finite.exists_max r
  set R : ℝ := r q₀ with hRdef
  clear_value r R

  have hu_cont : Continuous fun z : ℍ => (φ z).re := by
    have h1 : Continuous fun z : ℍ => φ z := by
      rw [continuous_iff_continuousAt]
      intro z
      have h2 : ContinuousAt (φ ∘ ofComplex) (z : ℂ) := (hφ z).differentiableAt.continuousAt
      have heq : (fun z : ℍ => φ z) = (φ ∘ ofComplex) ∘ (fun z : ℍ => (z : ℂ)) := by
        funext w
        simp [ofComplex_apply]
      rw [heq]
      exact h2.comp continuous_coe.continuousAt
    exact Complex.continuous_re.comp h1

  suffices hsuff : ∃ z₀ : ℍ, ∀ ζ : ℍ, (φ ζ).re ≤ (φ z₀).re by
    obtain ⟨z₀, hz₀⟩ := hsuff
    rw [re_eq_const_of_isMaxOn hφ hz₀ z, re_eq_const_of_isMaxOn hφ hz₀ w]
  by_cases hcase : ∃ ζ₀ : ℍ, R < (φ ζ₀).re
  ·

    obtain ⟨ζ₀, hζ₀⟩ := hcase
    set ε : ℝ := ((φ ζ₀).re - R) / 2 with hεdef
    have hε : 0 < ε := by
      rw [hεdef]
      linarith

    have hYq : ∀ q : SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ)), ∃ Y : ℝ, ∀ v : ℍ, Y ≤ v.im →
        ‖φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹‖ ≤ ε :=
      fun q => hthresh (Quotient.out q)⁻¹ ε hε
    set Yf : (SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ))) → ℝ := fun q => (hYq q).choose with hYfdef
    have hYfspec : ∀ q : SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ)), ∀ v : ℍ, Yf q ≤ v.im →
        ‖φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹‖ ≤ ε :=
      fun q => (hYq q).choose_spec
    obtain ⟨qY, hqY⟩ := Finite.exists_max Yf
    set Y : ℝ := Yf qY with hYdef

    set C : Set ℍ := (⋃ q : SL(2, ℤ) ⧸ (Gamma0 N : Subgroup SL(2, ℤ)), (fun v : ℍ => (Quotient.out q)⁻¹ • v) ''
        (ModularGroup.truncatedFundamentalDomain Y)) ∪ {ζ₀} with hCdef
    have hC_compact : IsCompact C := by
      apply IsCompact.union
      · apply isCompact_iUnion
        intro q
        exact (ModularGroup.isCompact_truncatedFundamentalDomain Y).image
          (continuous_smul_upperHalfPlane _)
      · exact isCompact_singleton
    have hC_nonempty : C.Nonempty := ⟨ζ₀, Set.mem_union_right _ rfl⟩
    obtain ⟨z₀, hz₀C, hz₀max⟩ := hC_compact.exists_isMaxOn hC_nonempty
      (hu_cont.continuousOn)
    refine ⟨z₀, fun ζ => ?_⟩

    obtain ⟨q, v, γ, hvfd, hγ, hζeq⟩ := exists_tile_translate (N := N) ζ
    have hval : (φ ζ).re = (φ ((Quotient.out q)⁻¹ • v)).re := by
      rw [hζeq]
      exact hinv γ hγ _
    by_cases hsplit : v.im ≤ Y
    ·
      have hmem : ((Quotient.out q)⁻¹ • v) ∈ C := by
        rw [hCdef]
        exact Set.mem_union_left _
          (Set.mem_iUnion.mpr ⟨q, Set.mem_image_of_mem _ ⟨hvfd, hsplit⟩⟩)
      rw [hval]
      exact hz₀max hmem
    ·
      push Not at hsplit
      have hvY : Yf q ≤ v.im := le_trans (hqY q) (le_of_lt hsplit)
      have hclose := hYfspec q v hvY
      have hre_le : (φ ((Quotient.out q)⁻¹ • v)).re ≤ r q + ε := by
        have h1 : (φ ((Quotient.out q)⁻¹ • v)).re - (A (Quotient.out q)⁻¹).re
            ≤ ‖φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹‖ := by
          have habs := Complex.abs_re_le_norm (φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹)
          rw [Complex.sub_re] at habs
          calc (φ ((Quotient.out q)⁻¹ • v)).re - (A (Quotient.out q)⁻¹).re
              ≤ |(φ ((Quotient.out q)⁻¹ • v)).re - (A (Quotient.out q)⁻¹).re| := le_abs_self _
            _ ≤ _ := habs
        simp only [hrdef]
        linarith
      have hζ₀C : ζ₀ ∈ C := Set.mem_union_right _ rfl
      have : (φ ((Quotient.out q)⁻¹ • v)).re ≤ (φ ζ₀).re := by
        have hrR : r q ≤ R := hq₀ q
        linarith
      rw [hval]
      exact le_trans this (hz₀max hζ₀C)
  ·

    push Not at hcase
    set δstar : SL(2, ℤ) := (Quotient.out q₀)⁻¹ with hδdef
    clear_value δstar

    set Φ : ℂ → ℂ := fun w => φ (δstar • ofComplex w) with hΦdef
    have hΦderiv : ∀ τ : ℍ, HasDerivAt Φ ((φ' ∣[(2:ℤ)] δstar) τ) ↑τ := fun τ =>
      Period.hasDerivAt_comp_smul hφ δstar τ
    clear_value Φ

    have hper : ∀ τ : ℍ, (Φ (↑τ + ↑(N:ℝ)) - Φ ↑τ).re = 0 := by
      intro τ
      have him : (0:ℝ) < ((τ : ℂ) + ↑(N:ℝ)).im := by simpa using τ.im_pos
      have hofc : ofComplex ((τ : ℂ) + ↑(N:ℝ)) = ((N:ℝ) +ᵥ τ) := by
        rw [ofComplex_apply_of_im_pos him]
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.coe_vadd]
        push_cast
        ring
      have hT : ((N:ℝ) +ᵥ τ) = ModularGroup.T ^ (N : ℤ) • τ := by
        rw [UpperHalfPlane.modular_T_zpow_smul]
        norm_num
      have hsmul : δstar • ((N:ℝ) +ᵥ τ)
          = (δstar * ModularGroup.T ^ (N:ℤ) * δstar⁻¹) • (δstar • τ) := by
        rw [hT, smul_smul, smul_smul]
        congr 1
        group
      simp only [hΦdef]
      rw [hofc, ofComplex_apply, hsmul]
      have := hinv (δstar * ModularGroup.T ^ (N:ℤ) * δstar⁻¹) (conj_T_pow_mem_Gamma0 δstar)
        (δstar • τ)
      rw [Complex.sub_re, this]
      ring

    have hΦlim : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ w : ℂ, Y ≤ w.im → ‖Φ w - A δstar‖ ≤ ε := by
      intro ε hε
      obtain ⟨Y, hY⟩ := hthresh δstar ε hε
      refine ⟨max Y 1, fun w hw => ?_⟩
      have hwpos : (0:ℝ) < w.im := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hw)
      have hofc : ofComplex w = (⟨w, hwpos⟩ : ℍ) := ofComplex_apply_of_im_pos hwpos
      simp only [hΦdef]
      rw [hofc]
      exact hY ⟨w, hwpos⟩ (le_trans (le_max_left _ _) hw)

    have hNpos : (0:ℝ) < (N:ℝ) := by
      have := Nat.pos_of_ne_zero (NeZero.ne N)
      exact_mod_cast this
    have hkey := horizontal_integral_eq_of_re_periodic_of_tendsto hΦderiv hNpos hper hΦlim
      (y := 1) (by norm_num)

    have hΦ_le : ∀ x : ℝ, (Φ (↑x + ↑(1:ℝ) * Complex.I)).re ≤ R := by
      intro x
      have := hcase (δstar • ofComplex (↑x + ↑(1:ℝ) * Complex.I))
      simpa [hΦdef] using this
    have hcont : Continuous fun x : ℝ => (Φ (↑x + ↑(1:ℝ) * Complex.I)).re := by
      have h1 : Continuous fun x : ℝ => Φ (↑x + ↑(1:ℝ) * Complex.I) :=
        continuous_horizontal hΦderiv (by norm_num)
      exact Complex.continuous_re.comp h1

    obtain ⟨xm, hxm_mem, hxm_max⟩ := (isCompact_Icc (a := (0:ℝ)) (b := (N:ℝ))).exists_isMaxOn
      ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, by positivity⟩⟩ hcont.continuousOn
    by_cases hattain : (Φ (↑xm + ↑(1:ℝ) * Complex.I)).re = R
    ·
      refine ⟨δstar • ofComplex (↑xm + ↑(1:ℝ) * Complex.I), fun ζ => ?_⟩
      have hval : (φ (δstar • ofComplex (↑xm + ↑(1:ℝ) * Complex.I))).re
          = (Φ (↑xm + ↑(1:ℝ) * Complex.I)).re := by
        simp only [hΦdef]
      rw [hval, hattain]
      exact hcase ζ
    ·

      exfalso
      have hm_lt : (Φ (↑xm + ↑(1:ℝ) * Complex.I)).re < R :=
        lt_of_le_of_ne (hΦ_le xm) hattain
      have hconstint : (∫ _x in (0:ℝ)..(N:ℝ), (Φ (↑xm + ↑(1:ℝ) * Complex.I)).re)
          = (N:ℝ) * (Φ (↑xm + ↑(1:ℝ) * Complex.I)).re := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      have hint_le : (∫ x in (0:ℝ)..(N:ℝ), (Φ (↑x + ↑(1:ℝ) * Complex.I)).re)
          ≤ (N:ℝ) * (Φ (↑xm + ↑(1:ℝ) * Complex.I)).re := by
        rw [← hconstint]
        exact intervalIntegral.integral_mono_on (le_of_lt hNpos)
          (hcont.intervalIntegrable 0 (N:ℝ)) intervalIntegrable_const
          (fun x hx => hxm_max hx)
      have hre_int : (∫ x in (0:ℝ)..(N:ℝ), (Φ (↑x + ↑(1:ℝ) * Complex.I)).re)
          = (N:ℝ) * R := by
        have hint : IntervalIntegrable (fun x : ℝ => Φ (↑x + ↑(1:ℝ) * Complex.I))
            MeasureTheory.volume 0 (N:ℝ) :=
          (continuous_horizontal hΦderiv (by norm_num)).intervalIntegrable _ _
        have hswap := Complex.reCLM.intervalIntegral_comp_comm hint
        rw [hkey] at hswap
        simp only [Complex.reCLM_apply] at hswap
        rw [hswap]
        rw [hRdef, hrdef]
        simp [hδdef, Complex.mul_re]
      have hNR : (N:ℝ) * (Φ (↑xm + ↑(1:ℝ) * Complex.I)).re < (N:ℝ) * R :=
        mul_lt_mul_of_pos_left hm_lt hNpos
      rw [hre_int] at hint_le
      linarith

end Engine
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section ReflectCLM

noncomputable def reflectCLM : ℂ →L[ℝ] ℂ :=
  -(Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap

@[scoped simp] theorem reflectCLM_apply (w : ℂ) : reflectCLM w = -(starRingEnd ℂ) w := by
  simp [reflectCLM]

theorem coe_reflect_eq_reflectCLM (z : ℍ) : ((reflect z : ℍ) : ℂ) = reflectCLM (z : ℂ) := by
  simp [coe_reflect]

theorem ofComplex_neg_conj (z : ℍ) :
    ofComplex (-(starRingEnd ℂ) (z : ℂ)) = reflect z := by
  have him : (0 : ℝ) < (-(starRingEnd ℂ) (z : ℂ)).im := by simpa using z.im_pos
  rw [ofComplex_apply_of_im_pos him]; exact UpperHalfPlane.ext rfl

end ReflectCLM
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section NamedInputs

variable (N : ℕ)

def MixedPrimitiveConstancy : Prop :=
  ∀ (f g : CuspForm (Gamma0 N) 2) (F G : ℍ → ℂ),
    (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) →
    (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) →
    (∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) →
    (∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => G (δ • w)) atImInfty (𝓝 L)) →
    (∀ γ : Gamma0 N, ∀ z : ℍ,
      F ((γ : SL(2, ℤ)) • z) - G (reflect ((γ : SL(2, ℤ)) • z)) = F z - G (reflect z)) →
    ∃ c : ℂ, ∀ z : ℍ, F z - G (reflect z) = c

def MixedPrimitiveVanishing : Prop :=
  ∀ (f g : CuspForm (Gamma0 N) 2) (F G : ℍ → ℂ),
    (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) →
    (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) →
    (∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) →
    (∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => G (δ • w)) atImInfty (𝓝 L)) →
    (∀ γ : Gamma0 N, ∀ z : ℍ,
      F ((γ : SL(2, ℤ)) • z) - G (reflect ((γ : SL(2, ℤ)) • z)) = F z - G (reflect z)) →
    f = 0

end NamedInputs
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section ReflAct

open ModularCurve.Period

private theorem jConjSL_entry_00 (γ : SL(2, ℤ)) : (jConjSL γ) 0 0 = γ 0 0 := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = _
  rw [jConjMat_apply_zero_zero]

private theorem jConjSL_entry_01 (γ : SL(2, ℤ)) : (jConjSL γ) 0 1 = -(γ 0 1) := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = _
  rw [jConjMat_apply_zero_one]

private theorem jConjSL_entry_10 (γ : SL(2, ℤ)) : (jConjSL γ) 1 0 = -(γ 1 0) := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = _
  rw [jConjMat_apply_one_zero]

private theorem jConjSL_entry_11 (γ : SL(2, ℤ)) : (jConjSL γ) 1 1 = γ 1 1 := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = _
  rw [jConjMat_apply_one_one]

theorem reflect_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    reflect (γ • τ) = jConjSL γ • reflect τ := by
  ext1
  rw [coe_reflect, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_reflect,
    jConjSL_entry_00, jConjSL_entry_01, jConjSL_entry_10, jConjSL_entry_11,
    map_neg, map_neg, Complex.ofReal_neg, Complex.ofReal_neg, map_div₀, map_add, map_add,
    map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_ofReal]
  ring

end ReflAct
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section Extraction

theorem eq_zero_of_hasDerivAt_of_mixed_eq_const {f g F G : ℍ → ℂ}
    (hFf : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ)
    (hGg : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ)
    {c : ℂ} (hconst : ∀ z : ℍ, F z - G (reflect z) = c) (τ : ℍ) : f τ = 0 := by
  classical
  have hUopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hζU : (τ : ℂ) ∈ {w : ℂ | 0 < w.im} := τ.im_pos
  set r : ℂ → ℂ := fun w => c + (G ∘ ofComplex) (reflectCLM w) with hrdef
  have heq : ∀ w ∈ {w : ℂ | 0 < w.im}, (F ∘ ofComplex) w = r w := by
    intro w hw
    have hw' : (0 : ℝ) < w.im := hw
    have hofc : ofComplex w = ⟨w, hw'⟩ := ofComplex_apply_of_im_pos hw'
    have hrm : reflectCLM w = -(starRingEnd ℂ) w := reflectCLM_apply w
    have him : (0 : ℝ) < (-(starRingEnd ℂ) w).im := by simpa using hw'
    have hofc' : ofComplex (-(starRingEnd ℂ) w) = reflect (⟨w, hw'⟩ : ℍ) := by
      rw [ofComplex_apply_of_im_pos him]; exact UpperHalfPlane.ext rfl
    have hc := hconst (⟨w, hw'⟩ : ℍ)
    show F (ofComplex w) = r w
    rw [hrdef]
    show F (ofComplex w) = c + G (ofComplex (reflectCLM w))
    rw [hofc, hrm, hofc']; linear_combination hc
  have hev : (F ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] r :=
    Filter.eventuallyEq_of_mem (hUopen.mem_nhds hζU) heq
  have hrefl_coe : ((reflect τ : ℍ) : ℂ) = reflectCLM (τ : ℂ) := coe_reflect_eq_reflectCLM τ
  have huF : HasFDerivAt (F ∘ ofComplex)
      (((1 : ℂ →L[ℂ] ℂ).smulRight (f τ)).restrictScalars ℝ) (τ : ℂ) :=
    (hFf τ).hasFDerivAt.restrictScalars ℝ
  have hvF : HasFDerivAt (G ∘ ofComplex)
      (((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ) (reflectCLM (τ : ℂ)) := by
    have h := (hGg (reflect τ)).hasFDerivAt.restrictScalars ℝ
    rwa [hrefl_coe] at h
  have hcomp : HasFDerivAt ((G ∘ ofComplex) ∘ reflectCLM)
      ((((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ).comp reflectCLM)
      (τ : ℂ) :=
    hvF.comp (τ : ℂ) reflectCLM.hasFDerivAt
  have hrF : HasFDerivAt r
      ((((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ).comp reflectCLM)
      (τ : ℂ) :=
    hcomp.const_add c
  have huF' : HasFDerivAt (F ∘ ofComplex)
      ((((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ).comp reflectCLM)
      (τ : ℂ) :=
    hrF.congr_of_eventuallyEq hev
  have hDeq := huF.unique huF'
  have h1 : f τ = -(g (reflect τ)) := by
    have := DFunLike.congr_fun hDeq (1 : ℂ)
    simpa [reflectCLM] using this
  have h2 : Complex.I * f τ = Complex.I * g (reflect τ) := by
    have := DFunLike.congr_fun hDeq Complex.I
    simpa [reflectCLM, mul_comm] using this
  have h2' : f τ = g (reflect τ) := mul_left_cancel₀ Complex.I_ne_zero h2
  linear_combination (1/2 : ℂ) * h1 + (1/2 : ℂ) * h2'

theorem CuspForm.eq_zero_of_primitive_mixed_eq_const {N : ℕ}
    {f g : CuspForm (Gamma0 N) 2} {F G : ℍ → ℂ}
    (hFf : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ)
    (hGg : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ)
    {c : ℂ} (hconst : ∀ z : ℍ, F z - G (reflect z) = c) : f = 0 := by
  ext τ
  have := eq_zero_of_hasDerivAt_of_mixed_eq_const hFf hGg hconst τ
  simpa using this

end Extraction
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

theorem mixedPrimitiveVanishing_of_mixedPrimitiveConstancy {N : ℕ}
    (h : MixedPrimitiveConstancy N) : MixedPrimitiveVanishing N := by
  intro f g F G hFf hGg hFlim hGlim hinv
  obtain ⟨c, hc⟩ := h f g F G hFf hGg hFlim hGlim hinv
  exact CuspForm.eq_zero_of_primitive_mixed_eq_const hFf hGg hc

open ModularCurve.Period

section Discharge

variable {N : ℕ} [NeZero N]

theorem hasDerivAt_conj_comp_reflect {G g : ℍ → ℂ}
    (hGg : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (τ : ℍ) :
    HasDerivAt ((fun z : ℍ => (starRingEnd ℂ) (G (reflect z))) ∘ ofComplex)
      (-(starRingEnd ℂ) (g (reflect τ))) ↑τ := by
  classical
  have hUopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ {w : ℂ | 0 < w.im} := τ.im_pos

  have hrefl : HasFDerivAt (fun w : ℂ => reflectCLM w) reflectCLM (τ : ℂ) :=
    reflectCLM.hasFDerivAt
  have houter : HasFDerivAt (G ∘ ofComplex)
      (((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ) (reflectCLM (τ : ℂ)) := by
    have h := (hGg (reflect τ)).hasFDerivAt.restrictScalars ℝ
    rwa [coe_reflect_eq_reflectCLM] at h
  have hconj : HasFDerivAt ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ → ℂ)
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ))
      ((G ∘ ofComplex) (reflectCLM (τ : ℂ))) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ)).hasFDerivAt

  have hcomp : HasFDerivAt (((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ → ℂ) ∘ (G ∘ ofComplex) ∘
      (reflectCLM : ℂ → ℂ))
      (((Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
        ((((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ).comp reflectCLM))
      (τ : ℂ) :=
    hconj.comp (τ : ℂ) (houter.comp (τ : ℂ) hrefl)

  have hev : ((fun z : ℍ => (starRingEnd ℂ) (G (reflect z))) ∘ ofComplex)
      =ᶠ[𝓝 (τ : ℂ)] (((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ → ℂ) ∘ (G ∘ ofComplex) ∘
        (reflectCLM : ℂ → ℂ)) := by
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hτU) ?_
    intro w hw
    have hw' : (0:ℝ) < w.im := hw
    have hofc : ofComplex w = (⟨w, hw'⟩ : ℍ) := ofComplex_apply_of_im_pos hw'
    have hrm : reflectCLM w = -(starRingEnd ℂ) w := reflectCLM_apply w
    have hofc' : ofComplex (reflectCLM w) = reflect (⟨w, hw'⟩ : ℍ) := by
      rw [hrm]
      exact ofComplex_neg_conj (⟨w, hw'⟩ : ℍ)
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
    rw [hofc, hofc']
  have hK : HasFDerivAt ((fun z : ℍ => (starRingEnd ℂ) (G (reflect z))) ∘ ofComplex)
      (((Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
        ((((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ).comp reflectCLM))
      (τ : ℂ) :=
    hcomp.congr_of_eventuallyEq hev

  have hCLM : ((1 : ℂ →L[ℂ] ℂ).smulRight (-(starRingEnd ℂ) (g (reflect τ)))).restrictScalars ℝ
      = ((Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
        ((((1 : ℂ →L[ℂ] ℂ).smulRight (g (reflect τ))).restrictScalars ℝ).comp reflectCLM) := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, reflectCLM_apply, Complex.conjCLE_apply, smul_eq_mul,
      map_mul, map_neg, Complex.conj_conj]
    ring
  have hfinal : HasFDerivAt ((fun z : ℍ => (starRingEnd ℂ) (G (reflect z))) ∘ ofComplex)
      ((1 : ℂ →L[ℂ] ℂ).smulRight (-(starRingEnd ℂ) (g (reflect τ)))) (τ : ℂ) :=
    hasFDerivAt_of_restrictScalars ℝ hK hCLM
  simpa using hfinal.hasDerivAt

theorem tendsto_reflect_atImInfty :
    Tendsto (fun w : ℍ => reflect w) atImInfty atImInfty := by
  have h : Tendsto (UpperHalfPlane.im ∘ fun w : ℍ => reflect w) atImInfty atTop := by
    have heq : (UpperHalfPlane.im ∘ fun w : ℍ => reflect w) = UpperHalfPlane.im := by
      funext w
      simp [Function.comp_apply, reflect_im]
    rw [heq]
    exact Filter.tendsto_comap
  exact Filter.tendsto_comap_iff.mpr h

theorem mixedPrimitiveConstancy_holds : MixedPrimitiveConstancy N := by
  intro f g F G hFf hGg hFlim hGlim hinv
  classical

  set K : ℍ → ℂ := fun z => (starRingEnd ℂ) (G (reflect z)) with hKdef
  have hKderiv : ∀ τ : ℍ, HasDerivAt (K ∘ ofComplex) (-(starRingEnd ℂ) (g (reflect τ))) ↑τ :=
    fun τ => hasDerivAt_conj_comp_reflect hGg τ

  have hKlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Tendsto (fun w : ℍ => K (δ • w)) atImInfty (𝓝 L) := by
    intro δ
    obtain ⟨L₂, hL₂⟩ := hGlim (jConjSL δ)
    refine ⟨(starRingEnd ℂ) L₂, ?_⟩
    have h1 : Tendsto (fun w : ℍ => G (jConjSL δ • reflect w)) atImInfty (𝓝 L₂) :=
      hL₂.comp tendsto_reflect_atImInfty
    have h2 : Tendsto (fun w : ℍ => (starRingEnd ℂ) (G (jConjSL δ • reflect w))) atImInfty
        (𝓝 ((starRingEnd ℂ) L₂)) := (Complex.conjCLE.continuous.tendsto L₂).comp h1
    refine h2.congr (fun w => ?_)
    simp only [hKdef]
    rw [reflect_sl_smul]

  set φ : ℍ → ℂ := fun z => F z - K z with hφdef
  set χ : ℍ → ℂ := fun z => -Complex.I * (F z + K z) with hχdef
  have hφderiv : ∀ τ : ℍ, HasDerivAt (φ ∘ ofComplex)
      (f τ + (starRingEnd ℂ) (g (reflect τ))) ↑τ := by
    intro τ
    have := (hFf τ).sub (hKderiv τ)
    simp [hφdef, Function.comp, sub_neg_eq_add] at this
    exact this
  have hχderiv : ∀ τ : ℍ, HasDerivAt (χ ∘ ofComplex)
      (-Complex.I * (f τ + -(starRingEnd ℂ) (g (reflect τ)))) ↑τ := by
    intro τ
    have h1 := (hFf τ).add (hKderiv τ)
    have h2 := h1.const_mul (-Complex.I)
    simp [hχdef, Function.comp] at h2 ⊢
    exact h2

  have hφre : ∀ z : ℍ, (φ z).re = (F z - G (reflect z)).re := by
    intro z
    rw [hφdef, hKdef]
    simp [Complex.sub_re, Complex.conj_re]
  have hχre : ∀ z : ℍ, (χ z).re = (F z - G (reflect z)).im := by
    intro z
    rw [hχdef, hKdef]
    simp only [Complex.neg_re, Complex.mul_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.sub_im]
    ring

  have hφinv : ∀ γ ∈ Gamma0 N, ∀ z : ℍ, (φ (γ • z)).re = (φ z).re := by
    intro γ hγ z
    rw [hφre, hφre]
    have := hinv ⟨γ, hγ⟩ z
    rw [this]
  have hχinv : ∀ γ ∈ Gamma0 N, ∀ z : ℍ, (χ (γ • z)).re = (χ z).re := by
    intro γ hγ z
    rw [hχre, hχre]
    have := hinv ⟨γ, hγ⟩ z
    rw [this]

  have hφlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Tendsto (fun w : ℍ => φ (δ • w)) atImInfty (𝓝 L) := by
    intro δ
    obtain ⟨L₁, hL₁⟩ := hFlim δ
    obtain ⟨L₂, hL₂⟩ := hKlim δ
    exact ⟨L₁ - L₂, by simpa [hφdef] using hL₁.sub hL₂⟩
  have hχlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Tendsto (fun w : ℍ => χ (δ • w)) atImInfty (𝓝 L) := by
    intro δ
    obtain ⟨L₁, hL₁⟩ := hFlim δ
    obtain ⟨L₂, hL₂⟩ := hKlim δ
    refine ⟨-Complex.I * (L₁ + L₂), ?_⟩
    have := (hL₁.add hL₂).const_mul (-Complex.I)
    simpa [hχdef] using this

  have hφconst := re_eq_const_of_invariant_of_tendsto (N := N) hφderiv hφinv hφlim
  have hχconst := re_eq_const_of_invariant_of_tendsto (N := N) hχderiv hχinv hχlim

  refine ⟨F UpperHalfPlane.I - G (reflect UpperHalfPlane.I), fun z => ?_⟩
  apply Complex.ext
  · have := hφconst z UpperHalfPlane.I
    rw [hφre, hφre] at this
    exact this
  · have := hχconst z UpperHalfPlane.I
    rw [hχre, hχre] at this
    exact this

theorem mixedPrimitiveVanishing_holds : MixedPrimitiveVanishing N :=
  mixedPrimitiveVanishing_of_mixedPrimitiveConstancy mixedPrimitiveConstancy_holds

end Discharge
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section Twins

p2m_open "CongruenceSubgroup UpperHalfPlane Filter Topology ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve ModularCurve.Period"

open scoped MatrixGroups

variable {N : ℕ} [NeZero N]

theorem CuspForm.eq_zero_of_charInvolution_periodMap_eq_neg
    (h : MixedPrimitiveVanishing N) {f : CuspForm (Gamma0 N) 2}
    (hf : charInvolution N ℂ ℂ (periodMap N f) = -(periodMap N f)) : f = 0 := by
  obtain ⟨F, hFf, -, hFe, hFlim⟩ := Period.CuspForm.exists_equivariantPrimitive_gamma0 (f := f)

  have hψ : periodMap N f = hFe.periodHom := periodMap_eq_periodHom hFe hFf

  refine h f ((-1 : ℂ) • f) F (fun z => -(F z)) hFf ?_ hFlim ?_ ?_
  · intro τ
    have hval : ((-1 : ℂ) • f) τ = -(f τ) := by
      show (-1 : ℂ) * f τ = -(f τ); ring
    rw [hval]; exact (hFf τ).neg
  · intro δ
    obtain ⟨L, hL⟩ := hFlim δ
    exact ⟨-L, hL.neg⟩
  ·
    intro γ z
    have h1 := hFe.sub_eq_period γ z
    have hpoint : reflect ((γ : SL(2, ℤ)) • z)
        = ((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) • reflect z := by
      rw [jConjGamma0_coe, reflect_sl_smul]
    have h2 := hFe.sub_eq_period (jConjGamma0 N γ) (reflect z)

    have hval1 : hFe.period γ = periodMap N f (Additive.ofMul γ) := by
      rw [hψ]; rfl
    have hval2 : hFe.period (jConjGamma0 N γ) = -(periodMap N f (Additive.ofMul γ)) := by
      have hstep : hFe.period (jConjGamma0 N γ)
          = charInvolution N ℂ ℂ (periodMap N f) (Additive.ofMul γ) := by
        rw [hψ]; rfl
      rw [hstep, hf]; rfl
    show F ((γ : SL(2, ℤ)) • z) - -(F (reflect ((γ : SL(2, ℤ)) • z)))
        = F z - -(F (reflect z))
    rw [hpoint]
    have hexp1 : F ((γ : SL(2, ℤ)) • z) = F z + periodMap N f (Additive.ofMul γ) := by
      linear_combination h1 + hval1
    have hexp2 : F (((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) • reflect z)
        = F (reflect z) - periodMap N f (Additive.ofMul γ) := by
      linear_combination h2 + hval2
    rw [hexp1, hexp2]; ring

theorem CuspForm.eq_zero_of_charInvolution_periodMap_eq_self
    (h : MixedPrimitiveVanishing N) {f : CuspForm (Gamma0 N) 2}
    (hf : charInvolution N ℂ ℂ (periodMap N f) = periodMap N f) : f = 0 := by
  obtain ⟨F, hFf, -, hFe, hFlim⟩ := Period.CuspForm.exists_equivariantPrimitive_gamma0 (f := f)
  have hψ : periodMap N f = hFe.periodHom := periodMap_eq_periodHom hFe hFf
  refine h f f F F hFf hFf hFlim hFlim ?_
  intro γ z
  have h1 := hFe.sub_eq_period γ z
  have hpoint : reflect ((γ : SL(2, ℤ)) • z)
      = ((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) • reflect z := by
    rw [jConjGamma0_coe, reflect_sl_smul]
  have h2 := hFe.sub_eq_period (jConjGamma0 N γ) (reflect z)
  have hval1 : hFe.period γ = periodMap N f (Additive.ofMul γ) := by rw [hψ]; rfl
  have hval2 : hFe.period (jConjGamma0 N γ) = periodMap N f (Additive.ofMul γ) := by
    have hstep : hFe.period (jConjGamma0 N γ)
        = charInvolution N ℂ ℂ (periodMap N f) (Additive.ofMul γ) := by
      rw [hψ]; rfl
    rw [hstep, hf]
  rw [hpoint]
  have hexp1 : F ((γ : SL(2, ℤ)) • z) = F z + periodMap N f (Additive.ofMul γ) := by
    rw [← hval1]; linear_combination h1
  have hexp2 : F (((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) • reflect z)
      = F (reflect z) + periodMap N f (Additive.ofMul γ) := by
    rw [← hval2]; linear_combination h2
  rw [hexp1, hexp2]; ring

end Twins
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

section FinalAlgebra

p2m_open "CongruenceSubgroup ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve ModularCurve.Period"

theorem periodHomPair_injective_of_twins {N : ℕ} (hex : ExistsPeriodMapLinear N)
    (hminus : ∀ f : CuspForm (Gamma0 N) 2,
      charInvolution N ℂ ℂ (periodMap N f) = -(periodMap N f) → f = 0)
    (hplus : ∀ g : CuspForm (Gamma0 N) 2,
      charInvolution N ℂ ℂ (periodMap N g) = periodMap N g → g = 0) :
    Function.Injective (periodHomPair N) := by
  obtain ⟨pml, hpml, hdef⟩ := periodHomPair_def N hex
  rw [hdef]
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨f, g⟩ h0
  set ι := charInvolution N ℂ ℂ with hιdef
  set p := periodMap N f with hp
  set q := periodMap N g with hq
  have h0' : p + ι p + (q - ι q) = 0 := by
    simpa [LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, hpml] using h0
  have hιι : ∀ ψ : Additive (Gamma0 N) →+ ℂ, ι (ι ψ) = ψ := charInvolution_charInvolution N ℂ ℂ
  have h1 : ι p + p + (ι q - q) = 0 := by
    have := congrArg ι h0'
    rw [map_add, map_add, map_sub, hιι, hιι, map_zero] at this
    exact this
  have hP : p + ι p = 0 := by
    have h2 : (2 : ℂ) • (p + ι p) = 0 := by
      have hsum : (p + ι p + (q - ι q)) + (ι p + p + (ι q - q)) = 0 := by rw [h0', h1, add_zero]
      have : (p + ι p + (q - ι q)) + (ι p + p + (ι q - q)) = (2 : ℂ) • (p + ι p) := by module
      rw [this] at hsum
      exact hsum
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hQ : q - ι q = 0 := by
    have h2 : (2 : ℂ) • (q - ι q) = 0 := by
      have hdiff : (p + ι p + (q - ι q)) - (ι p + p + (ι q - q)) = 0 := by rw [h0', h1, sub_zero]
      have : (p + ι p + (q - ι q)) - (ι p + p + (ι q - q)) = (2 : ℂ) • (q - ι q) := by module
      rw [this] at hdiff
      exact hdiff
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hf : f = 0 := hminus f (by rw [← hp]; exact (neg_eq_of_add_eq_zero_right hP).symm)
  have hg : g = 0 := hplus g (by rw [← hq]; exact (sub_eq_zero.mp hQ).symm)
  rw [hf, hg]
  rfl

end FinalAlgebra
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

end ModularCurve.SolESINJ
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

end
p2m_reactivate "P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve P2MW.S_ModularCurve_periodHomPair_injective.ModularCurve.SolESINJ"

theorem solution (N : ℕ) [NeZero N] :
    Function.Injective (ModularCurve.periodHomPair N) :=
  ModularCurve.SolESINJ.periodHomPair_injective_of_twins (ModularCurve.existsPeriodMapLinear N)
    (fun _ hf => ModularCurve.SolESINJ.CuspForm.eq_zero_of_charInvolution_periodMap_eq_neg
      ModularCurve.SolESINJ.mixedPrimitiveVanishing_holds hf)
    (fun _ hg => ModularCurve.SolESINJ.CuspForm.eq_zero_of_charInvolution_periodMap_eq_self
      ModularCurve.SolESINJ.mixedPrimitiveVanishing_holds hg)

#print axioms solution

end S_ModularCurve_periodHomPair_injective
end P2MW
export P2MW.S_ModularCurve_periodHomPair_injective (solution)
