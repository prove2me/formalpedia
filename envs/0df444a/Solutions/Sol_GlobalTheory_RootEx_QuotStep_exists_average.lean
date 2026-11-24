-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.exists_average
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:55.417073+00:00
-- url     : https://prove2.me/submissions/1580f0bb-2a43-4566-bef6-ce8eb3bf17da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TopologicalSpace X] [TopologicalSpace U] [MeasurableSpace X] [MeasurableSpace U]
    [OpensMeasurableSpace (X × U)] [T2Space X] [T2Space U]
    (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite ρ] [IsFiniteMeasureOnCompacts (μ.prod ρ)]
    [(μ.prod ρ).IsOpenPosMeasure]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (ι : X × U → G) (hι : Continuous ι) (t₁ : X × U) (h₁ : ι t₁ = 1)
    (hprop : ∀ C : Set G, IsCompact C → ∃ D, IsCompact D ∧ ∀ t, ι t ∈ C → t ∈ D)
    (δ : X → ℝ) (hδ : Continuous δ) (hδ0 : ∀ x, 0 < δ x)
    (hinv : ∀ φ : G → ℂ, Continuous φ → ∀ t, ∫ x, ∫ u, (δ x : ℂ) * φ (ι (x, u) * ι t) ∂ρ ∂μ =
      ∫ x, ∫ u, (δ x : ℂ) * φ (ι (x, u)) ∂ρ ∂μ)
    (f : G → ℂ) (hf : IsLocallyConstant f) (Ω : Set G) (hΩ : IsCompact Ω)
    (hsupp : ∀ h, f h ≠ 0 → ∃ t, ∃ w ∈ Ω, h = ι t * w)
    (hfδ : ∀ t h, f (ι t * h) = δ t.1 * f h) :
    ∃ F ∈ SB G, ∀ h, f h = ∫ x, ∫ u, F (ι (x, u) * h) ∂ρ ∂μ := by
  classical
  set C : Set G := Ω * (K : Set G) with hC
  have hCc : IsCompact C := hΩ.mul hKc
  have hlc : ∀ {Y : Type} (a : G → Y), (∀ h, ∀ κ ∈ K, a (h * κ) = a h) → IsLocallyConstant a := by
    intro Y a ha
    rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have : IsOpen {y : G | h⁻¹ * y ∈ K} := hKo.preimage (continuous_const.mul continuous_id)
    filter_upwards [this.mem_nhds (show h⁻¹ * h ∈ K by simp [one_mem])] with y hy
    rw [← ha h _ hy, mul_inv_cancel_left]
  let χ : G → ℝ := C.indicator fun _ => 1
  have hCK : ∀ h, ∀ κ ∈ K, h ∈ C → h * κ ∈ C := by
    rintro _ κ hκ ⟨w, hw, j, hj, rfl⟩
    exact ⟨w, hw, j * κ, mul_mem hj hκ, (mul_assoc _ _ _).symm⟩
  have hχK : ∀ h, ∀ κ ∈ K, χ (h * κ) = χ h := by
    intro h κ hκ
    by_cases hh : h ∈ C
    · simp [χ, hh, hCK h κ hκ hh]
    · have : h * κ ∉ C := fun h' => hh (by simpa using hCK _ _ (inv_mem hκ) h')
      simp [χ, hh, this]
  have hχ := hlc χ hχK
  let A : G → ℂ := fun h => ∫ x, ∫ u, (δ x : ℂ) * (χ (ι (x, u) * h) : ℂ) ∂ρ ∂μ
  have hA : IsLocallyConstant A := hlc A fun h κ hκ => by
    simp only [A, ← mul_assoc, hχK _ κ hκ]
  have hAι : ∀ t h, A (ι t * h) = A h := fun t h => by
    simp only [A, ← mul_assoc]
    exact hinv (fun g => (χ (g * h) : ℂ))
      (Complex.continuous_ofReal.comp (hχ.continuous.comp (continuous_id.mul continuous_const))) t
  have hA0 : ∀ w ∈ Ω, A w ≠ 0 := by
    intro w hw
    let a : X × U → ℝ := fun t => δ t.1 * χ (ι t * w)
    have ha : Continuous a := (hδ.comp continuous_fst).mul (hχ.continuous.comp (hι.mul continuous_const))
    obtain ⟨D, hD, hD'⟩ := hprop _ (hCc.image (continuous_mul_right w⁻¹))
    have hs : HasCompactSupport a := by
      refine HasCompactSupport.of_support_subset_isCompact hD fun t ht => hD' t ?_
      by_contra hn
      refine ht ?_
      have : ι t * w ∉ C := fun h' => hn ⟨_, h', by simp⟩
      simp [a, χ, this]
    have hpos : 0 < ∫ t, a t ∂(μ.prod ρ) := by
      refine ha.integral_pos_of_hasCompactSupport_nonneg_nonzero hs (x := t₁)
        (fun t => mul_nonneg (hδ0 _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) ?_
      have : w ∈ C := ⟨w, hw, 1, one_mem _, mul_one _⟩
      simp [a, χ, h₁, this, (hδ0 _).ne']
    rw [integral_prod _ (ha.integrable_of_hasCompactSupport hs)] at hpos
    have e : A w = ((∫ x, ∫ u, a (x, u) ∂ρ ∂μ : ℝ) : ℂ) := by
      simp only [A, a, ← integral_complex_ofReal, Complex.ofReal_mul]
    rw [e]
    exact_mod_cast hpos.ne'
  refine ⟨fun h => f h * (A h)⁻¹ * (χ h : ℂ), ⟨(hf.mul (hA.comp fun z => z⁻¹)).mul (hχ.comp fun z : ℝ => (z : ℂ)), ?_⟩, fun h => ?_⟩
  · refine HasCompactSupport.of_support_subset_isCompact hCc fun t ht => ?_
    by_contra hn
    exact ht (by simp [χ, hn])
  · have e : ∀ x u, f (ι (x, u) * h) * (A (ι (x, u) * h))⁻¹ * (χ (ι (x, u) * h) : ℂ) =
        f h * (A h)⁻¹ * ((δ x : ℂ) * (χ (ι (x, u) * h) : ℂ)) := fun x u => by
      rw [hfδ, hAι]; ring
    simp only [e, integral_const_mul]
    by_cases h0 : f h = 0
    · simp [h0]
    · obtain ⟨t, w, hw, rfl⟩ := hsupp h h0
      have := hA0 w hw
      rw [← hAι t] at this
      have e2 : (∫ x, (δ x : ℂ) * ∫ u, (χ (ι (x, u) * (ι t * w)) : ℂ) ∂ρ ∂μ) = A (ι t * w) := by
        simp only [A, integral_const_mul]
      rw [e2, inv_mul_cancel_right₀ this]
end GlobalTheory.RootEx.QuotStep
