-- Prove2me | solution 1 for GlobalTheory.KSp.WeilFormula.weil_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:04.74818+00:00
-- url     : https://prove2.me/submissions/6a678f6e-cd57-4f34-9fb3-0138d099b8d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilFormulaFourierQuadraticCharacter
import Theorems.Thm_GlobalTheory_KSp_WeilFormula_setIntegral_addSubgroup_add_right
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_T_bicharacterFourierTransform_mem_schwartzBruhat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.WeilFormula
namespace GlobalTheory.KSp.WeilFormula
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ (f g : X → ℂ) (s : X → X) (γ : ℂ), Continuous f → Continuous s →
    (∀ y u, f y * e y u = g u * f (y + s u)) → HasGauss μ f γ → ∀ φ ∈ SB X, ∀ x,
    four μ e (fun y => f y * four μ e φ y) x = γ * ∫ z, g (x + z) * φ z ∂μ := by
  intro X _ _ _ _ hG μ _ e he f g s γ hf hs hfg hga φ hφ x
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hφ4 : four μ e φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hK1 : IsCompact (tsupport (four μ e φ)) := hφ4.2
  have hφc : IsCompact (tsupport φ) := hφ.2
  have hK2 : IsCompact (s '' ((fun z => x + z) '' tsupport φ)) :=
    (hφc.image (continuous_const.add continuous_id)).image hs
  obtain ⟨L, hLc, hLo, hKL, hLγ⟩ := hga _ (hK1.union hK2)
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have he_cont : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hφcont : Continuous φ := hφ.1.continuous
  have h0 : ∀ y, y ∉ (L : Set X) → e x y * (f y * four μ e φ y) = 0 := by
    intro y hy
    have : four μ e φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hKL (Or.inl h)))
    simp [this]
  have h1 : four μ e (fun y => f y * four μ e φ y) x
      = ∫ y in (L : Set X), ∫ z, e x y * f y * (e y z * φ z) ∂μ ∂μ := by
    calc four μ e (fun y => f y * four μ e φ y) x = ∫ y, e x y * (f y * four μ e φ y) ∂μ := rfl
      _ = ∫ y in (L : Set X), e x y * (f y * four μ e φ y) ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = _ := by
          congr 1; funext y
          simp only [four]
          rw [← mul_assoc, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
      ((μ.restrict (L : Set X)).prod μ) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hc : Continuous (Function.uncurry fun y z => e x y * f y * (e y z * φ z)) := by
      have h1' : Continuous fun p : X × X => e x p.1 := he_cont.comp (continuous_const.prodMk continuous_fst)
      exact (h1'.mul (hf.comp continuous_fst)).mul (he_cont.mul (hφcont.comp continuous_snd))
    have hon : IntegrableOn (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
        ((L : Set X) ×ˢ tsupport φ) (μ.prod μ) := hc.continuousOn.integrableOn_compact (hLc.prod hφc)
    refine hon.of_forall_sdiff_eq_zero (hLm.prod MeasurableSet.univ) ?_
    rintro ⟨y, z⟩ ⟨⟨hy, -⟩, hn⟩
    have hz : z ∉ tsupport φ := fun h => hn ⟨hy, h⟩
    simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  have h3 : ∀ z, ∫ y in (L : Set X), e x y * f y * (e y z * φ z) ∂μ = γ * (g (x + z) * φ z) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzt : z ∈ tsupport φ := subset_tsupport _ hz
      have hsL : s (x + z) ∈ L := hKL (Or.inr ⟨x + z, ⟨z, hzt, rfl⟩, rfl⟩)
      have hpt : ∀ y, e x y * f y * (e y z * φ z) = φ z * g (x + z) * f (y + s (x + z)) := by
        intro y
        have hexy : e x y * e y z = e y (x + z) := by
          rw [he.symm y (x + z), he.add, he.symm z y]
        rw [mul_assoc (φ z), ← hfg y (x + z), ← hexy]; ring
      simp_rw [hpt]
      rw [integral_const_mul, setIntegral_addSubgroup_add_right μ L hLo f hsL, hLγ]; ring
  rw [h1, integral_integral_swap hint]
  simp_rw [h3]
  rw [integral_const_mul]
end GlobalTheory.KSp.WeilFormula
