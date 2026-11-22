-- Prove2me | solution 1 for MeasureTheory.pi_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:32.74294+00:00
-- url     : https://prove2.me/submissions/9102715c-4a2a-48f1-ab06-81cedd8a5deb

module
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Theorems.Thm_MeasureTheory_lintegral_fintype_prod_eq_prod

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory
open scoped ENNReal
open MeasureTheory
variable {ι : Type*} [Fintype ι]
namespace MeasureTheory
theorem _root_.solution {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (g : (i : ι) → E i → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    [∀ i, SigmaFinite ((μ i).withDensity (g i))] :
    Measure.pi (fun i => (μ i).withDensity (g i))
      = (Measure.pi μ).withDensity (fun x => ∏ i, g i (x i)) := by
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (g i)) (fun s hs => ?_)
  -- LHS on the rectangle: ∏ᵢ ((μ i).withDensity gᵢ) (s i) = ∏ᵢ ∫⁻_{sᵢ} gᵢ.
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  -- Set-integral over the rectangle = ∫⁻ of the indicator-times-density.
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  -- The integrand `(pi s).indicator (∏ g)` equals `∏ᵢ (sᵢ.indicator gᵢ)(xᵢ)`.
  have hint : ((Set.univ.pi s).indicator (fun x => ∏ i, g i (x i)))
      = fun x => ∏ i, (s i).indicator (g i) (x i) := by
    classical
    funext x
    rw [Set.indicator_apply]
    split_ifs with hx
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (Set.mem_univ_pi.mp hx i)]
    · rw [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  rw [hint, lintegral_fintype_prod_eq_prod (μ := μ)
    (fun i => (s i).indicator (g i)) (fun i => (hg i).indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]
end MeasureTheory
