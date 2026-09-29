-- Prove2me | solution 1 for HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/dce1216a-643e-5249-81bd-42ad879bb533

import Definitions.Def_HaarQuotient
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_HaarQuotient_map_mk_withDensity_eq_smul_measure
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace KcHaarQuotientMulRight

variable {G : Type*} [Group G]

theorem apply_out_mk {H : Subgroup G} {α : Type*} {Φ : G → α}
    (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) (g : G) :
    Φ (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = Φ g := by
  have h : (MulAction.orbitRel H G) (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out g :=
    Quotient.exact (Quotient.out_eq _)
  obtain ⟨x, hx⟩ := MulAction.orbitRel_apply.1 h
  rw [← hx]
  exact hinv x g

theorem measurable_comp_out [MeasurableSpace G] {H : Subgroup G} {α : Type*}
    [MeasurableSpace α] {Φ : G → α} (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => Φ q.out := by
  refine measurable_from_quotient.2 ?_
  have : (fun q : MulAction.orbitRel.Quotient H G => Φ q.out) ∘ Quotient.mk'' = Φ :=
    funext fun g => apply_out_mk hinv g
  rw [this]
  exact hΦ

theorem measurable_weight [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · simp_rw [ENNReal.tsum_eq_iSup_sum]
    refine Measurable.iSup fun s => s.measurable_fun_sum fun n _ => ?_
    exact measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet))
  · exact measurable_const

theorem measurable_density [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

theorem lintegral_withDensity_eq_of_admissible [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) = ∫⁻ g, Φ g ∂(μ.withDensity ρ) := by
  have hmk : Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ) =
      Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
        (μ.withDensity (HaarQuotient.density H μH)) := by
    rw [HaarQuotient.map_mk_withDensity_eq_smul_measure μ H hH μH ρ hρ 1 hρc, one_smul]
    rfl
  set Ψ : MulAction.orbitRel.Quotient H G → ℝ≥0∞ := fun q => Φ q.out with hΨ
  have hΨm : Measurable Ψ := measurable_comp_out hΦ hinv
  have hΦΨ : Φ = fun g => Ψ (Quotient.mk'' g) := funext fun g => (apply_out_mk hinv g).symm
  rw [hΦΨ]
  change ∫⁻ g, Ψ (Quotient.mk'' g) ∂_ = ∫⁻ g, Ψ (Quotient.mk'' g) ∂_
  rw [← lintegral_map hΨm measurable_quotient_mk'', ← lintegral_map hΨm measurable_quotient_mk'', hmk]

theorem lintegral_density_mul_comp_mul_right_eq [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (h : G)
    (hμh : Measure.map (fun g : G => g * h) μ = μ) :
    ∫⁻ g, HaarQuotient.density H μH g * f (g * h) ∂μ = ∫⁻ g, HaarQuotient.density H μH g * f g ∂μ := by
  set D := HaarQuotient.density H μH with hDdef
  have hD : Measurable D := measurable_density H μH
  have hinv : ∀ (x : H) (g : G), f ((x : G) * g) = f g := fun x g => hfH x x.2 g

  let ρ : G → ℝ≥0∞ := fun g => D (g * h⁻¹)
  have hρ : Measurable ρ := hD.comp (measurable_mul_const _)
  have hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1 := by
    intro g
    show ∫⁻ x : H, D ((x : G) * g * h⁻¹) ∂μH = 1
    simp_rw [mul_assoc]
    exact HaarQuotient.lintegral_density_mul_eq_one H hH μH (g * h⁻¹)

  have h1 : ∫⁻ g, D g * f (g * h) ∂μ = ∫⁻ g, (fun g' => ρ g' * f g') (g * h) ∂μ := by
    refine lintegral_congr fun g => ?_
    show D g * f (g * h) = D (g * h * h⁻¹) * f (g * h)
    rw [mul_inv_cancel_right]
  have h2 : ∫⁻ g, (fun g' => ρ g' * f g') (g * h) ∂μ = ∫⁻ g, ρ g * f g ∂(Measure.map (fun g : G => g * h) μ) :=
    (lintegral_map (hρ.mul hf) (measurable_mul_const h)).symm
  have h3 : ∫⁻ g, ρ g * f g ∂(Measure.map (fun g : G => g * h) μ) = ∫⁻ g, ρ g * f g ∂μ := by
    rw [hμh]
  have h4 : ∫⁻ g, ρ g * f g ∂μ = ∫⁻ g, f g ∂(μ.withDensity ρ) := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hρ hf]
    rfl
  have h5 : ∫⁻ g, f g ∂(μ.withDensity D) = ∫⁻ g, D g * f g ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hD hf]
    rfl
  rw [h1, h2, h3, h4, ← lintegral_withDensity_eq_of_admissible μ H hH μH ρ hρ hρc f hf hinv, h5]

end KcHaarQuotientMulRight

end

open MeasureTheory in

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (h : G)
    (hμh : Measure.map (· * h) μ = μ) :
    ∫⁻ g, HaarQuotient.density H μH g * f (g * h) ∂μ = ∫⁻ g, HaarQuotient.density H μH g * f g ∂μ :=
  KcHaarQuotientMulRight.lintegral_density_mul_comp_mul_right_eq μ H hH μH f hf hfH h hμh

end S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
end P2MW
export P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq (solution)
