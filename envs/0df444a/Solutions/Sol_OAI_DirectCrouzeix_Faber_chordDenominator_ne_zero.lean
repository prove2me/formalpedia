-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.chordDenominator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:11:43.408958+00:00
-- url     : https://prove2.me/submissions/ee9070a9-413a-4f4b-8f40-c8cb066c3948

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DividedDifferences.lean:L103-L121
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.chordDenominator_ne_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Theorems.Thm_OAI_DirectCrouzeix_Faber_chordIntegral_deriv_mul

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem chordIntegral_deriv_eq_dslope {s : Set ℂ} (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    chordIntegral (deriv f) (fun _ => 1) u v = dslope f v u := by
  by_cases huv : u = v
  · subst u
    have he (t : ℝ) : chord v v t = v := by
      rw [chord, ← add_smul, sub_add_cancel, one_smul]
    simp [chordIntegral, he, dslope_same]
  · rw [dslope_of_ne f huv, slope, smul_eq_mul]
    simp only [vsub_eq_sub]
    have hm := chordIntegral_deriv_mul hconv hf hu hv
    field_simp
    linear_combination -hm

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.DividedDifferences ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem divided_eq_dslope {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    divided g u v = dslope g v u := chordIntegral_deriv_eq_dslope hconv hg hu hv

theorem hasDerivAt_exterior {s : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s)
    (c : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) (hζs : ζ⁻¹ ∈ s) :
    HasDerivAt (exterior c g) (c-ζ⁻¹^2*deriv g ζ⁻¹) ζ := by
  have hd := ((hasDerivAt_id ζ).const_mul c).add
    ((hg ζ⁻¹ hζs).differentiableAt.hasDerivAt.comp ζ (hasDerivAt_inv hζ))
  change HasDerivAt (fun z => exterior c g z) _ ζ
  simpa only [exterior, Function.comp_def, id_eq, mul_one, Pi.add_apply, inv_pow,
    div_eq_mul_inv, sub_eq_add_neg, mul_neg, mul_comm, mul_left_comm] using! hd

theorem chordDenominator_off_diagonal {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u v : ℂ}
    (hu : u ∈ s) (hv : v ∈ s) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    chordDenominator c g u v = (exterior c g u⁻¹ - exterior c g v⁻¹) / (u⁻¹-v⁻¹) := by
  rw [chordDenominator, divided_eq_dslope hconv hg hu hv, dslope_of_ne g huv]
  simp only [slope, smul_eq_mul, vsub_eq_sub, exterior, inv_inv]
  field_simp
  ring

theorem chordDenominator_diagonal {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u : ℂ} (hu : u ∈ s) :
    chordDenominator c g u u = c-u^2*deriv g u := by
  rw [chordDenominator, divided_eq_dslope hconv hg hu hu, dslope_same]
  ring

theorem chordDenominator_ne_zero {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ} (hc : c ≠ 0)
    (hinj : InjOn (exterior c g) (Inv.inv ⁻¹' s \ {0}))
    (hd : ∀ ζ, ζ ≠ 0 → ζ⁻¹ ∈ s → deriv (exterior c g) ζ ≠ 0)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) : chordDenominator c g u v ≠ 0 := by
  by_cases hu0 : u = 0
  · simp [chordDenominator, hu0, hc]
  by_cases hv0 : v = 0
  · simp [chordDenominator, hv0, hc]
  by_cases huv : u = v
  · subst v
    rw [chordDenominator_diagonal hconv hg c hu]
    have hder := (hasDerivAt_exterior hg c (inv_ne_zero hu0) (by simpa using hu)).deriv
    have hn := hd u⁻¹ (inv_ne_zero hu0) (by simpa using hu)
    rwa [hder,inv_inv] at hn
  · rw [chordDenominator_off_diagonal hconv hg c hu hv hu0 hv0 huv]
    exact div_ne_zero (sub_ne_zero.mpr (fun he => huv (inv_injective (hinj
      ⟨by simpa using hu, by simpa using hu0⟩ ⟨by simpa using hv, by simpa using hv0⟩ he))))
      (sub_ne_zero.mpr (fun he => huv (inv_injective he)))

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.chordDenominator_ne_zero := @_root_.OAI.DirectCrouzeix.Faber.chordDenominator_ne_zero
