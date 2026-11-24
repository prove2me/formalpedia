-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.SphLaw.chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:28.778387+00:00
-- url     : https://prove2.me/submissions/a571a829-cd14-4205-a8bc-3c871d0b4f3b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.SphLaw
namespace GlobalTheory.CompanionTheory.QL.SphLaw
theorem _root_.solution {F : Type} [Field F] {nrm : AbsoluteValue F ℝ} {q : ℕ} (hq : 1 < q)
    (hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e))
    {c : ℕ} {χ : Fin c → F → ℂ} {α : Fin c → ℂ} (hU : UnrChar nrm q χ α) (i : Fin c)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : χ i (x * y) = χ i x * χ i y := by
  obtain ⟨e, he⟩ := hv x hx
  obtain ⟨e', he'⟩ := hv y hy
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    positivity
  have hxy : nrm (x * y) = (q : ℝ) ^ (-(e + e')) := by
    rw [map_mul, he, he', neg_add, zpow_add₀ hq0]
  rw [hU.2 i _ _ hxy, hU.2 i _ _ he, hU.2 i _ _ he', zpow_add₀ (hU.1 i)]
end GlobalTheory.CompanionTheory.QL.SphLaw
