-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:05.504645+00:00
-- url     : https://prove2.me/submissions/1bd1ec9e-c874-4b8e-a4b8-fd180b2ec828

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (A : Subalgebra ℚ Ω) (v : σ → Ω)
    (hv : ∀ p, v p ∈ A) (g : MvPolynomial σ ℤ) : aeval v g ∈ A := by
  induction g using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem A n
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (hv i)
end GlobalTheory.CompanionTheory.Ar.SegreChart
