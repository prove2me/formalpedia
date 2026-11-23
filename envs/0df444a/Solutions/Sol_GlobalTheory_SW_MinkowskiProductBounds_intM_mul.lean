-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.intM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:34.919802+00:00
-- url     : https://prove2.me/submissions/ee4dc76f-a519-4043-b5db-b5792d8d32ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution {α β γ : Type} [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A)
    (hB : IntM B) : IntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun k _ => (hA i k).mul (hB k j)
end GlobalTheory.SW.MinkowskiProductBounds
