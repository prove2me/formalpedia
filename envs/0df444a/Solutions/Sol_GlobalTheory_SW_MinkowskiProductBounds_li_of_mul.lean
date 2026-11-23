-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.li_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:42.570655+00:00
-- url     : https://prove2.me/submissions/9925c600-0f65-4973-af73-f1bfae98fceb

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
theorem _root_.solution {k a b : ℕ} {A : Matrix (Fin k) (Fin a) E} {R : Matrix (Fin a) (Fin b) E}
    (h : LinearIndependent E fun i => (A * R) i) : LinearIndependent E fun i => A i :=
  LinearIndependent.of_comp (Matrix.vecMulLinear R) h
end GlobalTheory.SW.MinkowskiProductBounds
