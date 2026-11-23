-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.den_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:00.136199+00:00
-- url     : https://prove2.me/submissions/bdee29ab-72d0-4298-989d-95458ec4b222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_intM_mul
import Theorems.Thm_GlobalTheory_SW_RowExt_intM_mul


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
omit [IsCMField E]
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {α β γ : Type} [Fintype β] {a b : ℕ} {A : Matrix α β E} {B : Matrix β γ E}
    (hA : Den a A) (hB : Den b B) : Den (a * b) (A * B) := by
  have := intM_mul hA hB
  rwa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Nat.cast_mul] at this
end GlobalTheory.SW.ShortStep
