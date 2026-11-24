-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.map_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:30.632798+00:00
-- url     : https://prove2.me/submissions/6fa16467-5cef-448a-b2b2-0ef834e16fe8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_ShortStep_map_conj

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
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (V w : Matrix (Fin 1) (Fin n) E) : (1 - G * wᴴ * V - G * Vᴴ * w).map τ =
      1 - G.map τ * (w.map τ)ᴴ * V.map τ - G.map τ * (V.map τ)ᴴ * w.map τ := by
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_mul, map_conj, map_conj, Matrix.map_one _ (map_zero _) (map_one _)]
end GlobalTheory.SW.ShortStep
