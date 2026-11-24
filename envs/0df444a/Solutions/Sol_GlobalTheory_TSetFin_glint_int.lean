-- Prove2me | solution 1 for GlobalTheory.TSetFin.glint_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:07.120729+00:00
-- url     : https://prove2.me/submissions/af3c40ef-97a4-42a9-98d4-f3f2a26a9c99

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut
noncomputable section
open GlobalTheory GlobalTheory.TSetFin
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
namespace GlobalTheory.TSetFin
theorem _root_.solution {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {a : GL (Fin n) (v.adicCompletion F)} (ha : a ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring) :
    (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((g : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2
  · rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) (v.adicCompletionIntegers F).toSubring) : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2
end GlobalTheory.TSetFin
