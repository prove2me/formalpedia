-- Prove2me | solution 1 for GlobalTheory.TSetFin.local_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:18:35.727447+00:00
-- url     : https://prove2.me/submissions/2b973cde-443b-4e56-8413-1e8bb9c4952c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Theorems.Thm_GlobalTheory_T_heckeDoubleCoset_adicCompletion_inv_mul_integral


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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (ϖ : v.adicCompletion F) (k : ℕ) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (a a' b b' g g' : GL (Fin n) (v.adicCompletion F))
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hc : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hg' : (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 :=
  GlobalTheory.T.heckeDoubleCoset_adicCompletion_inv_mul_integral F v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hc hg hg'
end GlobalTheory.TSetFin
