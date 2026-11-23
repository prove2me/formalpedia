-- Prove2me | solution 1 for GlobalTheory.HilbFam.autEmb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:26.435709+00:00
-- url     : https://prove2.me/submissions/e98ce064-046e-4bf1-a595-908f1485cfdb

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AutEmbInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) (y : F) :
    ((autEmb g i y : ℝ) : ℂ) = g ((i y : ℝ) : ℂ) :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).coe_embedding_apply y
end GlobalTheory.HilbFam
