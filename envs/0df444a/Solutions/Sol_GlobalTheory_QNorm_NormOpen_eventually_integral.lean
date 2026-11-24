-- Prove2me | solution 1 for GlobalTheory.QNorm.NormOpen.eventually_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:11:08.383918+00:00
-- url     : https://prove2.me/submissions/454298db-6b4c-49a5-be46-7e8ef71c90a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Topology
open GlobalTheory GlobalTheory.QNorm
open GlobalTheory.QNorm.NormOpen
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.QNorm.NormOpen
theorem _root_.solution :
    ∀ᶠ a in 𝓝 (1 : FiniteAdeleRing (𝓞 F) F), ∀ v, a v ∈ v.adicCompletionIntegers F := by
  have ho : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a.1 v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  exact ho.mem_nhds (fun v => (one_mem (v.adicCompletionIntegers F) : _))
end GlobalTheory.QNorm.NormOpen
