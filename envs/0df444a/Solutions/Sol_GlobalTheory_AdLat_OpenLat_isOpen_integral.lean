-- Prove2me | solution 1 for GlobalTheory.AdLat.OpenLat.isOpen_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:39.596222+00:00
-- url     : https://prove2.me/submissions/0c940c66-a333-4ebb-b618-d6f91d92ebfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Theorems.Thm_GlobalTheory_IntegralNeighbourhoodZero_isOpen_integral
import Theorems.Thm_GlobalTheory_IntegralOpen_isOpen_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.OpenLat
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.AdLat.OpenLat
theorem _root_.solution :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  first
  | exact @_root_.GlobalTheory.IntegralOpen.isOpen_integral
  | exact _root_.GlobalTheory.IntegralOpen.isOpen_integral
  | (apply _root_.GlobalTheory.IntegralOpen.isOpen_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralOpen.isOpen_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralOpen.isOpen_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralOpen.isOpen_integral ..)
end GlobalTheory.AdLat.OpenLat
