-- Prove2me | solution 1 for GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:47.8038+00:00
-- url     : https://prove2.me/submissions/7f74e294-4280-4c15-88ae-a24c4ecc7d95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Theorems.Thm_GlobalTheory_IntegralNeighbourhoodZero_nsmul_integral_mem_nhds_zero


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
theorem _root_.solution (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (𝓞 F) F | ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
  first
  | exact @_root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | exact _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | (apply _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero ..)
end GlobalTheory.AdLat.OpenLat
