-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.exists_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:38.906272+00:00
-- url     : https://prove2.me/submissions/6339ba59-63d9-4a0a-9ed6-b5f27076bb0b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_RowLev_Red_map_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open GlobalTheory.RowLev.PrimeIdem
namespace GlobalTheory.RowLev.PrimeIdem
theorem _root_.solution {S : Type} [CommRing S] (J : Ideal S) [HenselianRing S J] (a : S) (ha : a * a - a ∈ J) :
    ∃ y, y * y = y ∧ y - a ∈ J := by
  have hm : (Polynomial.X ^ 2 - Polynomial.X : Polynomial S).Monic := by
    nontriviality S
    monicity!
  obtain ⟨y, hy, hy'⟩ := HenselianRing.is_henselian (I := J) _ hm a (by simpa [sq] using ha) (by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (2 * a - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    have := J.mul_mem_left 4 ha
    convert this using 1
    simp
    ring)
  refine ⟨y, ?_, hy'⟩
  have : y ^ 2 - y = 0 := by simpa using hy
  linear_combination this
end GlobalTheory.RowLev.PrimeIdem
