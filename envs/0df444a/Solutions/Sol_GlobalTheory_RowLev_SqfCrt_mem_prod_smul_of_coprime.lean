-- Prove2me | solution 1 for GlobalTheory.RowLev.SqfCrt.mem_prod_smul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:21.439835+00:00
-- url     : https://prove2.me/submissions/d85180d2-8880-44bc-9362-723a8774b4ab

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsProdLeOfIsRadical
import Theorems.Thm_GlobalTheory_RowLev_SqfCrt_mem_mul_smul_of_coprime
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.SqfCrt
namespace GlobalTheory.RowLev.SqfCrt
theorem _root_.solution {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    (J : ι → Ideal S) (hJ : ∀ i j, i ≠ j → IsCoprime (J i) (J j)) {y : M} (hy : y ∈ N) (T : Finset ι)
    (h : ∀ i ∈ T, y ∈ J i • N) : y ∈ (∏ i ∈ T, J i) • N := by
  induction T using Finset.induction_on with
  | empty => simpa [Ideal.one_eq_top, Submodule.top_smul] using hy
  | @insert a T haT ih =>
    rw [Finset.prod_insert haT]
    refine mem_mul_smul_of_coprime N ?_ (h a (Finset.mem_insert_self a T))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact IsCoprime.prod_right fun i hi => hJ a i fun hai => haT (hai ▸ hi)
end GlobalTheory.RowLev.SqfCrt
