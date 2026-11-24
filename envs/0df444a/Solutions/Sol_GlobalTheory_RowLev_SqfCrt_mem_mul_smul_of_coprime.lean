-- Prove2me | solution 1 for GlobalTheory.RowLev.SqfCrt.mem_mul_smul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:32.738123+00:00
-- url     : https://prove2.me/submissions/223cd10e-278c-4622-b88b-e4d5e9de681a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsProdLeOfIsRadical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.SqfCrt
namespace GlobalTheory.RowLev.SqfCrt
theorem _root_.solution {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    {A B : Ideal S} (h : IsCoprime A B) {y : M} (hA : y ∈ A • N) (hB : y ∈ B • N) : y ∈ (A * B) • N := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have hsplit : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul ha hB
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hb hA
end GlobalTheory.RowLev.SqfCrt
