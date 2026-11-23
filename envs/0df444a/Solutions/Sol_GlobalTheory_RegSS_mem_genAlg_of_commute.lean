-- Prove2me | solution 1 for GlobalTheory.RegSS.mem_genAlg_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:27.096261+00:00
-- url     : https://prove2.me/submissions/5d44bd2d-89fc-4920-a193-374906affa99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_GlobalTheory_RegSS_commute_of_mem_genAlg
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
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution {M N : Matrix n n A} {v : n → A}
    (hv : Function.Bijective (fun l : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M => (l : Matrix n n A) *ᵥ v))
    (h : N * M = M * N) : N ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M := by
  obtain ⟨l, hl⟩ := hv.2 (N *ᵥ v)
  have hlM : (l : Matrix n n A) * M = M * l :=
    (_root_.GlobalTheory.RegSS.commute_of_mem_genAlg (M := M) (N := M) rfl l.2).symm
  have key : N = l := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨l', rfl⟩ := hv.2 w
    have hll' : (l : Matrix n n A) * l' = l' * l :=
      _root_.GlobalTheory.RegSS.commute_of_mem_genAlg hlM l'.2
    have hNl' : N * (l' : Matrix n n A) = l' * N :=
      _root_.GlobalTheory.RegSS.commute_of_mem_genAlg h l'.2
    simp only [Matrix.toLin'_apply]
    simp only at hl
    rw [Matrix.mulVec_mulVec, hNl', ← Matrix.mulVec_mulVec, ← hl, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hll']
  exact key ▸ l.2
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
