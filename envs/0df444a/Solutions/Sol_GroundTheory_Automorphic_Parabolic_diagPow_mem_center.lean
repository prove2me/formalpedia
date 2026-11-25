-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagPow_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:39:55.140745+00:00
-- url     : https://prove2.me/submissions/dc6f8ebc-f488-4e9a-94f3-085ff86ba147

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
open Cartan
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {c : Fin n → ℤ} (hc : ∀ i j, β i = β j → c i = c j) :
    (⟨diagPow F n c, diagPow_mem_levi c⟩ : levi F n β) ∈ Submonoid.center (levi F n β) := by
  rw [Submonoid.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  ext i j
  show (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (diagPow F n c : Matrix (Fin n) (Fin n) F)) i j
    = ((diagPow F n c : Matrix (Fin n) (Fin n) F) * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) i j
  rw [coe_diagPow, mul_diagonal, diagonal_mul]
  by_cases h : β i = β j
  · rw [hc i j h, mul_comm]
  · have : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := mem_levi.1 g.2 i j h
    rw [this, zero_mul, mul_zero]
end GroundTheory.Automorphic.Parabolic
