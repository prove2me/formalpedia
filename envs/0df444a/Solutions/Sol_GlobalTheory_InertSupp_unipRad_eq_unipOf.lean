-- Prove2me | solution 1 for GlobalTheory.InertSupp.unipRad_eq_unipOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:20.038632+00:00
-- url     : https://prove2.me/submissions/a0de2292-3c32-4224-a8d3-6ae8cdbab81d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_GodementJacquetZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Theorems.Thm_GlobalTheory_InertSupp_mem_unipOf
import Theorems.Thm_GlobalTheory_SmGL_CuspMax_mem_unipRad_iff_entries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory
open GlobalTheory GlobalTheory.InertSupp
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
open ValuativeRel Matrix MeasureTheory
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)]
variable (R)
namespace GlobalTheory.InertSupp
namespace _root_.GlobalTheory.InertSupp
theorem _root_.solution {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by
  ext g
  rw [_root_.GlobalTheory.InertSupp.mem_unipOf, _root_.GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]
  simp only [h]
end _root_.GlobalTheory.InertSupp
end GlobalTheory.InertSupp
