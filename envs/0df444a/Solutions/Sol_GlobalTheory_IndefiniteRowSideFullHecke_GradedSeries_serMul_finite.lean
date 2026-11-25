-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:12:58.951214+00:00
-- url     : https://prove2.me/submissions/90c7f723-ac60-4c14-84c0-d4aed713d373

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
open TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
theorem _root_.solution (f : PowerSeries L) {u : ℤ → M}
    (hu : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent u) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j f • u (k - (j : ℤ))).Finite := by
  obtain ⟨m, hm⟩ := hu
  refine (Set.finite_Iic (k - m).toNat).subset ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Iic]
  by_contra h
  push_neg at h
  exact hj (by rw [hm _ (by omega), smul_zero])
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
end GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
