-- Prove2me | solution 1 for GlobalTheory.subsingleton_of_residueField_fibres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:14.863716+00:00
-- url     : https://prove2.me/submissions/2f49b986-c330-4c46-bca7-25c8fbee9b46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct
open TensorProduct
open TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (O Q : Type) [CommRing O]
    [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    (h : ∀ q : PrimeSpectrum O, Subsingleton (q.asIdeal.ResidueField ⊗[O] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := O), Set.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq
  exact not_nontrivial_iff_subsingleton.mpr (h q) hq
end _root_.GlobalTheory
end GlobalTheory
