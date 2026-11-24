-- Prove2me | solution 1 for GlobalTheory.derivation_mem_of_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:04.293551+00:00
-- url     : https://prove2.me/submissions/d30934d1-b7ff-4aaf-b00c-229ba6c5f869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GenericResidueLinearIndependence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (δ : Derivation k A A) (q : Ideal A) {x : A} (hx : x ∈ q ^ 2) : δ x ∈ q := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact q.add_mem (q.mul_mem_right _ hm) (q.mul_mem_right _ hn)
  · intro x y hx hy
    rw [map_add]; exact q.add_mem hx hy
end GlobalTheory
