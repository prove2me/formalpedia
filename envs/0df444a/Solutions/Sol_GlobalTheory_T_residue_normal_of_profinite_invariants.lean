-- Prove2me | solution 1 for GlobalTheory.T.residue_normal_of_profinite_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:15.6104+00:00
-- url     : https://prove2.me/submissions/c18fcd24-9960-47dd-9fea-34252f5c2305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueNormalOfProfiniteInvariants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueNormalOfProfiniteInvariantsStatement
import Theorems.Thm_GlobalTheory_Ideal_Quotient_normal_of_profinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal], letI := Ideal.Quotient.field P; letI := Ideal.Quotient.field Q; Normal (A ⧸ P) (B ⧸ Q) := by
  first | exact @GlobalTheory.Ideal.Quotient.normal_of_profinite | exact GlobalTheory.Ideal.Quotient.normal_of_profinite | (intros; apply GlobalTheory.Ideal.Quotient.normal_of_profinite <;> assumption)
end _root_.GlobalTheory.T
