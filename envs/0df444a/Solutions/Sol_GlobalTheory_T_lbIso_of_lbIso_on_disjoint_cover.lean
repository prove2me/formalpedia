-- Prove2me | solution 1 for GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:35:59.10869+00:00
-- url     : https://prove2.me/submissions/15662a78-8eb8-4e05-b72a-63436d1e2cc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LbIsoOfDisjointCover
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LbIsoOfDisjointCoverStatement
import Theorems.Thm_GlobalTheory_DisjointCoverLB_lbIso_of_disjoint_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) → (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) → LBIso P Q := by
  first | exact @GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | exact GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | (intros; apply GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover <;> assumption)
end _root_.GlobalTheory.T
