-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.partialProd_mul_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:10.114198+00:00
-- url     : https://prove2.me/submissions/69150787-511d-420d-ba98-442eb1ea0d5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
import Theorems.Thm_GlobalTheory_SimpleRoots_card_roots_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SimpleRoots
open Polynomial
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) :
    partialProd p u x * partialProd p uᶜ x = p.map (MvPolynomial.eval x) := by
  classical
  unfold partialProd
  rw [← Multiset.prod_add, ← Multiset.map_add]
  convert Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map (MvPolynomial.eval x))
    (by rw [card_roots_map hp x, hp.natDegree_map]) using 3
  convert Multiset.filter_add_not (fun y => (x, y) ∈ u) (p.map (MvPolynomial.eval x)).roots using 2
  congr 1
end GlobalTheory.SimpleRoots
