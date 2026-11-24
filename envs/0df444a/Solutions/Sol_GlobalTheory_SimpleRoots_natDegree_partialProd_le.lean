-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.natDegree_partialProd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:49:10.81757+00:00
-- url     : https://prove2.me/submissions/c174beb9-106b-4dac-82aa-127aa899177d

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
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : (partialProd p u x).natDegree ≤ p.natDegree := by
  classical
  unfold partialProd
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← card_roots_map hp x]
  exact Multiset.card_le_card (Multiset.filter_le _ _)
end GlobalTheory.SimpleRoots
