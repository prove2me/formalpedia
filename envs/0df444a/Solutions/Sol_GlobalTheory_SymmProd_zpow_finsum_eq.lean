-- Prove2me | solution 1 for GlobalTheory.SymmProd.zpow_finsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:55.613866+00:00
-- url     : https://prove2.me/submissions/3c508c4e-5c89-45a5-9613-0928e324b25e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SymmProd
open scoped Matrix
namespace GlobalTheory.SymmProd
theorem _root_.solution {U : Type} [CommGroup U] {ι : Type} (s : Finset ι) (x : U) (f : ι → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]
end GlobalTheory.SymmProd
