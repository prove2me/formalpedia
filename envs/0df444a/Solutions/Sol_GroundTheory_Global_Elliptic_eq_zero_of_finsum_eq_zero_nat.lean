-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.eq_zero_of_finsum_eq_zero_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.197641+00:00
-- url     : https://prove2.me/submissions/97fb3cb4-d13a-4384-aa63-667144bc5bba

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (h : ∑ᶠ x, u x = 0) (x : α) : u x = 0 := by
  classical
  by_contra hx
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset) (by simp)] at h
  exact hx ((Finset.sum_eq_zero_iff.1 h) x (by simpa using hx))
end GroundTheory.Global.Elliptic
