-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.degree_weierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:33.280109+00:00
-- url     : https://prove2.me/submissions/5a1e4e39-917c-4a01-a8b2-58a95e567d17

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_torusOrder_mk
import Theorems.Thm_GroundTheory_Global_Elliptic_toNat_neg_untopD_eq_zero_of_nonneg
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_isEllipticFunction_weierstrassP


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
theorem _root_.solution : degree L ℘[L] = 2 := by
  have hP : IsEllipticFunction L ℘[L] := isEllipticFunction_weierstrassP
  have h0 : (0 : Torus L) = Torus.mk L 0 := (QuotientAddGroup.mk_zero _).symm
  rw [degree, finsum_eq_single _ (0 : Torus L) ?_]
  · rw [h0, torusOrder_mk hP]
    have h2 : meromorphicOrderAt ℘[L] 0 = ((-2 : ℤ) : WithTop ℤ) := by
      rw [L.order_weierstrassP 0 (zero_mem _)]
      norm_num
    rw [h2, WithTop.untopD_coe]
    rfl
  · intro x hx
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    have hz : z ∉ L.lattice := fun h ↦ hx (by
      rw [h0]
      exact (Torus.mk_eq_mk_iff L).2 (by simpa using h))
    rw [torusOrder_mk hP]
    exact toNat_neg_untopD_eq_zero_of_nonneg
      (L.analyticOnNhd_weierstrassP z hz).meromorphicOrderAt_nonneg
end GroundTheory.Global.Elliptic
