-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:30.242026+00:00
-- url     : https://prove2.me/submissions/7d5b2db8-ad46-4189-be4b-3a0ac23bd6c0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization

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
variable (L : PeriodPair)
variable {L}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {w : ℂ} (hw : w ∉ L.lattice) :
    2 * w ∈ L.lattice ↔ ℘'[L] w = 0 := by
  classical
  refine ⟨derivWeierstrassP_eq_zero_of_two_mul_mem, fun h' ↦ ?_⟩
  by_contra h2
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hne : Torus.mk L w ≠ Torus.mk L (-w) :=
    torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
  have hsum := sum_le_finsum_of_finite (finite_support_toNat_torusOrder_weierstrassP_sub (℘[L] w))
    {Torus.mk L w, Torus.mk L (-w)}
  rw [finsum_toNat_torusOrder_weierstrassP_sub, Finset.sum_pair hne] at hsum
  have o1 := two_le_toNat_torusOrder_weierstrassP_sub hw rfl h'
  have o2 := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
  omega
end GroundTheory.Global.Elliptic
