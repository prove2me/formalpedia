-- Prove2me | solution 1 for ModularCurve.CuspSpace.sum_cuspWidth_eq_dedekindPsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a98f4dc8-c7fb-590b-b420-1d784f11d8c7

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_CuspSpace_card_fromCoset_fiber
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CuspSpace_sum_cuspWidth_eq_dedekindPsi
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup ModularGroup
open scoped MatrixGroups
open ModularCurve ModularCurve.CuspSpace

theorem solution (N : ℕ) [NeZero N] (s : Finset (ModularCurve.CuspSpace N)) (hs : ∀ x : ModularCurve.CuspSpace N, x ∈ s) :
    ∑ c ∈ s, ModularCurve.CuspSpace.cuspWidth c = ModularCurve.dedekindPsi N := by
  haveI : Fintype (CuspSpace N) := Fintype.ofFinite _
  haveI hfin : Finite (SL(2, ℤ) ⧸ Gamma0 N) := by
    apply Nat.finite_of_card_ne_zero
    show (Gamma0 N).index ≠ 0
    rw [ModularCurve.Gamma0_index]
    exact (ModularCurve.dedekindPsi_pos N (NeZero.ne N)).ne'
  have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.mpr hs
  subst hsu
  calc ∑ c ∈ Finset.univ, cuspWidth c
      = ∑ c : CuspSpace N, Nat.card {y : SL(2, ℤ) ⧸ Gamma0 N // fromCoset N y = c} :=
        Finset.sum_congr rfl fun c _ => (ModularCurve.CuspSpace.card_fromCoset_fiber c).symm
    _ = Nat.card ((c : CuspSpace N) × {y : SL(2, ℤ) ⧸ Gamma0 N // fromCoset N y = c}) :=
        Nat.card_sigma.symm
    _ = Nat.card (SL(2, ℤ) ⧸ Gamma0 N) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv (fromCoset N))
    _ = (Gamma0 N).index := rfl
    _ = dedekindPsi N := ModularCurve.Gamma0_index N

end S_ModularCurve_CuspSpace_sum_cuspWidth_eq_dedekindPsi
end P2MW
export P2MW.S_ModularCurve_CuspSpace_sum_cuspWidth_eq_dedekindPsi (solution)
