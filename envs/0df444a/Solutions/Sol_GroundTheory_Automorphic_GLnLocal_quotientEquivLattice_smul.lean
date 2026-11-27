-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:32.924662+00:00
-- url     : https://prove2.me/submissions/1990cb74-46c3-4e3e-a593-e1c66e01961a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (g : GL (Fin n) F) (x : GL (Fin n) F ⧸ integralGL F n) :
    quotientEquivLattice F n (g • x) = g • quotientEquivLattice F n x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, quotientEquivLattice_mk, quotientEquivLattice_mk, smul_eq_mul,
      mul_smul]
end GroundTheory.Automorphic.GLnLocal
