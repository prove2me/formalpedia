-- Prove2me | solution 1 for GlobalTheory.DualLabel.rootsBar_normRev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:33.659848+00:00
-- url     : https://prove2.me/submissions/113687a6-00eb-4f70-bbae-0c56608bc6a7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Theorems.Thm_GlobalTheory_DualLabel_roots_reverse_prod
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.DualLabel
namespace GlobalTheory.DualLabel
theorem _root_.solution {K : Type} [Field K] {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K (C (f.coeff 0)⁻¹ * f.reverse) =
      (Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f).map (·⁻¹) := by
  have hz : (0 : AlgebraicClosure K) ∉ Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f := fun h => by
    rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, mem_roots (hm.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero,
      coeff_map] at h
    exact h0 ((map_eq_zero _).1 h)
  have e : f.reverse.map (algebraMap K (AlgebraicClosure K)) = (f.map (algebraMap K (AlgebraicClosure K))).reverse := by
    rw [reverse, reverse, reflect_map, natDegree_map]
  have hf := (IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hm.map _)
  rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
  exact roots_reverse_prod _ hz
end GlobalTheory.DualLabel
