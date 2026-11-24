-- Prove2me | solution 1 for GlobalTheory.DualLabel.eq_of_rootsBar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:22.112639+00:00
-- url     : https://prove2.me/submissions/880cb225-ae12-4d0a-9f6e-d95db7150dbb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.DualLabel
namespace GlobalTheory.DualLabel
theorem _root_.solution {K : Type} [Field K] {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f = Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K g) : f = g := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K (AlgebraicClosure K)).injective
  rw [(IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (g.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hg.map _)]
  exact congrArg (fun s => (s.map fun a => X - C a).prod) h
end GlobalTheory.DualLabel
