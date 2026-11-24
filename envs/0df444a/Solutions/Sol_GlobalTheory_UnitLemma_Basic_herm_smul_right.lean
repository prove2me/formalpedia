-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Basic.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:21:21.150794+00:00
-- url     : https://prove2.me/submissions/3196a9c2-c54c-4bed-8823-bf63324a5dd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NLineOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.UnitLemma.Basic
variable {K : UQ} (B : InvAlg K)
variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
private theorem sigma_smul_eq_conj_smul (e : K.E) (v : B.A) : B.σ (e • v) = K.c e • B.σ v := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
end GlobalTheory.UnitLemma.Basic
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Basic
variable {K : UQ} (B : InvAlg K)
variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K)
namespace GlobalTheory.UnitLemma.Basic
namespace _root_.GlobalTheory.UnitLemma.Basic
theorem _root_.solution (x y z : B.A) (e : K.E) :
    B.herm x y (e • z) = K.c e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [sigma_smul_eq_conj_smul, mul_smul_comm, map_smul, smul_eq_mul]
end _root_.GlobalTheory.UnitLemma.Basic
end GlobalTheory.UnitLemma.Basic
