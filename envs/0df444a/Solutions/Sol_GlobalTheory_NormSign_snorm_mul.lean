-- Prove2me | solution 1 for GlobalTheory.NormSign.snorm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:44.798784+00:00
-- url     : https://prove2.me/submissions/f5c9a173-a608-484b-b809-8d8e692b544c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.NormSign
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.NormSign
namespace _root_.GlobalTheory.NormSign
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (x y : NumberField.mixedEmbedding.mixedSpace K) :
    _root_.GlobalTheory.NormSign.snorm (x * y) = _root_.GlobalTheory.NormSign.snorm x * _root_.GlobalTheory.NormSign.snorm y := by
  simp only [_root_.GlobalTheory.NormSign.snorm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]
  ring
end _root_.GlobalTheory.NormSign
end GlobalTheory.NormSign
