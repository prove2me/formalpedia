-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.trace_mat_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:12.234302+00:00
-- url     : https://prove2.me/submissions/784daa0e-1d9b-4f30-bee9-961ef7f5e8cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
namespace GlobalTheory.UnitLemma.SgnProd
theorem _root_.solution {E A : Type} [Field E] [CommRing A] [Algebra E A] {ι κ : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι E A) (x : κ → A) (f : ι → A) :
    (Matrix.of fun k l => Algebra.trace E A (x k * f l)) =
      (Matrix.of fun k i => Algebra.trace E A (x k * b i)) * b.toMatrix f := by
  ext k l
  rw [Matrix.of_apply, Matrix.mul_apply, ← b.sum_toMatrix_smul_self f l, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, Matrix.of_apply, mul_comm]
end GlobalTheory.UnitLemma.SgnProd
