-- Prove2me | solution 1 for GlobalTheory.PDiv.cotMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:37.521042+00:00
-- url     : https://prove2.me/submissions/573586c6-5a99-4abc-8f83-e72b137106bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply



set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution [IsCocomm R C] (f g : WithConv (C →ₐc[R] A)) :
    cotMap (f * g).ofConv = cotMap f.ofConv + cotMap g.ofConv :=
  AugCot.hom_ext fun c => by
    have r := Coalgebra.Repr.arbitrary R c
    have h : (f * g).ofConv c = ∑ i ∈ r.index, f.ofConv (r.left i) * g.ofConv (r.right i) :=
      r.convMul_apply (toConv f.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap)
    have h1 := congrArg (fun x => dUnit R (g.ofConv x)) (Coalgebra.sum_counit_smul r)
    have h2 : ∑ i ∈ r.index, counit (R := R) (r.right i) • r.left i = c := by
      have := congrArg (TensorProduct.rid R C) (Coalgebra.sum_tmul_counit_eq r)
      simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using this
    have h3 := congrArg (fun x => dUnit R (f.ofConv x)) h2
    simp only [map_sum, map_smul] at h1 h3
    rw [LinearMap.add_apply, cotMap_d, cotMap_d, cotMap_d, h, ← h1, ← h3, add_comm,
      ← Finset.sum_add_distrib, dUnit, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AugCot.d_mul]
    simp
end GlobalTheory.PDiv
