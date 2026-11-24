-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.toMixed_embA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:41.824291+00:00
-- url     : https://prove2.me/submissions/0b569692-f0b0-4a3b-b741-c2b12dfd4344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLattice
import Theorems.Thm_GlobalTheory_CMVal_Model_IsCMType_bijective
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HeckePoisson_embA_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
noncomputable section
open GlobalTheory GlobalTheory.HeckePoisson
open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckePoisson
theorem _root_.solution {φ : I → K →+* ℂ} (h : IsCMType φ) (α : 𝓞 K) :
    toMixed h (embA φ α) = mixedEmbedding K (α : K) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
  rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
  simp only [toMixed, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, embA_apply]
  set i := (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).symm w.1 with hi
  have hw : InfinitePlace.mk (φ i) = w.1 :=
    (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).apply_symm_apply w.1
  split_ifs with hs
  · rw [hs, hw]
  · have hc := (InfinitePlace.embedding_mk_eq (φ i)).resolve_left (fun e => hs e.symm)
    rw [← hw, hc]
    simp [ComplexEmbedding.conjugate_coe_eq]
end GlobalTheory.HeckePoisson
