-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.tm_isClosedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:24.482233+00:00
-- url     : https://prove2.me/submissions/20d674b5-cc80-4f3b-baf5-d869fe8537ef

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom
import Theorems.Thm_GlobalTheory_JR_LinDesc_tm_coe
import Theorems.Thm_GlobalTheory_JR_LinDesc_tm_inv_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : A.K ≃ₜ (Fin r → F) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let g : (Fin r → F) →ₗ[F] Matrix (Fin r) (Fin r) F :=
    (Algebra.leftMulMatrix (bas A hG)).toLinearMap ∘ₗ e.symm.toLinearMap
  have hg : IsClosedEmbedding g := by
    refine LinearMap.isClosedEmbedding_of_injective ?_
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h1 := Algebra.leftMulMatrix_injective (bas A hG) hxy
    exact e.symm.injective h1
  let f : A.K → Matrix (Fin r) (Fin r) F := fun x => Algebra.leftMulMatrix (bas A hG) x
  have hf : IsClosedEmbedding f := by
    have : f = g ∘ eh := by
      funext x; simp [f, g, eh, e]
    rw [this]; exact hg.comp eh.isClosedEmbedding
  haveI : T2Space A.K := eh.isEmbedding.t2Space
  have hfo : IsClosedEmbedding (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x))) :=
    MulOpposite.opHomeomorph.isClosedEmbedding.comp (hf.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hP : IsClosedEmbedding (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) :=
    hf.prodMap hfo
  have hK : IsClosedEmbedding (Units.embedProduct A.K) := Units.isClosedEmbedding_embedProduct
  have hM : IsClosedEmbedding (Units.embedProduct (Matrix (Fin r) (Fin r) F)) := Units.isClosedEmbedding_embedProduct
  have hcomp : (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG) =
      (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) ∘ Units.embedProduct A.K := by
    funext t
    simp only [Function.comp_apply, Units.embedProduct_apply, Prod.map_apply, MulOpposite.unop_op]
    refine Prod.ext ?_ ?_
    · exact tm_coe A hG t
    · simp only
      rw [tm_inv_coe]
  have hc : IsClosedEmbedding ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
    rw [hcomp]; exact hP.comp hK
  have hcont : Continuous (LinDesc.tm A hG) := by
    rw [hM.isInducing.continuous_iff]; exact hc.continuous
  refine ⟨⟨Topology.IsInducing.of_comp hcont hM.continuous hc.isInducing, ?_⟩, ?_⟩
  · intro x y hxy
    exact hc.injective (by simp [Function.comp_apply, hxy])
  · have : Set.range (LinDesc.tm A hG) = (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ⁻¹' Set.range ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
      ext x; constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩; exact ⟨t, hM.injective ht⟩
    rw [this]; exact hc.isClosed_range.preimage hM.continuous
end GlobalTheory.JR.LinDesc
