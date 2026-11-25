-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.isStableGauss_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:10.494894+00:00
-- url     : https://prove2.me/submissions/e333128d-2e1c-4aaa-9272-09422bfcff9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussAtUniformiserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralTransformWeil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
open scoped Pointwise
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K)
    {G G' : ℂ} (h : IsStableGauss A ψ x μ u G) (h' : IsStableGauss A ψ x μ u G') : G = G' := by
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  obtain ⟨Λ₀, ho, hc, hG⟩ := h
  obtain ⟨Λ₁, ho', hc', hG'⟩ := h'
  have hs : ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) = (Λ₀ : Set A.L) + (Λ₁ : Set A.L) := AddSubgroup.add_normal Λ₀ Λ₁
  have hO : IsOpen ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := AddSubgroup.isOpen_mono le_sup_left ho
  have hC : IsCompact ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := by rw [hs]; exact hc.add hc'
  rw [← hG _ hO hC le_sup_left, ← hG' _ hO hC le_sup_right]
end GlobalTheory.JR.WeilQuad
