-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.smul_smul_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:51.336645+00:00
-- url     : https://prove2.me/submissions/0cbfdcf8-f36c-46ca-ad6e-e57746c96ccf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {δ ψ : G}
    (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hψ : ψ ∈ (L : Subgroup G)) {y : A}
    (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) : δ • ψ • y = ψ • δ • y := by
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hc : δ⁻¹ * ψ⁻¹ * δ * ψ ∈ (L : Subgroup G) ⊓ D.deg.ker := by
    refine ⟨?_, ?_⟩
    · have h1 : δ⁻¹ * ψ⁻¹ * δ⁻¹⁻¹ ∈ (L : Subgroup G) :=
        hconj δ⁻¹ (K.inv_mem hδ.1) _ (L.inv_mem hψ)
      rw [inv_inv] at h1
      exact L.mul_mem h1 hψ
    · have hdδ : D.deg δ = 1 := hδ.2
      show D.deg (δ⁻¹ * ψ⁻¹ * δ * ψ) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hdδ]
      simp
  calc δ • ψ • y = (ψ * δ * (δ⁻¹ * ψ⁻¹ * δ * ψ)) • y := by rw [← mul_smul]; group
    _ = ψ • δ • y := by rw [mul_smul, hy _ hc, mul_smul]
end GroundTheory.LocalField.Abstract.ClassFieldData
