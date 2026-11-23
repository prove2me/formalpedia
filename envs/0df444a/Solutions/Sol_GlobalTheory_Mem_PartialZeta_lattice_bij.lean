-- Prove2me | solution 1 for GlobalTheory.Mem.PartialZeta.lattice_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:01.202462+00:00
-- url     : https://prove2.me/submissions/219dd924-af8f-4c8e-b070-e28c6c768229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.PartialZeta
theorem _root_.solution (N B : Ideal (𝓞 K)) (hB : IsCoprime B N) (e : Module.Basis (Fin 2) ℤ ↥(N * B))
    (x₀ : 𝓞 K) (h0 : x₀ ∈ B) (h1 : x₀ - 1 ∈ N) :
    ∃ f : ℤ × ℤ ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N},
      ∀ p, (f p : 𝓞 K) = x₀ + p.1 * (e 0 : 𝓞 K) + p.2 * (e 1 : 𝓞 K) := by
  have hmemNB : ∀ y : ↥(N * B), (y : 𝓞 K) ∈ B ∧ (y : 𝓞 K) ∈ N := fun y =>
    ⟨Ideal.mul_le_right y.2, Ideal.mul_le_left y.2⟩
  let g : ↥(N * B) ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N} :=
    { toFun := fun y => ⟨x₀ + y, B.add_mem h0 (hmemNB y).1, by
        rw [add_sub_right_comm]; exact N.add_mem h1 (hmemNB y).2⟩
      invFun := fun x => ⟨x.1 - x₀, by
        rw [← Ideal.inf_eq_mul_of_isCoprime hB.symm]
        refine ⟨?_, ?_⟩
        · have : x.1 - x₀ = (x.1 - 1) - (x₀ - 1) := by ring
          rw [this]; exact N.sub_mem x.2.2 h1
        · exact B.sub_mem x.2.1 h0⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  refine ⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩
  simp [g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]
end GlobalTheory.Mem.PartialZeta
