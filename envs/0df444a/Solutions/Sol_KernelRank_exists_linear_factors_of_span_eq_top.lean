-- Prove2me | solution 1 for KernelRank.exists_linear_factors_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:12:36.927309+00:00
-- url     : https://prove2.me/submissions/1c96f7b2-2d99-484c-9601-5540dcd3744d

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 α V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] {d R : ℕ} {v : α → V} (hv : Submodule.span 𝕜 (Set.range v) = ⊤)
    (T : MultilinearMap 𝕜 (fun _ : Fin d => V) 𝕜)
    (hK : IsSumOfProducts (fun s : Fin d → α => T fun j => v (s j)) R) :
    ∃ ℓ : Fin R → Fin d → (V →ₗ[𝕜] 𝕜),
      ∀ u : Fin d → V, T u = ∑ n, ∏ j, ℓ n j (u j) := by
  obtain ⟨f, hf⟩ := hK
  obtain ⟨κ, a, _, hsp, hli⟩ := exists_linearIndependent' 𝕜 v
  let B : Module.Basis κ 𝕜 V := Module.Basis.mk hli (hv ▸ hsp).ge
  let ℓ (n : Fin R) (j : Fin d) : V →ₗ[𝕜] 𝕜 := B.constr ℕ fun k => f n j (a k)
  refine ⟨ℓ, fun u => ?_⟩
  let T' : MultilinearMap 𝕜 (fun _ : Fin d => V) 𝕜 :=
    ∑ n : Fin R, (MultilinearMap.mkPiAlgebra 𝕜 (Fin d) 𝕜).compLinearMap (ℓ n)
  have heq : T = T' := Module.Basis.ext_multilinear (fun _ => B) fun k => by
    have hBk (j : Fin d) : B (k j) = v (a (k j)) := Module.Basis.mk_apply hli (hv ▸ hsp).ge (k j)
    have hℓB (n : Fin R) (j : Fin d) : ℓ n j (B (k j)) = f n j (a (k j)) :=
      B.constr_basis ℕ _ (k j)
    simp only [T', FunLike.coe_sum, Finset.sum_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, hℓB]
    simp_rw [hBk]
    exact hf fun j => a (k j)
  simpa [T'] using congrArg (· u) heq
end KernelRank
