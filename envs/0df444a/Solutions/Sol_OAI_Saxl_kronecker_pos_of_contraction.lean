-- Prove2me | solution 1 for OAI.Saxl.kronecker_pos_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:32:15.023679+00:00
-- url     : https://prove2.me/submissions/16db2777-242b-4e9c-8f5a-8f12978dcdb3

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_Saxl_intertwiningLiftSubrep_injective

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/
theorem hom_to_cyclic_of_pair {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule)
    (u : WordSpace n e) (hu : star u = u)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation
      (cyclic (wordRep n e) u).toRepresentation, f ≠ 0 := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  let f := (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)).comp ((wordMap L).comp inc)
  refine ⟨f, ?_⟩
  intro hf
  have hp := subrepProject_pair (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx) (wordMap L x.val) ⟨u, mem_cyclic _ _⟩
  have he : f x = 0 := by rw [hf]; rfl
  change (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)) (wordMap L x.val) = 0 at he
  rw [he] at hp
  exact h (hp.symm.trans (zero_dotProduct _))

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SquareDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma spechtTensorMap_injective {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) : Function.Injective (spechtTensorMap a b) := by
  unfold spechtTensorMap
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub a).toSubmodule.subtype_injective (spechtSub b).toSubmodule.subtype_injective

lemma polytabloidTensor_real {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) :
    star (wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid b)) =
      wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid b) := by
  funext w
  simp only [Pi.star_apply, wordTensor_tmul, star_mul]
  have h₁ := congrFun (polytabloid_real a) (splitLeft w)
  have h₂ := congrFun (polytabloid_real b) (splitRight w)
  change star (polytabloid b (splitRight w)) * star (polytabloid a (splitLeft w)) = _
  rw [show star (polytabloid a (splitLeft w)) = _ from h₁,
    show star (polytabloid b (splitRight w)) = _ from h₂]
  exact mul_comm _ _

lemma polytabloidTensor_cyclic_le_range {n : ℕ} {α β : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) :
    cyclic (wordRep n (α.colLen 0 * β.colLen 0))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≤
        (spechtTensorMap a b).range := by
  unfold spechtTensorMap
  apply (cyclic_le _ _ _).mpr
  exact ⟨(⟨polytabloid a', polytabloid_mem_all a a'⟩ : Specht a) ⊗ₜ[ℂ]
    (⟨polytabloid b', polytabloid_mem_all b b'⟩ : Specht b), rfl⟩

theorem kronecker_pos_of_contraction_oai {n : ℕ} {α β μ : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) (t s : Tableau n μ)
    (L : Fin (μ.colLen 0) → Fin (α.colLen 0 * β.colLen 0) → ℂ)
    (h : dotProduct (wordMap L (polytabloid s))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0) :
    0 < kronecker a b t := by
  let z := wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')
  let S := cyclic (wordRep n (α.colLen 0 * β.colLen 0)) z
  obtain ⟨f, hf⟩ := hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid s, polytabloid_mem_all t s⟩ z (polytabloidTensor_real a' b') h
  let F := @intertwiningLiftSubrep (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  have hF : Function.Injective F := @intertwiningLiftSubrep_injective (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  apply (kronecker_pos_iff a b t).mpr
  refine ⟨F.comp f, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hzero := congrArg (fun H => H x) hz
  change F (f x) = 0 at hzero
  change F (f x) = F 0
  simpa only [map_zero] using hzero

end Saxl
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.kronecker_pos_of_contraction_oai := @OAI.Saxl.kronecker_pos_of_contraction_oai
