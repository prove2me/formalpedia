-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isIrreducible_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:21.376776+00:00
-- url     : https://prove2.me/submissions/acd25489-96eb-4d06-850d-fcd63c0882c7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isStable_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
omit hρ hKc hKo
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (hρ : IsSmooth ρ) [Nontrivial V]
    (h : ∀ x y : V, x ≠ 0 → ∃ (K : Subgroup G) (hKc : IsCompact (K : Set G))
      (hKo : IsOpen (K : Set G)), x ∈ fixedVectors ρ K ∧ y ∈ fixedVectors ρ K ∧
        IsSimpleUnder (heckeOps hρ hKc hKo)) :
    ρ.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h0] at this
    exact hx this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }
  by_cases hX : X.toSubmodule = ⊥
  · left
    ext x
    constructor
    · intro hx
      have : x ∈ X.toSubmodule := hx
      rw [hX] at this
      exact this
    · intro hx
      have : x = 0 := hx
      rw [this]
      exact X.toSubmodule.zero_mem
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  ext y
  refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
  obtain ⟨K, hKc, hKo, hxK, hyK, hsimple⟩ := h x y hx0
  have hst := isStable_comap hρ hKc hKo X
  rcases hsimple.2 _ hst with h0 | h0
  · exfalso
    have : (⟨x, hxK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype := hx
    rw [h0, Submodule.mem_bot] at this
    exact hx0 (congrArg Subtype.val this)
  · have : (⟨y, hyK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype := by
      rw [h0]; trivial
    exact this
end GroundTheory.Automorphic.RestrictedTensor
