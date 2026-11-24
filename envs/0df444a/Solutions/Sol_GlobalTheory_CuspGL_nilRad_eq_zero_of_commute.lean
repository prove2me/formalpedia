-- Prove2me | solution 1 for GlobalTheory.CuspGL.nilRad_eq_zero_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:41.109987+00:00
-- url     : https://prove2.me/submissions/76b192a4-7786-4f40-bcd3-e92114cded96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsConjEqAddOfIsCoprime
import Theorems.Thm_GlobalTheory_CuspGL_intertwine_aeval_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (hc : IsCoprime (LinearMap.charpoly (g.restrict hg))
      (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))))
    (u : Module.End F V) (hu : u ∈ nilRad A) (hug : ∀ x, u (g x) = g (u x)) : u = 0 := by
  obtain ⟨a, b, hab⟩ := hc
  set p₁ := LinearMap.charpoly (g.restrict hg) with hp₁
  set p₂ := LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) with hp₂
  have h1 : ∀ y ∈ A, aeval g p₁ y = 0 := by
    intro y hy
    have := intertwine_aeval_apply A.subtype (g.restrict hg) g (fun x => rfl) p₁ ⟨y, hy⟩
    rw [hp₁, LinearMap.aeval_self_charpoly] at this
    simpa using this.symm
  have h2 : ∀ y, aeval g p₂ y ∈ A := by
    intro y
    have := intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hg x hx)) (fun x => rfl) p₂ y
    rw [hp₂, LinearMap.aeval_self_charpoly] at this
    simpa using this
  ext x
  have hx : x = aeval g p₁ (aeval g a x) + aeval g p₂ (aeval g b x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← LinearMap.add_apply, ← map_add,
      mul_comm p₁, mul_comm p₂, hab]
    simp
  rw [hx, map_add, hu.2 _ (h2 _), intertwine_aeval_apply u g g hug, h1 _ (hu.1 _)]
  simp
end GlobalTheory.CuspGL
