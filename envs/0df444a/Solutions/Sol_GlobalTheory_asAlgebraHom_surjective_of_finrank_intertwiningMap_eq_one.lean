-- Prove2me | solution 1 for GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:57.6822+00:00
-- url     : https://prove2.me/submissions/fae5354f-5527-48ec-ae56-f2b5800a0969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped MonoidAlgebra
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V), Module.finrank K (Representation.IntertwiningMap τ τ) = 1 → Nontrivial V ∧ Function.Surjective τ.asAlgebraHom := by
  intro K _ _ G _ _ V _ _ _ τ h
  classical
  have : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hV : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (Representation.IntertwiningMap τ τ) :=
      ⟨fun f g => Representation.IntertwiningMap.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, ?_⟩
  have : Nontrivial τ.asModule := hV
  have hE : Module.finrank K (Module.End K[G] τ.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd τ).toLinearEquiv.finrank_eq]
    exact h
  have hscalar : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, c • (1 : Module.End K[G] τ.asModule) = φ :=
    (finrank_eq_one_iff_of_nonzero' _ one_ne_zero).mp hE
  have : IsScalarTower K (Module.End K[G] τ.asModule) τ.asModule := ⟨fun _ _ _ => rfl⟩
  have : Module.Finite (Module.End K[G] τ.asModule) τ.asModule :=
    Module.Finite.of_restrictScalars_finite K _ _
  intro f
  let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
    { toFun := fun m => f m
      map_add' := fun x y => f.map_add x y
      map_smul' := fun φ m => by
        obtain ⟨c, rfl⟩ := hscalar φ
        exact f.map_smul c m }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := τ.asModule) F
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  exact congrArg (fun g => g v) ha
end GlobalTheory
