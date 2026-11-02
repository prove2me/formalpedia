-- Prove2me | solution 1 for LieTwoAlg.Equiv.proposition_35
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:54:34.862719+00:00
-- url     : https://prove2.me/submissions/9c22ffb5-171e-4f97-867b-a3cb46667b96

import Definitions.Def_LieTwoAlg_Equiv_Model
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open LieTwoAlg.Equiv

universe u

/-- Proposition 35, p. 30: the category laws of 2TermL∞. -/
theorem solution {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) :
    (∀ {V W X : LInfData k} (hV : IsLInf V) (hW : IsLInf W) (hX : IsLInf X)
      (φ : LInfHom V W) (ψ : LInfHom W X),
      IsLInfHom φ → IsLInfHom ψ → IsLInfHom (φ.comp ψ)) ∧
    (∀ (V : LInfData k), IsLInf V → IsLInfHom (LInfHom.id V)) ∧
    (∀ {V W X Y : LInfData k} (φ : LInfHom V W) (ψ : LInfHom W X)
      (χ : LInfHom X Y), IsLInfHom φ → IsLInfHom ψ → IsLInfHom χ →
      (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)) ∧
    (∀ {V W : LInfData k} (φ : LInfHom V W), IsLInfHom φ →
      (LInfHom.id V).comp φ = φ ∧ φ.comp (LInfHom.id W) = φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V W X hV hW hX φ ψ hφ hψ
    constructor
    · intro h
      exact (hψ.chain (φ.φ1 h)).trans (congrArg ψ.φ0 (hφ.chain h))
    · intro x y
      change ψ.φ2 (φ.φ0 x) (φ.φ0 y) + ψ.φ1 (φ.φ2 x y) =
        -(ψ.φ2 (φ.φ0 y) (φ.φ0 x) + ψ.φ1 (φ.φ2 y x))
      rw [hψ.skew (φ.φ0 x) (φ.φ0 y), hφ.skew x y, map_neg]
      abel
    · intro x y
      simp only [LInfHom.comp, preBilin, postBilin, LinearMap.add_apply,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, map_add]
      rw [hψ.one, hψ.chain, hφ.one, map_sub]
      abel
    · intro x h
      simp only [LInfHom.comp, preBilin, postBilin, LinearMap.add_apply,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
      rw [← hφ.chain, hψ.two, hφ.two, map_sub]
      abel
    · intro x y z
      simp only [LInfHom.comp, preBilin, postBilin, LinearMap.add_apply,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
      have one (a b : V.V0) : φ.φ0 (V.l2 a b) = W.d (φ.φ2 a b) + W.l2 (φ.φ0 a) (φ.φ0 b) := by
        rw [hφ.one]; abel
      rw [one x y, one y z, one x z]
      simp only [map_add, LinearMap.add_apply]
      rw [hψ.skew (W.d (φ.φ2 x y)), hψ.skew (W.d (φ.φ2 x z))]
      rw [hψ.two, hψ.two, hψ.two]
      have eqφ := congrArg ψ.φ1 (hφ.three x y z)
      simp only [map_add, map_sub, map_neg] at eqφ
      have eqψ := hψ.three (φ.φ0 x) (φ.φ0 y) (φ.φ0 z)
      linear_combination (norm := abel) eqφ + eqψ
  · intro V hV
    constructor <;> intros <;> simp [LInfHom.id]
  · intro V W X Y φ ψ χ hφ hψ hχ
    cases φ; cases ψ; cases χ
    simp only [LInfHom.comp]
    congr 1 <;> ext <;> simp [preBilin, postBilin, map_add, add_assoc]
  · intro V W φ hφ
    constructor <;> cases φ <;> simp only [LInfHom.comp, LInfHom.id] <;>
      congr 1 <;> ext <;> simp [preBilin, postBilin]



