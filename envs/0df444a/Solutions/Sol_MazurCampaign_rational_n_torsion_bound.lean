-- Prove2me | solution 1 for MazurCampaign.rational_n_torsion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T07:10:26.140491+00:00
-- url     : https://prove2.me/submissions/12bff7eb-f69f-4713-950b-b3658e71e237

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Bridge from Anthropic's FLT n-torsion cardinality theorem to the canonical
Mathlib rational-point group used by the full Mazur mission.
-/
import Definitions.Def_MazurCampaign_target_objects
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.NormNum

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) :
    Finite (Submodule.torsionBy ℤ (E⁄ℚ).Point n) ∧
      Nat.card (Submodule.torsionBy ℤ (E⁄ℚ).Point n) ≤ n ^ 2 := by
  classical
  let j : (E⁄ℚ).Point →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    WeierstrassCurve.Affine.Point.baseChange (W' := E) ℚ (AlgebraicClosure ℚ)
  let f : Submodule.torsionBy ℤ (E⁄ℚ).Point n →
      Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n := fun P =>
    ⟨j P.1, by
      apply (Submodule.mem_torsionBy_iff _ _).mpr
      have hP := (Submodule.mem_torsionBy_iff _ _).mp P.property
      simpa only [map_zsmul, map_zero] using congrArg j hP⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact WeierstrassCurve.Affine.Point.map_injective
      (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (congrArg Subtype.val h)
  have hnK : (n : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hn
  have hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n) = n ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed E hnK
  letI : Finite (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hn)
  exact ⟨Finite.of_injective f hf, hcard ▸ Nat.card_le_card_of_injective f hf⟩
