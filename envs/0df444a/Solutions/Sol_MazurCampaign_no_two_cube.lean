-- Prove2me | solution 1 for MazurCampaign.no_two_cube
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T07:18:15.841759+00:00
-- url     : https://prove2.me/submissions/b60cc7c3-f863-4b46-8023-116a343b12d3

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_rational_n_torsion_bound
import Mathlib.Tactic.NormNum

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2)
      (MazurCampaign.RationalTorsion E) := by
  intro φ hφ
  let φ' : (ZMod 2 × ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype.comp φ
  have hφ' : Function.Injective φ' :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective.comp hφ
  let f : (ZMod 2 × ZMod 2 × ZMod 2) →
      Submodule.torsionBy ℤ (E⁄ℚ).Point 2 := fun x =>
    ⟨φ' x, by
      apply (Submodule.mem_torsionBy_iff _ _).mpr
      have hx : (2 : ℕ) • x = 0 := ZModModule.char_nsmul_eq_zero 2 x
      have hm : (2 : ℕ) • φ' x = 0 := by rw [← map_nsmul, hx, map_zero]
      simpa only [ofNat_zsmul] using hm⟩
  have hf : Function.Injective f := by
    intro x y h
    have h' : φ' x = φ' y := congrArg
      (fun p : Submodule.torsionBy ℤ (E⁄ℚ).Point 2 => p.val) h
    exact hφ' h' 
  obtain ⟨hfinite, hbound⟩ := MazurCampaign.rational_n_torsion_bound E 2 (by decide)
  letI := hfinite
  have hsmall := Nat.card_le_card_of_injective f hf
  have hbig : Nat.card (ZMod 2 × ZMod 2 × ZMod 2) = 8 := by
    simp [Nat.card_prod, Nat.card_zmod]
  rw [hbig] at hsmall
  change Nat.card (Submodule.torsionBy ℤ (E⁄ℚ).Point 2) ≤ 4 at hbound
  omega
