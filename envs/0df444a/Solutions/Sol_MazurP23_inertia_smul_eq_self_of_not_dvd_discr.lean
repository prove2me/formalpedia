-- Prove2me | solution 1 for MazurP23.inertia_smul_eq_self_of_not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:10:27.152299+00:00
-- url     : https://prove2.me/submissions/7488cc0f-921b-486a-ad03-aebd3c231cc2

import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_ValuationSubring_ReduceAt
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23

theorem _root_.solution (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hgood : ¬ (ℓ : ℤ) ∣ W.Δ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    {n : ℕ} (hn : ¬ ℓ ∣ n)
    (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hy : n • y = 0) :
    τ • y = y := by
  classical

  obtain ⟨τ', hτ'I, hττ'⟩ := Subgroup.mem_map.mp hτ

  have hVW : (W.map (Int.castRingHom A)).map A.subtype
      = ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) := by
    show (W.map (Int.castRingHom A)).map A.subtype
      = (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
  have hΔred : ((W.map (Int.castRingHom A)).map (IsLocalRing.residue A)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
    exact ValuationSubring.residue_intCast_ne_zero hℓ hA hgood
  have hnres : ((n : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
    have h0 := ValuationSubring.residue_intCast_ne_zero hℓ hA
      (n := (n : ℤ)) (by exact_mod_cast hn)
    have h2 : ((n : ℤ) : A) = ((n : ℕ) : A) := by push_cast; rfl
    rw [h2, map_natCast] at h0
    exact h0

  rcases hPy : y with _ | ⟨x₁, y₁, h₁⟩
  · rfl

  obtain ⟨hns, hτsome⟩ : ∃ hns :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (τ x₁) (τ y₁),
      τ • (Point.some x₁ y₁ h₁ :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = Point.some (τ x₁) (τ y₁) hns :=
    ⟨_, Point.map_some τ.toAlgHom h₁⟩
  rw [hPy] at hy
  have hy' : n • (Point.some (τ x₁) (τ y₁) hns :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    have h2 : τ • (n • (Point.some x₁ y₁ h₁ :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point))
        = n • (τ • (Point.some x₁ y₁ h₁ :
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) := by
      rw [← natCast_zsmul, WeierstrassCurve.Affine.Point.algEquiv_smul_zsmul, natCast_zsmul]
    rw [← hτsome, ← h2, hy]
    rfl

  have hτD : τ ∈ A.decompositionSubgroup ℚ := hττ' ▸ τ'.2
  have hfix := WeierstrassCurve.fixed_of_mem_inertia_of_nsmul_eq_zero
    (A := A) (W := W.map (Int.castRingHom A)) hVW hΔred (σ := τ) hτD
    (by
      have heq : (⟨τ, hτD⟩ : A.decompositionSubgroup ℚ) = τ' := Subtype.ext hττ'.symm
      rw [heq]
      exact hτ'I)
    hnres h₁ hns hy hy'
  rw [hτsome]
  simp only [hfix.1, hfix.2]

end MazurP23
