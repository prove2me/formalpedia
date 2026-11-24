-- Prove2me | solution 1 for GlobalTheory.exists_zlattice_basis_realCoord_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:59.053137+00:00
-- url     : https://prove2.me/submissions/a36942d4-4c6a-49be-b8b6-9358fd79a587

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeRealCoordinateBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace GlobalTheory
theorem _root_.solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by
  intro g Λ hd hs
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let bZ0 := Module.Free.chooseBasis ℤ Λ
  let bZ := bZ0.reindex (Fintype.equivFin _)
  let bR := bZ.ofZLatticeBasis ℝ Λ
  refine ⟨_, fun i => bZ i, fun i => bR.coord i, ?_, ?_⟩
  · intro v
    have h := bR.sum_repr v
    conv_rhs => rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [bR]
  · intro φ x
    have hx : ∀ i, bR.coord i (x : Fin g → ℂ) = ((bZ.repr x i : ℤ) : ℝ) := by
      intro i
      simp [bR, Module.Basis.ofZLatticeBasis_repr_apply]
    simp_rw [hx]
    conv_rhs => rw [← bZ.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul, map_zsmul]
end GlobalTheory
