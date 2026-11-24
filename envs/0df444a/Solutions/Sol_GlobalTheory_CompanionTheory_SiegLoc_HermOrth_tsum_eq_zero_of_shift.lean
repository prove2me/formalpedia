-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.HermOrth.tsum_eq_zero_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:49.342189+00:00
-- url     : https://prove2.me/submissions/16b59369-9d64-4c70-99c8-a8b4a38aafe8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth
theorem _root_.solution {G : Type} [AddCommGroup G] (H : Set G)
    (hadd : ∀ a b, a ∈ H → b ∈ H → a + b ∈ H) (hneg : ∀ a, a ∈ H → -a ∈ H)
    (f : G → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) (B₀ : G) (hB₀ : B₀ ∈ H) (h : f B₀ ≠ 1) :
    ∑' B : H, f B.1 = 0 := by
  let e : H ≃ H :=
    { toFun := fun B => ⟨B₀ + B.1, hadd _ _ hB₀ B.2⟩
      invFun := fun B => ⟨-B₀ + B.1, hadd _ _ (hneg _ hB₀) B.2⟩
      left_inv := fun B => Subtype.ext (by simp)
      right_inv := fun B => Subtype.ext (by simp) }
  have key : ∑' B : H, f B.1 = f B₀ * ∑' B : H, f B.1 := by
    calc ∑' B : H, f B.1 = ∑' B : H, f (e B).1 := (e.tsum_eq (fun B : H => f B.1)).symm
      _ = ∑' B : H, f B₀ * f B.1 := tsum_congr fun B => by
          show f (B₀ + B.1) = _
          exact hf _ _
      _ = f B₀ * ∑' B : H, f B.1 := tsum_mul_left
  have hzero : (f B₀ - 1) * ∑' B : H, f B.1 = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact absurd (sub_eq_zero.mp h') h
  · exact h'
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
