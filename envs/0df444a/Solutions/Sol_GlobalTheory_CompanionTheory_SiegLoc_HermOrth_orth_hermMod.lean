-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:36.069951+00:00
-- url     : https://prove2.me/submissions/df6a8bfd-d156-425c-bae8-0223d9f8acc7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_red_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_tsum_eq_zero_of_shift
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_hermMod_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_hermMod_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_eq_zero_of_trivial

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
theorem _root_.solution (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)]
    (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (hψ : IsLevelChars σ ϖ ψ) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hY : Y ∈ hermMod σ ϖ n k) :
    (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) =
        (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧
      (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0) := by
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · subst h0
    simp only [Matrix.mul_zero, Matrix.trace_zero, AddChar.map_zero_eq_one]
    rw [tsum_const, nsmul_eq_mul, mul_one]
  · have hY' := hY
    unfold PositivityTheory.PfSWUS.Loc.hermMod at hY'
    obtain ⟨y, hy, rfl⟩ := hY'
    by_contra hsum
    apply hne
    apply GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial hR hψ n k y hy
    intro b hb
    rw [← GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul]
    by_contra hb1
    exact hsum (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.tsum_eq_zero_of_shift _
      (fun a₁ a₂ h₁ h₂ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add a₁ a₂ h₁ h₂)
      (fun a₁ h₁ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_neg a₁ h₁)
      (fun B => ψ k (Matrix.trace (B * PositivityTheory.PfSWUS.Loc.red ϖ k y)))
      (fun a₁ a₂ => by simp only [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul])
      (PositivityTheory.PfSWUS.Loc.red ϖ k b) ⟨b, hb, rfl⟩ hb1)
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
