-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.exists_nat_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:22.967806+00:00
-- url     : https://prove2.me/submissions/bdbac401-13fd-49d5-b031-ad45068f004b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}
namespace GlobalTheory.CompanionTheory.PatGrp
theorem _root_.solution {H V : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (L : H → ℂ) (hL : ∀ a b, L (a * b) = L a * L b)
    (σ : H →* Module.End ℂ V) :
    ∃ m : ℕ, (Fintype.card H : ℂ)⁻¹ * ∑ h, L h * LinearMap.trace ℂ V (σ h) = m := by
  by_cases h1 : L 1 = 0
  · refine ⟨0, ?_⟩
    have hL0 : ∀ x, L x = 0 := fun x => by rw [← mul_one x, hL, h1, mul_zero]
    simp [hL0]
  · have hL1 : L 1 = 1 := by
      have h11 := hL 1 1
      rw [mul_one] at h11
      exact (mul_left_cancel₀ h1 (by rw [mul_one]; exact h11)).symm
    let σ' : Representation ℂ H V :=
      { toFun := fun x => L x • σ x
        map_one' := by
          show L 1 • σ 1 = 1
          rw [map_one, hL1, one_smul]
        map_mul' := fun a b => by
          show L (a * b) • σ (a * b) = (L a • σ a) * (L b • σ b)
          rw [hL, map_mul, smul_mul_smul_comm] }
    haveI : Invertible (Nat.card H : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
    refine ⟨Module.finrank ℂ (Representation.invariants (FDRep.of σ').ρ), ?_⟩
    rw [← FDRep.average_char_eq_finrank_invariants, Nat.card_eq_fintype_card]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    show L x * LinearMap.trace ℂ V (σ x) = LinearMap.trace ℂ V (L x • σ x)
    rw [LinearMap.map_smul, smul_eq_mul]
end GlobalTheory.CompanionTheory.PatGrp
