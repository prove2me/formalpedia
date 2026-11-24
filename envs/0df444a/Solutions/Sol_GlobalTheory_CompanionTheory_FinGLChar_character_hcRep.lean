-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGLChar.character_hcRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:24:30.272832+00:00
-- url     : https://prove2.me/submissions/020ca71e-b8d4-464e-8b06-a663838857af

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_mul_mul_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_trace_infl
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_GlobalTheory_BadShare_trace_coind_mul_card
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGLChar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
namespace GlobalTheory.CompanionTheory.FinGLChar
theorem _root_.solution :
    (hcRep K b lam).character = indF (parab K b) (hcFun b fun c => (lam c).character) := by
  classical
  funext g
  have : FiniteDimensional ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c))
  let _ : Fintype (parab K b) := Fintype.ofFinite _
  have h1 : (hcRep K b lam).character g = LinearMap.trace ℂ _
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam) g) := rfl
  have h := GlobalTheory.BadShare.trace_coind_mul_card (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam) g
  rw [← h1] at h
  have hc : (Fintype.card (parab K b) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold indF
  rw [Nat.card_eq_fintype_card, eq_inv_mul_iff_mul_eq₀ hc, mul_comm, h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x * g * x⁻¹ ∈ parab K b
  · have key : ∀ γ : parab K b, (parab K b).subtype γ * (x * g) = x ↔ γ = (⟨_, hx⟩ : parab K b)⁻¹ := by
      intro γ
      rw [mul_mul_eq_iff]
      constructor
      · intro e
        refine Subtype.ext ?_
        show (γ : GL ι K) = (x * g * x⁻¹)⁻¹
        rw [← e]
        simp
      · rintro rfl
        exact inv_inv _
    simp only [key]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos hx, inv_inv]
    exact trace_infl b lam _
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun γ _ => if_neg fun e => hx ?_
    rw [← (mul_mul_eq_iff _ x g).1 e]
    exact (parab K b).inv_mem γ.2
end GlobalTheory.CompanionTheory.FinGLChar
