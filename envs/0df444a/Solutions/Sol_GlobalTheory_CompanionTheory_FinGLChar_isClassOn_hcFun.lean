-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGLChar.isClassOn_hcFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:00:44.045929+00:00
-- url     : https://prove2.me/submissions/7f9ad2d0-0b5b-4647-a09c-d2018f46d84b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGLChar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
namespace GlobalTheory.CompanionTheory.FinGLChar
theorem _root_.solution :
    IsClassOn (parab K b) (hcFun b fun c => (lam c).character) := by
  intro x hx h hh
  have hm : x * h * x⁻¹ ∈ parab K b := (parab K b).mul_mem ((parab K b).mul_mem hx hh) ((parab K b).inv_mem hx)
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [blkGL, blkGL, dif_pos hm, dif_pos hh]
  have e : (⟨x * h * x⁻¹, hm⟩ : parab K b) = ⟨x, hx⟩ * ⟨h, hh⟩ * (⟨x, hx⟩ : parab K b)⁻¹ := rfl
  have e' : levi K b c ⟨x * h * x⁻¹, hm⟩ =
      leviHom b c ⟨x, hx⟩ * leviHom b c ⟨h, hh⟩ * (leviHom b c ⟨x, hx⟩)⁻¹ := by
    rw [e, ← map_inv, ← map_mul, ← map_mul]
    rfl
  beta_reduce
  rw [e', mul_assoc, FDRep.char_mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  rfl
end GlobalTheory.CompanionTheory.FinGLChar
