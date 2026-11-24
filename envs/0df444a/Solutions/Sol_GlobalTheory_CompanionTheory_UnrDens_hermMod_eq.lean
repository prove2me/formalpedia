-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.hermMod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:08:12.578508+00:00
-- url     : https://prove2.me/submissions/35e51b00-8a56-430e-8ef8-79949691be06

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPow
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_exists_trace_one
import Theorems.Thm_GlobalTheory_GramCount_exists_trace_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (h : IsUnrQuad R σ ϖ q ε) (n k : ℕ) :
    hermMod σ ϖ n k = {H | ∀ a b, barσ σ ϖ h.fix_ϖ k (H b a) = H a b} := by
  ext H
  simp only [PositivityTheory.PfSWUS.Loc.hermMod, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, hh, rfl⟩ a b
    have hab := congrFun (congrFun hh a) b
    simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply] at hab
    simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, barσ_mk]
    rw [hab]
  · intro hH
    obtain ⟨-, θ, -, hθ⟩ := exists_trace_one h
    choose lift hlift using fun a b => Ideal.Quotient.mk_surjective (H a b)
    refine ⟨Matrix.of fun a b => θ * lift a b + σ (θ * lift b a), ?_, ?_⟩
    · ext a b
      simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_add,
        h.inv]
      ring
    · ext a b
      have e1 : Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (σ (lift b a)) = barσ σ ϖ h.fix_ϖ k (H b a) := by
        rw [← hlift b a, barσ_mk]
      have hθ' : Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) θ + Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (σ θ) = 1 := by
        rw [← map_add, hθ, map_one]
      simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.of_apply, map_add, map_mul, hlift]
      rw [e1, hH a b]
      linear_combination (H a b) * hθ'
end GlobalTheory.CompanionTheory.UnrDens
