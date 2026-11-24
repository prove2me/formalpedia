-- Prove2me | solution 1 for GlobalTheory.DualLabel.lab_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:29.654918+00:00
-- url     : https://prove2.me/submissions/ff2b93ac-afd9-4f87-bac5-52010b929618

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Theorems.Thm_GlobalTheory_DualLabel_monic_normRev
import Theorems.Thm_GlobalTheory_DualLabel_rootsBar_normRev
import Theorems.Thm_GlobalTheory_DualLabel_eq_of_rootsBar_eq
import Theorems.Thm_Formalism_L2_NT_coeff_zero_ne_of_monic_irr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.DualLabel
namespace GlobalTheory.DualLabel
theorem _root_.solution : ∀ {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Simple τ' →
    Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ' →
    (∀ γ : GL (Fin d) K, LinearMap.trace ℂ τ'.V (τ'.ρ γ) = LinearMap.trace ℂ τ.V (τ.ρ γ⁻¹)) →
    O.lab d τ' = Polynomial.C ((O.lab d τ).coeff 0)⁻¹ * (O.lab d τ).reverse := by
  intro K _ _ _ C O hO d τ τ' hd hs hc hs' hc' htr
  have h := hO.2 d τ τ' hd hs hc hs' hc' htr
  obtain ⟨hm, hi, hX, -⟩ := O.lab_spec d τ hd hs hc
  have h0 := Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX
  refine eq_of_rootsBar_eq (O.lab_spec d τ' hd hs' hc').1 (monic_normRev h0) ?_
  rw [h, rootsBar_normRev hm h0]
end GlobalTheory.DualLabel
