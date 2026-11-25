-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.exists_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:16.055837+00:00
-- url     : https://prove2.me/submissions/ee89e59c-d2e0-4e4d-b579-2497dc50431c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
import Theorems.Thm_GlobalTheory_Sandwich_Model_mem_mixed_Fil
import Theorems.Thm_GlobalTheory_Sandwich_Model_mem_mixed_Lie
import Theorems.Thm_GlobalTheory_Sandwich_Model_theta_mu
import Theorems.Thm_GlobalTheory_Sandwich_Model_mu_ne_zero
import Theorems.Thm_GlobalTheory_PadicComplexHost_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
namespace GlobalTheory.Sandwich.Model
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
      (ε : PreTilt 𝓞_ℂ_[p] p) (D : Datum ε 2 (Fin 2 → ℤ_[p])),
      IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p ∧ mu ε ≠ 0 ∧
      D.Fil ≠ ⊥ ∧ D.Fil ≠ ⊤ ∧ D.Lie ≠ ⊥ ∧ D.Lie ≠ ⊤ := by
  obtain ⟨h1, h2, ε, hv, hε⟩ := GlobalTheory.PadicComplexHost.main p
  have hμ := theta_mu hv hε
  refine ⟨h1, h2, ε, mixed ε 2 {0}, hε, mu_ne_zero hv hε, ?_, ?_, ?_, ?_⟩
  · intro H
    have : (Pi.single 1 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Fil := by
      rw [mem_mixed_Fil ε hμ]; simp
    rw [H, Submodule.mem_bot] at this
    simpa using congrFun this 1
  · intro H
    have : (Pi.single 0 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Fil := by rw [H]; trivial
    rw [mem_mixed_Fil ε hμ] at this
    simpa using this 0
  · intro H
    have : (Pi.single 0 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Lie := by
      rw [mem_mixed_Lie ε hμ]; intro i hi; simp at hi; simp [hi]
    rw [H, Submodule.mem_bot] at this
    simpa using congrFun this 0
  · intro H
    have : (Pi.single 1 1 : Fin 2 → 𝓞_ℂ_[p]) ∈ (mixed ε 2 {0}).Lie := by rw [H]; trivial
    rw [mem_mixed_Lie ε hμ] at this
    simpa using this 1
end GlobalTheory.Sandwich.Model
