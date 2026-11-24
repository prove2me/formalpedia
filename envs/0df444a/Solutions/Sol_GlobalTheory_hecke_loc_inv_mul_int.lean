-- Prove2me | solution 1 for GlobalTheory.hecke_loc_inv_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:59:06.281496+00:00
-- url     : https://prove2.me/submissions/be1d52e2-bca4-41ee-b4e0-c83d458c8700

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegral
import Theorems.Thm_GlobalTheory_HeckeLocInt_inv_mul_int_of_left_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F) (k : ℕ), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (a a' b b' g g' : GL (Fin n) (v.adicCompletion F)), (∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) → (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  intro F _ _ v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'
  exact HeckeLocInt.inv_mul_int_of_left_congr ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'
end GlobalTheory
