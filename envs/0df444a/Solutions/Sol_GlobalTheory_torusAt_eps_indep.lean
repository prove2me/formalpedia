-- Prove2me | solution 1 for GlobalTheory.torusAt_eps_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:47.414096+00:00
-- url     : https://prove2.me/submissions/72625068-4817-4285-8d3b-bbd384ee3b87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_B_int
import Theorems.Thm_GlobalTheory_SemicharIndep_smul_mem
import Theorems.Thm_GlobalTheory_SemicharIndep_parity_eq
import Theorems.Thm_GlobalTheory_SemicharIndep_eps_val
import Theorems.Thm_GlobalTheory_SemicharIndep_par_of_torusAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open SemicharIndep
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ (x x' : Frame X.Ψ r) (A : TorusAt X.toData x) (A' : TorusAt X.toData x') (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ v ∈ X.Λ, A'.T.eps (A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) = A.T.eps (A.φ v) := by
  intro E _ _ _ r X _ x x' A A' γ hγ v hv
  obtain ⟨a, ha⟩ := B_int X hv (smul_mem X.toData A.w0 hv)
  obtain ⟨b, hb⟩ := B_int X hv (smul_mem X.toData A'.w0 hv)
  have hb' : B X.toData ((γ : Matrix (Fin r) (Fin r) E).mulVec v)
      ((A'.w0 : E) • (γ : Matrix (Fin r) (Fin r) E).mulVec v) = b := by
    rw [← hb, B, B, ← Matrix.mulVec_smul, hγ.1]
  rw [eps_val A hv ha, eps_val A' ((hγ.2 v).1 hv) hb']
  obtain ⟨k, hk⟩ := parity_eq X (par_of_torusAt X A') (par_of_torusAt X A) hv
  rw [ha, hb] at hk
  have hk' : b - a = 2 * k := by exact_mod_cast hk
  rw [(Int.negOnePow_eq_iff b a).2 ⟨k, by omega⟩]
end GlobalTheory
