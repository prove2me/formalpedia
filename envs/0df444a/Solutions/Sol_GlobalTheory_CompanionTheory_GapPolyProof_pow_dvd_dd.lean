-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.pow_dvd_dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:53.244942+00:00
-- url     : https://prove2.me/submissions/a40bf15d-ac25-4e89-a01a-f87894bbbad1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dvd_minpoly_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.CompanionTheory.GapPolyProof
theorem _root_.solution [FiniteDimensional ℂ E] (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1)
    (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x)
    (ψ : E →ₗ[ℂ] ℂ) (z : ℂ) (hz : ¬ T.HasEigenvalue z) :
    (X - C z) ^ (S.count z) ∣ dd n v ψ := by
  have hG : (S.map (fun t => X - C t)).prod.roots = S := roots_multiset_prod_X_sub_C S
  have hcount : S.count z = rootMultiplicity z (S.map (fun t => X - C t)).prod := by
    rw [← count_roots, hG]
  have h1 : (X - C z) ^ (S.count z) ∣ (S.map (fun t => X - C t)).prod := by
    rw [hcount]; exact pow_rootMultiplicity_dvd _ _
  have h2 := h1.trans (dvd_minpoly_mul S n hS T v x h0 hn hrec ψ)
  have hcop : IsCoprime (X - C z) (minpoly ℂ T) := by
    rw [(irreducible_X_sub_C z).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact fun h => hz (Module.End.hasEigenvalue_of_isRoot h)
  exact (hcop.pow_left).dvd_of_dvd_mul_left h2
end GlobalTheory.CompanionTheory.GapPolyProof
