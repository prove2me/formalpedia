-- Prove2me | solution 1 for GlobalTheory.CMLattice.eq_top_of_forall_embAll_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:20:23.307328+00:00
-- url     : https://prove2.me/submissions/b1e7e8c2-19c9-490a-bd56-b9300cea4025

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Theorems.Thm_GlobalTheory_CMLattice_exists_real_combination
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMLattice
theorem _root_.solution (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ → ComplexEmbedding.conjugate τ ∉ Ψ) (r : ℕ)
    (S : Submodule ℝ (Ψ → Fin r → ℂ)) (hS : ∀ v, embAll Ψ r v ∈ S) : S = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro y -
  choose c hc using fun a : Fin r => exists_real_combination Ψ h (fun τ => y τ a)
  have : y = ∑ a, ∑ i, c a i • embAll Ψ r (Pi.single a (integralBasis E i)) := by
    ext τ a
    rw [hc a τ]
    simp only [Finset.sum_apply, Pi.smul_apply, embAll_apply]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne' hb]
    · simp
  rw [this]
  exact S.sum_mem fun a _ => S.sum_mem fun i _ => S.smul_mem _ (hS _)
end GlobalTheory.CMLattice
