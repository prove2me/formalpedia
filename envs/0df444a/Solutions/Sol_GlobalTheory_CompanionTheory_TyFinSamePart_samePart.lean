-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.samePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:51.825811+00:00
-- url     : https://prove2.me/submissions/0aeb2231-53d9-4bc4-b5f1-321021a6c118

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_avg_of_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_ip_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_ip_univ
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_blkGL_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_blkGL_ren
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_ell_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
namespace GlobalTheory.CompanionTheory.TyFinSamePart
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SamePart := by
  intro K _ _ _ ι _ _ s s' b π χ ψ
  classical
  let F : (∀ c, GL {i // b i = c} K) → ℂ := fun q =>
    ∏ c, (χ c (q c)⁻¹ * ψ (π c) (glEquiv K (ren b π c) (q c)))
  have key : ∀ h : (parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)),
      hcFun b χ (h : GL ι K)⁻¹ * hcFun (π ∘ b) ψ h = F (ell b π h) := by
    rintro ⟨g, h1, h2⟩
    simp only [F, Finset.prod_mul_distrib, hcFun]
    congr 1
    · exact Finset.prod_congr rfl fun c _ => by rw [blkGL_inv b c h1]; rfl
    · rw [← Equiv.prod_comp π]
      exact Finset.prod_congr rfl fun c _ => by rw [blkGL_ren b π c h1 h2]; rfl
  rw [ip_coe, Finset.sum_congr rfl (fun h _ => key h),
    avg_of_surjective (ell (K := K) b π) (ell_surjective b π) F]
  simp only [ip_univ, F]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
end GlobalTheory.CompanionTheory.TyFinSamePart
