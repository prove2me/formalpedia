-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:26:39.677512+00:00
-- url     : https://prove2.me/submissions/3bd1e515-353b-46f9-ae21-b697890ad7fe

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialSignRuleQuadratic
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeSplitCasimir_jW_mul_transpose
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeSplitCasimir_anticomm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeSplitCasimir
namespace GlobalTheory.CompanionTheory.WedgeSplitCasimir
theorem _root_.solution : StdD → (∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0) → WedgeQ := by
  intro hS hW k r m
  ext ⟨J, s⟩ ⟨J', s'⟩
  have h1 : qMat (wedge k r m) (vr k r false) (J, s) (J', s') =
      (wedge k r m).dC (Matrix.single s' s 1) J J' := by
    simp only [qMat, Matrix.sum_apply, Matrix.kroneckerMap_apply, (hS k r _).1]
    rw [Finset.sum_eq_single s', Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [ha]
    · simp
  rw [h1, hW, Matrix.sub_apply, jW_mul_transpose, anticomm, Matrix.one_apply]
  congr 1
  simp only [Prod.mk.injEq, Subtype.ext_iff]
end GlobalTheory.CompanionTheory.WedgeSplitCasimir
