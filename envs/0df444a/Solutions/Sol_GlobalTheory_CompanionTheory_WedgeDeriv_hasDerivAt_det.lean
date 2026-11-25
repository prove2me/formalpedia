-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeDeriv.hasDerivAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:25.991975+00:00
-- url     : https://prove2.me/submissions/8b60db27-f924-4126-bfd8-e80252ad8e1b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeDeriv
namespace GlobalTheory.CompanionTheory.WedgeDeriv
theorem _root_.solution {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (A' : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) (∑ j, ∑ i, adjugate (A 0) j i * A' i j) 0 := by
  have h1 : HasDerivAt (fun t => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ j, (∏ i ∈ univ.erase j, A 0 (σ i) i) • A' (σ j) j) 0 := by
    refine HasDerivAt.fun_sum fun σ _ => HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_finset_prod (f := fun i t => A t (σ i) i) fun i _ => h _ _
  have h2 : ∀ j, ∑ i, adjugate (A 0) j i * A' i j = ((A 0).updateCol j fun i => A' i j).det := by
    intro j
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  simp only [h2, Matrix.det_apply']
  convert h1 using 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul _ _ (mem_univ j), updateCol_self, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun i hi => updateCol_ne (ne_of_mem_erase hi)
end GlobalTheory.CompanionTheory.WedgeDeriv
