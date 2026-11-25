-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:37:03.248822+00:00
-- url     : https://prove2.me/submissions/9fbcb1cb-2deb-4445-b553-a50839a2787b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_sum_adj
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_dR_wedge
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_reH_add_imH

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
theorem _root_.solution : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by
  intro k r m a b J J'
  have h := sum_adj _ _ (J.1.orderEmbOfFin J.2).strictMono (J'.1.orderEmbOfFin J'.2).strictMono a b
  rw [Finset.image_orderEmbOfFin_univ, Finset.image_orderEmbOfFin_univ] at h
  rw [← h, FRep.dC, Matrix.add_apply, Matrix.smul_apply, dR_wedge, dR_wedge, smul_eq_mul, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← reH_add_imH k r (Matrix.single a b 1)]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring
end GlobalTheory.CompanionTheory.WedgeDeriv
