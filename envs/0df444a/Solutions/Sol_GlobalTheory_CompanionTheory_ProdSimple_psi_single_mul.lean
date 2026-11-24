-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSimple.psi_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:39.404824+00:00
-- url     : https://prove2.me/submissions/139644de-7b65-4be5-b92c-0501896cf7ed

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_psi_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple
variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.ProdSimple
theorem _root_.solution (ρ : Representation ℂ (∀ c, L c) W) (v : W) (g : ∀ c, L c)
    (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v (fun c => MonoidAlgebra.single (g c) (1 : ℂ) * x c) = ρ g (psi ρ v x) := by
  rw [psi_apply, psi_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => ?_
  simp only [MonoidAlgebra.coeff_single_mul_apply, one_mul, map_smul, Equiv.coe_mulLeft,
    Pi.mul_apply, Pi.inv_apply]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
end GlobalTheory.CompanionTheory.ProdSimple
