-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSimple.psi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:33.864582+00:00
-- url     : https://prove2.me/submissions/f6f128b3-5842-465e-8b1e-bd1bd48be2d0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_cf_apply

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
theorem _root_.solution (ρ : Representation ℂ (∀ c, L c) W) (v : W) (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v x = ∑ g : ∀ c, L c, (∏ c, (x c).coeff (g c)) • ρ g v := by
  simp [psi, MultilinearMap.sum_apply, cf_apply]
end GlobalTheory.CompanionTheory.ProdSimple
