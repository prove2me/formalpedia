-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Formal.IsoThick.exists_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:28:44.174884+00:00
-- url     : https://prove2.me/submissions/edb24b67-411f-4ce9-ac44-7a85473ad101

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick
open TensorProduct
namespace GlobalTheory.CompanionTheory.Formal.IsoThick
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (y : M ⊗[R] (R ⧸ K)) : ∃ m : M, y = m ⊗ₜ[R] (1 : R ⧸ K) := by
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.tensorQuotEquivQuotSMul M K y)
  refine ⟨m, ?_⟩
  rw [← TensorProduct.tensorQuotEquivQuotSMul_symm_mk, hm, LinearEquiv.symm_apply_apply]
end GlobalTheory.CompanionTheory.Formal.IsoThick
