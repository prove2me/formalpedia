-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.absSpace_eq_bot_of_norm_charpoly_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:06:34.446254+00:00
-- url     : https://prove2.me/submissions/91261043-5941-45d0-9719-85c4603009ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TemperedOfLpDimLeOneOfUnitEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {r : ℝ} (hr : r ≠ 1) :
    absSpace f r = ⊥ := by
  refine eq_bot_iff.mpr (iSup₂_le fun α hα => ?_)
  by_contra hne
  have hev : f.HasEigenvalue α := Module.End.hasEigenvalue_iff.mpr fun h => hne (h ▸ le_refl _)
  have hroot : (minpoly ℂ f).IsRoot α := Module.End.hasEigenvalue_iff_isRoot.mp hev
  have hc : α ∈ f.charpoly.roots := by
    rw [mem_roots (LinearMap.charpoly_monic f).ne_zero, ← Polynomial.dvd_iff_isRoot]
    exact (Polynomial.dvd_iff_isRoot.mpr hroot).trans (LinearMap.minpoly_dvd_charpoly f)
  exact hr (hα ▸ hf α hc)
end GlobalTheory.WeilDeligne
