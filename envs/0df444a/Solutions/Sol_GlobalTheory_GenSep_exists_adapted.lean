-- Prove2me | solution 1 for GlobalTheory.GenSep.exists_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:19.186579+00:00
-- url     : https://prove2.me/submissions/4d46311b-2bbd-4e66-9745-787667b276d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_nonneg_of_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
namespace GlobalTheory.GenSep
theorem _root_.solution (x : Fin N → Ω) (hx : ∃ k, x k ≠ 0) (v : AddValuation Ω (WithTop ℤ)) :
    ∃ j0, x j0 ≠ 0 ∧ ∀ k, 0 ≤ v (x k / x j0) := by
  obtain ⟨k0, hk0⟩ := hx
  haveI : Nonempty (Fin N) := ⟨k0⟩
  obtain ⟨j0, -, hj⟩ := Finset.univ.exists_min_image (fun k => v (x k)) Finset.univ_nonempty
  have hne : x j0 ≠ 0 := by
    intro h
    have := hj k0 (Finset.mem_univ _)
    rw [h, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hk0 this
  refine ⟨j0, hne, fun k => ValuationResidueLemmas.wt_nonneg_of_add (b := v (x j0)) (c := v (x k)) ?_ ?_ (hj k (Finset.mem_univ _))⟩
  · rw [Ne, AddValuation.top_iff]; exact hne
  · rw [← AddValuation.map_mul, div_mul_cancel₀ _ hne]
end GlobalTheory.GenSep
