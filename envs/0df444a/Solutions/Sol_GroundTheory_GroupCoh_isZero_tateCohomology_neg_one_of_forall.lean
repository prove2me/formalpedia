-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_neg_one_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:47.633875+00:00
-- url     : https://prove2.me/submissions/24d6979f-4833-4291-8731-1ad396def1aa

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} k G)
    (h : ∀ m : M, M.ρ.norm m = 0 → ∃ z : G →₀ M, d₁₀ M z = m) :
    IsZero (tateCohomology M (-1)) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousChains M).X 0, M.tateNorm x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 1, (inhomogeneousChains M).d 1 0 x₁ = x₂
  intro x₂ hx
  have hn : M.ρ.norm ((chainsIso₀ M).hom x₂) = 0 := by
    have := congr_arg (fun x => (cochainsIso₀ M).hom x) hx
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, map_zero] at this
    exact this
  obtain ⟨z, hz⟩ := h _ hn
  refine ⟨(chainsIso₁ M).inv z, ?_⟩
  rw [eq_d₁₀_comp_inv_apply, hz, Iso.hom_inv_id_apply]
end GroundTheory.GroupCoh
