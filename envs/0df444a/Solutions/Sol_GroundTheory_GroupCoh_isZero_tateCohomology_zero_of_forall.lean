-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_zero_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:49.22006+00:00
-- url     : https://prove2.me/submissions/9c548953-f56f-4925-b0b6-f38d047b213d

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
    (h : ∀ m : M, (∀ g : G, M.ρ g m = m) → ∃ y : M, M.ρ.norm y = m) :
    IsZero (tateCohomology M 0) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousCochains M).X 0, (inhomogeneousCochains M).d 0 1 x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 0, M.tateNorm x₁ = x₂
  intro x₂ hd
  have hinv : ∀ g : G, M.ρ g ((cochainsIso₀ M).hom x₂) = (cochainsIso₀ M).hom x₂ := by
    intro g
    have key : (d₀₁ M).hom ((cochainsIso₀ M).hom.hom x₂) =
        (cochainsIso₁ M).hom.hom (((inhomogeneousCochains M).d 0 1).hom x₂) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, comp_d₀₁_eq]; rfl
    rw [show ((inhomogeneousCochains M).d 0 1).hom x₂ = 0 from hd, map_zero] at key
    have := congr_fun key g
    exact sub_eq_zero.mp this
  obtain ⟨y, hy⟩ := h _ hinv
  refine ⟨(chainsIso₀ M).inv y, ?_⟩
  simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change (cochainsIso₀ M).inv (M.ρ.norm y) = x₂
  rw [hy, Iso.hom_inv_id_apply]
end GroundTheory.GroupCoh
