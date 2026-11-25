-- Prove2me | solution 1 for GroundTheory.LocalField.cycHerbrand_eq_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:27.883292+00:00
-- url     : https://prove2.me/submissions/fbebbe14-0e9f-4767-a337-617f320dd992

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_toAdditive_cycSubOne
import Theorems.Thm_GroundTheory_LocalField_toAdditive_cycNorm
import Theorems.Thm_GroundTheory_Global_cycNorm_cycSubOne
import Theorems.Thm_GroundTheory_Global_cycSubOne_cycNorm
import Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_iff_of_injective_of_finite
import Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_of_injective_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
section
namespace GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
section Injective
variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]
private theorem range_toAdditive (i : M →* N) :
    (MonoidHom.toAdditive i).range = i.range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨x.toMul, by rw [← hx]; rfl⟩,
    fun ⟨x, hx⟩ => ⟨Additive.ofMul x, Additive.toMul.injective hx⟩⟩
end Injective
end GroundTheory.LocalField
end

set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]
namespace GroundTheory.LocalField
theorem _root_.solution (i : M →* N) (hinj : Function.Injective i)
    (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) [i.range.FiniteIndex] (τ : G) :
    (HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) τ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G N) τ)
        (cycNorm (Representation.ofMulDistribMulAction G N))) ∧
    cycHerbrand (Representation.ofMulDistribMulAction G M) τ =
      cycHerbrand (Representation.ofMulDistribMulAction G N) τ := by
  have hfi : (MonoidHom.toAdditive i).range.FiniteIndex := by
    constructor
    rw [range_toAdditive, Subgroup.index_toAddSubgroup]
    exact Subgroup.FiniteIndex.index_ne_zero
  have : Finite (Additive N ⧸ (MonoidHom.toAdditive i).range) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  have hinj' : Function.Injective (MonoidHom.toAdditive i) := hinj
  exact ⟨hasHerbrandQuotient_iff_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ),
    herbrandQuotient_eq_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ)⟩
end GroundTheory.LocalField
