-- Prove2me | solution 1 for GlobalTheory.exists_sum_tmul_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:53.658692+00:00
-- url     : https://prove2.me/submissions/1e7a9dd6-71f6-4c69-b787-7d47dad60776

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (t : TensorProduct F M N) :
    ∃ (m : ℕ) (e : Fin m → M) (c : Fin m → N), LinearIndependent F e ∧ t = ∑ k, TensorProduct.tmul F (e k) (c k) := by
  classical
  let B := Module.Basis.ofVectorSpace F M
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B t
  let σ := c.support.equivFin.symm
  refine ⟨_, fun k => B (σ k), fun k => c (σ k), ?_, ?_⟩
  · exact B.linearIndependent.comp (fun k => (σ k).val) (Subtype.val_injective.comp σ.injective)
  · rw [← hc, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp σ (fun i => TensorProduct.tmul F (B i) (c i))).symm
end GlobalTheory
