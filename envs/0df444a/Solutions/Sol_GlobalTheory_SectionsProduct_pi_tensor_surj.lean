-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.pi_tensor_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:58.581973+00:00
-- url     : https://prove2.me/submissions/e45723fc-0f31-46fe-bf39-0c23abb39dbb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
variable {F : Type} [CommRing F]
variable {P Q : Type} [Finite P] [Finite Q] {A : P → Type} {B : Q → Type}
  [∀ p, AddCommGroup (A p)] [∀ p, Module F (A p)] [∀ p, AddCommGroup (B p)] [∀ p, Module F (B p)]
namespace GlobalTheory.SectionsProduct
theorem _root_.solution (c : ∀ p q, A p ⊗[F] B q) : ∃ t : (∀ p, A p) ⊗[F] (∀ q, B q),
    ∀ p q, TensorProduct.map (LinearMap.proj p) (LinearMap.proj q) t = c p q := by
  classical
  cases nonempty_fintype P
  cases nonempty_fintype Q
  refine ⟨∑ p, ∑ q, TensorProduct.map (LinearMap.single F A p) (LinearMap.single F B q) (c p q), fun p q => ?_⟩
  simp only [map_sum, TensorProduct.map_map]
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [LinearMap.proj_comp_single_same]
  · intro q' _ hq
    rw [LinearMap.proj_comp_single_ne F B q q' hq.symm, TensorProduct.map_zero_right, LinearMap.zero_apply]
  · simp
  · intro p' _ hp
    simp [LinearMap.proj_comp_single_ne F A p p' hp.symm]
  · simp
end GlobalTheory.SectionsProduct
