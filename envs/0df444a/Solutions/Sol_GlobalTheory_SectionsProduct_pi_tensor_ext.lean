-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.pi_tensor_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:11.50038+00:00
-- url     : https://prove2.me/submissions/60e9457a-46a1-419d-b9f6-68dbe4ce2c0f

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
theorem _root_.solution (t : (∀ p, A p) ⊗[F] (∀ q, B q))
    (h : ∀ p q, TensorProduct.map (LinearMap.proj p) (LinearMap.proj q) t = 0) : t = 0 := by
  classical
  cases nonempty_fintype P
  cases nonempty_fintype Q
  have : ∀ t : (∀ p, A p) ⊗[F] (∀ q, B q), t = ∑ p, ∑ q, TensorProduct.map (LinearMap.single F A p) (LinearMap.single F B q)
      (TensorProduct.map (LinearMap.proj p) (LinearMap.proj q) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.proj_apply, LinearMap.single_apply, ← TensorProduct.tmul_sum,
        ← TensorProduct.sum_tmul, Finset.univ_sum_single]
    | add x y hx hy =>
      simp only [map_add, Finset.sum_add_distrib]
      rw [← hx, ← hy]
  rw [this t]
  simp [h]
end GlobalTheory.SectionsProduct
