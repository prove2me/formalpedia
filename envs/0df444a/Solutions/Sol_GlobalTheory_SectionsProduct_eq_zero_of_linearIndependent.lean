-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.eq_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:39:01.852038+00:00
-- url     : https://prove2.me/submissions/9bedeb9b-2e6d-4d6c-b0ee-1593a8dc78a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_pi_tensor_ext
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
theorem _root_.solution (hF : IsField F) {C : Type} [AddCommGroup C] [Module F C] {n : ℕ} (a : Fin n → ∀ p, A p)
    (ha : LinearIndependent F a) (b : Fin n → C) (h : ∀ p, ∑ i, a i p ⊗ₜ[F] b i = 0) (k : Fin n) : b k = 0 := by
  letI := hF.toField
  have e : ∑ i, a i ⊗ₜ[F] (fun _ : Unit => b i) = 0 :=
    pi_tensor_ext (B := fun _ : Unit => C) _ fun p q => by simpa [map_sum] using h p
  obtain ⟨l, hl⟩ := (Finsupp.linearCombination F a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 ha)
  have hl' : ∀ i, l (a i) = Finsupp.single i 1 := fun i => by
    simpa using LinearMap.congr_fun hl (Finsupp.single i 1)
  have := congrArg (fun t => TensorProduct.lid F (Unit → C) ((Finsupp.lapply k ∘ₗ l).rTensor (Unit → C) t) ()) e
  simpa [map_sum, hl', Finsupp.single_apply, ite_apply] using this
end GlobalTheory.SectionsProduct
