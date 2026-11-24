-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.exists_sum_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:06.071925+00:00
-- url     : https://prove2.me/submissions/980d3fc7-59ab-449a-a4aa-6ea753c8d2da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_sum_of_ker
import Theorems.Thm_GlobalTheory_SectionsProduct_pi_tensor_ext
import Theorems.Thm_GlobalTheory_SectionsProduct_pi_tensor_surj
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
theorem _root_.solution (hF : IsField F) {A' : P → P → Type} {B' : Q → Q → Type}
    [∀ p p', AddCommGroup (A' p p')] [∀ p p', Module F (A' p p')]
    [∀ p p', AddCommGroup (B' p p')] [∀ p p', Module F (B' p p')]
    (ρ₁ : ∀ p p', A p →ₗ[F] A' p p') (ρ₂ : ∀ p p', A p' →ₗ[F] A' p p')
    (σ₁ : ∀ p p', B p →ₗ[F] B' p p') (σ₂ : ∀ p p', B p' →ₗ[F] B' p p')
    (c : ∀ p q, A p ⊗[F] B q)
    (h₁ : ∀ p p' q, (ρ₁ p p').rTensor (B q) (c p q) = (ρ₂ p p').rTensor (B q) (c p' q))
    (h₂ : ∀ p q q', (σ₁ q q').lTensor (A p) (c p q) = (σ₂ q q').lTensor (A p) (c p q')) :
    ∃ (n : ℕ) (a : Fin n → ∀ p, A p) (b : Fin n → ∀ q, B q), (∀ i p p', ρ₁ p p' (a i p) = ρ₂ p p' (a i p')) ∧
      (∀ i q q', σ₁ q q' (b i q) = σ₂ q q' (b i q')) ∧ ∀ p q, c p q = ∑ i, a i p ⊗ₜ[F] b i q := by
  obtain ⟨t, ht⟩ := pi_tensor_surj c
  let d₁ : (∀ p, A p) →ₗ[F] (∀ x : P × P, A' x.1 x.2) :=
    LinearMap.pi fun x => ρ₁ x.1 x.2 ∘ₗ LinearMap.proj x.1 - ρ₂ x.1 x.2 ∘ₗ LinearMap.proj x.2
  let d₂ : (∀ p, B p) →ₗ[F] (∀ x : Q × Q, B' x.1 x.2) :=
    LinearMap.pi fun x => σ₁ x.1 x.2 ∘ₗ LinearMap.proj x.1 - σ₂ x.1 x.2 ∘ₗ LinearMap.proj x.2
  obtain ⟨n, a, b, ha, hb, e⟩ := exists_sum_of_ker hF d₁ d₂ t (pi_tensor_ext _ fun x q => by
      rw [← sub_eq_zero.2 (h₁ x.1 x.2 q), ← ht, ← ht]
      clear ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [d₁, TensorProduct.sub_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]; abel)
    (pi_tensor_ext _ fun p x => by
      rw [← sub_eq_zero.2 (h₂ p x.1 x.2), ← ht, ← ht]
      clear ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [d₂, TensorProduct.tmul_sub]
      | add x y hx hy => simp only [map_add, hx, hy]; abel)
  refine ⟨n, a, b, fun i p p' => sub_eq_zero.1 (congrFun (ha i) (p, p')),
    fun i p p' => sub_eq_zero.1 (congrFun (hb i) (p, p')), fun p q => ?_⟩
  rw [← ht, e]
  simp [map_sum]
end GlobalTheory.SectionsProduct
