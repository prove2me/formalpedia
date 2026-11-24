-- Prove2me | solution 1 for GlobalTheory.FlatFibreInjective.one_tmul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:33:25.784938+00:00
-- url     : https://prove2.me/submissions/579491bb-ba75-4e56-bbc2-56bbde7a05a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Theorems.Thm_GlobalTheory_FlatFibreInjective_one_tmul_ne_zero_of_domain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatFibreInjective
open TensorProduct
namespace GlobalTheory.FlatFibreInjective
theorem _root_.solution {R₀ P k : Type} [CommRing R₀] [AddCommGroup P] [Module R₀ P]
    [Field k] [Algebra R₀ k] (p : Ideal R₀) (hk : ∀ a, algebraMap R₀ k a = 0 ↔ a ∈ p)
    (hP : Module.IsTorsionBySet R₀ P p) (y : P) (hy : ∀ a : R₀, a • y = 0 → a ∈ p) :
    (1 : k) ⊗ₜ[R₀] y ≠ 0 := by
  intro h
  have hker : p = RingHom.ker (algebraMap R₀ k) := by
    ext a; simp [RingHom.mem_ker, hk]
  haveI : p.IsPrime := hker ▸ RingHom.ker_isPrime _
  letI : Module (R₀ ⧸ p) P := hP.module
  haveI : IsScalarTower R₀ (R₀ ⧸ p) P := hP.isScalarTower
  letI : Algebra (R₀ ⧸ p) k :=
    (Ideal.Quotient.lift p (algebraMap R₀ k) (fun a ha => (hk a).2 ha)).toAlgebra
  haveI : IsScalarTower R₀ (R₀ ⧸ p) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap (R₀ ⧸ p) k) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hk a).1 ha)
  refine one_tmul_ne_zero_of_domain (A := R₀ ⧸ p) hinj y ?_ ?_
  · intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hy a ha)
  · have := congrArg (TensorProduct.mapOfCompatibleSMul (R₀ ⧸ p) R₀ R₀ k P) h
    rwa [TensorProduct.mapOfCompatibleSMul_tmul, map_zero] at this
end GlobalTheory.FlatFibreInjective
