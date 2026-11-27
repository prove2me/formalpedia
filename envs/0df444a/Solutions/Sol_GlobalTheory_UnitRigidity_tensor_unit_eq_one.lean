-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.tensor_unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:27.653482+00:00
-- url     : https://prove2.me/submissions/ab7b0dcb-18b1-4eda-b798-67e266cf4e77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_UnitRigidity_coeff_mem
import Theorems.Thm_GlobalTheory_UnitRigidity_mem_range_of_forall_valuationSubring
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.UnitRigidity
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {K A B : Type} [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A]
    [CommRing B] [Algebra K B]
    (hB : ∀ (F : Type) [Field F] [Algebra K F], NoZeroDivisors (F ⊗[K] B))
    (φ : A →ₐ[K] K) (ψ : B →ₐ[K] K) (u : A ⊗[K] B) (hu : IsUnit u)
    (h1 : Algebra.TensorProduct.lift (AlgHom.id K A) ((Algebra.ofId K A).comp ψ)
      (fun _ _ => Commute.all _ _) u = 1)
    (h2 : Algebra.TensorProduct.lift ((Algebra.ofId K B).comp φ) (AlgHom.id K B)
      (fun _ _ => Commute.all _ _) u = 1) : u = 1 := by
  classical
  let L := FractionRing A
  let b := Module.Basis.ofVectorSpace K B
  set j := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A L) (AlgHom.id K B) with hj
  have hrepr : ∀ z i, (Algebra.TensorProduct.basis L b).repr (j z) i =
      algebraMap A L ((Algebra.TensorProduct.basis A b).repr z i) := by
    intro z i
    induction z with
    | zero => simp
    | tmul x y => simp [hj, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
    | add x y hx hy => simp [hx, hy]
  have hev : ∀ z, Algebra.TensorProduct.lift (AlgHom.id K L) ((Algebra.ofId K L).comp ψ)
      (fun _ _ => Commute.all _ _) (j z) = algebraMap A L
        (Algebra.TensorProduct.lift (AlgHom.id K A) ((Algebra.ofId K A).comp ψ)
          (fun _ _ => Commute.all _ _) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [hj, Algebra.ofId_apply, ← IsScalarTower.algebraMap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hco : ∀ i, ∃ k : K, (Algebra.TensorProduct.basis A b).repr u i = algebraMap K A k := by
    intro i
    obtain ⟨k, hk⟩ := mem_range_of_forall_valuationSubring (K := K)
      ((Algebra.TensorProduct.basis L b).repr (j u) i) (fun O hO => by
        letI : Algebra K O := ((algebraMap K L).codRestrict O.toSubring hO).toAlgebra
        haveI : IsScalarTower K O L := IsScalarTower.of_algebraMap_eq fun _ => rfl
        haveI := hB (IsLocalRing.ResidueField O)
        exact coeff_mem b O ψ (j u) (hu.map j) (by rw [hev, h1, map_one]) i)
    refine ⟨k, IsFractionRing.injective A L ?_⟩
    rw [← hrepr, ← hk, ← IsScalarTower.algebraMap_apply]
  choose k hk using hco
  have hu' : u = 1 ⊗ₜ ∑ i ∈ ((Algebra.TensorProduct.basis A b).repr u).support, k i • b i := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).linearCombination_repr u,
      Finsupp.linearCombination_apply, Finsupp.sum]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk, Algebra.TensorProduct.basis_apply, algebraMap_smul, TensorProduct.tmul_smul]
  rw [hu'] at h2
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.id_apply] at h2
  rw [hu', h2, Algebra.TensorProduct.one_def]
end GlobalTheory.UnitRigidity
