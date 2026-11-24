-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.exists_smul_mem_range_of_unique_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:52.99789+00:00
-- url     : https://prove2.me/submissions/bf957c19-df39-44de-9965-3c5c665e4057

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRetractionNearOfUniquePoint
import Theorems.Thm_GlobalTheory_ZM_NearBuild_FibData_comp
import Theorems.Thm_GlobalTheory_algebraMap_surjective_of_unramified_of_unique_point
import Theorems.Thm_GlobalTheory_nontrivial_tensor_of_mem_support


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild
namespace GlobalTheory.ZM.NearBuild
theorem _root_.solution (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K)
    (y : B →+* K) (hy : y.comp (algebraMap R B) = x) (hu : ∀ z : B →+* K, z.comp (algebraMap R B) = x → z = y) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b := by
  let _ : Algebra R K := x.toAlgebra
  let yA : B →ₐ[R] K := { y with commutes' := fun r => RingHom.congr_fun hy r }
  let φ : K ⊗[R] B →ₐ[K] K :=
    Algebra.TensorProduct.lift (Algebra.ofId K K) yA (fun _ _ => Commute.all _ _)
  have hall : ∀ ψ : K ⊗[R] B →ₐ[K] K, ∀ (a : K) (b : B), ψ (a ⊗ₜ[R] b) = a * y b := by
    intro ψ a b
    have hz : ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hu
      ext r
      exact ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h1 : ψ ((1 : K) ⊗ₜ[R] b) = y b := by
      have := RingHom.congr_fun hz b
      simpa using this
    have h2 : a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul']
      simp
    rw [h2, map_smul, h1, _root_.smul_eq_mul]
  have huniq : ∀ ψ : K ⊗[R] B →ₐ[K] K, ψ = φ := by
    intro ψ
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [hall ψ, hall φ]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  have hsurj := algebraMap_surjective_of_unramified_of_unique_point K (K ⊗[R] B) φ huniq
  set N : Submodule R B := LinearMap.range (Algebra.linearMap R B) with hN
  have hone : N.mkQ (1 : B) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩
  have hzero : ∀ t : K ⊗[R] (B ⧸ N), t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul a c =>
      obtain ⟨b, rfl⟩ := N.mkQ_surjective c
      obtain ⟨c', hc'⟩ := hsurj (a ⊗ₜ[R] b)
      rw [← LinearMap.lTensor_tmul, ← hc', Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul, hone,
        TensorProduct.tmul_zero]
    | add s t hs ht => rw [hs, ht, add_zero]
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hns : p ∉ Module.support R (B ⧸ N) := by
    intro h
    have hnt := nontrivial_tensor_of_mem_support R (B ⧸ N) K p rfl h
    obtain ⟨s, t, hst⟩ := hnt.exists_pair_ne
    exact hst ((hzero s).trans (hzero t).symm)
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.mp hns
  refine ⟨f, hfp, fun b => ?_⟩
  have hfb : f • N.mkQ b = 0 := Module.mem_annihilator.mp hf _
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfb
  obtain ⟨a, ha⟩ := hfb
  exact ⟨a, by rw [← Algebra.smul_def, ← ha, Algebra.linearMap_apply]⟩
end GlobalTheory.ZM.NearBuild
