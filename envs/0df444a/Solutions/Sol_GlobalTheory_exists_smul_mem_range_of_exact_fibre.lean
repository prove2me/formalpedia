-- Prove2me | solution 1 for GlobalTheory.exists_smul_mem_range_of_exact_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:04.245711+00:00
-- url     : https://prove2.me/submissions/8d3128d6-216e-4a7b-8384-fa10a8a90774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulHomologyEqZeroOfAcyclicFibre
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_exact_lTensor_iff_residueField
import Theorems.Thm_GlobalTheory_exact_of_homotopy
import Theorems.Thm_GlobalTheory_exists_homotopy_of_forall_exact_residueField
import Theorems.Thm_GlobalTheory_forall_exact_residueField_of_isLocalRing
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [Module.Finite R B] [Module.Projective R B] [Module.Finite R C] [Module.Projective R C]
    (K : Type*) [Field K] [Algebra R K] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor K) (g.lTensor K)) (b : B) (hb : g b = 0) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧ r • b ∈ LinearMap.range f := by
  let P : Ideal R := RingHom.ker (algebraMap R K)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  let O := Localization.AtPrime P
  have h1 := (exact_lTensor_iff_residueField P K rfl f g).1 h
  have h2 : Exact (AlgebraTensorModule.lTensor O P.ResidueField f)
      (AlgebraTensorModule.lTensor O P.ResidueField g) ↔
      Exact ((f.baseChange O).lTensor P.ResidueField) ((g.baseChange O).lTensor P.ResidueField) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField C)
      (by ext; simp) (by ext; simp)
  have h3 := h2.1 h1
  have hfg' : g.baseChange O ∘ₗ f.baseChange O = 0 := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero]
  obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField hfg'
    (fun m _ => forall_exact_residueField_of_isLocalRing h3 m)
  have h4 := exact_of_homotopy hfg' hst
  obtain ⟨x, hx⟩ := (h4 ((1 : O) ⊗ₜ[R] b)).1 (by simp [hb])
  obtain ⟨⟨a, u⟩, ha⟩ := IsLocalizedModule.surj P.primeCompl (TensorProduct.mk R O A 1) x
  have h5 : TensorProduct.mk R O B 1 ((u : R) • b) = TensorProduct.mk R O B 1 (f a) := by
    have := congrArg (f.lTensor O) ha
    rw [Submonoid.smul_def, map_smul] at this
    have hx' : f.lTensor O x = (1 : O) ⊗ₜ[R] b := hx
    rw [hx'] at this
    simpa using this
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) h5
  refine ⟨(v * u : P.primeCompl), (v * u).2, (v : R) • a, ?_⟩
  rw [map_smul, Submonoid.coe_mul, mul_smul]
  exact hv.symm
end GlobalTheory
