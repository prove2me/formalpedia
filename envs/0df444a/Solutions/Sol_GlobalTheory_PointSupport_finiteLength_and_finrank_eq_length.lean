-- Prove2me | solution 1 for GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:25.976115+00:00
-- url     : https://prove2.me/submissions/b246ab1c-b7c5-4da7-bc44-b1637dbe6b92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_GlobalTheory_PointSupport_exists_algHom_ker_eq
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_IsGradedMap_id
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
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
open TensorProduct
open GlobalTheory GlobalTheory.PointSupport
open TensorProduct
open TensorProduct
namespace GlobalTheory.PointSupport
namespace _root_.GlobalTheory.PointSupport
theorem _root_.solution :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
      [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
      [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)]
      (H : Type) [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
      [Module.Finite R H],
      (∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) →
      IsFiniteLength O (O ⊗[R] H) ∧ Module.Finite K H ∧
        (Module.finrank K H : ℕ∞) = Module.length O (O ⊗[R] H) := by
  intro K _ _ R _ _ _ χ₀ O _ _ _ _ H _ _ _ _ _ hsupp
  classical
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hχ₀ : Function.Surjective χ₀ := fun k => ⟨algebraMap K R k, χ₀.commutes k⟩
  haveI hP : (RingHom.ker χ₀).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ₀

  have hmax : ∀ M : Ideal R, M.IsMaximal → Module.annihilator R H ≤ M → M = RingHom.ker χ₀ := by
    intro M hM hle
    obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq K R M
    by_cases h : χ = χ₀
    · rw [← hχ, h]
    · obtain ⟨r, hr, hrz⟩ := hsupp χ h
      have hrM : r ∈ M := hle (Module.mem_annihilator.mpr hrz)
      rw [← hχ] at hrM
      exact absurd (RingHom.mem_ker.mp hrM) hr

  have hprime : ∀ Q : Ideal R, Q.IsPrime → Module.annihilator R H ≤ Q → Q = RingHom.ker χ₀ := by
    intro Q hQ hle
    rw [← IsJacobsonRing.out' Q hQ.isRadical]
    apply le_antisymm
    · obtain ⟨J, hJ, hQJ⟩ := Ideal.exists_le_maximal Q hQ.ne_top
      rw [← hmax J hJ (hle.trans hQJ)]
      exact sInf_le ⟨hQJ, hJ⟩
    · exact le_sInf fun J hJ => (hmax J hJ.2 (hle.trans hJ.1)).ge

  letI : Module (R ⧸ Module.annihilator R H) H := Module.quotientAnnihilator
  have hmk : ∀ (r : R) (z : H), (Ideal.Quotient.mk (Module.annihilator R H) r) • z = r • z :=
    fun _ _ => rfl
  haveI : IsScalarTower R (R ⧸ Module.annihilator R H) H :=
    ⟨fun r a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, hmk, hmk, mul_smul]⟩
  haveI : IsScalarTower K (R ⧸ Module.annihilator R H) H :=
    ⟨fun k a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmk, hmk, ← Algebra.smul_def,
        smul_assoc]⟩
  haveI : Module.Finite (R ⧸ Module.annihilator R H) H :=
    Module.Finite.of_restrictScalars_finite R _ H
  have hprimeq : ∀ Q : Ideal (R ⧸ Module.annihilator R H), Q.IsPrime →
      Q.comap (Ideal.Quotient.mk _) = RingHom.ker χ₀ := fun Q hQ =>
    hprime _ (Ideal.comap_isPrime _ Q) fun r hr => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact Q.zero_mem
  haveI : Ring.KrullDimLE 0 (R ⧸ Module.annihilator R H) := Ring.KrullDimLE.mk₀ fun Q hQ => by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hprimeq Q hQ]
    refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, ← hprimeq Q hQ]
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Q.zero_mem
  haveI : Module.Finite K (R ⧸ Module.annihilator R H) :=
    (Module.finite_iff_krullDimLE_zero K _).mpr inferInstance
  haveI hfin : Module.Finite K H := Module.Finite.trans (R ⧸ Module.annihilator R H) H

  have hunit : ∀ s : (RingHom.ker χ₀).primeCompl, IsUnit (algebraMap R (Module.End R H) s) := by
    intro s
    have ha : IsUnit (Ideal.Quotient.mk (Module.annihilator R H) (s : R)) := by
      by_contra h
      obtain ⟨I, hI, hsI⟩ := exists_max_ideal_of_mem_nonunits h
      have hsI' : (s : R) ∈ Ideal.comap (Ideal.Quotient.mk (Module.annihilator R H)) I := hsI
      rw [hprimeq I hI.isPrime] at hsI'
      exact s.2 hsI'
    rw [Module.End.isUnit_iff]
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    refine ⟨fun x y hxy => ?_, fun z => ⟨b • z, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hmk, ← hmk] at hxy
      exact ha.smul_left_cancel.mp hxy
    · rw [Module.algebraMap_end_apply, ← hmk, smul_smul, hb, one_smul]
  haveI : IsLocalizedModule (RingHom.ker χ₀).primeCompl (LinearMap.id : H →ₗ[R] H) :=
    IsLocalizedModule.mk hunit (fun y => ⟨⟨y, 1⟩, one_smul _ _⟩)
      (fun {x₁ x₂} h => ⟨1, by simpa using h⟩)
  let e : H ≃ₗ[R] O ⊗[R] H := IsLocalizedModule.linearEquiv (RingHom.ker χ₀).primeCompl
    LinearMap.id (TensorProduct.mk R O H 1)

  letI : Algebra K O := ((algebraMap R O).comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eK : H ≃ₗ[K] O ⊗[R] H := e.restrictScalars K
  haveI : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O (RingHom.ker χ₀)
  haveI : IsLocalHom (algebraMap K O) := ⟨fun k hk => by
    by_cases h0 : k = 0
    · rw [h0, map_zero] at hk
      exact absurd hk not_isUnit_zero
    · exact isUnit_iff_ne_zero.mpr h0⟩
  haveI : Module.Finite K (O ⊗[R] H) := Module.Finite.equiv eK

  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)) := by
    have hR : ∀ r : R, IsLocalRing.residue O (algebraMap R O r) ∈
        (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).fieldRange := by
      intro r
      refine ⟨IsLocalRing.residue K (χ₀ r), ?_⟩
      have hmem : algebraMap R O (r - algebraMap K R (χ₀ r)) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O (RingHom.ker χ₀), RingHom.mem_ker,
          map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at hmem
      rw [hmem]
      exact IsLocalRing.ResidueField.map_residue (algebraMap K O) (χ₀ r)
    intro x
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker χ₀).primeCompl o
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul]
    have hs : IsLocalRing.residue O (IsLocalization.mk' O (1 : R) s) =
        (IsLocalRing.residue O (algebraMap R O s))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]
    rw [hs]
    exact Subfield.mul_mem _ (hR r) (Subfield.inv_mem _ (hR s))
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O) = 1 := by
    let f := LinearEquiv.ofBijective
      (Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O))
      ⟨(algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).injective, hsurj⟩
    rw [← f.length_eq, Module.length_eq_one_iff]
    infer_instance
  have hlen := IsLocalRing.length_restrictScalars K O (O ⊗[R] H)
  rw [hres, mul_one, Module.length_eq_finrank K] at hlen
  have hfr : Module.finrank K H = Module.finrank K (O ⊗[R] H) := eK.finrank_eq
  refine ⟨?_, hfin, ?_⟩
  · rw [← Module.length_ne_top_iff, ← hlen]
    exact ENat.coe_ne_top _
  · rw [hfr]
    exact hlen
end _root_.GlobalTheory.PointSupport
end GlobalTheory.PointSupport
