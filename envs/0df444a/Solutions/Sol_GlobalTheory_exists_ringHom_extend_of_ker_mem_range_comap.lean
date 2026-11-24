-- Prove2me | solution 1 for GlobalTheory.exists_ringHom_extend_of_ker_mem_range_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:27.820355+00:00
-- url     : https://prove2.me/submissions/34259b66-275f-45ae-a37e-57e4f1fd55c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtend
import Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_finiteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {B A L : Type*} [CommRing B] [CommRing A]
    [Algebra B A] [Algebra.FiniteType B A] [Field L] [IsAlgClosed L] (φ : B →+* L)
    (h : (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A))) :
    ∃ ψ : A →+* L, ψ.comp (algebraMap B A) = φ := by
  obtain ⟨P, hP⟩ := h
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hPp : RingHom.ker φ = P.asIdeal.comap (algebraMap B A) := by
    have := congrArg PrimeSpectrum.asIdeal hP
    simpa using this.symm

  let σ : (RingHom.ker φ).ResidueField →+* L :=
    Ideal.ResidueField.lift (RingHom.ker φ) φ le_rfl (fun x hx => by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact isUnit_iff_ne_zero.mpr fun h0 => hx (RingHom.mem_ker.mpr h0))

  let g : (RingHom.ker φ).ResidueField →ₐ[B] P.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ (RingHom.ker φ) P.asIdeal (Algebra.ofId B A) hPp
  let F : (RingHom.ker φ).ResidueField ⊗[B] A →ₐ[B] P.asIdeal.ResidueField :=
    Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom B A _) (fun _ _ => Commute.all _ _)
  have : Nontrivial ((RingHom.ker φ).ResidueField ⊗[B] A) := F.toRingHom.domain_nontrivial
  obtain ⟨χ, hχ⟩ := exists_ringHom_extend_of_finiteType (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A) L σ
  refine ⟨χ.comp (Algebra.TensorProduct.includeRight (R := B)
    (A := (RingHom.ker φ).ResidueField) (B := A)).toRingHom, RingHom.ext fun b => ?_⟩
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply B (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A), hχ]
  exact Ideal.ResidueField.lift_algebraMap _ _ _ _ _
end GlobalTheory
