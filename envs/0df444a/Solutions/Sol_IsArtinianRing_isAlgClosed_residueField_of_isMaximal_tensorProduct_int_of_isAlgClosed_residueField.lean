-- Prove2me | solution 1 for IsArtinianRing.isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2377ff39-bf34-58aa-8d13-f93050bb822d

import Mathlib
import Theorems.Thm_IsArtinianRing_finite_of_isLocalRing_of_finite_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] [CharP (ResidueField C) ℓ]
    (O : Type) [CommRing O] [IsLocalRing O] (hℓ : maximalIdeal O = Ideal.span {((ℓ : ℕ) : O)})
    (hac : IsAlgClosed (ResidueField O))
    (𝔫 : Ideal (C ⊗[ℤ] O)) [𝔫.IsMaximal] :
    IsAlgClosed 𝔫.ResidueField ∧ CharP 𝔫.ResidueField ℓ := by
  classical
  haveI hfinC : Finite C := IsArtinianRing.finite_of_isLocalRing_of_finite_residueField C
  letI : Fintype C := Fintype.ofFinite C

  let C' := C ⊗[ℤ] O
  let F := 𝔫.ResidueField
  let π : C' →+* F := algebraMap C' F
  have hπ : Function.Surjective π := Ideal.algebraMap_residueField_surjective 𝔫
  let ιO : O →+* C' := (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C').toRingHom
  let ιC : C →+* C' := algebraMap C C'
  have hιC : ∀ c : C, ιC c = c ⊗ₜ[ℤ] (1 : O) := fun c => rfl
  have hιO : ∀ o : O, ιO o = (1 : C) ⊗ₜ[ℤ] o := fun o => rfl

  have hℓC : IsNilpotent ((ℓ : ℕ) : C) := by
    have hmem : ((ℓ : ℕ) : C) ∈ maximalIdeal C := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ ℓ
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
    refine ⟨N, ?_⟩
    have : ((ℓ : ℕ) : C) ^ N ∈ maximalIdeal C ^ N := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    exact (Submodule.mem_bot C).mp this
  have hℓF : ((ℓ : ℕ) : F) = 0 := by
    have : IsNilpotent ((ℓ : ℕ) : F) := by
      have := hℓC.map (π.comp ιC)
      rwa [map_natCast] at this
    exact this.eq_zero
  have hchar : CharP F ℓ := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hℓF

  let ψ : O →+* F := π.comp ιO
  have hψ : ∀ a ∈ maximalIdeal O, ψ a = 0 := by
    intro a ha
    rw [hℓ, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_natCast, hℓF, mul_zero]
  let φ : ResidueField O →+* F := Ideal.Quotient.lift (maximalIdeal O) ψ hψ
  have hφ : ∀ o : O, φ (IsLocalRing.residue O o) = ψ o := fun o => rfl
  letI : Algebra (ResidueField O) F := φ.toAlgebra

  haveI : Module.Finite (ResidueField O) F := by
    refine ⟨⟨(Finset.univ : Finset C).image (fun c => π (c ⊗ₜ[ℤ] (1 : O))), ?_⟩⟩
    rw [eq_top_iff]
    rintro x -
    obtain ⟨t, rfl⟩ := hπ x
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul c o =>
      have e1 : c ⊗ₜ[ℤ] o = (c ⊗ₜ[ℤ] (1 : O)) * ((1 : C) ⊗ₜ[ℤ] o) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have e2 : π (c ⊗ₜ[ℤ] o) = (IsLocalRing.residue O o) • π (c ⊗ₜ[ℤ] (1 : O)) := by
        rw [e1, map_mul, Algebra.smul_def, mul_comm]
        show _ = φ (IsLocalRing.residue O o) * _
        rw [hφ]
        rfl
      rw [e2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))
    | add s t hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht

  haveI := hac
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField O) (K := F)
  exact ⟨IsAlgClosed.of_ringEquiv (ResidueField O) F (RingEquiv.ofBijective (algebraMap (ResidueField O) F) hbij), hchar⟩

end S_IsArtinianRing_isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField
end P2MW
export P2MW.S_IsArtinianRing_isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField (solution)
