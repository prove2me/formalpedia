-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:53.145195+00:00
-- url     : https://prove2.me/submissions/3139e01e-c0e6-4127-aa24-1f164af417c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_isQuasiRegularSeq_iff_lTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace GlobalTheory
section Monomials
variable {R : Type*} {ι : Type*}
variable [CommRing R]
variable [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
end Monomials
section Piece
variable {R : Type*} [CommRing R]
namespace powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)
end powGr
end Piece
section Quasi
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}
namespace IsQuasiRegularSeq
end IsQuasiRegularSeq
end Quasi
section Basis
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
end Basis
section Flat
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
private theorem injective_lTensor_tensor_iff (N : Type*) [AddCommGroup N] [Module R N]
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q) :
    Function.Injective (g.lTensor (N ⊗[R] M)) ↔ Function.Injective ((g.lTensor M).lTensor N) := by
  rw [LinearMap.lTensor_tensor, LinearMap.coe_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, (TensorProduct.assoc R N M Q).symm.injective.of_comp_iff,
    Function.Injective.of_comp_iff' _ (TensorProduct.assoc R N M P).bijective]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]
end Flat
section Examples
variable {R : Type*} [CommRing R]
example : IsQuasiRegularSeq ℤ ![(2 : ℤ)] :=
  isQuasiRegularSeq_singleton (IsSMulRegular.of_ne_zero two_ne_zero)
example : ¬ IsQuasiRegularSeq ℤ ![(0 : ℤ)] := fun h => by
  simpa using (isQuasiRegularSeq_singleton_iff _).mp h 1 1 0 (by simp)
example : ¬ IsQuasiRegularSeq (ZMod 4) ![(2 : ℤ)] := fun h => by
  have := (isQuasiRegularSeq_singleton_iff _).mp h 2 1 0 (by decide)
  revert this
  decide
example : monoVal ![(2 : ℤ), 3] (Finsupp.single 0 2 + Finsupp.single 1 1) = 12 := by
  simp [monoVal_add]
example (a : ℕ) : Nontrivial (powGr (MvPolynomial.idealOfVars (Fin 2) ℚ)
    (MvPolynomial (Fin 2) ℚ) a) := by
  have hI : MvPolynomial.idealOfVars (Fin 2) ℚ ≠ ⊤ := fun h => by
    have := (MvPolynomial.C_mem_pow_idealOfVars_iff (σ := Fin 2) 1 (1 : ℚ)).mp (by simp [h])
    simp at this
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  exact nontrivial_of_ne _ _
    (((isQuasiRegularSeq_X (R := ℚ) (Fin 2)).powGrBasis a).ne_zero ⟨Finsupp.single 0 a, by simp⟩)
end Examples
end GlobalTheory
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {f : ι → R} (h : IsQuasiRegularSeq M f) (N : Type*)
    [AddCommGroup N] [Module R N] [Module.Flat R N] : IsQuasiRegularSeq (N ⊗[R] M) f := by
  rw [isQuasiRegularSeq_iff_lTensor] at h ⊢
  exact fun a => (injective_lTensor_tensor_iff N _).mpr
    (Module.Flat.lTensor_preserves_injective_linearMap _ (h a))
end IsQuasiRegularSeq
end GlobalTheory
