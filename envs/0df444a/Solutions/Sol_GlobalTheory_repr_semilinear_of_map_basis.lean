-- Prove2me | solution 1 for GlobalTheory.repr_semilinear_of_map_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:26.848824+00:00
-- url     : https://prove2.me/submissions/0c46fa1d-9b7a-4950-bce1-734380366fd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.coe_symplecticGroupMap

set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R Λ M l : Type*} [CommRing S] [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup Λ] [Module S Λ] [AddCommGroup M] [Module R M] [Fintype l]
  {f : S →+* R} {B : LinearMap.BilinForm S Λ} {B' : LinearMap.BilinForm R M}
omit [Finite (MaximalSpectrum R)]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (φ : Λ →ₛₗ[f] M) {b : Basis ι S Λ}
    {c : Basis ι R M} (h : ∀ i, φ (b i) = c i) (x : Λ) (i : ι) :
    c.repr (φ x) i = f (b.repr x i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum φ, φ.map_smulₛₗ, h, c.repr_sum_self]
end GlobalTheory
