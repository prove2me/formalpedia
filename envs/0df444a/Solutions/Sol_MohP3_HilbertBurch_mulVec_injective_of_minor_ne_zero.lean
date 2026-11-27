-- Prove2me | solution 1 for MohP3.HilbertBurch.mulVec_injective_of_minor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:09.66265+00:00
-- url     : https://prove2.me/submissions/aae9c1e6-8c94-43cf-a59f-070d515bfd2f

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
attribute [local simp] MohP3.HilbertBurch.rowMap_apply

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
variable {S : Type*} [CommRing S] [IsDomain S]
namespace MohP3.HilbertBurch
theorem _root_.solution (Φ : Matrix (Fin 4) (Fin 3) S) (i : Fin 4)
    (hi : maximalMinor Φ i ≠ 0) : Function.Injective (Matrix.mulVecLin Φ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  change Φ *ᵥ v = 0 at hv
  set B := Φ.submatrix i.succAbove id
  have hB : B *ᵥ v = 0 := by
    ext r
    have := congrFun hv (i.succAbove r)
    simpa [B, Matrix.mulVec, dotProduct] using this
  have h2 : (B.adjugate * B) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  ext r
  have := congrFun h2 r
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hi
end MohP3.HilbertBurch
