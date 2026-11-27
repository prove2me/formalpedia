-- Prove2me | solution 1 for MohP3.HilbertBurch.mem_span_of_monic_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:04.402211+00:00
-- url     : https://prove2.me/submissions/5c82b358-ae12-4e6d-97ce-18dd8d7ea9ed

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
open MvPolynomial
variable {K : Type*} [CommRing K]
namespace MohP3.HilbertBurch
theorem _root_.solution (h : MvPolynomial (Fin 2) K) (t u : MvPolynomial (Fin 3) K)
    (ht : (xEquiv t).Monic)
    (hu : t * u ∈ Ideal.span {xEquiv.symm (Polynomial.C h)}) :
    u ∈ Ideal.span {xEquiv.symm (Polynomial.C h)} := by
  set e := (xEquiv : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K))
  have hmap : ∀ v, v ∈ Ideal.span {e.symm (Polynomial.C h)} ↔ e v ∈ Ideal.span {Polynomial.C h} := by
    intro v
    constructor
    · intro hv
      simpa [Ideal.map_span] using Ideal.mem_map_of_mem e hv
    · intro hv
      simpa [Ideal.map_span] using Ideal.mem_map_of_mem e.symm hv
  rw [hmap] at hu ⊢
  set φ := Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span {h}))
  have hker : RingHom.ker φ = Ideal.span {Polynomial.C h} := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
  rw [← hker, RingHom.mem_ker] at hu ⊢
  rw [map_mul, map_mul] at hu
  have hmon : (φ (e t)).Monic := ht.map _
  exact hmon.mul_right_eq_zero_iff.mp hu
end MohP3.HilbertBurch
