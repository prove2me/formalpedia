-- Prove2me | solution 1 for GlobalTheory.LocBounded.det_hankel_trace_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:12.556019+00:00
-- url     : https://prove2.me/submissions/175d0f2b-a94c-409c-9e29-05ff36b06bb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
import Theorems.Thm_GlobalTheory_CharpolyPow_card_roots_charpoly
import Theorems.Thm_GlobalTheory_CharpolyPow_roots_charpoly_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded
namespace GlobalTheory.LocBounded
theorem _root_.solution (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K)
    (h : N.charpoly.Separable) :
    (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace).det ≠ 0 := by
  classical
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  set M := N.map f with hM
  have hcp : M.charpoly = N.charpoly.map f := Matrix.charpoly_map N f
  have hsepM : M.charpoly.Separable := hcp ▸ h.map
  have hnd : M.charpoly.roots.Nodup := nodup_roots hsepM
  have hcard : Multiset.card M.charpoly.roots = n := GlobalTheory.CharpolyPow.card_roots_charpoly M
  set s := M.charpoly.roots.toFinset with hsdef
  have hs : s.card = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  have hsval : s.val = M.charpoly.roots := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let lam : Fin n → L := fun i => (e i : L)
  have hinj : Function.Injective lam := Subtype.val_injective.comp e.injective
  have htr : ∀ m : ℕ, (M ^ m).trace = ∑ i, lam i ^ m := by
    intro m
    rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, ← hsval,
      ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s (fun x => x ^ m)]
    exact (Equiv.sum_comp e (fun x : s => (x : L) ^ m)).symm
  have hV : (Matrix.of fun j k : Fin n => (M ^ ((j : ℕ) + (k : ℕ))).trace) =
      (Matrix.vandermonde lam).transpose * Matrix.vandermonde lam := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [htr]
    simp only [pow_add]
  have hmap : f.mapMatrix (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace) =
      Matrix.of fun j k : Fin n => (M ^ ((j : ℕ) + (k : ℕ))).trace := by
    ext j k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hM, ← Matrix.map_pow]
    simp [Matrix.trace, map_sum]
  intro h0
  have h1 : f (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace).det = 0 := by
    rw [h0, map_zero]
  rw [RingHom.map_det, hmap, hV, Matrix.det_mul, Matrix.det_transpose] at h1
  exact Matrix.det_vandermonde_ne_zero_iff.2 hinj (mul_self_eq_zero.1 h1)
end GlobalTheory.LocBounded
