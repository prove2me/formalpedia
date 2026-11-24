-- Prove2me | solution 1 for GlobalTheory.VolFin.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:34.435035+00:00
-- url     : https://prove2.me/submissions/acf7c867-b030-46f0-b881-8acbdc9ef2b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
import Theorems.Thm_GlobalTheory_VolFin_mem_piece
import Theorems.Thm_GlobalTheory_VolFin_Den_family
import Theorems.Thm_GlobalTheory_VolFin_mem_span_of_frac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}
variable [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] [Finite ι]
namespace GlobalTheory.VolFin
theorem _root_.solution {R : ι → Subalgebra K F} {γ : ι → F} {R' : ι → Subalgebra K F'} (h : Den R γ)
    (hR : ∀ i, ∀ a ∈ R i, algebraMap F F' a ∈ R' i)
    (hS : ∀ i, ∀ t : F', ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a)
    (hfin : ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e)) :
    ∃ c, ∀ e, Module.Finite K (piece R γ e) → finrank F F' * finrank K (piece R γ e) ≤
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) (e + c)) := by
  classical
  have b : Basis (Fin (finrank F F')) F F' := Module.finBasis F F'
  have hspan : ∀ i, ∀ t : F', t ∈ Submodule.span F (R' i : Set F') := fun i t =>
    mem_span_of_frac (R' i) (hS i) (fun x _ => (IsIntegral.of_finite F x).isAlgebraic) t
  choose n f s hfs using fun p : ι × Fin (finrank F F') =>
    Submodule.mem_span_set'.1 (hspan p.1 (b p.2))
  obtain ⟨c, q, -, hq0, hu⟩ := h.family (κ := Σ p : ι × Fin (finrank F F'), Fin (n p))
    (fun k => f k.1 k.2)
  let v : Fin (finrank F F') → F' := fun j => q • b j
  have hv : ∀ j, v j ∈ piece R' (fun i => algebraMap F F' (γ i)) c := by
    intro j
    refine mem_piece.2 fun i => ?_
    have hvj : v j * algebraMap F F' (γ i) ^ c =
        ∑ l, algebraMap F F' (q * f (i, j) l * γ i ^ c) * (s (i, j) l : F') := by
      simp only [v]
      rw [show b j = _ from (hfs (i, j)).symm, Finset.smul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Algebra.smul_def, map_mul, map_pow]
      ring
    rw [hvj]
    exact Subalgebra.sum_mem _ fun l _ =>
      (R' i).mul_mem (hR i _ (mem_piece.1 (hu ⟨(i, j), l⟩) i)) (s (i, j) l).2
  refine ⟨c, fun e hP => ?_⟩
  have := hP
  have := hfin (e + c)
  have key : ∀ x : Fin (finrank F F') → piece R γ e,
      ∑ j, (x j : F) • v j ∈ piece R' (fun i => algebraMap F F' (γ i)) (e + c) := by
    intro x
    refine mem_piece.2 fun i => ?_
    rw [Finset.sum_mul]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    have hxj : (x j : F) • v j * algebraMap F F' (γ i) ^ (e + c) =
        algebraMap F F' ((x j : F) * γ i ^ e) * (v j * algebraMap F F' (γ i) ^ c) := by
      rw [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
    rw [hxj]
    exact (R' i).mul_mem (hR i _ (mem_piece.1 (x j).2 i)) (mem_piece.1 (hv j) i)
  let Φ : (Fin (finrank F F') → piece R γ e) →ₗ[K]
      piece R' (fun i => algebraMap F F' (γ i)) (e + c) :=
    { toFun := fun x => ⟨∑ j, (x j : F) • v j, key x⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        apply Subtype.ext
        simp [Finset.smul_sum, smul_assoc] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∑ j, ((x j : F) * q) • b j = 0 := by
      have := congrArg Subtype.val hx
      simpa [Φ, v, smul_smul] using this
    funext j
    have hj := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h0 j
    exact Subtype.ext (by simpa using (mul_eq_zero.1 hj).resolve_right hq0)
  calc finrank F F' * finrank K (piece R γ e)
      = finrank K (Fin (finrank F F') → piece R γ e) := by
        simp [Module.finrank_pi_fintype]
    _ ≤ _ := LinearMap.finrank_le_finrank_of_injective hinj
end GlobalTheory.VolFin
