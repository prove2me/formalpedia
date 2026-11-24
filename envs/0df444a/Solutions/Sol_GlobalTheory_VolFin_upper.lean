-- Prove2me | solution 1 for GlobalTheory.VolFin.upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:35.351833+00:00
-- url     : https://prove2.me/submissions/92fd90bd-bb2c-4603-8d11-ad83459a3c80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
import Theorems.Thm_GlobalTheory_VolFin_mem_piece
import Theorems.Thm_GlobalTheory_VolFin_Den_family

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
    (hG : ∀ i, ∃ (n : ℕ) (g : Fin n → F'), ∀ t ∈ R' i, ∃ w : Fin n → F,
      (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • g l)
    (hfin : ∀ e, Module.Finite K (piece R γ e)) :
    ∃ c, ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e) ∧
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) e) ≤
        finrank F F' * finrank K (piece R γ (e + c)) := by
  classical
  choose n g hg using hG
  have b : Basis (Fin (finrank F F')) F F' := Module.finBasis F F'
  obtain ⟨c, q, -, hq0, hu⟩ := h.family (κ := Σ i : ι, Fin (n i) × Fin (finrank F F'))
    (fun k => b.repr (g k.1 k.2.1) k.2.2)
  refine ⟨c, fun e => ?_⟩
  have := hfin (e + c)
  have key : ∀ f ∈ piece R' (fun i => algebraMap F F' (γ i)) e, ∀ j,
      q * b.repr f j ∈ piece R γ (e + c) := by
    intro f hf j
    refine mem_piece.2 fun i => ?_
    obtain ⟨w, hw, hfw⟩ := hg i _ (mem_piece.1 hf i)
    have hfw' : (γ i ^ e) • f = ∑ l, w l • g i l := by
      rw [Algebra.smul_def, map_pow, mul_comm]
      exact hfw
    have h1 : γ i ^ e * b.repr f j = ∑ l, w l * b.repr (g i l) j := by
      have := congrArg (fun x => b.repr x j) hfw'
      simpa [map_sum, Finsupp.finsetSum_apply] using this
    have h2 : q * b.repr f j * γ i ^ (e + c) = ∑ l, w l * (q * b.repr (g i l) j * γ i ^ c) := by
      rw [pow_add, show q * b.repr f j * (γ i ^ e * γ i ^ c)
        = (γ i ^ e * b.repr f j) * (q * γ i ^ c) by ring, h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [h2]
    exact Subalgebra.sum_mem _ fun l _ => (R i).mul_mem (hw l) (mem_piece.1 (hu ⟨i, l, j⟩) i)
  let Φ : piece R' (fun i => algebraMap F F' (γ i)) e →ₗ[K] (Fin (finrank F F') → piece R γ (e + c)) :=
    { toFun := fun f j => ⟨q * b.repr f j, key f f.2 j⟩
      map_add' := fun f f' => by
        funext j
        apply Subtype.ext
        simp [mul_add]
      map_smul' := fun a f => by
        funext j
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply]
        rw [← algebraMap_smul F a (f : F'), map_smul, Finsupp.smul_apply, smul_eq_mul,
          Algebra.smul_def]
        ring }
  have hinj : Function.Injective Φ := by
    intro f f' hff
    apply Subtype.ext
    apply b.repr.injective
    ext j
    have := congrArg (fun x => ((x j : piece R γ (e + c)) : F)) hff
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact mul_left_cancel₀ hq0 this
  have : Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e) :=
    Module.Finite.of_injective Φ hinj
  refine ⟨this, ?_⟩
  calc finrank K (piece R' (fun i => algebraMap F F' (γ i)) e)
      ≤ finrank K (Fin (finrank F F') → piece R γ (e + c)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = finrank F F' * finrank K (piece R γ (e + c)) := by
        simp [Module.finrank_pi_fintype]
end GlobalTheory.VolFin
