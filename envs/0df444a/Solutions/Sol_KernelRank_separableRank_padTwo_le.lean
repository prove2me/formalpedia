-- Prove2me | solution 1 for KernelRank.separableRank_padTwo_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:37.84213+00:00
-- url     : https://prove2.me/submissions/0066e1b9-35a2-407d-954d-827f73e1d165

import Mathlib
import Definitions.Def_KernelRankLean_Defs

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 α : Type*} [CommSemiring 𝕜] [Zero α] {d : ℕ} (hd : 2 ≤ d)
    (K : (Fin d → α) → 𝕜) :
    separableRank (fun y : Fin 2 → α => K (padTwo y)) ≤ separableRank K := by
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨f, hf⟩ := hN
  let rest : Finset (Fin d) := Finset.univ.filter fun i : Fin d => ¬ (i : ℕ) < 2
  let c (n : Fin N) : 𝕜 := ∏ i ∈ rest, f n i 0
  let g (n : Fin N) : ∀ k : Fin 2, α → 𝕜 :=
    Fin.cases (fun u => c n * f n (Fin.castLE hd 0) u)
      (fun _ u => f n (Fin.castLE hd 1) u)
  refine iInf₂_le N ⟨g, fun y => ?_⟩
  dsimp only
  rw [hf]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hsplit := (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin d => (i : ℕ) < 2) (fun i => f n i (padTwo y i))).symm
  have hrest : ∏ i ∈ rest, f n i (padTwo y i) = c n :=
    Finset.prod_congr rfl fun i hi => by
      have hi' : ¬ (i : ℕ) < 2 := (Finset.mem_filter.mp hi).2
      simp [padTwo, hi']
  have htwo : ∏ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2), f n i (padTwo y i) =
      f n (Fin.castLE hd 0) (y 0) * f n (Fin.castLE hd 1) (y 1) := by
    have hset : Finset.univ.filter (fun i : Fin d => (i : ℕ) < 2) =
        {Fin.castLE hd 0, Fin.castLE hd 1} := by
      ext ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE, Fin.val_zero, Fin.val_one]
      omega
    have hne : Fin.castLE hd 0 ≠ Fin.castLE hd 1 := by simp [Fin.ext_iff]
    rw [hset, Finset.prod_pair hne]
    simp [padTwo, Fin.castLE]
  rw [hsplit, hrest, htwo, Fin.prod_univ_two]
  change f n (Fin.castLE hd 0) (y 0) * f n (Fin.castLE hd 1) (y 1) * c n =
    c n * f n (Fin.castLE hd 0) (y 0) * f n (Fin.castLE hd 1) (y 1)
  ring
end KernelRank
