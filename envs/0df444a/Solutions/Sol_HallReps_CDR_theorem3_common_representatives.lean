-- Prove2me | solution 1 for HallReps.CDR.theorem3_common_representatives
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:24:53.281823+00:00
-- url     : https://prove2.me/submissions/18325ca2-2eaa-4a5d-9774-2163e2d06e54

import Mathlib
import Definitions.Def_HallReps_CDR_System
import Theorems.Thm_HallReps_CDR_theorem1_hall

set_option autoImplicit false

open HallReps.CDR

theorem solution {α : Type*} {m : ℕ} (p q : α → Fin m)
    (h : ∀ s : Finset (Fin m), s.card ≤ (p '' (q ⁻¹' (s : Set (Fin m)))).ncard) :
    ∃ σ : Equiv.Perm (Fin m), ∃ a : Fin m → α, ∀ i, p (a i) = i ∧ q (a i) = σ i := by
  classical
  -- the system of `p`-classes met by the `q`-class `j`
  let T : Fin m → Set (Fin m) := fun j => p '' (q ⁻¹' {j})
  have hH : HallCondition T := by
    intro s
    have hU : (⋃ j ∈ s, T j) = p '' (q ⁻¹' (s : Set (Fin m))) := by
      ext y
      simp only [T, Set.mem_iUnion, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff,
        Finset.mem_coe, exists_prop]
      constructor
      · rintro ⟨j, hj, x, hx, rfl⟩
        exact ⟨x, hx ▸ hj, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨q x, hx, x, rfl, rfl⟩
    rw [hU]
    have hfin : (p '' (q ⁻¹' (s : Set (Fin m)))).Finite := Set.toFinite _
    rw [← hfin.cast_ncard_eq]
    exact_mod_cast h s
  obtain ⟨b, hbinj, hbmem⟩ := HallReps.CDR.theorem1_hall T hH
  have hbij : Function.Bijective b := Finite.injective_iff_bijective.mp hbinj
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective b hbij
  -- an element of the `q`-class `j` lying in the `p`-class `b j`
  choose a' ha' using hbmem
  refine ⟨τ.symm, fun i => a' (τ.symm i), fun i => ?_⟩
  obtain ⟨hq, hp⟩ := ha' (τ.symm i)
  refine ⟨?_, hq⟩
  have : b (τ.symm i) = i := τ.apply_symm_apply i
  rw [hp, this]

#print axioms solution
