-- Prove2me | solution 1 for KarpPapadimitriou.Facial.hull_isPolyhedron_of_small
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:17:31.077352+00:00
-- url     : https://prove2.me/submissions/f0aaabb9-2fc6-47cb-8a6d-0f7356d94124

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

open KarpPapadimitriou.Facial

theorem solution (C : COP) (F : Triples C)
    (hF : IsFacialDescription C F) (hs : IsSmall C F) (z : List Bool) (hz : z ∈ C.L) :
    {fg : (Fin (C.n z) → ℤ) × ℤ |
        (⟨z, fg⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F}.Finite ∧
      ∃ H : Finset ((Fin (C.n z) → ℚ) × ℚ),
        hull C z = {x : Fin (C.n z) → ℚ | ∀ h ∈ H, h.1 ⬝ᵥ x ≤ h.2} := by
  classical
  obtain ⟨k, hk⟩ := hs
  let B : ℤ := 2 ^ ((z.length + C.n z) ^ k + k)
  let T : Set ((Fin (C.n z) → ℤ) × ℤ) :=
    {fg | (⟨z, fg⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F}
  have ht : T.Finite := by
    have hp : {f : Fin (C.n z) → ℤ | ∀ i, f i ∈ Set.Icc (-B) B}.Finite :=
      Set.Finite.pi' (fun _ => Set.finite_Icc (-B) B)
    apply (hp.prod (Set.finite_Icc (-B) B)).subset
    intro fg hfg
    obtain ⟨hf, hg⟩ := hk ⟨z, fg⟩ hfg
    exact ⟨fun i => abs_le.mp (hf i), abs_le.mp hg⟩
  refine ⟨ht, ?_⟩
  let castPair : ((Fin (C.n z) → ℤ) × ℤ) → ((Fin (C.n z) → ℚ) × ℚ) :=
    fun fg => (fun i => (fg.1 i : ℚ), (fg.2 : ℚ))
  refine ⟨ht.toFinset.image castPair, ?_⟩
  ext x
  rw [hF.2 z hz x]
  constructor
  · intro hx h hh
    obtain ⟨fg, hfg, rfl⟩ := Finset.mem_image.mp hh
    exact hx fg.1 fg.2 (ht.mem_toFinset.mp hfg)
  · intro hx f g hfg
    exact hx (castPair (f, g)) (Finset.mem_image.mpr
      ⟨(f, g), ht.mem_toFinset.mpr hfg, rfl⟩)

#print axioms solution

