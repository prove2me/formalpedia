-- Prove2me | solution 1 for MazurTransfer.residueField_equiv_of_surjective_local_map
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T11:56:03.545698+00:00
-- url     : https://prove2.me/submissions/cd4c3a23-745e-4d05-a181-2685aac1cfbc

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: exact residue field through a given surjective local map.
Named downstream consumer: the original decomposition-fixed ring at13
and the actual local Picard formal subgroup. -/
import Mathlib

theorem solution (R k : Type) [CommRing R] [IsLocalRing R] [Field k]
    (π : R →+* k) (hs : Function.Surjective π)
    (hπ : ∀ r : R, π r = 0 ↔ ¬ IsUnit r) :
    ∃ e : IsLocalRing.ResidueField R ≃+* k,
      ∀ r : R, e (IsLocalRing.residue R r) = π r := by
  let f : IsLocalRing.ResidueField R →+* k := Ideal.Quotient.lift
    (IsLocalRing.maximalIdeal R) π (by
      intro r hr
      apply (hπ r).mpr
      exact (IsLocalRing.mem_maximalIdeal r).mp hr)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨r, hr⟩ := hs y
    exact ⟨IsLocalRing.residue R r, hr⟩
  exact ⟨RingEquiv.ofBijective f ⟨f.injective, hf⟩, fun r => rfl⟩

#print axioms solution
