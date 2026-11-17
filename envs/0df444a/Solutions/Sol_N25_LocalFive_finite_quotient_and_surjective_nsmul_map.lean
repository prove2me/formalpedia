-- Prove2me | solution 1 for N25.LocalFive.finite_quotient_and_surjective_nsmul_map
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:20.913207+00:00
-- url     : https://prove2.me/submissions/69322f9b-4aad-45d4-9e94-590cdf7f6446

import Mathlib

noncomputable section

namespace N25.LocalFive

/-- Finite quotient and scalar division descend along a surjective additive map. -/
theorem _root_.solution
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A →+ B) (he : Function.Surjective e)
    (n : ℕ) (U : AddSubgroup A)
    (hfin : Finite (A ⧸ U))
    (hU : Function.Surjective (fun u : U => n • u)) :
    Finite (B ⧸ U.map e) ∧
      Function.Surjective (fun u : U.map e => n • u) := by
  letI := hfin
  have hle : U ≤ (U.map e).comap e := fun x hx => ⟨x, hx, rfl⟩
  let q := QuotientAddGroup.map U (U.map e) e hle
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (U.map e) b
    obtain ⟨a, rfl⟩ := he b
    exact ⟨QuotientAddGroup.mk' U a, rfl⟩
  refine ⟨Finite.of_surjective q hq, ?_⟩
  intro b
  obtain ⟨a, ha, hab⟩ := b.property
  obtain ⟨v, hv⟩ := hU ⟨a, ha⟩
  refine ⟨⟨e v, ⟨v, v.property, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change n • e (v : A) = (b : B)
  rw [← map_nsmul, show n • (v : A) = a from congrArg Subtype.val hv]
  exact hab

end N25.LocalFive
