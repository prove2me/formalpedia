-- Prove2me | solution 1 for N25.LocalFive.finite_quotient_and_surjective_nsmul_comap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:20.128513+00:00
-- url     : https://prove2.me/submissions/66a0c4f1-6fc1-4315-bb83-24f6173e6965

import Mathlib

noncomputable section

namespace N25.LocalFive

/-- Scalar-saturated embeddings pull finite-index scalar-divisible subgroups back. -/
theorem _root_.solution
    {M L : Type*} [AddCommGroup M] [AddCommGroup L]
    (e : M →+ L) (he : Function.Injective e)
    (n : ℕ)
    (hsat : ∀ y : L, n • y ∈ e.range → y ∈ e.range)
    (U₀ : AddSubgroup L)
    (hfin : Finite (L ⧸ U₀))
    (hU₀ : Function.Surjective (fun u : U₀ => n • u)) :
    Finite (M ⧸ U₀.comap e) ∧
      Function.Surjective (fun u : U₀.comap e => n • u) := by
  letI := hfin
  let q := QuotientAddGroup.map (U₀.comap e) U₀ e le_rfl
  have hq : Function.Injective q := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (U₀.comap e) x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (U₀.comap e) y
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change e (x - y) ∈ U₀
    rw [map_sub]
    exact QuotientAddGroup.eq_iff_sub_mem.mp hxy
  refine ⟨Finite.of_injective q hq, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hU₀ ⟨e x, x.property⟩
  have hny : n • (y : L) = e x := congrArg Subtype.val hy
  obtain ⟨z, hz⟩ := hsat y (by rw [hny]; exact ⟨x, rfl⟩)
  have hmem : z ∈ U₀.comap e := by
    change e z ∈ U₀
    rw [hz]
    exact y.property
  refine ⟨⟨z, hmem⟩, Subtype.ext (he ?_)⟩
  change e (n • z) = e (x : M)
  rw [map_nsmul, hz, hny]

end N25.LocalFive
