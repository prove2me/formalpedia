-- Prove2me | solution 1 for KAdaptability.EpsApprox.lemma_1_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:38:13.786417+00:00
-- url     : https://prove2.me/submissions/e5960be9-6c96-475f-ab1a-3b2b0f45e7ad

import Mathlib
import Definitions.Def_KAdaptability_EpsApprox_Approx

set_option autoImplicit false
open KAdaptability.EpsApprox Filter Topology

theorem solution {N M L nQ R K : ℕ} (P : Problem N M L nQ R)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y)
    (ℓ : Fin K → Fin (L + 1)) :
    ∀ ξ ∈ P.XiL x y ℓ, ∃ ε' > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε', ξ ∈ P.XiEps ε x y ℓ := by
  intro ξ hξ
  obtain ⟨hXi, h0, hneg⟩ := hξ
  have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ∀ k (i : Fin L), ℓ k = i.succ → P.rhs ξ i + ε ≤ P.lhs x (y k) i := by
    rw [Filter.eventually_all]; intro k
    rw [Filter.eventually_all]; intro i
    by_cases h : ℓ k = i.succ
    · have hg := hneg k i h
      have h1 : ∀ᶠ ε in nhds (0:ℝ), ε < P.lhs x (y k) i - P.rhs ξ i :=
        Iio_mem_nhds (by linarith)
      exact (h1.filter_mono nhdsWithin_le_nhds).mono (fun ε hε _ => by linarith)
    · exact Filter.Eventually.of_forall (fun ε h' => absurd h' h)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 hev
  exact ⟨u, hu, fun ε hε => ⟨hXi, h0, hsub hε⟩⟩
