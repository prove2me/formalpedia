-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_regular_of_condM_localization
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:08:49.842929+00:00
-- url     : https://prove2.me/submissions/cdfe852e-7351-4ff5-963c-125d6244e8f4

import Theorems.Thm_MasulloGRH_strictLF_nhds_zero_of_absConvex_traces
import Theorems.Thm_MasulloGRH_strictLF_quotient_condM_absConvex_localization
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hM : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by
  have hTG : IsTopologicalAddGroup E := by
    obtain ⟨⟨hlc, -⟩, -⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop
    obtain ⟨ι, _, p, hp⟩ := hlc
    exact hp.topologicalAddGroup
  intro n
  obtain ⟨m, hnm, U, hU, hW⟩ :=
    strictLF_quotient_condM_absConvex_localization E X hmono hexh hX htop V hV hM n
  refine ⟨m, hnm, U, hU, fun W hWm => ?_⟩
  obtain ⟨Ω, hconv, hbal, htr, hΩ⟩ := hW W hWm
  have hΩE : Ω ∈ nhds (0 : E) :=
    strictLF_nhds_zero_of_absConvex_traces E X hmono hexh (fun n => (hX n).1) htop Ω hconv hbal htr
  refine ⟨V.mkQ '' Ω, ?_, ?_⟩
  · have := (Submodule.isOpenMap_mkQ V).image_mem_nhds hΩE
    simpa using this
  · rintro x hx ⟨y, hy, hxy⟩
    apply hΩ x hx y hy
    have : Submodule.Quotient.mk (x : E) = Submodule.Quotient.mk (p := V) y := by
      simpa using hxy.symm
    rw [Submodule.Quotient.eq] at this
    exact this
