-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_condM_absConvex_localization
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:23:01.880186+00:00
-- url     : https://prove2.me/submissions/8b0c80db-217e-485a-9739-3c894feecd79

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_localization
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
      ∃ Ω : Set E, Convex ℝ Ω ∧ Balanced ℂ Ω ∧
        (∀ k, ((↑) : X k → E) ⁻¹' Ω ∈ nhds (0 : X k)) ∧
        ∀ x ∈ U, ∀ y ∈ Ω, ((x : E) - y) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by
  intro n
  obtain ⟨m, hnm, U, hU, hL⟩ :=
    strictLF_quotient_regular_of_condM_localization E X hmono hexh hX htop V hV hM n
  obtain ⟨⟨ι, _, p, hp⟩, _⟩ :=
    (strictLF_hlcs_and_closed_steps E X hmono hexh (fun k => (hX k).1) htop).1
  refine ⟨m, hnm, U, hU, fun W hW => ?_⟩
  obtain ⟨G, hG, hGW⟩ := hL W hW
  have hpre : (Submodule.Quotient.mk : E → E ⧸ V) ⁻¹' G ∈ nhds (0 : E) := by
    have hc : Continuous (Submodule.Quotient.mk : E → E ⧸ V) := continuous_quot_mk
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hG)
  obtain ⟨s, r, hr, hsub⟩ := (hp.mem_nhds_iff 0 _).1 hpre
  refine ⟨(s.sup p).ball 0 r, Seminorm.convex_ball _ _ _, Seminorm.balanced_ball_zero _ _,
    fun k => ?_, ?_⟩
  · have hΩ : (s.sup p).ball 0 r ∈ nhds (0 : E) := (hp.mem_nhds_iff 0 _).2 ⟨s, r, hr, le_rfl⟩
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hΩ)
  · intro x hx y hy hxy
    apply hGW x hx
    have hq : (Submodule.Quotient.mk (x : E) : E ⧸ V) = Submodule.Quotient.mk y :=
      (Submodule.Quotient.eq V).2 hxy
    rw [hq]
    exact hsub hy

