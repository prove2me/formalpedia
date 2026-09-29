-- Prove2me | solution 1 for Ideal.mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/585bd116-2bfb-58cd-b262-77b6115d452d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) :
    g ∈ 𝔶.inertia G ↔ (g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits) := by

  have hnu : ∀ (h : G) (x : F), x ∈ (h • P).nonunits ↔ h⁻¹ • x ∈ P.nonunits := by
    intro h x
    simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      smul_inv'', smul_eq_zero_iff_eq]

  have hmem : ∀ {h : G}, h ∈ 𝔶.inertia G → ∀ b : B, h • b ∈ 𝔶 ↔ b ∈ 𝔶 := by
    intro h hh b
    have hb := hh b
    constructor
    · intro h1; simpa using 𝔶.sub_mem h1 hb
    · intro h1; simpa using 𝔶.add_mem hb h1
  constructor
  · intro hg

    have hstab : g • P = P := by
      apply huniq
      · intro b
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hρ]
        exact hP _
      · intro b
        rw [hnu, hρ, hPy]
        exact hmem (inv_mem hg) b
    refine ⟨hstab, fun e => ?_⟩

    obtain ⟨b, hb⟩ := hres e
    have h1 : g • ((e : F) - ρ b) ∈ P.nonunits := by
      have : g • ((e : F) - ρ b) ∈ (g • P).nonunits := by
        rw [hnu, inv_smul_smul]; exact hb
      rwa [hstab] at this
    have h2 : g • ρ b - ρ b ∈ P.nonunits := by
      rw [hρ, ← map_sub]; exact (hPy _).mpr (hg b)
    have h3 : ρ b - (e : F) ∈ P.nonunits := by
      have := P.nonunits.neg_mem hb
      rwa [neg_sub] at this
    have : g • (e : F) - e = g • ((e : F) - ρ b) + (g • ρ b - ρ b) + (ρ b - e) := by
      rw [smul_sub]; ring
    rw [this]
    exact P.nonunits.add_mem (P.nonunits.add_mem h1 h2) h3
  · rintro ⟨-, hres'⟩ b
    have h := hres' ⟨ρ b, hP b⟩
    change g • ρ b - ρ b ∈ P.nonunits at h
    rw [hρ, ← map_sub] at h
    exact (hPy _).mp h

end S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
end P2MW
export P2MW.S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits (solution)
