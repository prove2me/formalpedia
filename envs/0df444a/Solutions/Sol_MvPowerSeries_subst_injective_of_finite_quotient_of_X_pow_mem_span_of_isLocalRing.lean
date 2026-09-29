-- Prove2me | solution 1 for MvPowerSeries.subst_injective_of_finite_quotient_of_X_pow_mem_span_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6ddee3b5-58c5-5287-8bea-9dc65dbf7379

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_basis_subst_of_finite_quotient_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_subst_injective_of_finite_quotient_of_X_pow_mem_span_of_isLocalRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (H H' : MvPowerSeries (Fin n) B) (h : MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H') : H = H' := by
  classical
  have ha : MvPowerSeries.HasSubst ρ := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  have hsub0 : MvPowerSeries.subst ρ (0 : MvPowerSeries (Fin n) B) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom ha, map_zero]
  obtain ⟨d, b, hb⟩ := MvPowerSeries.exists_basis_subst_of_finite_quotient_of_isLocalRing ρ hρ0 hN hfin
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    subst hd
    have h0 : ∀ f : MvPowerSeries (Fin n) B, f = 0 := fun f => by
      obtain ⟨c, hc, -⟩ := hb f
      rw [hc]
      simp
    rw [h0 H, h0 H']
  · let j₀ : Fin d := ⟨0, hd⟩
    have hrep : ∀ G : MvPowerSeries (Fin n) B,
        MvPowerSeries.subst ρ G * b j₀ =
          ∑ j, MvPowerSeries.subst ρ ((Pi.single j₀ G : Fin d → MvPowerSeries (Fin n) B) j) * b j := by
      intro G
      rw [Finset.sum_eq_single j₀, Pi.single_eq_same]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, hsub0, zero_mul]
      · intro hj₀
        exact absurd (Finset.mem_univ j₀) hj₀
    have hc : (Pi.single j₀ H : Fin d → MvPowerSeries (Fin n) B) = Pi.single j₀ H' :=
      (hb (MvPowerSeries.subst ρ H * b j₀)).unique (hrep H) (by rw [h]; exact hrep H')
    have := congrFun hc j₀
    rwa [Pi.single_eq_same, Pi.single_eq_same] at this

end S_MvPowerSeries_subst_injective_of_finite_quotient_of_X_pow_mem_span_of_isLocalRing
end P2MW
export P2MW.S_MvPowerSeries_subst_injective_of_finite_quotient_of_X_pow_mem_span_of_isLocalRing (solution)
