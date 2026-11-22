-- Prove2me | solution 1 for MasulloGRH.isCompact_moduleKernel_and_compact_le
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:04:33.053061+00:00
-- url     : https://prove2.me/submissions/32d86704-c316-4d69-9cdf-82f67c3f3ea5

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

namespace MasulloGRHG1Aux

open MasulloGRH Filter

variable {G : Type*} [CommGroup G] [TopologicalSpace G] {m : G → ℝ}

lemma m_one (hm : IsModule m) : m 1 = 1 := by
  have h := hm.map_mul 1 1
  rw [mul_one] at h
  have hp := hm.pos 1
  field_simp at h
  linarith [h]

lemma m_pow (hm : IsModule m) (g : G) (n : ℕ) : m (g ^ n) = m g ^ n := by
  induction n with
  | zero => simp [m_one hm]
  | succ n ih => rw [pow_succ, hm.map_mul, ih, pow_succ]

lemma m_inv (hm : IsModule m) (g : G) : m g⁻¹ = (m g)⁻¹ := by
  have h := hm.map_mul g g⁻¹
  rw [mul_inv_cancel, m_one hm] at h
  have hp := hm.pos g
  field_simp
  linarith [h]

lemma not_one_lt (hm : IsModule m) (k : Subgroup G) (hk : IsCompact (k : Set G))
    (g : G) (hg : g ∈ k) : ¬ 1 < m g := by
  intro h
  obtain ⟨B, hB⟩ := (hk.image hm.continuous).isBounded.bddAbove
  obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  have : m (g ^ n) ≤ B := hB ⟨g ^ n, k.pow_mem hg n, rfl⟩
  rw [m_pow hm] at this
  linarith

end MasulloGRHG1Aux

open MasulloGRH MasulloGRHG1Aux in
theorem solution (G : Type*) [CommGroup G] [TopologicalSpace G] (m : G → ℝ)
    (hm : IsRposModule m) (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1) :
    IsCompact (G1 : Set G) ∧ ∀ k : Subgroup G, IsCompact (k : Set G) → k ≤ G1 := by
  constructor
  · have : (G1 : Set G) = m ⁻¹' Set.Icc 1 1 := by
      ext g
      simp only [SetLike.mem_coe, hG1, Set.mem_preimage, Set.Icc_self, Set.mem_singleton_iff]
    rw [this]
    exact hm.1.proper 1 1 one_pos
  · intro k hk g hg
    rw [hG1]
    have h1 := not_one_lt hm.1 k hk g hg
    have h2 := not_one_lt hm.1 k hk g⁻¹ (k.inv_mem hg)
    rw [m_inv hm.1] at h2
    have hp := hm.1.pos g
    have h3 : ¬ m g < 1 := fun h => h2 (one_lt_inv₀ hp |>.2 h)
    push Not at h1 h3
    linarith
