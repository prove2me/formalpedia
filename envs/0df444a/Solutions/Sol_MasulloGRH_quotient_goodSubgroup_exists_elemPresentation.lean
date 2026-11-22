-- Prove2me | solution 1 for MasulloGRH.quotient_goodSubgroup_exists_elemPresentation
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:02:48.870621+00:00
-- url     : https://prove2.me/submissions/dcf78614-8e44-481c-9511-d8d1b48a34af

import Theorems.Thm_MasulloGRH_quotient_goodSubgroup_dual_compactlyGenerated
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

universe u

namespace QEAux

lemma exists_root (t : ℝ) (ht : 0 < t) : ∃ n : ℕ, 0 < n ∧ 1 / 2 ≤ t ^ (1 / (n : ℝ)) ∧
    t ^ (1 / (n : ℝ)) ≤ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|Real.log t| / Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hl2.le) hn
    exact_mod_cast this
  refine ⟨n, hn0, ?_, ?_⟩
  all_goals
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have hb : |Real.log t| / n < Real.log 2 := by
      rw [div_lt_iff₀ hnr]; rw [div_lt_iff₀ hl2] at hn; linarith
    have hpos : 0 < t ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos ht _
    have hlog : Real.log (t ^ (1 / (n : ℝ))) = Real.log t / n := by
      rw [Real.log_rpow ht]; ring
    have habs := abs_lt.1 (lt_of_le_of_lt (by rw [abs_div, abs_of_pos hnr]) hb :
      |Real.log t / n| < Real.log 2)
  · rw [← Real.log_le_log_iff (by norm_num) hpos, hlog]
    have : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
    linarith [habs.1]
  · rw [← Real.log_le_log_iff hpos (by norm_num), hlog]
    linarith [habs.2]

end QEAux

open MasulloGRH QEAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (k : Subgroup G) (hk : IsGoodSubgroup k) :
    ∃ (a n r s : ℕ) (d : Fin s → ℕ)
      (π₀ : (⊤ : Subgroup (G ⧸ k)) →* Multiplicative (ElemGroup a n r s d)),
      IsStructuralPair (⊤ : Subgroup (G ⧸ k)) ⊥ ∧ IsElemPresentation ⊤ ⊥ π₀ := by
  haveI : IsClosed (k : Set G) := hk.1
  have hmod := hm.1
  let C : Set G := m ⁻¹' Set.Icc (1 / 2) 2
  have hC : IsCompact C := hmod.proper _ _ (by norm_num)
  have h1 : m 1 = 1 := by
    have h := hmod.map_mul 1 1
    rw [mul_one] at h
    have hp := hmod.pos 1
    nlinarith
  -- `C` generates `G`
  have hgen : Subgroup.closure C = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨n, hn0, hlo, hhi⟩ := exists_root (m g) (hmod.pos g)
    obtain ⟨h, hh⟩ := hm.2 _ (Real.rpow_pos_of_pos (hmod.pos g) (1 / (n : ℝ)))
    have hpow : ∀ j : ℕ, m (h ^ j) = m h ^ j := by
      intro j; induction j with
      | zero => simp [h1]
      | succ j ih => rw [pow_succ, hmod.map_mul, ih, pow_succ]
    have hhn : m (h ^ n) = m g := by
      rw [hpow, hh, ← Real.rpow_natCast, ← Real.rpow_mul (hmod.pos g).le]
      rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn0.ne'), Real.rpow_one]
    have hinv : ∀ x, m x⁻¹ = (m x)⁻¹ := by
      intro x
      have := hmod.map_mul x x⁻¹
      rw [mul_inv_cancel, h1] at this
      field_simp [(hmod.pos x).ne']
      linarith
    have hrest : g * (h ^ n)⁻¹ ∈ Subgroup.closure C := by
      apply Subgroup.subset_closure
      show m (g * (h ^ n)⁻¹) ∈ Set.Icc (1 / 2 : ℝ) 2
      rw [hmod.map_mul, hinv, hhn, mul_inv_cancel₀ (hmod.pos g).ne']
      norm_num
    have hhC : h ∈ Subgroup.closure C := Subgroup.subset_closure (show m h ∈ Set.Icc _ _ by
      rw [hh]; exact ⟨hlo, hhi⟩)
    have := Subgroup.mul_mem _ hrest (Subgroup.pow_mem _ hhC n)
    simpa using this
  -- the image in `G ⧸ k`
  let q : G →* G ⧸ k := QuotientGroup.mk' k
  have hq : Continuous q := continuous_quot_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hcg : IsCompactlyGeneratedSubgroup (⊤ : Subgroup (G ⧸ k)) := by
    refine ⟨q '' C, hC.image hq, fun _ _ => trivial, ⟨q '' (m ⁻¹' Set.Ioo (1 / 2) 2), ?_, ?_⟩, ?_⟩
    · refine (hqo _ ((isOpen_Ioo).preimage hmod.continuous)).mem_nhds ⟨1, ?_, map_one q⟩
      show m 1 ∈ Set.Ioo (1 / 2 : ℝ) 2
      rw [h1]; norm_num
    · rintro _ ⟨⟨x, hx, rfl⟩, -⟩
      exact ⟨x, Set.Ioo_subset_Icc_self hx, rfl⟩
    · rw [← MonoidHom.map_closure, hgen, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective k)
  have hbot : IsGoodSubgroup (⊥ : Subgroup (G ⧸ k)) := by
    refine ⟨?_, ?_, ⊤, ?_, quotient_goodSubgroup_dual_compactlyGenerated G k hk⟩
    · show IsClosed ((⊥ : Subgroup (G ⧸ k)) : Set (G ⧸ k))
      rw [Subgroup.coe_bot]; exact isClosed_singleton
    · have : annihilator (⊥ : Subgroup (G ⧸ k)) = Set.univ := by
        ext χ; simp [annihilator]
      rw [this]; exact isOpen_univ
    · ext χ; simp [annihilator]
  have hs : IsStructuralPair (⊤ : Subgroup (G ⧸ k)) ⊥ :=
    ⟨by rw [Subgroup.coe_top]; exact isOpen_univ, hcg, hbot, bot_le⟩
  obtain ⟨a, n, r, s, d, π₀, hπ₀⟩ := exists_elemPresentation_of_isStructuralPair (G ⧸ k) ⊤ ⊥ hs
  exact ⟨a, n, r, s, d, π₀, hs, hπ₀⟩
