-- Prove2me | solution 1 for NumberField.Units.exists_forall_abs_two_mul_log_add_log_sub_div_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/372c3a23-dfae-5a6e-81c9-9e2780793bfb

import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Units_exists_forall_abs_two_mul_log_add_log_sub_div_le

set_option autoImplicit false

open NumberField NumberField.Units NumberField.InfinitePlace

theorem solution
    (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ r : InfinitePlace F → ℝ, (∀ w, 0 < r w) →
      ∃ ε : (𝓞 F)ˣ, ∀ w : InfinitePlace F,
        |2 * Real.log (w (algebraMap (𝓞 F) F ε)) + Real.log (r w)
            - (∑ w' : InfinitePlace F, (w'.mult : ℝ) * Real.log (r w')) / (Module.finrank ℚ F)| ≤ C := by
  classical

  set b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F) with hb
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.1 (ZSpan.fundamentalDomain_isBounded b)
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ z ∈ ZSpan.fundamentalDomain b, ‖z‖ ≤ R := fun z hz => (hR₀ z hz).trans (le_max_left _ _)
  have hRnn : 0 ≤ R := le_max_right _ _
  set N : ℕ := Fintype.card (InfinitePlace F) with hN
  refine ⟨4 * R * (N + 1), fun r hr => ?_⟩

  set t : ℝ := (∑ w' : InfinitePlace F, ((w'.mult : ℝ)) * Real.log (r w')) / (Module.finrank ℚ F) with ht

  set y : dirichletUnitTheorem.logSpace F :=
    fun w => (w.1.mult : ℝ) * (Real.log (r w.1) - t) / 2 with hy
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b y

  have hvL : (v : dirichletUnitTheorem.logSpace F) ∈ unitLattice F := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice F) (basisUnitLattice F)]
    exact v.2
  obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hvL
  set ε : (𝓞 F)ˣ := Additive.toMul u with hε
  have hcomp : ∀ w : {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀},
      (v : dirichletUnitTheorem.logSpace F) w = (w.1.mult : ℝ) * Real.log (w.1 (algebraMap (𝓞 F) F ε)) := by
    intro w
    rw [← hu]
    exact dirichletUnitTheorem.logEmbedding_component (Additive.toMul u) w

  set D : InfinitePlace F → ℝ := fun w =>
    2 * Real.log (w (algebraMap (𝓞 F) F ε)) + Real.log (r w) - t with hD
  refine ⟨ε, fun w => ?_⟩
  show |D w| ≤ 4 * R * (N + 1)

  have hoff : ∀ w : {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀}, |D w.1| ≤ 2 * R := by
    intro w
    have h1 : ‖(v +ᵥ y) w‖ ≤ R := (norm_le_pi_norm _ w).trans (hR _ hv)
    have h1' : (v +ᵥ y) w = (v : dirichletUnitTheorem.logSpace F) w + y w := rfl
    rw [h1', Real.norm_eq_abs, hcomp w] at h1
    simp only [hy] at h1
    have hm : (1 : ℝ) ≤ w.1.mult := InfinitePlace.one_le_mult
    have hkey : (w.1.mult : ℝ) * Real.log (w.1 (algebraMap (𝓞 F) F ε)) +
        (w.1.mult : ℝ) * (Real.log (r w.1) - t) / 2 = (w.1.mult : ℝ) / 2 * D w.1 := by
      simp only [hD]; ring
    have hmpos : (0 : ℝ) < w.1.mult := Nat.cast_pos.mpr InfinitePlace.mult_pos
    rw [hkey, abs_mul, abs_of_pos (by positivity)] at h1
    calc |D w.1| = (2 / (w.1.mult : ℝ)) * ((w.1.mult : ℝ) / 2 * |D w.1|) := by
          field_simp
      _ ≤ (2 / (w.1.mult : ℝ)) * R := by gcongr
      _ ≤ 2 * R := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith

  have hsum : ∑ w : InfinitePlace F, (w.mult : ℝ) * D w = 0 := by
    have h1 : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F ε)) = 0 :=
      Units.sum_mult_mul_log ε
    have h2 : ∑ w : InfinitePlace F, (w.mult : ℝ) = Module.finrank ℚ F := by
      exact_mod_cast InfinitePlace.sum_mult_eq
    have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    simp only [hD, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    have h3 : ∑ x : InfinitePlace F, (x.mult : ℝ) * (2 * Real.log (x (algebraMap (𝓞 F) F ε)))
        = 2 * ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (x (algebraMap (𝓞 F) F ε)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have h4 : ∑ x : InfinitePlace F, (x.mult : ℝ) * Real.log (r x) = t * Module.finrank ℚ F := by
      rw [ht, div_mul_cancel₀ _ hn]
    rw [h3, h1, mul_zero, zero_add, h4, h2]
    ring

  have h2R : 2 * R ≤ 4 * R * (N + 1) := by nlinarith [hRnn, (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  by_cases hw : w = dirichletUnitTheorem.w₀
  · subst hw
    have hsplit := Fintype.sum_eq_add_sum_subtype_ne (fun w : InfinitePlace F => (w.mult : ℝ) * D w)
      (dirichletUnitTheorem.w₀ : InfinitePlace F)
    rw [hsum] at hsplit
    have hm : (1 : ℝ) ≤ (dirichletUnitTheorem.w₀ : InfinitePlace F).mult := InfinitePlace.one_le_mult
    have hm0pos : (0 : ℝ) < (dirichletUnitTheorem.w₀ : InfinitePlace F).mult := Nat.cast_pos.mpr InfinitePlace.mult_pos
    have hD0 : |D dirichletUnitTheorem.w₀| ≤ |((dirichletUnitTheorem.w₀ : InfinitePlace F).mult : ℝ) * D dirichletUnitTheorem.w₀| := by
      rw [abs_mul, abs_of_pos hm0pos]
      exact le_mul_of_one_le_left (abs_nonneg _) hm
    refine hD0.trans ?_
    rw [show ((dirichletUnitTheorem.w₀ : InfinitePlace F).mult : ℝ) * D dirichletUnitTheorem.w₀
        = -∑ w : {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀}, ((w.1.mult : ℝ) * D w.1) by linarith,
      abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ w : {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀}, |(w.1.mult : ℝ) * D w.1| ≤ 2 * (2 * R) := by
      intro w
      rw [abs_mul, abs_of_pos (Nat.cast_pos.mpr InfinitePlace.mult_pos)]
      have hm2 : (w.1.mult : ℝ) ≤ 2 := by
        have : w.1.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> omega
        exact_mod_cast this
      exact mul_le_mul hm2 (hoff w) (abs_nonneg _) (by norm_num)
    calc ∑ w : {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀}, |(w.1.mult : ℝ) * D w.1|
        ≤ ∑ _w : {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀}, 2 * (2 * R) := Finset.sum_le_sum fun w _ => hterm w
      _ = (Fintype.card {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀} : ℝ) * (2 * (2 * R)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * (2 * R)) := by
          gcongr
          exact_mod_cast (Fintype.card_subtype_le _)
      _ ≤ 4 * R * (N + 1) := by nlinarith [hRnn, (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  · exact (hoff ⟨w, hw⟩).trans h2R

end S_NumberField_Units_exists_forall_abs_two_mul_log_add_log_sub_div_le
end P2MW
export P2MW.S_NumberField_Units_exists_forall_abs_two_mul_log_add_log_sub_div_le (solution)
