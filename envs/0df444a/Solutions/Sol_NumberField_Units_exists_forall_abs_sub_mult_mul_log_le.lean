-- Prove2me | solution 1 for NumberField.Units.exists_forall_abs_sub_mult_mul_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7f3aa063-057f-5fb6-a649-4ae782d88c57

import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open Module

open scoped Classical

noncomputable section

namespace M4aP1R
namespace UnitBalance

variable (K : Type*) [Field K] [NumberField K]

theorem exists_norm_sub_logEmbedding_le :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ t' : logSpace K, ∃ u : (𝓞 K)ˣ,
      ‖t' - logEmbedding K (Additive.ofMul u)‖ ≤ R₀ := by
  classical
  let L : Submodule ℤ (logSpace K) := unitLattice K
  let b := Module.Free.chooseBasis ℤ L
  let B : Basis _ ℝ (logSpace K) := b.ofZLatticeBasis ℝ L
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun t' => ?_⟩

  have hv : t' - ZSpan.fract B t' ∈ L := by
    have h1 : t' - ZSpan.fract B t' = (ZSpan.floor B t' : logSpace K) := by
      rw [ZSpan.fract_apply]; abel
    rw [h1]
    exact (b.ofZLatticeBasis_span ℝ L).le (ZSpan.floor B t').2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hv
  refine ⟨Additive.toMul x, ?_⟩
  have hx' : logEmbedding K (Additive.ofMul (Additive.toMul x)) = t' - ZSpan.fract B t' := by
    rw [ofMul_toMul]; exact hx
  rw [hx', sub_sub_cancel]
  exact ZSpan.norm_fract_le B t'

end M4aP1R.UnitBalance

open M4aP1R.UnitBalance in

theorem M4aP1R.UnitBalance.exists_forall_abs_sub_mult_mul_log_le_impl (K : Type*) [Field K]
    [NumberField K] : ∃ R : ℝ, ∀ t : NumberField.InfinitePlace K → ℝ, ∑ w, t w = 0 →
      ∃ u : (NumberField.RingOfIntegers K)ˣ, ∀ w : NumberField.InfinitePlace K,
        |t w - (w.mult : ℝ) * Real.log (w (u : K))| ≤ R := by
  classical
  obtain ⟨R₀, hR₀, hcov⟩ := exists_norm_sub_logEmbedding_le K
  refine ⟨(Fintype.card (InfinitePlace K)) * R₀, fun t ht => ?_⟩

  obtain ⟨u, hu⟩ := hcov (fun w => t w.val)
  refine ⟨u, fun w => ?_⟩

  have hdev : ∀ w' : {w : InfinitePlace K // w ≠ w₀},
      |t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K))| ≤ R₀ := by
    intro w'
    have h1 := norm_le_pi_norm ((fun w => t w.val) - logEmbedding K (Additive.ofMul u)) w'
    rw [Pi.sub_apply, logEmbedding_component, Real.norm_eq_abs] at h1
    exact h1.trans hu
  have hcard1 : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hcard2 : (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ)
      ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_subtype_le _
  by_cases hw : w = w₀
  ·
    subst hw
    have hsumt : t w₀ + ∑ w' : {w : InfinitePlace K // w ≠ w₀}, t w'.val = 0 := by
      rw [← Fintype.sum_eq_add_sum_subtype_ne t w₀]; exact ht
    have hsumu : ∑ w' : {w : InfinitePlace K // w ≠ w₀},
        (w'.val.mult : ℝ) * Real.log (w'.val (u : K))
          = -((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ (u : K)) := by
      have := sum_logEmbedding_component u
      simpa [logEmbedding_component] using this
    have hkey : t w₀ - ((w₀ : InfinitePlace K).mult : ℝ) * Real.log (w₀ (u : K))
        = -∑ w' : {w : InfinitePlace K // w ≠ w₀},
            (t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K))) := by
      rw [Finset.sum_sub_distrib, hsumu]; linarith
    rw [hkey, abs_neg]
    calc |∑ w' : {w : InfinitePlace K // w ≠ w₀},
            (t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K)))|
        ≤ ∑ w' : {w : InfinitePlace K // w ≠ w₀},
            |t w'.val - (w'.val.mult : ℝ) * Real.log (w'.val (u : K))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w' : {w : InfinitePlace K // w ≠ w₀}, R₀ := Finset.sum_le_sum fun w' _ => hdev w'
      _ = (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ) * R₀ := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * R₀ :=
          mul_le_mul_of_nonneg_right hcard2 hR₀
  · calc |t w - (w.mult : ℝ) * Real.log (w (u : K))|
        ≤ R₀ := hdev ⟨w, hw⟩
      _ = 1 * R₀ := (one_mul _).symm
      _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * R₀ := mul_le_mul_of_nonneg_right hcard1 hR₀

theorem solution (K : Type*) [Field K]
    [NumberField K] : ∃ R : ℝ, ∀ t : NumberField.InfinitePlace K → ℝ, ∑ w, t w = 0 →
      ∃ u : (NumberField.RingOfIntegers K)ˣ, ∀ w : NumberField.InfinitePlace K,
        |t w - (w.mult : ℝ) * Real.log (w (u : K))| ≤ R := by
  exact M4aP1R.UnitBalance.exists_forall_abs_sub_mult_mul_log_le_impl K

end
end S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le
end P2MW
export P2MW.S_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le (solution)
