-- Prove2me | solution 1 for GlobalTheory.finite_units_quot_sq_normed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:05.989077+00:00
-- url     : https://prove2.me/submissions/7be6ce7a-815b-40eb-86c6-e6d92682a9f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPair
import Theorems.Thm_GlobalTheory_isOpenUnits_and_eventually_sq_normed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (R : Type) [NormedCommRing R] [Nontrivial R] [NormedAlgebra F R]
    [Module.Finite F R] (hR : ∀ x : R, x ≠ 0 → IsUnit x) :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by
  classical
  obtain ⟨-, hsq⟩ := isOpenUnits_and_eventually_sq_normed F R
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hsq
  obtain ⟨b, hb0, hb1⟩ := NormedField.exists_norm_lt_one F
  have hρ2 : 0 < ‖b‖ ^ 2 := by positivity
  have : ProperSpace R := FiniteDimensional.proper F R
  let C : Set R := {x | ‖b‖ ^ 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
  have hCc : IsCompact C := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : R)) (r := 1)).subset
        (fun x hx => by simpa using hx.2)
  have hCu : ∀ c ∈ C, IsUnit c := fun c hc => hR c (by
    intro h
    have h1 := hc.1
    rw [h, norm_zero] at h1
    linarith)
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover
    (fun c => {x : R | dist (x * Ring.inverse c) 1 < ε}) (by
      intro c hc
      apply IsOpen.mem_nhds
      · exact isOpen_lt (by fun_prop) continuous_const
      · simp [Ring.mul_inverse_cancel _ (hCu c hc), hε])
  let f : R → Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range := fun x =>
    if h : IsUnit x then QuotientGroup.mk h.unit else 1
  have hsurj : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)) ⊆ f '' (t : Set R) := by
    rintro q -
    induction q using QuotientGroup.induction_on with | H u => ?_
    have hu0 : 0 < ‖(u : R)‖ := norm_pos_iff.mpr u.ne_zero
    have hy : 1 < (‖b‖ ^ 2)⁻¹ := (one_lt_inv₀ hρ2).mpr (by nlinarith [norm_nonneg b])
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu0 hy
    have hb0' : b ≠ 0 := norm_pos_iff.mp hb0
    have hβ0 : b ^ (n + 1) ≠ 0 := zpow_ne_zero _ hb0'
    have hnv : ‖(b ^ (n + 1)) ^ 2 • (u : R)‖ = ‖(u : R)‖ / ((‖b‖ ^ 2)⁻¹) ^ (n + 1) := by
      rw [norm_smul, norm_pow, norm_zpow, _root_.inv_zpow, div_inv_eq_mul, mul_comm, ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_mul, ← _root_.zpow_mul]
      rw [mul_comm (n + 1)]
    have hv : (b ^ (n + 1)) ^ 2 • (u : R) ∈ C := by
      have hpos : 0 < ((‖b‖ ^ 2)⁻¹) ^ n := zpow_pos (by positivity) n
      refine ⟨?_, ?_⟩
      · rw [hnv, zpow_add₀ (by positivity), zpow_one, le_div_iff₀ (by positivity)]
        calc ‖b‖ ^ 2 * (((‖b‖ ^ 2)⁻¹) ^ n * (‖b‖ ^ 2)⁻¹) = ((‖b‖ ^ 2)⁻¹) ^ n := by field_simp
          _ ≤ ‖(u : R)‖ := hn1.le
      · rw [hnv, div_le_one (by positivity)]
        exact hn2
    obtain ⟨c, hct, hcv⟩ := Set.mem_iUnion₂.mp (hcov hv)
    have hcu := hCu c (htC c hct)
    obtain ⟨s, hs⟩ := hball hcv
    have hsU : IsUnit s := by
      have : IsUnit (s ^ 2) := by
        have hic : Ring.inverse c = ↑(hcu.unit⁻¹) := by rw [← Ring.inverse_unit, IsUnit.unit_spec]
        rw [hs, Algebra.smul_def, hic]
        exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hβ0)).map (algebraMap F R) |>.mul u.isUnit).mul
          (hcu.unit⁻¹).isUnit
      exact (isUnit_pow_iff two_ne_zero).mp this
    refine ⟨c, hct, ?_⟩
    simp only [f, dif_pos hcu]
    rw [QuotientGroup.eq, MonoidHom.mem_range]
    let bu : Rˣ := Units.map (algebraMap F R).toMonoidHom (Units.mk0 _ hβ0)
    have hs' : hsU.unit ^ 2 = bu ^ 2 * u * hcu.unit⁻¹ := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec, bu, Units.coe_map,
        Units.val_mk0]
      rw [hs, ← Ring.inverse_unit, IsUnit.unit_spec, Algebra.smul_def, map_pow]
      rfl
    refine ⟨hsU.unit * bu⁻¹, ?_⟩
    rw [powMonoidHom_apply, mul_pow, inv_pow, hs']
    simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  have hfin : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)).Finite :=
    (t.finite_toSet.image f).subset hsurj
  exact Set.finite_univ_iff.mp hfin
end GlobalTheory
