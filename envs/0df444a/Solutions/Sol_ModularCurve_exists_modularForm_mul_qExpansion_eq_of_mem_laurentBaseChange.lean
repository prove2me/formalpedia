-- Prove2me | solution 1 for ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fb4dac89-153a-559e-ab17-bff06c476255

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "divisorExpansions modularFunctionFieldFull coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange mem_laurentBaseChange_iff exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq"
namespace RatioFieldOfLevel
p2m_open "ModularCurve"

variable {N : ℕ}

abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem qL_mul {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N), PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N), PowerSeries.coe_add]

theorem qL_one : qL (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)) =
      algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem one_ne_zero' : (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) ≠ 0 := by
  intro h
  have := congrArg
    (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) 0 => (F : ℍ → ℂ) UpperHalfPlane.I) h
  simp [ModularForm.one_coe_eq_one] at this

theorem mul_ne_zero' {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  have h := congrArg (qL (N := N)) hfg
  rw [qL_mul] at h
  have h0 : qL (0 : ModularForm (CongruenceSubgroup.Gamma0 N) (a + b)) = 0 := by
    simp only [qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]
  rw [h0] at h
  exact (mul_ne_zero (qL_ne_zero f hf) (qL_ne_zero g hg)) h

variable (N) in

def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧ x * qL h = qL g

theorem isRatio_algebraMap (c : ℂ) : IsRatio N (algebraMap ℂ (LaurentSeries ℂ) c) :=
  ⟨0, c • 1, 1, one_ne_zero', by rw [qL_one, mul_one, qL_const]⟩

theorem isRatio_one : IsRatio N 1 := by
  simpa using isRatio_algebraMap (N := N) 1

theorem IsRatio.mul {x y : LaurentSeries ℂ} (hx : IsRatio N x) (hy : IsRatio N y) :
    IsRatio N (x * y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul g', h.mul h', mul_ne_zero' h h' hh hh', ?_⟩
  rw [qL_mul, qL_mul, ← hxe, ← hye]; ring

theorem IsRatio.add {x y : LaurentSeries ℂ} (hx : IsRatio N x) (hy : IsRatio N y) :
    IsRatio N (x + y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul h' + ModularForm.mcast (add_comm b a) (g'.mul h), h.mul h',
    mul_ne_zero' h h' hh hh', ?_⟩
  have hc : qL (ModularForm.mcast (add_comm b a) (g'.mul h)) = qL g' * qL h := by
    rw [← qL_mul]; simp only [qL, ModularForm.coe_mcast]
  rw [qL_add, qL_mul, qL_mul, hc, ← hxe, ← hye]; ring

theorem IsRatio.neg {x : LaurentSeries ℂ} (hx : IsRatio N x) : IsRatio N (-x) := by
  have : -x = algebraMap ℂ (LaurentSeries ℂ) (-1) * x := by rw [map_neg, map_one]; ring
  rw [this]
  exact (isRatio_algebraMap (-1)).mul hx

theorem IsRatio.inv {x : LaurentSeries ℂ} (hx : IsRatio N x) : IsRatio N x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using isRatio_algebraMap (N := N) 0
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  have hg : g ≠ 0 := by
    intro hg0
    have : qL g = 0 := by
      simp only [hg0, qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ),
        PowerSeries.coe_zero]
    rw [this] at hxe
    exact (mul_ne_zero hx0 (qL_ne_zero h hh)) hxe
  refine ⟨a, h, g, hg, ?_⟩
  rw [← hxe, mul_comm x, mul_comm x⁻¹, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

theorem coeffEmb_algebraMap (r : ℚ) :
    coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℂ (LaurentSeries ℂ) (r : ℂ) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
    coeffMap_single]
  simp

variable (N) in

theorem isRatio_coeffEmb [NeZero N] {y : LaurentSeries ℚ} (hy : y ∈ modularFunctionFieldFull N) :
    IsRatio N (coeffEmb ℂ y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)
    at hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨r, rfl⟩ | ⟨d, hd0, hdN, rfl⟩
      · rw [coeffEmb_algebraMap]; exact isRatio_algebraMap _
      · haveI := hd0
        obtain ⟨k, g, h, hh, he⟩ :=
          ModularCurve.exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq N d hdN
        exact ⟨k, g, h, hh, he⟩
  | one => simpa using isRatio_one (N := N)
  | add x y _ _ hx hy => simpa using hx.add hy
  | neg x _ hx => simpa using hx.neg
  | inv x _ hx => simpa using hx.inv
  | mul x y _ _ hx hy => simpa using hx.mul hy

variable (N) in
theorem isRatio_of_mem [NeZero N] {x : LaurentSeries ℂ}
    (hx : x ∈ laurentBaseChange ℂ (modularFunctionFieldFull N)) : IsRatio N x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨y, hy, rfl⟩
      · exact isRatio_algebraMap c
      · exact isRatio_coeffEmb N hy
  | one => exact isRatio_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end ModularCurve.RatioFieldOfLevel

end

open UpperHalfPlane in
theorem solution (N : ℕ)
    [NeZero N] (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  ModularCurve.RatioFieldOfLevel.isRatio_of_mem N hx

end S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange (solution)
