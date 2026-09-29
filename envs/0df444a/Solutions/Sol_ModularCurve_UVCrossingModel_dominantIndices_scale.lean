-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.dominantIndices_scale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6acd397f-7560-57be-83af-c08d7348bff0

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_dominantIndices_scale

set_option maxHeartbeats 800000
set_option autoImplicit false

universe u

namespace DominantScaleSol

open ModularCurve ModularCurve.UVCrossingModel

variable {W : Type u} [CommRing W]

theorem enat_map_iInf_eq_of_monotone {ι : Type*} [Nonempty ι] (g : ℕ∞ → ℕ∞) (hg : Monotone g) (f : ι → ℕ∞) :
    g (⨅ i, f i) = ⨅ i, g (f i) := by
  apply le_antisymm
  · exact le_iInf fun i => hg (iInf_le f i)
  · obtain ⟨i, hi⟩ := ciInf_mem f
    rw [← hi]
    exact iInf_le (fun i => g (f i)) i

theorem enat_natCast_mul_left_cancel (q : ℕ) (hq : 1 ≤ q) {a b : ℕ∞} (h : (q : ℕ∞) * a = (q : ℕ∞) * b) :
    a = b := by
  have hq0 : (q : ℕ∞) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe b =>
      exfalso
      rw [ENat.mul_top hq0, ← Nat.cast_mul] at h
      exact ENat.coe_ne_top _ h.symm
  | coe a =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.mul_top hq0, ← Nat.cast_mul] at h
      exact ENat.coe_ne_top _ h
    | coe b =>
      rw [← Nat.cast_mul, ← Nat.cast_mul] at h
      have h' : q * a = q * b := by exact_mod_cast h
      exact_mod_cast Nat.eq_of_mul_eq_mul_left (by omega) h'

theorem annulusWeight_scale (q E t : ℕ) (d : Fin 2 →₀ ℕ) :
    annulusWeight (q * E) (q * t) d = q * annulusWeight E t d := by
  simp only [annulusWeight, ← mul_tsub]; ring

theorem repGaussOrder_scale (v : W → ℕ∞) (E t q : ℕ) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder (fun w => (q : ℕ∞) * v w) (q * E) (q * t) F = (q : ℕ∞) * repGaussOrder v E t F := by
  simp only [repGaussOrder, annulusWeight_scale, Nat.cast_mul, ← mul_add]
  exact (enat_map_iInf_eq_of_monotone (fun x => (q : ℕ∞) * x) (fun a b h => mul_le_mul_right h _) _).symm

theorem termOrder_scale (v : W → ℕ∞) (E t q : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab n = (q : ℕ∞) * termOrder v E t ab n := by
  simp only [termOrder, annulusWeight_scale, Nat.cast_mul, mul_add]

theorem dominantIndices_scale (v : W → ℕ∞) (E t q : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab = dominantIndices v E t ab := by
  ext n
  simp only [dominantIndices, Set.mem_setOf_eq, termOrder_scale, repGaussOrder_scale]
  exact ⟨enat_natCast_mul_left_cancel q hq, fun h => by rw [h]⟩

end DominantScaleSol

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem solution
    {W : Type u} [CommRing W] (v : W → ℕ∞) (E t q : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab = dominantIndices v E t ab :=
  DominantScaleSol.dominantIndices_scale v E t q hq ab

end S_ModularCurve_UVCrossingModel_dominantIndices_scale
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_dominantIndices_scale (solution)
