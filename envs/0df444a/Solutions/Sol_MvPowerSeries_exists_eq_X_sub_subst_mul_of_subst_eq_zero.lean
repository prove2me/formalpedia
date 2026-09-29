-- Prove2me | solution 1 for MvPowerSeries.exists_eq_X_sub_subst_mul_of_subst_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7972471e-ce26-5e95-ba84-3370bd63f450

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero

set_option autoImplicit false

universe u

open MvPowerSeries

namespace FactorThmGC7

variable {k : Type u} [CommRing k]

noncomputable abbrev Sb (φ : PowerSeries k) : Fin 2 → PowerSeries k := ![(PowerSeries.X : PowerSeries k), φ]

theorem hasSubst_Sb {φ : PowerSeries k} (hφ : PowerSeries.constantCoeff φ = 0) : HasSubst (Sb φ) := by
  apply hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  · show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0
    exact PowerSeries.constantCoeff_X
  · show MvPowerSeries.constantCoeff φ = 0
    exact hφ

end FactorThmGC7

open FactorThmGC7 in
theorem solution
    {R : Type u} [CommRing R] (f : MvPowerSeries (Fin 2) R)
    (φ : PowerSeries R) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (hroot : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), φ] f = 0) :
    ∃ M : MvPowerSeries (Fin 2) R,
      f = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ) * M := by
  classical
  set φX : MvPowerSeries (Fin 2) R := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ with hφX

  obtain ⟨Q, hQ⟩ := MvPowerSeries.exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero R φ hφ0 f

  have hb : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) :=
    hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_X 0)
  have hcomp : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) R), φX] f =
      MvPowerSeries.subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R))
        (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), φ] f) := by
    rw [subst_comp_subst_apply (hasSubst_Sb hφ0) hb]
    congr 1
    funext s
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => l.elim0) j) s
    · show (X 0 : MvPowerSeries (Fin 2) R) = subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (Sb φ 0)
      simp only [Sb, Matrix.cons_val_zero]
      exact (subst_X hb ()).symm
    · show φX = subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (Sb φ 1)
      simp only [Sb, Matrix.cons_val_one, Matrix.head_cons]
      rw [hφX, PowerSeries.subst_def]
      rfl
  have hrem : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) R), φX] f = 0 := by
    rw [hcomp, hroot, ← coe_substAlgHom hb, map_zero]
  exact ⟨Q, by rw [hQ, hrem, add_zero]⟩

end S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero
end P2MW
export P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero (solution)
