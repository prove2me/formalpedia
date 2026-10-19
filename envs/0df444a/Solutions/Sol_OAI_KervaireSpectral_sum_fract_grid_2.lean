-- Prove2me | solution 2 for OAI.KervaireSpectral.sum_fract_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:14:33.179865+00:00
-- url     : https://prove2.me/submissions/06197133-3e05-4569-9b88-ed0ad6b8d9fb

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseGrids.lean:L30-L72
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.sum_fract_grid. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids

-- ---- from OAI.GroupTheory.Kervaire.PhaseGrids ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireSpectral

section

/-- The unnormalized sum of the grid points `j/d`. -/
theorem sum_fin_val_real (d : ℕ) :
    (∑ j : Fin d, (j.val : ℝ)) = (d : ℝ) * ((d : ℝ)-1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- The exact fractional-part grid identity, including values on the cut. -/
theorem sum_fract_grid (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
    (∑ j : Fin d, Int.fract (x + (j.val : ℝ) / d)) =
      ((d : ℝ)-1)/2 + Int.fract ((d : ℝ)*x) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdx : 0 ≤ (d : ℝ)*x := mul_nonneg hdR.le hx.1
  let q : Fin d := ⟨⌊(d : ℝ)*x⌋₊, by
    apply (Nat.floor_lt hdx).mpr
    nlinarith⟩
  let r : ℝ := Int.fract ((d : ℝ)*x)
  have hr0 : 0 ≤ r := Int.fract_nonneg _
  have hr1 : r < 1 := Int.fract_lt_one _
  have hqr : (q.val : ℝ) + r = (d : ℝ)*x := by
    dsimp [q,r]
    rw [natCast_floor_eq_intCast_floor hdx, Int.floor_add_fract]
  have hgrid (j : Fin d) :
      Int.fract (x+(j.val : ℝ)/d) = (r + ((q+j).val : ℝ)) / d := by
    let a : ℕ := (q.val+j.val)/d
    apply Int.fract_eq_iff.mpr
    refine ⟨div_nonneg (add_nonneg hr0 (Nat.cast_nonneg _)) hdR.le, ?_,
      (a : ℤ), ?_⟩
    · apply (div_lt_one hdR).mpr
      have hval : ((q+j).val : ℝ) + 1 ≤ d := by
        exact_mod_cast Nat.succ_le_of_lt (q+j).isLt
      linarith
    · change x + (j.val : ℝ) / d - (r + ((q+j).val : ℝ)) / d = (a : ℝ)
      have hm : (q+j).val + d * a = q.val+j.val :=
        Nat.mod_add_div _ _
      have hmR : ((q+j).val : ℝ) + (d : ℝ)*(a : ℝ) =
          (q.val : ℝ) + j.val := by exact_mod_cast hm
      apply (mul_right_inj' hdR.ne').mp
      field_simp
      nlinarith
  simp_rw [hgrid]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have he : (∑ j : Fin d, ((q+j).val : ℝ)) = ∑ j : Fin d, (j.val : ℝ) :=
    Equiv.sum_comp (Equiv.addLeft q) (fun j : Fin d => (j.val : ℝ))
  rw [he, sum_fin_val_real]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [r]
  field_simp
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open KervaireTraceCalculus KervaireScalarPhase
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder


theorem solution : type_of% @_root_.OAI.KervaireSpectral.sum_fract_grid := @_root_.OAI.KervaireSpectral.sum_fract_grid
