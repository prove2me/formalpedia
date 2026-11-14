-- Prove2me | solution 1 for LatticePrepro.LatticeFamily.latticeDist_eq_infDist
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:07.681902+00:00
-- url     : https://prove2.me/submissions/8f7b30da-9390-4373-bedd-3390ccb55959

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.LatticeFamily end LatticePrepro.LatticeFamily

namespace LatticePrepro

namespace PNorm

lemma norm_nonneg {M : Type} [Fintype M] (pn : PNorm) (v : M → ℝ) : 0 ≤ pn.norm v := by
  cases pn with
  | fin p hp =>
      show 0 ≤ (∑ i, |v i| ^ p) ^ (1 / p)
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _
  | inf =>
      show 0 ≤ ⨆ i, |v i|
      exact Real.iSup_nonneg fun i => abs_nonneg _

end PNorm

end LatticePrepro

namespace LatticePrepro

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (x : X)

lemma dist_nonneg (v : Λ.M → ℤ) : 0 ≤ Λ.dist pn x v := pn.norm_nonneg _

lemma bddBelow_range_dist : BddBelow (Set.range fun v : Λ.lattice => Λ.dist pn x v) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact Λ.dist_nonneg pn x v⟩

theorem latticeDist_le {v : Λ.M → ℤ} (hv : v ∈ Λ.lattice) :
    Λ.latticeDist pn x ≤ Λ.dist pn x v :=
  ciInf_le (Λ.bddBelow_range_dist pn x) ⟨v, hv⟩

end LatticeFamily

end LatticePrepro

namespace LatticePrepro

open scoped ENNReal

open WithLp

namespace PNorm

variable {M : Type} [Fintype M]

/-- `PNorm.norm` is the norm of `PiLp p (fun _ : M => ℝ)`. -/
theorem norm_eq_piLp (pn : PNorm) (v : M → ℝ) :
    pn.norm v = ‖(toLp pn.toENNReal v : PiLp pn.toENNReal fun _ : M => ℝ)‖ := by
  cases pn with
  | fin p hp =>
    have hp0 : 0 < p := by linarith
    have ht : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
    show (∑ i, |v i| ^ p) ^ (1 / p) =
      ‖(toLp (ENNReal.ofReal p) v : PiLp (ENNReal.ofReal p) fun _ : M => ℝ)‖
    rw [PiLp.norm_eq_sum (by rw [ht]; exact hp0)]
    simp only [ht, Real.norm_eq_abs]
  | inf =>
    show (⨆ i, |v i|) = ‖(toLp ⊤ v : PiLp ⊤ fun _ : M => ℝ)‖
    rw [PiLp.norm_eq_ciSup]
    simp only [Real.norm_eq_abs]

end PNorm

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X)

lemma toReal_sub {M : Type} (v w : M → ℤ) : toReal (v - w) = toReal v - toReal w := by
  funext i
  simp [toReal]

/-- `LatticeFamily.dist` is the distance in `PiLp p (fun _ : M => ℝ)`. -/
theorem dist_eq_piLp (pn : PNorm) (x : X) (v : Λ.M → ℤ) :
    Λ.dist pn x v =
      Dist.dist (toLp pn.toENNReal (toReal (Λ.target x)) : PiLp pn.toENNReal fun _ => ℝ)
        (toLp pn.toENNReal (toReal v)) := by
  rw [dist_eq_norm, ← toLp_sub, LatticeFamily.dist, pn.norm_eq_piLp, toReal_sub]

lemma mem_realLattice_iff (w : Λ.M → ℝ) :
    w ∈ Λ.realLattice ↔ ∃ v ∈ Λ.lattice, toReal v = w :=
  Submodule.mem_map

lemma toReal_mem_realLattice {v : Λ.M → ℤ} (hv : v ∈ Λ.lattice) : toReal v ∈ Λ.realLattice :=
  Submodule.mem_map_of_mem hv

/-- `latticeDist` is Mathlib's `Metric.infDist` from the target to the real image of the lattice,
in `PiLp p (fun _ : M => ℝ)`. -/
private theorem latticeDist_eq_infDist (pn : PNorm) (x : X) :
    Λ.latticeDist pn x =
      Metric.infDist (toLp pn.toENNReal (toReal (Λ.target x)) : PiLp pn.toENNReal fun _ => ℝ)
        (toLp pn.toENNReal '' (Λ.realLattice : Set (Λ.M → ℝ))) := by
  rw [Metric.infDist_eq_iInf, LatticeFamily.latticeDist]
  set t : PiLp pn.toENNReal fun _ : Λ.M => ℝ := toLp pn.toENNReal (toReal (Λ.target x)) with ht
  set s : Set (PiLp pn.toENNReal fun _ : Λ.M => ℝ) :=
    toLp pn.toENNReal '' (Λ.realLattice : Set (Λ.M → ℝ)) with hs
  have : Nonempty s := ⟨⟨toLp pn.toENNReal (toReal 0), toReal 0,
    Λ.toReal_mem_realLattice Λ.lattice.zero_mem, rfl⟩⟩
  have hbdd : BddBelow (Set.range fun y : s => Dist.dist t y) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact _root_.dist_nonneg⟩
  apply le_antisymm
  · refine le_ciInf fun y => ?_
    obtain ⟨y, w, hw, rfl⟩ := y
    obtain ⟨v, hv, rfl⟩ := (Λ.mem_realLattice_iff w).mp hw
    rw [← Λ.dist_eq_piLp pn x v]
    exact Λ.latticeDist_le pn x hv
  · refine le_ciInf fun v => ?_
    rw [Λ.dist_eq_piLp pn x v]
    exact ciInf_le hbdd ⟨toLp pn.toENNReal (toReal v), toReal v, Λ.toReal_mem_realLattice v.2, rfl⟩

end LatticeFamily

end LatticePrepro

open LatticePrepro
open scoped ENNReal
open WithLp
open LatticePrepro.LatticeFamily
variable {X : Type} (Λ : LatticeFamily X)
theorem solution (pn : PNorm) (x : X) :
    Λ.latticeDist pn x =
      Metric.infDist (toLp pn.toENNReal (toReal (Λ.target x)) : PiLp pn.toENNReal fun _ => ℝ)
        (toLp pn.toENNReal '' (Λ.realLattice : Set (Λ.M → ℝ))) :=
  @LatticePrepro.LatticeFamily.latticeDist_eq_infDist X Λ pn x
