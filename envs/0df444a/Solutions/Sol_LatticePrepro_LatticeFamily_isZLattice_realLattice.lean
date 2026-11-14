-- Prove2me | solution 1 for LatticePrepro.LatticeFamily.isZLattice_realLattice
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:08.427196+00:00
-- url     : https://prove2.me/submissions/65766e27-2e78-4a9b-bb2f-ea53e32159d0

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

open scoped ENNReal

open WithLp

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X)

lemma toReal_mem_realLattice {v : Λ.M → ℤ} (hv : v ∈ Λ.lattice) : toReal v ∈ Λ.realLattice :=
  Submodule.mem_map_of_mem hv

/-- A lattice containing `N · ℤ^M` for some `N > 0` is an `IsZLattice`: a discrete `ℤ`-submodule
of `ℝ^M` spanning `ℝ^M` (the full-rank condition of Lemma 3.12). -/
private theorem isZLattice_realLattice {N : ℕ} (hN : 0 < N)
    (h : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice) : IsZLattice ℝ Λ.realLattice := by
  refine ⟨eq_top_iff.mpr ?_⟩
  rw [← (Pi.basisFun ℝ Λ.M).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hmem : toReal ((N : ℤ) • Pi.single i 1) ∈ Λ.realLattice :=
    Λ.toReal_mem_realLattice (h _)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbasis : Pi.basisFun ℝ Λ.M i = (N : ℝ)⁻¹ • toReal ((N : ℤ) • Pi.single i 1) := by
    funext j
    simp only [Pi.basisFun_apply, Pi.smul_apply, toReal, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp [hNr]
  rw [hbasis]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end LatticeFamily

end LatticePrepro

open LatticePrepro
open scoped ENNReal
open WithLp
open LatticePrepro.LatticeFamily
variable {X : Type} (Λ : LatticeFamily X)
theorem solution {N : ℕ} (hN : 0 < N)
    (h : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice) : IsZLattice ℝ Λ.realLattice :=
  @LatticePrepro.LatticeFamily.isZLattice_realLattice X Λ N hN h
