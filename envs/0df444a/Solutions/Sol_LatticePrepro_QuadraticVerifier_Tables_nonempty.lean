-- Prove2me | solution 1 for LatticePrepro.QuadraticVerifier.Tables.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:19:33.90391+00:00
-- url     : https://prove2.me/submissions/9f62af61-a2e7-40aa-a842-4aa598b01b21

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT_Ext
import Definitions.Def_LatticePrepro_Explicit
import Theorems.Thm_LatticePrepro_exists_base
import Theorems.Thm_LatticePrepro_exists_explicit_momentRepresentation

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier
namespace LatticePrepro.QuadraticVerifier.Tables end LatticePrepro.QuadraticVerifier.Tables

namespace LatticePrepro

lemma momentAxes_spec {δ : ℝ} (hδ1 : δ < 1) :
    1 ≤ momentAxes δ ∧ δ * (momentAxes δ + 1) < momentAxes δ := by
  refine ⟨by unfold momentAxes; omega, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hm : δ / (1 - δ) < momentAxes δ := by
    unfold momentAxes
    push_cast
    linarith [Nat.le_ceil (δ / (1 - δ))]
  rw [div_lt_iff₀ h1δ] at hm
  nlinarith

end LatticePrepro

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} [hp : Fact p.Prime]

namespace Tables

variable {V : QuadraticVerifier p} {δ : ℝ}

/-- Tables exist for every verifier with at least two assignment coordinates (the choice of the
base in the proof of Theorem 4.8, and Theorem A.8). -/
private theorem nonempty (V : QuadraticVerifier p) (hS : 2 ≤ V.S) {δ : ℝ} (hδ1 : δ < 1) :
    Nonempty (V.Tables δ) := by
  have hm := (momentAxes_spec hδ1).1
  have hN1 : 1 ≤ Fintype.card V.TblIdx := Fintype.card_pos_iff.mpr ⟨Sum.inl V.mainIdx⟩
  have hg : 1 ≤ (V.S + 1) ^ gapExp p δ := Nat.one_le_pow _ _ (by omega)
  obtain ⟨B, hB2, hYB, hBY⟩ :=
    exists_base (Y := 8 * Fintype.card V.TblIdx * (V.S + 1) ^ gapExp p δ) hm
      (Nat.mul_pos (Nat.mul_pos (by norm_num) hN1) hg)
  obtain ⟨E⟩ := exists_explicit_momentRepresentation p V.S (momentAxes δ) B hS hm hB2
  exact ⟨⟨B, hB2, hYB, hBY, E⟩⟩

end Tables

end QuadraticVerifier

end LatticePrepro

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [hp : Fact p.Prime]
open LatticePrepro.QuadraticVerifier.Tables
variable {V : QuadraticVerifier p} {δ : ℝ}
theorem solution (V : QuadraticVerifier p) (hS : 2 ≤ V.S) {δ : ℝ} (hδ1 : δ < 1) :
    Nonempty (V.Tables δ) :=
  @LatticePrepro.QuadraticVerifier.Tables.nonempty p _ V hS δ hδ1
