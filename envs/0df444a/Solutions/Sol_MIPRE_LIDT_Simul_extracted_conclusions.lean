-- Prove2me | solution 1 for MIPRE.LIDT.Simul.extracted_conclusions
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:34:02.694982+00:00
-- url     : https://prove2.me/submissions/10d4074d-41c1-41c3-a6d4-f3c51a4653df

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (solution of MIPRE.LIDT.Simul.extracted_conclusions);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_LIDT_Simul_inconsistency_extract_left_le
import Theorems.Thm_MIPRE_LIDT_Simul_inconsistency_extract_right_le
import Theorems.Thm_MIPRE_LIDT_Simul_inconsistency_map_le
import Theorems.Thm_MIPRE_POVM_map_map

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
theorem sum_uniform_one (X : Type*) [Fintype X] [Nonempty X] : ∑ x, uniform X x = 1 := by
  simp [uniform, Finset.card_univ]
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem extractPM_toPOVM (hd : 1 ≤ d) (hr : r ≤ K) {n : Type*} [Fintype n] [DecidableEq n]
    (R : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix n n ℂ)) :
    (extractPM hd hr R).toPOVM () = (R.toPOVM ()).map (extract hd hr) := by
  classical
  unfold extractPM
  convert ProjectiveMeasurement.toPOVM_ofIsPVM _ _ ()
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem evalTuplePOVM_extractPM (hd : 1 ≤ d) (hr : r ≤ K) {n : Type*} [Fintype n]
    [DecidableEq n]
    (R : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix n n ℂ)) (y : Point F m) :
    evalTuplePOVM (extractPM hd hr R) y = (R.toPOVM ()).map fun g => extEval hd hr g y := by
  rw [evalTuplePOVM, extractPM_toPOVM, POVM.map_map]
  rfl
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution (hd : 1 ≤ d) (hr : r ≤ K) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (A : Point F m → POVM (Fin r → F) dA)
    (B : Point F m → POVM (Fin r → F) dB)
    (RA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dA dA ℂ))
    (RB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix dB dB ℂ)) {δ : ℝ}
    (h1 : inconsistency (uniform (Point F (K + m))) ψ (combPOVM hd A) (evalPOVM RB) ≤ δ)
    (h2 : inconsistency (uniform (Point F (K + m))) ψ (evalPOVM RA) (combPOVM hd B) ≤ δ)
    (h3 : inconsistency (uniform Unit) ψ (fun _ => RA.toPOVM ()) (fun _ => RB.toPOVM ()) ≤ δ) :
    inconsistency (uniform (Point F m)) ψ A (evalTuplePOVM (extractPM hd hr RB))
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform (Point F m)) ψ (evalTuplePOVM (extractPM hd hr RA)) B
        ≤ δ + (K + m) * d / Fintype.card F ∧
      inconsistency (uniform Unit) ψ (fun _ => (extractPM hd hr RA).toPOVM ())
        (fun _ => (extractPM hd hr RB).toPOVM ()) ≤ δ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := inconsistency_extract_right_le hd hr hψ A (RB.toPOVM ())
    have heq : (fun y => evalTuplePOVM (extractPM hd hr RB) y)
        = fun y => (RB.toPOVM ()).map fun g => extEval hd hr g y :=
      funext fun y => evalTuplePOVM_extractPM hd hr RB y
    rw [show evalTuplePOVM (extractPM hd hr RB) = fun y => evalTuplePOVM (extractPM hd hr RB) y
      from rfl, heq]
    exact h.trans (by unfold combPOVM evalPOVM at h1; linarith)
  · have h := inconsistency_extract_left_le hd hr hψ (RA.toPOVM ()) B
    have heq : (fun y => evalTuplePOVM (extractPM hd hr RA) y)
        = fun y => (RA.toPOVM ()).map fun g => extEval hd hr g y :=
      funext fun y => evalTuplePOVM_extractPM hd hr RA y
    rw [show evalTuplePOVM (extractPM hd hr RA) = fun y => evalTuplePOVM (extractPM hd hr RA) y
      from rfl, heq]
    exact h.trans (by unfold combPOVM evalPOVM at h2; linarith)
  · rw [extractPM_toPOVM, extractPM_toPOVM]
    exact (inconsistency_map_le (fun _ => by simp only [uniform]; positivity)
      (sum_uniform_one Unit) hψ (fun _ => RA.toPOVM ()) (fun _ => RB.toPOVM ())
      (extract hd hr)).trans h3
end MIPRE.LIDT.Simul
