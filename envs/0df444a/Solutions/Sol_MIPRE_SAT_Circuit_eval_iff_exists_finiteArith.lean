-- Prove2me | solution 1 for MIPRE.SAT.Circuit.eval_iff_exists_finiteArith
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:13.899666+00:00
-- url     : https://prove2.me/submissions/ee81e5fe-aee6-44a6-85bf-7d5f88f76239

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FiniteCircuitArithmetization.lean (solution of MIPRE.SAT.Circuit.eval_iff_exists_finiteArith);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Theorems.Thm_MIPRE_SAT_Circuit_eval_routedArith_iff
import Theorems.Thm_MIPRE_SAT_Circuit_routedConsistent_iff
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_congr

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem WellFormed.inputsLt {C : Circuit} (h : C.WellFormed) : C.InputsLt := h.inputs_lt
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem eval_congr (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
    (hx : ∀ i < C.inputs, x i = x' i) : C.eval x = C.eval x' := by
  unfold eval
  split_ifs
  · rfl
  · exact valueAt_congr C hin x x' hx _
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
/-- The routed consistency equations and the output literal characterize
acceptance, using exactly the original input and gate variables. -/
theorem eval_iff_routedConsistent (C : Circuit) (hne : C.gates ≠ []) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ w, C.RoutedConsistent x w ∧ w (C.size - 1) = true := by
  have hsize : 0 < C.size := List.length_pos_iff.mpr hne
  constructor
  · intro h
    refine ⟨C.valueAt x, (routedConsistent_iff C x _).mpr (by simp), ?_⟩
    simpa [Circuit.eval, hne, size] using h
  · rintro ⟨w, hw, ho⟩
    have hvals := (routedConsistent_iff C x w).mp hw
    rw [hvals _ (by omega)] at ho
    simpa [Circuit.eval, hne, size] using ho
end
end MIPRE.SAT.Circuit

namespace MIPRE.LowDegree
noncomputable section
open MvPolynomial
open scoped Classical
variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)
/-- Evaluation after restriction equals evaluation at the zero extension. -/
theorem eval_killCompl (p : MvPolynomial τ F) (x : σ → F) :
    eval x (killCompl hf p) = eval (extendZero hf x) p := by
  have he : (eval x).comp (killCompl hf).toRingHom = eval (extendZero hf x) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        killCompl, aeval_X, eval_X, extendZero]
      split <;> simp
  exact RingHom.congr_fun he p
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
open MvPolynomial
open scoped Classical
variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)
/-- A useful form of restriction correctness: any zero extension agrees. -/
theorem eval_killCompl_eq (p : MvPolynomial τ F) (x : σ → F) (y : τ → F)
    (hxy : ∀ i, y (f i) = x i) (hy : ∀ j, j ∉ Set.range f → y j = 0) :
    eval x (killCompl hf p) = eval y p := by
  rw [eval_killCompl]
  have he : extendZero hf x = y := by
    funext j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [extendZero_apply, hxy]
    · simp [extendZero, hj, hy j hj]
  rw [he]
end
end MIPRE.LowDegree

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
theorem eval_finiteArith (C : Circuit) (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith =
      MvPolynomial.eval (Sum.elim (fun i => ofBool (C.inputPart z i))
        (fun j => ofBool (C.gatePart z j))) C.routedArith := by
  apply eval_killCompl_eq
  · intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp [inputPart]
      rfl
    · simp [gatePart]
      rfl
  · intro v hv
    cases v with
    | inl i =>
      have hi : ¬ i < C.inputs := by
        intro hi
        exact hv ⟨Fin.castAdd C.size ⟨i, hi⟩, wireEmbedding_input C ⟨i, hi⟩⟩
      simp [inputPart, hi, ofBool]
    | inr j =>
      have hj : ¬ j < C.size := by
        intro hj
        exact hv ⟨Fin.natAdd C.inputs ⟨j, hj⟩, wireEmbedding_gate C ⟨j, hj⟩⟩
      simp [gatePart, hj, ofBool]
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
variable [CharP F 2]
/-- The finite polynomial enforces all gate values and the output literal. -/
theorem eval_finiteArith_iff (C : Circuit) (hC : C.WellFormed)
    (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 ↔
      C.RoutedConsistent (C.inputPart z) (C.gatePart z) ∧ C.gatePart z (C.size - 1) = true := by
  rw [eval_finiteArith, eval_routedArith_iff C hC]
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
variable [CharP F 2]
/-- A finite assignment whose input coordinates equal `x` reads `x` on every
input the circuit can use. -/
theorem inputPart_eq (C : Circuit) (x : ℕ → Bool) (z : Fin (C.inputs + C.size) → Bool)
    (h : ∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i) :
    ∀ i < C.inputs, C.inputPart z i = x i := by
  intro i hi
  simp only [inputPart, dif_pos hi]
  exact h ⟨i, hi⟩
end
end MIPRE.SAT.Circuit

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
variable [CharP F 2]
theorem _root_.solution (C : Circuit) (hC : C.WellFormed) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ z : Fin (C.inputs + C.size) → Bool,
      (∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i) ∧
      MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 := by
  have hs : 0 < C.size := List.length_pos_iff.mpr hC.nonempty
  constructor
  · intro hx
    let z : Fin (C.inputs + C.size) → Bool :=
      Fin.addCases (fun i => x i) (fun j => C.valueAt x j)
    have hz : ∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i := by intro i; simp [z]
    have hg : ∀ j < C.size, C.gatePart z j = C.valueAt x j := by
      intro j hj
      simp only [gatePart, dif_pos hj]
      simp only [z, Fin.addCases_right]
    have he := C.valueAt_congr hC.inputsLt (C.inputPart z) x (inputPart_eq C x z hz)
    refine ⟨z, hz, (eval_finiteArith_iff C hC z).mpr ⟨?_, ?_⟩⟩
    · apply (routedConsistent_iff C _ _).mpr
      intro k hk
      rw [hg k hk, he k]
    · rw [hg _ (by omega)]
      simpa [Circuit.eval, hC.nonempty, size] using hx
  · rintro ⟨z, hz, hp⟩
    have hc := (eval_finiteArith_iff C hC z).mp hp
    have hv := (eval_iff_routedConsistent C hC.nonempty (C.inputPart z)).mpr
      ⟨C.gatePart z, hc⟩
    rw [C.eval_congr hC.inputsLt (C.inputPart z) x (inputPart_eq C x z hz)] at hv
    exact hv
end MIPRE.SAT.Circuit
