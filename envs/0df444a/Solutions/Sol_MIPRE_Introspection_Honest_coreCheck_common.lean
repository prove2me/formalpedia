-- Prove2me | solution 1 for MIPRE.Introspection.Honest.coreCheck_common
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:56:06.22976+00:00
-- url     : https://prove2.me/submissions/fc6cf06a-d720-4240-a92f-c91d85c1bc0c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestCoreGame.lean (solution of MIPRE.Introspection.Honest.coreCheck_common);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Theorems.Thm_MIPRE_Introspection_Honest_source_commute
import Theorems.Thm_MIPRE_SampledGame_dist_eq_card
import Theorems.Thm_MIPRE_re_eq_zero_of_tracialValue_eq_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
/-- `SyncStrategy.value` is the generic tracial value at the normalized trace, by definition.
Named so that the application below need not ask the unifier to see through `value`, which is
a `whnf` timeout when it does. -/
theorem value_eq_tracialValue (S : SyncStrategy G) :
    S.value = tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P := rfl
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
open scoped Matrix in
/-- The real part of the normalized trace, written out. Stated once because both the value-one
characterization and the faithfulness lemmas below need it. -/
theorem normalizedTrace_re (S : SyncStrategy G) (M : Matrix (Fin S.d) (Fin S.d) ℂ) :
    ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) M).re
      = M.trace.re / (S.d : ℝ) := by
  show ((Fintype.card (Fin S.d) : ℂ)⁻¹ * M.trace).re = _
  rw [Fintype.card_fin, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, inv_mul_eq_div]
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
/-- The synchronous spelling: a value-`1` synchronous strategy has `Tr(M^x_a M^y_b) = 0` for
every rejected answer pair at every question pair of positive weight. -/
theorem re_eq_zero_of_value_eq_one (S : SyncStrategy G) (h : S.value = 1)
    {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    (S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ) = 0 := by
  have h' : tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P = 1 := by
    rw [← value_eq_tracialValue]; exact h
  rw [← normalizedTrace_re]
  exact re_eq_zero_of_tracialValue_eq_one G _ S.P h' hxy hD
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
open scoped Matrix in
/-- A self-adjoint idempotent whose normalized trace vanishes is the zero operator. -/
theorem eq_zero_of_trace_re_eq_zero (S : SyncStrategy G) {M : Matrix (Fin S.d) (Fin S.d) ℂ}
    (hsa : star M = M) (hidem : M * M = M) (h : M.trace.re / (S.d : ℝ) = 0) : M = 0 := by
  have hd : (S.d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr S.d_pos.ne'
  have hre : M.trace.re = 0 := (div_eq_zero_iff.mp h).resolve_right hd
  have him : M.trace.im = 0 := by
    refine Complex.conj_eq_iff_im.mp ?_
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose, hsa]
  have htr : M.trace = 0 := Complex.ext hre him
  have hH : Mᴴ * M = M := by rw [← Matrix.star_eq_conjTranspose, hsa, hidem]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hH, htr])
end
end MIPRE.SyncStrategy

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
theorem source_mu_pos (z : ι → F) :
    0 < (sourceGame L D).doubled.μ (false, (L false).eval z) (true, (L true).eval z) := by
  change 0 < SampledGame.dist (L false).eval (L true).eval ((L false).eval z) ((L true).eval z)
  rw [SampledGame.dist_eq_card, div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)]
  simp only [Nat.cast_pos, Finset.card_pos, Finset.nonempty_def, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨z, rfl, rfl⟩
end
end MIPRE.Introspection.Honest

namespace MIPRE.Introspection.Honest
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem source_reject_zero (hR : R.IsPCC) (hval : R.value = 1)
    (z : ι → F) (a b : A) (hD : D ((L false).eval z) ((L true).eval z) a b = false) :
    R.P.M (false, (L false).eval z) a * R.P.M (true, (L true).eval z) b = 0 := by
  have hc := source_commute L D R hR false true z a b
  apply R.eq_zero_of_trace_re_eq_zero
  · rw [star_mul, R.P.selfAdjoint, R.P.selfAdjoint]
    exact hc.eq.symm
  · rw [mul_assoc, ← mul_assoc (R.P.M (true, (L true).eval z) b), hc.eq.symm,
      mul_assoc (R.P.M (false, (L false).eval z) a), R.P.projective, ← mul_assoc,
      R.P.projective]
  · exact R.re_eq_zero_of_value_eq_one hval (source_mu_pos L D z) hD
end
end MIPRE.Introspection.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
variable (R : SyncStrategy (sourceGame L D).doubled)
theorem _root_.solution (hR : R.IsPCC) (hval : R.value = 1)
    (t u : CoreType) (z : ι → F) (a b : A)
    (hNZ : R.P.M (t.2, (L t.2).eval z) a * R.P.M (u.2, (L u.2).eval z) b ≠ 0) :
    coreCheck L D t u (displayed L t z, a) (displayed L u z, b) = true := by
  have hab : t.2 = u.2 → a = b := by
    intro hw
    by_contra hn
    apply hNZ
    rw [hw]
    exact R.orthogonal _ hn
  have hforward : t.2 = false → u.2 = true →
      D ((L false).eval z) ((L true).eval z) a b = true := by
    intro ht hu
    cases hd : D ((L false).eval z) ((L true).eval z) a b with
    | true => rfl
    | false => exact False.elim (hNZ (by simpa [ht, hu] using source_reject_zero L D R hR hval z a b hd))
  have hreverse : t.2 = true → u.2 = false →
      D ((L false).eval z) ((L true).eval z) b a = true := by
    intro ht hu
    cases hd : D ((L false).eval z) ((L true).eval z) b a with
    | true => rfl
    | false =>
      apply False.elim
      apply hNZ
      rw [(source_commute L D R hR t.2 u.2 z a b).eq]
      simpa [ht, hu] using source_reject_zero L D R hR hval z b a hd
  rcases t with ⟨s, w⟩; rcases u with ⟨t, v⟩
  cases w <;> cases v
  · have he := hab rfl; subst b
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, CLChecks.sampling]
  · have hd := hforward rfl rfl
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, hd]
  · have hd := hreverse rfl rfl
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, hd]
  · have he := hab rfl; subst b
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, CLChecks.sampling]
end MIPRE.Introspection.Honest
