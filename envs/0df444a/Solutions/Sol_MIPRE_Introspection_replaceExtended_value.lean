-- Prove2me | solution 1 for MIPRE.Introspection.replaceExtended_value
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:32:10.612106+00:00
-- url     : https://prove2.me/submissions/78a38b8e-3964-4079-8380-6cfc64105fac

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/StrategyReplacement.lean (solution of MIPRE.Introspection.replaceExtended_value);
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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_Foundations_WeylEPR
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Theorems.Thm_MIPRE_Introspection_povmValue_stability_at
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_kron_one_mul_ancillaEmbed

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]
/-- **A POVM is determined by its operators.** The remaining fields are propositions. -/
theorem POVM.ext' {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N := by
  have hm : M.mats = N.mats := funext fun a => Subtype.ext (h a)
  obtain ⟨mM, hM1, hM2⟩ := M
  obtain ⟨mN, hN1, hN2⟩ := N
  simp only at hm
  subst hm
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- **A rectangular isometry preserves the norm.** -/
theorem norm_evec_mulVec_eq {M : Type*} [Fintype M] {A : Matrix M N ℂ} [DecidableEq N]
    (h : Aᴴ * A = 1) (v : N → ℂ) : ‖evec (A *ᵥ v)‖ = ‖evec v‖ := by
  have hsq : ‖evec (A *ᵥ v)‖ ^ 2 = ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, h, Matrix.one_mulVec, norm_evec_sq]
  nlinarith [norm_nonneg (evec (A *ᵥ v)), norm_nonneg (evec v), hsq]
end
end MIPRE

namespace MIPRE
section
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
/-- Pulling a Born-rule expectation back along a linear map `W` conjugates the observable:
`⟨Wv| M |Wv⟩ = ⟨v| Wᴴ M W |v⟩`. With `W` an isometry and `M` a projection this is how a
dilated projective measurement compresses back to the POVM it came from. -/
theorem dotProduct_mulVec_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix κ ι ℂ) (M : Matrix κ κ ℂ) (v : ι → ℂ) :
    star (W *ᵥ v) ⬝ᵥ (M *ᵥ (W *ᵥ v)) = star v ⬝ᵥ ((Wᴴ * (M * W)) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
theorem ancillaEmbed_kron_isometry (a₀ : A) :
    (((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ *
        ((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ)))
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    ancillaEmbed_isometry, Matrix.one_mul, Matrix.one_kronecker_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- The extension does not change the norm: the padding is an isometry. -/
theorem norm_evec_extVecA (ψ : dA × dB → ℂ) (a₀ : A) :
    ‖evec (extVecA ψ a₀)‖ = ‖evec ψ‖ :=
  norm_evec_mulVec_eq (ancillaEmbed_kron_isometry a₀) ψ
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
/-- An operator with an inert ancilla compresses to itself. -/
theorem compress_aOp (b₀ : Bnc) (N : Matrix dB dB ℂ) :
    (ancillaEmbed dB b₀)ᴴ * ((aOp N : Matrix (dB × Bnc) _ ℂ) * ancillaEmbed dB b₀) = N := by
  rw [aOp, kron_one_mul_ancillaEmbed,
    ← Matrix.mul_assoc ((ancillaEmbed dB b₀)ᴴ) (ancillaEmbed dB b₀) N, ancillaEmbed_isometry,
    Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] {d E : Type*} [Fintype d] [DecidableEq d] [Fintype E]
  [DecidableEq E]
/-- Extending by the identity commutes with relabelling the outcomes. -/
theorem POVM.map_aOp {B : Type*} [Fintype B] [DecidableEq B] (f : A → B) (M : POVM A d) :
    (M.map f).aOp (E := E) = (M.aOp (E := E)).map f :=
  POVM.ext' fun b => by
    rw [POVM.aOp_mats, POVM.map_mats, POVM.map_mats, aOp_sum]
    rfl
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K A T : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]
/-- The one-party fixed-ancilla embedding changes no Born probability after
compressing the measured operator. -/
theorem bornProb_extVecA (ψ : H × K → ℂ) (a₀ : T)
    (P : Matrix (H × T) (H × T) ℂ) (B : Matrix K K ℂ) :
    bornProb (extVecA ψ a₀) P B =
      bornProb ψ ((ancillaEmbed H a₀)ᴴ * (P * ancillaEmbed H a₀)) B := by
  rw [bornProb, bornProb, extVecA, dotProduct_mulVec_conj]
  congr 2
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
theorem replaceExtended_other (MA : X → POVM A H) (q x : X) (R : POVM A (H × T))
    (hx : x ≠ q) : replaceExtended MA q R x = (MA x).aOp := by
  simp [replaceExtended, hx]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
/-- Adding an inert Alice ancilla preserves the whole game's value exactly. -/
theorem povmValue_extVecA (G : Game X Y A B) (ψ : H × K → ℂ) (a₀ : T)
    (MA : X → POVM A H) (MB : Y → POVM B K) :
    povmValue G (extVecA ψ a₀) (fun x => (MA x).aOp) MB = povmValue G ψ MA MB := by
  unfold povmValue condWin
  simp only [POVM.aOp_mats, bornProb_extVecA, compress_aOp]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]
theorem _root_.solution (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (a₀ : T)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (M : POVM C H) (R : POVM C (H × T)) (f : C → A)
    (hMA : MA q = M.map f) (hM : IsPVM fun c => (M.mats c).val)
    (hR : IsPVM fun c => (R.mats c).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm (extVecA ψ a₀)
      (aOp (M.mats c).val - (R.mats c).val) ≤ δ) :
    |povmValue G ψ MA MB -
      povmValue G (extVecA ψ a₀) (replaceExtended MA q (R.map f)) MB| ≤ 2*Real.sqrt δ := by
  rw [← povmValue_extVecA G ψ a₀ MA MB]
  apply povmValue_stability_at G (extVecA ψ a₀) (by rwa [norm_evec_extVecA])
    (fun x => (MA x).aOp) (replaceExtended MA q (R.map f)) MB q M.aOp R f
  · rw [hMA, POVM.map_aOp]
  · exact replaceExtended_at MA q (R.map f)
  · intro x hx
    exact (replaceExtended_other MA q x (R.map f) hx).symm
  · exact hM.aOp
  · exact hR
  · exact hMB
  · exact hd
end MIPRE.Introspection
