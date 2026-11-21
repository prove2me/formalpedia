-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.reduced_basis_admissible_width_schedule
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:37:33.490729+00:00
-- url     : https://prove2.me/submissions/0edc1b22-5009-42bd-b341-a1bb9498d2fc

/-
Portions derived from the Hex implementation and correctness proofs.
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Copyright (c) 2026 Slava Naprienko. All rights reserved.
Original authors of these portions: Kim Morrison and Slava Naprienko.
The source was adapted to resolve public modules and elaborate independently.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for describing the origin of the Work and
      reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may accept and charge a
      fee for acceptance of support, warranty, indemnity, or other liability
      obligations and/or rights consistent with this License. However, in
      accepting such obligations, You may act only on Your own behalf
      and on Your sole responsibility, not on behalf of any other Contributor,
      and only if You agree to indemnify, defend, and hold each Contributor
      harmless for any liability incurred by, or claims asserted against,
      such Contributor by reason of your accepting any such warranty or
      additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing permissions and
   limitations under the License.

-/

import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_LARLLL_CurrentData
import Theorems.Thm_InfoLossLAR_WorstCase_NativeLLL_elementary_updates_preserve_validity
import Theorems.Thm_Hex_GramSchmidt_Int_getArrayEntry_scaledCoeffRowsSchur_eq
import Theorems.Thm_Hex_Matrix_bareissWith_eq_bareissDataWith_det
import Theorems.Thm_Hex_Matrix_det_gramMatrix_nonneg
import Theorems.Thm_InfoLossLAR_WorstCase_NativeLLL_basis_lattice_eq
import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Init.Grind.Ring.Field
import Mathlib
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic
import Std
import Std.Data.ExtTreeMap.Lemmas
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_reciprocal_dual_norm

set_option linter.all false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option autoImplicit true
namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase
namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt
namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native
namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch
namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
end InfoLossLAR.WorstCase.TM2Boolean.RPN
namespace Integration9_9
end Integration9_9
namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding
namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine
namespace Integration9_9.TM2NativeAffineApply
end Integration9_9.TM2NativeAffineApply
namespace Integration9_9.TM2NativeAffineEncoding
end Integration9_9.TM2NativeAffineEncoding
namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw
namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries
namespace Integration9_9.TM2NativeRootGroupProfiles
end Integration9_9.TM2NativeRootGroupProfiles
namespace Integration9_9.TM2NativeSliceProbability
end Integration9_9.TM2NativeSliceProbability
namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength
namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization
namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget
namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary
namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic
namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly
namespace QMCNumericRuntime
end QMCNumericRuntime
section
section
namespace Hex
universe u
namespace ExactDivLaws
variable {R : Type u}
end ExactDivLaws
variable {R : Type u}
theorem one_ne_zero_of_nonzero {S : Type u} [Lean.Grind.CommRing S]
    {a : S} (ha : a ≠ 0) : (1 : S) ≠ 0 := by
  intro hone
  apply ha
  calc
    a = a * 1 := (Lean.Grind.Semiring.mul_one _).symm
    _ = a * 0 := by rw [hone]
    _ = 0 := Lean.Grind.Semiring.mul_zero _
end Hex
end
end
section
section
namespace List
universe u v w
variable {α : Type v} {β : Type w} {R : Type u}
section Semiring
variable [Lean.Grind.Semiring R]
theorem foldl_add_eq_add_foldl (xs : List α) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc + f x) z
      = z + xs.foldl (fun acc x => acc + f x) 0 :=
  calc xs.foldl (fun acc x => acc + f x) z
      = (xs.map f).foldl (· + ·) z :=
        (List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := z)).symm
    _ = (xs.map f).foldl (· + ·) (z + 0) := by rw [Lean.Grind.Semiring.add_zero]
    _ = z + (xs.map f).foldl (· + ·) 0 := by
        letI : Std.Associative (fun (a b : R) => a + b) :=
          ⟨Lean.Grind.Semiring.add_assoc⟩
        exact List.foldl_assoc
    _ = z + xs.foldl (fun acc x => acc + f x) 0 := by
        rw [List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := 0)]
theorem foldl_add_zero (xs : List α) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z :=
  foldl_add_eq_self xs (fun _ => 0) z fun _ _ => rfl
theorem foldl_add_mul_right (xs : List α) (f : α → R) (c z : R) :
    xs.foldl (fun acc x => acc + f x) z * c =
      xs.foldl (fun acc x => acc + f x * c) (z * c) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (z := z + f x), show (z + f x) * c = z * c + f x * c by grind]
end Semiring
section Ring
variable [Lean.Grind.Ring R]
end Ring
section Semiring
variable [Lean.Grind.Semiring R]
end Semiring
section Ring
variable [Lean.Grind.Ring R]
end Ring
section Semiring
variable [Lean.Grind.Semiring R]
theorem foldl_add_comm {γ : Type w} (xs : List α) (ys : List γ) (f : α → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
    simp only [List.foldl_nil]
    exact (foldl_add_zero ys 0).symm
  | cons x xs ih =>
    have hLHS :
        (x :: xs).foldl
            (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            xs.foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
      simp only [List.foldl_cons]
      rw [foldl_add_eq_add_foldl xs
            (fun x' => ys.foldl (fun acc' y => acc' + f x' y) 0)
            (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
      grind
    have hRHS :
        ys.foldl
            (fun acc y => acc + (x :: xs).foldl
              (fun acc' x' => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            ys.foldl
              (fun acc y => acc + xs.foldl
                (fun acc' x' => acc' + f x' y) 0) 0 := by
      have hfun :
          (fun (acc : R) y =>
              acc + (x :: xs).foldl (fun acc' x' => acc' + f x' y) 0) =
            (fun (acc : R) y =>
              acc + (f x y + xs.foldl (fun acc' x' => acc' + f x' y) 0)) := by
        funext acc y
        congr 1
        simp only [List.foldl_cons]
        rw [foldl_add_eq_add_foldl xs (fun x' => f x' y) (0 + f x y)]
        grind
      rw [hfun]
      exact foldl_add_add ys (fun y => f x y)
        (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
    rw [hLHS, hRHS, ih]
end Semiring
section Semiring
variable [Lean.Grind.Semiring R]
theorem foldl_add_mul_right_zero (xs : List α) (f : α → R) (c : R) :
    xs.foldl (fun acc x => acc + f x * c) 0 =
      xs.foldl (fun acc x => acc + f x) 0 * c := by
  simpa [Lean.Grind.Semiring.zero_mul] using
    (foldl_add_mul_right xs f c 0).symm
end Semiring
theorem foldl_add_flatMap [Add R] {γ : Type w}
    (xs : List α) (f : α → List γ) (g : γ → R) (z : R) :
    (xs.flatMap f).foldl (fun acc x => acc + g x) z =
      xs.foldl (fun acc x => (f x).foldl (fun acc y => acc + g y) acc) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
    exact ih ((f x).foldl (fun acc y => acc + g y) z)
section CommSemiring
variable [Lean.Grind.CommSemiring R]
end CommSemiring
end List
end
end
section
section
namespace Hex
universe u v
end Hex
namespace Vector
end Vector
namespace Hex
namespace Matrix
variable {R : Type u} {n m k : Nat}
@[grind =] theorem setRow_get_self (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v)[dst] = v := by
  show getRow (setRow M dst v) dst = v
  rw [← getElem_rows (setRow M dst v) dst.val dst.isLt, rows_setRow,
    Vector.getElem_set_self dst.isLt]
theorem setRow_row_ne (M : Matrix R n m) (dst r : Fin n) (v : Vector R m)
    (h : r ≠ dst) :
    (setRow M dst v)[r] = M[r] := by
  show getRow (setRow M dst v) r = getRow M r
  rw [← getElem_rows (setRow M dst v) r.val r.isLt, rows_setRow,
    Vector.getElem_set_ne dst.isLt r.isLt (fun heq => h (Fin.ext heq.symm)),
    getElem_rows]
@[simp, grind =] theorem col_transpose (M : Matrix R n m) (i : Fin n) :
    col (transpose M) i = row M i := by
  ext k hk
  show (col (transpose M) i)[(⟨k, hk⟩ : Fin m)] = (row M i)[(⟨k, hk⟩ : Fin m)]
  rw [getElem_col, getElem_transpose, getElem_row]
@[grind =] theorem getElem_mul [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) (j : Fin k) :
    (M * N)[i][j] = (row M i).dotProduct (col N j) := by
  show (mul M N)[i][j] = (row M i).dotProduct (col N j)
  rw [mul, getElem_ofFn]
private theorem gapH387 {N : Nat} (idxA idxB : Fin m → Nat)
    (bdA : ∀ t, idxA t < N) (bdB : ∀ t, idxB t < N) {p : Nat} (hp : p < N) :
    ∀ (xs : List (Fin m)) (d0 : Vector R N), (∀ t ∈ xs, idxA t ≠ p ∧ idxB t ≠ p) →
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[p]'hp
        = d0[p]'hp := by
  intro xs
  induction xs with
  | nil => intro d0 _; rfl
  | cons x xs ih =>
    intro d0 hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht)),
      Vector.getElem_swap, if_neg (fun heq => (hne x List.mem_cons_self).1 heq.symm),
      if_neg (fun heq => (hne x List.mem_cons_self).2 heq.symm)]
private theorem gapH411 {N : Nat} (idxA idxB : Fin m → Nat)
    (bdA : ∀ t, idxA t < N) (bdB : ∀ t, idxB t < N)
    (hdisj : ∀ a b : Fin m, a ≠ b →
      idxA a ≠ idxA b ∧ idxA a ≠ idxB b ∧ idxB a ≠ idxA b ∧ idxB a ≠ idxB b) :
    ∀ (xs : List (Fin m)), xs.Nodup → ∀ (d0 : Vector R N) (r : Fin m), r ∈ xs →
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[idxA r]'(bdA r)
          = d0[idxB r]'(bdB r) ∧
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[idxB r]'(bdB r)
          = d0[idxA r]'(bdA r) := by
  intro xs
  induction xs with
  | nil => intro _ d0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd d0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · have hnotail : ∀ t ∈ xs, t ≠ r := fun t ht heq =>
        (List.nodup_cons.mp hnd).1 (heq ▸ ht)
      constructor
      · rw [gapH387 idxA idxB bdA bdB (bdA r) xs _ (fun t ht =>
          ⟨(hdisj t r (hnotail t ht)).1, (hdisj t r (hnotail t ht)).2.2.1⟩),
          Vector.getElem_swap, if_pos rfl]
      · rw [gapH387 idxA idxB bdA bdB (bdB r) xs _ (fun t ht =>
          ⟨(hdisj t r (hnotail t ht)).2.1, (hdisj t r (hnotail t ht)).2.2.2⟩),
          Vector.getElem_swap]
        by_cases hab : idxB r = idxA r
        · rw [if_pos hab]
          simp only [hab]
        · rw [if_neg hab, if_pos rfl]
    · have hxr : x ≠ r := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hr')
      have hd := hdisj x r hxr
      obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mp hnd).2
        (d0.swap (idxA x) (idxB x) (bdA x) (bdB x)) r hr'
      constructor
      · rw [h1, Vector.getElem_swap, if_neg (fun heq => hd.2.1 heq.symm),
          if_neg (fun heq => hd.2.2.2 heq.symm)]
      · rw [h2, Vector.getElem_swap, if_neg (fun heq => hd.1 heq.symm),
          if_neg (fun heq => hd.2.2.1 heq.symm)]
private theorem gapH354 {i j : Nat} (hij : i ≠ j) :
    ∀ a b : Fin m, a ≠ b →
      i * m + a.val ≠ i * m + b.val ∧ i * m + a.val ≠ j * m + b.val ∧
      j * m + a.val ≠ i * m + b.val ∧ j * m + a.val ≠ j * m + b.val := by
  intro a b hab
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine ⟨fun h => hv (by omega), fun h => ?_, fun h => ?_, fun h => hv (by omega)⟩
  · have h1 : (i * m + a.val) / m = i := flatIdx_div a.isLt
    have h2 : (j * m + b.val) / m = j := flatIdx_div b.isLt
    rw [h, h2] at h1
    exact hij h1.symm
  · have h1 : (j * m + a.val) / m = j := flatIdx_div a.isLt
    have h2 : (i * m + b.val) / m = i := flatIdx_div b.isLt
    rw [h, h2] at h1
    exact hij h1
@[simp, grind =] theorem rows_swap (M : Matrix R n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    (M.swap i j hi hj).rows = M.rows.swap i j hi hj := by
  obtain ⟨d⟩ := M
  by_cases hij : i = j
  · subst hij
    apply Vector.ext
    intro r hr
    rw [getElem_rows, Vector.getElem_swap]
    have hswap : ∀ t : Fin m, ∀ (dd : Vector R (n * m)),
        dd.swap (i * m + t.val) (i * m + t.val) (flatIdx_lt hi t.isLt) (flatIdx_lt hi t.isLt)
          = dd := by
      intro t dd
      apply Vector.ext
      intro p hp
      rw [Vector.getElem_swap]
      by_cases hpt : p = i * m + t.val
      · subst hpt
        rw [if_pos rfl]
      · rw [if_neg hpt, if_neg hpt]
    have hid : (swap (⟨d⟩ : Matrix R n m) i i hi hi).data = d := by
      simp only [swap]
      rw [Fin.foldl_eq_finRange_foldl]
      generalize List.finRange m = xs
      induction xs with
      | nil => rfl
      | cons x xs ihx => rw [List.foldl_cons, hswap x d]; exact ihx
    apply Vector.ext
    intro t ht
    rw [getElem_getRow_nat]
    show (swap (⟨d⟩ : Matrix R n m) i i hi hi).data[r * m + t]'(flatIdx_lt hr ht) = _
    rw [hid]
    by_cases hri : r = i
    · rw [if_pos hri, getElem_rows, getElem_getRow_nat]
      simp only [hri]
    · rw [if_neg hri, if_neg hri, getElem_rows, getElem_getRow_nat]
  · apply Vector.ext
    intro r hr
    rw [getElem_rows, Vector.getElem_swap]
    have hfold : (swap (⟨d⟩ : Matrix R n m) i j hi hj).data =
        (List.finRange m).foldl
          (fun dd (t : Fin m) => dd.swap (i * m + t.val) (j * m + t.val)
            (flatIdx_lt hi t.isLt) (flatIdx_lt hj t.isLt)) d := by
      simp only [swap]
      rw [Fin.foldl_eq_finRange_foldl]
    by_cases hri : r = i
    · subst hri
      rw [if_pos rfl]
      apply Vector.ext
      intro t ht
      rw [getElem_getRow_nat, getElem_rows, getElem_getRow_nat]
      show (swap (⟨d⟩ : Matrix R n m) r j hr hj).data[r * m + t]'(flatIdx_lt hr ht) = _
      rw [hfold]
      exact (gapH411 _ _ (fun s => flatIdx_lt hr s.isLt) (fun s => flatIdx_lt hj s.isLt)
        (gapH354 hij) (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩
        (List.mem_finRange _)).1
    · by_cases hrj : r = j
      · subst hrj
        rw [if_neg hri, if_pos rfl]
        apply Vector.ext
        intro t ht
        rw [getElem_getRow_nat, getElem_rows, getElem_getRow_nat]
        show (swap (⟨d⟩ : Matrix R n m) i r hi hr).data[r * m + t]'(flatIdx_lt hr ht) = _
        rw [hfold]
        exact (gapH411 _ _ (fun s => flatIdx_lt hi s.isLt) (fun s => flatIdx_lt hr s.isLt)
          (gapH354 hij) (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩
          (List.mem_finRange _)).2
      · rw [if_neg hri, if_neg hrj, getElem_rows]
        apply Vector.ext
        intro t ht
        rw [getElem_getRow_nat, getElem_getRow_nat]
        show (swap (⟨d⟩ : Matrix R n m) i j hi hj).data[r * m + t]'(flatIdx_lt hr ht) = _
        rw [hfold]
        exact gapH387 _ _ (fun s => flatIdx_lt hi s.isLt) (fun s => flatIdx_lt hj s.isLt)
          (flatIdx_lt hr ht) (List.finRange m) d (fun s _ => by
            constructor
            · intro heq
              have h1 : (i * m + s.val) / m = i := flatIdx_div s.isLt
              have h2 : (r * m + t) / m = r := flatIdx_div ht
              rw [heq, h2] at h1
              exact hri h1
            · intro heq
              have h1 : (j * m + s.val) / m = j := flatIdx_div s.isLt
              have h2 : (r * m + t) / m = r := flatIdx_div ht
              rw [heq, h2] at h1
              exact hrj h1)
private theorem gapH396 {c : Nat} (hc : c < m) :
    ∀ a b : Fin n, a.val * m + c = b.val * m + c → a = b := by
  intro a b h
  have h1 : (a.val * m + c) / m = a.val := flatIdx_div hc
  have h2 : (b.val * m + c) / m = b.val := flatIdx_div hc
  rw [h, h2] at h1
  exact Fin.ext h1.symm
@[grind =] theorem getElem_setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R)
    (r : Fin n) (c : Fin m) :
    (setCol M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  obtain ⟨d⟩ := M
  rw [getElem_eq_getRow, getElem_getRow, getElem_eq_getRow, getElem_getRow]
  show (Fin.foldl n (fun d (i : Fin n) =>
      d.set (i.val * m + dst.val) (v i) (flatIdx_lt i.isLt dst.isLt)) d)[r.val * m + c.val]'_ = _
  rw [Fin.foldl_eq_finRange_foldl]
  by_cases hc : c = dst
  · subst hc
    rw [if_pos rfl]
    exact foldl_set_mem (fun i : Fin n => i.val * m + c.val) v
      (fun i => flatIdx_lt i.isLt c.isLt) (gapH396 c.isLt)
      (List.finRange n) (nodup_finRange n) d r (List.mem_finRange _)
  · rw [if_neg hc]
    exact foldl_set_ne (fun i : Fin n => i.val * m + dst.val) v
      (fun i => flatIdx_lt i.isLt dst.isLt) (flatIdx_lt r.isLt c.isLt)
      (List.finRange n) d (fun i _ heq => by
        have h1 : (i.val * m + dst.val) % m = dst.val := flatIdx_mod dst.isLt
        have h2 : (r.val * m + c.val) % m = c.val := flatIdx_mod c.isLt
        rw [heq, h2] at h1
        exact hc (Fin.ext h1))
@[simp] theorem setCol_self (M : Matrix R n m) (dst : Fin m) :
    setCol M dst (fun r => M[r][dst]) = M := by
  apply ext_getElem
  intro r c
  rw [getElem_setCol]
  by_cases hc' : c = dst
  · rw [if_pos hc']
    exact congrArg (fun c' : Fin m => M[r][c']) hc'.symm
  · rw [if_neg hc']
@[grind =] theorem getElem_modifyCol (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R)
    (r : Fin n) (c : Fin m) :
    (modifyCol M dst g)[r][c] = if c = dst then g r (M[r][dst]) else M[r][c] := by
  obtain ⟨d⟩ := M
  rw [getElem_eq_getRow, getElem_getRow, getElem_eq_getRow, getElem_getRow,
    getElem_getRow]
  show (Fin.foldl n (fun d (i : Fin n) =>
      d.modify (i.val * m + dst.val) (g i)) d)[r.val * m + c.val]'_ = _
  rw [Fin.foldl_eq_finRange_foldl]
  by_cases hc : c = dst
  · subst hc
    rw [if_pos rfl]
    exact foldl_modify_mem (fun i : Fin n => i.val * m + c.val) g
      (fun i => flatIdx_lt i.isLt c.isLt) (gapH396 c.isLt)
      (List.finRange n) (nodup_finRange n) d r (List.mem_finRange _)
  · rw [if_neg hc]
    exact foldl_modify_ne (fun i : Fin n => i.val * m + dst.val) g
      (flatIdx_lt r.isLt c.isLt) (List.finRange n) d (fun i _ heq => by
        have h1 : (i.val * m + dst.val) % m = dst.val := flatIdx_mod dst.isLt
        have h2 : (r.val * m + c.val) % m = c.val := flatIdx_mod c.isLt
        rw [heq, h2] at h1
        exact hc (Fin.ext h1))
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
private theorem gapH489 (M : Matrix R n m) (i : Fin n) : M.rows[i] = getRow M i := by
  simp [rows]
theorem getElem_rowSwap (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  rw [rowSwap, getElem_eq_getRow, ← gapH489, rows_swap]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp_all [getElem_eq_getRow, Fin.ext_iff]
theorem getElem_rowAdd [Mul R] [Add R]
    (M : Matrix R n m) (src dst r : Fin n) (c : R) (k : Fin m) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  rw [rowAdd, getElem_modifyEntries]
  by_cases h : r = dst
  · rw [if_pos (congrArg Fin.val h), if_pos h, h]
    rw [show (getRow M src)[k] = M[src][k] from rfl]
  · rw [if_neg (fun hv => h (Fin.ext hv)), if_neg h]
@[simp, grind =] theorem row_rowAdd_dst [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin n) (c : R) :
    row (rowAdd M src dst c) dst =
      Vector.ofFn (fun k => M[dst][k] + c * M[src][k]) := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowAdd M src dst c) dst)[kk] =
    (Vector.ofFn (fun k => M[dst][k] + c * M[src][k]))[kk]
  rw [getElem_row, getElem_rowAdd]
  simp
theorem row_rowAdd_of_ne [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin n) {dst r : Fin n} (c : R)
    (hrdst : r ≠ dst) :
    row (rowAdd M src dst c) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowAdd M src dst c) r)[kk] = (row M r)[kk]
  rw [getElem_row, getElem_row, getElem_rowAdd]
  simp [hrdst]
theorem rowAdd_eq_set [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin n) (c : R) :
    rowAdd M src dst c =
      setRow M dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]) := by
  apply ext_getElem
  intro r k
  rw [getElem_rowAdd]
  by_cases h : r = dst
  · subst h
    rw [setRow_get_self]
    simp [Vector.getElem_ofFn]
  · rw [if_neg h, setRow_row_ne M dst r _ h]
theorem getElem_colAdd [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin m) (c : R) (i : Fin n) (j : Fin m) :
    (colAdd M src dst c)[i][j] =
      if j = dst then M[i][j] + c * M[i][src] else M[i][j] := by
  rw [colAdd, getElem_modifyCol]
  by_cases hj : j = dst
  · rw [if_pos hj, if_pos hj, hj, getElem_col]
  · rw [if_neg hj, if_neg hj]
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u v w
namespace Matrix
theorem mul_assoc_vec [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (v : Vector R k) :
    (A * B) * v = A * (B * v) := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show ((A * B) * v)[ii] = (A * (B * v))[ii]
  simp only [getElem_mulVec, getElem_mul, getElem_row, getElem_col, Vector.dotProduct]
  change
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
      (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0
  calc
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
        (List.finRange k).foldl
          (fun acc l =>
            acc + (List.finRange m).foldl
              (fun acc j => acc + A[ii][j] * B[j][l] * v[l]) 0) 0 := by
          apply List.foldl_add_congr
          intro l _hl
          rw [List.foldl_add_mul_right]
          grind
    _ = (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0 := by
          rw [List.foldl_add_comm]
          apply List.foldl_add_congr
          intro j _hj
          rw [← List.foldl_add_mul_left]
          have hzero : A[ii][j] * (0 : R) = 0 := by grind
          rw [hzero]
          apply List.foldl_add_congr
          intro l _hl
          grind
theorem transpose_mul_of_mul_comm [Lean.Grind.CommRing R]
    (A : Matrix R n m) (B : Matrix R m k) :
    Matrix.transpose (A * B) = Matrix.transpose B * Matrix.transpose A := by
  apply ext_getElem
  intro ii jj
  rw [getElem_transpose, getElem_mul, getElem_mul, row_transpose, col_transpose,
    Vector.dotProduct, Vector.dotProduct]
  apply List.foldl_add_congr
  intro l _hl
  rw [Lean.Grind.CommSemiring.mul_comm]
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
end Matrix
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
private theorem gapH190
    (b : Matrix Rat n m) (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (basisRows b.rows.toList)[i]!.dotProduct (basisRows b.rows.toList)[j]! = 0 := by
  let rows := basisRows b.rows.toList
  have hlen : rows.length = n := by
    simp [rows, basisRows_length]
  have hirows : i < rows.length := by simpa [hlen] using hi
  have hjrows : j < rows.length := by simpa [hlen] using hj
  have hpair : rows.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
    simpa [rows] using basisRows_pairwise (rows := b.rows.toList)
  have hget_i : rows[i]! = rows[i] := by simp [hirows]
  have hget_j : rows[j]! = rows[j] := by simp [hjrows]
  by_cases hlt : i < j
  · have hrel :=
      (List.pairwise_iff_getElem.1 hpair) i j hirows hjrows hlt
    rw [hget_i, hget_j]
    exact hrel.1
  · have hji : j < i := by
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hij h.symm)
    have hrel :=
      (List.pairwise_iff_getElem.1 hpair) j i hjrows hirows hji
    rw [hget_i, hget_j]
    exact hrel.2
private theorem gapH287 (basisRow : Vector Rat m) :
    subtractProjection 0 basisRow = 0 := by
  have hdot : (0 : Vector Rat m).dotProduct basisRow = 0 := by
    unfold Vector.dotProduct
    induction List.finRange m with
    | nil =>
        rfl
    | cons i rest ih =>
      simp only [List.foldl_cons]
      have hentry : (0 : Vector Rat m)[i] = 0 := by
        change (0 : Vector Rat m)[i.val] = 0
        rw [Vector.getElem_zero]
      rw [hentry, show (0 : Rat) + 0 * basisRow[i] = 0 by grind]
      exact ih
  apply Vector.ext
  intro idx hidx
  by_cases hnorm : basisRow.dotProduct basisRow = 0
  · have hcoeff : projectionCoeff 0 basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff]
    change (0 : Rat) - 0 * basisRow[idx] = 0
    grind
  · have hcoeff : projectionCoeff 0 basisRow = 0 := by
      have hh561 : (0 : Rat) / basisRow.dotProduct basisRow = 0 := by
        grind
      simp [projectionCoeff, hnorm, hdot, hh561]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff]
    change (0 : Rat) - 0 * basisRow[idx] = 0
    grind
private theorem gapH82 (basisRev : List (Vector Rat m)) :
    reduceAgainstBasis basisRev 0 = 0 := by
  induction basisRev with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [gapH287]
      change reduceAgainstBasis rest 0 = 0
      exact ih
private theorem gapH308
    (row basisRow : Vector Rat m) (h : row.dotProduct basisRow = 0) :
    subtractProjection row basisRow = row := by
  apply Vector.ext
  intro idx hidx
  by_cases hnorm : basisRow.dotProduct basisRow = 0
  · have hcoeff : projectionCoeff row basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_smul, hcoeff]
    change row[idx] - 0 * basisRow[idx] = row[idx]
    grind
  · have hcoeff : projectionCoeff row basisRow = 0 := by
      have hh561 : (0 : Rat) / basisRow.dotProduct basisRow = 0 := by
        grind
      simp [projectionCoeff, h, hnorm, hh561]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_smul, hcoeff]
    change row[idx] - 0 * basisRow[idx] = row[idx]
    grind
private theorem gapH106
    (basisRev : List (Vector Rat m)) (row : Vector Rat m)
    (h : ∀ basisRow ∈ basisRev, row.dotProduct basisRow = 0) :
    reduceAgainstBasis basisRev row = row := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      have hhead : subtractProjection row basisRow = row :=
        gapH308 row basisRow (h basisRow (by simp))
      rw [hhead]
      exact ih row (by
        intro later hlater
        exact h later (by simp [hlater]))
private theorem gapH248 (basisRow : Vector Rat m) :
    subtractProjection basisRow basisRow = 0 := by
  by_cases hnorm : basisRow.dotProduct basisRow = 0
  · apply Vector.ext
    intro idx hidx
    have hzero : basisRow[idx] = 0 :=
      dot_self_eq_zero_get basisRow hnorm ⟨idx, hidx⟩
    have hcoeff : projectionCoeff basisRow basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff, hzero]
    change (0 : Rat) - 0 * 0 = 0
    grind
  · apply Vector.ext
    intro idx hidx
    have hdiv : basisRow.dotProduct basisRow / basisRow.dotProduct basisRow = 1 := by
      grind
    have hcoeff : projectionCoeff basisRow basisRow = 1 := by
      simp [projectionCoeff, hnorm, hdiv]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff]
    change basisRow[idx] - 1 * basisRow[idx] = 0
    grind
private theorem gapH191
    (basisRow : Vector Rat m) (rest : List (Vector Rat m)) :
    reduceAgainstBasis (basisRow :: rest) basisRow = 0 := by
  rw [reduceAgainstBasis]
  simp only [List.foldl_cons]
  rw [gapH248]
  change reduceAgainstBasis rest 0 = 0
  exact gapH82 rest
private theorem gapH104
    (rows : List (Vector Rat m)) (j : Nat) (hj : j < rows.length) :
    reduceAgainstBasis ((basisRows rows).take (j + 1)).reverse
        (basisRows rows)[j]! = 0 := by
  have hlen : j < (basisRows rows).length := by
    simpa [basisRows_length] using hj
  have htake :
      (basisRows rows).take (j + 1) =
        (basisRows rows).take j ++ [(basisRows rows)[j]!] := by
    rw [List.take_succ_eq_append_getElem hlen]
    congr 1
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  rw [htake, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  exact gapH191
    ((basisRows rows)[j]!) ((basisRows rows).take j).reverse
end GramSchmidt
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
private theorem gapH427
    (xs : List (Fin m)) (a b c : Vector Rat m) (accA accB : Rat) :
    xs.foldl (fun acc i => acc + (a + b)[i] * (c)[i]) (accA + accB) =
      xs.foldl (fun acc i => acc + a[i] * (c)[i]) accA +
        xs.foldl (fun acc i => acc + b[i] * (c)[i]) accB := by
  induction xs generalizing accA accB with
  | nil => simp
  | cons i xs ih =>
      have hentry : (a + b)[i] = a[i] + b[i] := by
        change (a + b)[i.val] = a[i.val] + b[i.val]
        rw [Vector.getElem_add]
      simp only [List.foldl_cons]
      have hstart :
          accA + accB + (a + b)[i] * (c)[i] =
            (accA + a[i] * (c)[i]) + (accB + b[i] * (c)[i]) := by
        rw [hentry]
        grind
      rw [hstart]
      exact ih (accA := accA + a[i] * (c)[i]) (accB := accB + b[i] * (c)[i])
private theorem gapH382 (a b c : Vector Rat m) :
    (a + b).dotProduct c = a.dotProduct c + b.dotProduct c := by
  unfold Vector.dotProduct
  have hzero : (0 : Rat) + 0 = 0 := by grind
  simpa [hzero, Fin.foldl_eq_finRange_foldl] using
    gapH427 (xs := List.finRange m) (a := a) (b := b) (c := c)
      (accA := 0) (accB := 0)
private theorem gapH399
    (xs : List (Fin m)) (s : Rat) (a c : Vector Rat m) (acc : Rat) :
    xs.foldl (fun acc i => acc + (s • a)[i] * (c)[i]) (s * acc) =
      s * xs.foldl (fun acc i => acc + a[i] * (c)[i]) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons i xs ih =>
      have hentry : (s • a)[i] = s * a[i] := by
        change (s • a)[i.val] = s * a[i.val]
        rw [Vector.getElem_smul]; rfl
      simp only [List.foldl_cons]
      have hstart :
          s * acc + (s • a)[i] * (c)[i] =
            s * (acc + a[i] * (c)[i]) := by
        rw [hentry]; grind
      rw [hstart]
      exact ih (acc := acc + a[i] * (c)[i])
private theorem gapH342 (s : Rat) (a c : Vector Rat m) :
    (s • a).dotProduct c = s * a.dotProduct c := by
  unfold Vector.dotProduct
  have hzero : s * (0 : Rat) = 0 := by grind
  simpa [hzero, Fin.foldl_eq_finRange_foldl] using
    gapH399 (xs := List.finRange m) (s := s) (a := a) (c := c) (acc := 0)
private theorem gapH124 (a b c : Vector Rat m) :
    projectionCoeff (a + b) c = projectionCoeff a c + projectionCoeff b c := by
  unfold projectionCoeff
  by_cases hnorm : c.dotProduct c = 0
  · simp [hnorm] <;> grind
  · simp [hnorm]
    rw [gapH382]
    grind
private theorem gapH116 (s : Rat) (a c : Vector Rat m) :
    projectionCoeff (s • a) c = s * projectionCoeff a c := by
  unfold projectionCoeff
  by_cases hnorm : c.dotProduct c = 0
  · simp [hnorm]
  · simp [hnorm]
    rw [gapH342]
    grind
private theorem gapH294 (a b c : Vector Rat m) :
    subtractProjection (a + b) c =
      subtractProjection a c + subtractProjection b c := by
  apply Vector.ext
  intro k hk
  unfold subtractProjection
  have hcoeff := gapH124 a b c
  have hentry_lhs :
      ((a + b) - projectionCoeff (a + b) c • c)[k] =
        a[k] + b[k] - projectionCoeff (a + b) c * (c)[k] := by
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    rfl
  have hentry_rhs :
      (a - projectionCoeff a c • c + (b - projectionCoeff b c • c))[k] =
        a[k] - projectionCoeff a c * (c)[k] +
          (b[k] - projectionCoeff b c * (c)[k]) := by
    rw [Vector.getElem_add, Vector.getElem_sub, Vector.getElem_sub,
      Vector.getElem_smul, Vector.getElem_smul]
    rfl
  rw [hentry_lhs, hentry_rhs, hcoeff]
  grind
private theorem gapH278 (s : Rat) (a c : Vector Rat m) :
    subtractProjection (s • a) c = s • subtractProjection a c := by
  apply Vector.ext
  intro k hk
  unfold subtractProjection
  have hcoeff := gapH116 s a c
  have hentry_lhs :
      (s • a - projectionCoeff (s • a) c • c)[k] =
        s * a[k] - projectionCoeff (s • a) c * (c)[k] := by
    rw [Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_smul]
    rfl
  have hentry_rhs :
      (s • (a - projectionCoeff a c • c))[k] =
        s * (a[k] - projectionCoeff a c * (c)[k]) := by
    rw [Vector.getElem_smul, Vector.getElem_sub, Vector.getElem_smul]
    rfl
  rw [hentry_lhs, hentry_rhs, hcoeff]
  grind
private theorem gapH50
    (basisRev : List (Vector Rat m)) (a b : Vector Rat m) :
    reduceAgainstBasis basisRev (a + b) =
      reduceAgainstBasis basisRev a + reduceAgainstBasis basisRev b := by
  induction basisRev generalizing a b with
  | nil => simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [gapH294]
      change reduceAgainstBasis rest
          (subtractProjection a basisRow + subtractProjection b basisRow) =
        reduceAgainstBasis rest (subtractProjection a basisRow) +
          reduceAgainstBasis rest (subtractProjection b basisRow)
      exact ih (a := subtractProjection a basisRow) (b := subtractProjection b basisRow)
private theorem gapH79
    (basisRev : List (Vector Rat m)) (s : Rat) (a : Vector Rat m) :
    reduceAgainstBasis basisRev (s • a) = s • reduceAgainstBasis basisRev a := by
  induction basisRev generalizing a with
  | nil => simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [gapH278]
      change reduceAgainstBasis rest (s • subtractProjection a basisRow) =
        s • reduceAgainstBasis rest (subtractProjection a basisRow)
      exact ih (a := subtractProjection a basisRow)
private theorem gapH315
    (l₁ l₂ : List (Vector Rat m)) (row : Vector Rat m) :
    reduceAgainstBasis (l₁ ++ l₂) row =
      reduceAgainstBasis l₂ (reduceAgainstBasis l₁ row) := by
  unfold reduceAgainstBasis
  rw [List.foldl_append]
private theorem gapH39
    (rows : List (Vector Rat m)) (i j : Nat)
    (hi : i < rows.length) (hj : j < rows.length) (hij : i ≠ j) :
    (basisRows rows)[i]!.dotProduct (basisRows rows)[j]! = 0 := by
  have hilen : i < (basisRows rows).length := by simpa [basisRows_length]
  have hjlen : j < (basisRows rows).length := by simpa [basisRows_length]
  have hpair : (basisRows rows).Pairwise
      (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) :=
    basisRows_pairwise rows
  have hget_i : (basisRows rows)[i]! = (basisRows rows)[i] := by simp [hilen]
  have hget_j : (basisRows rows)[j]! = (basisRows rows)[j] := by simp [hjlen]
  by_cases hlt : i < j
  · have hrel :=
      (List.pairwise_iff_getElem.1 hpair) i j hilen hjlen hlt
    rw [hget_i, hget_j]
    exact hrel.1
  · have hji : j < i :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hij h.symm)
    have hrel :=
      (List.pairwise_iff_getElem.1 hpair) j i hjlen hilen hji
    rw [hget_i, hget_j]
    exact hrel.2
private theorem gapH461 (v : Vector Rat m) : (0 : Vector Rat m) + v = v := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_add, Vector.getElem_zero]
  grind
private theorem gapH448 (s : Rat) : s • (0 : Vector Rat m) = 0 := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_smul, Vector.getElem_zero]
  show s * (0 : Rat) = 0
  grind
private theorem gapH15
    (rows : List (Vector Rat m)) (ℓ k : Nat)
    (hℓk : ℓ < k) (hk : k ≤ rows.length) :
    reduceAgainstBasis ((basisRows rows).take k).reverse
        (basisRows rows)[ℓ]! = 0 := by
  have hℓlen : ℓ < rows.length := Nat.lt_of_lt_of_le hℓk hk
  have hℓbasis : ℓ < (basisRows rows).length := by simpa [basisRows_length]
  have hkbasis : k ≤ (basisRows rows).length := by simpa [basisRows_length]
  have htake_take :
      ((basisRows rows).take k).take (ℓ + 1) = (basisRows rows).take (ℓ + 1) := by
    rw [List.take_take]
    congr 1
    omega
  have hsplit :
      (basisRows rows).take k =
        (basisRows rows).take (ℓ + 1) ++
          ((basisRows rows).take k).drop (ℓ + 1) := by
    rw [← htake_take]
    exact (List.take_append_drop (ℓ + 1) ((basisRows rows).take k)).symm
  rw [hsplit, List.reverse_append, gapH315]
  have hinner :
      reduceAgainstBasis (((basisRows rows).take k).drop (ℓ + 1)).reverse
          (basisRows rows)[ℓ]! = (basisRows rows)[ℓ]! := by
    apply gapH106
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hilen, hbget⟩ := hmem
    have hdroplen :
        (((basisRows rows).take k).drop (ℓ + 1)).length =
          ((basisRows rows).take k).length - (ℓ + 1) := by
      rw [List.length_drop]
    have htakelen : ((basisRows rows).take k).length = k := by
      rw [List.length_take]; omega
    rw [hdroplen, htakelen] at hilen
    have hidx_lt_basis : i + (ℓ + 1) < (basisRows rows).length := by
      have : k ≤ (basisRows rows).length := hkbasis
      omega
    have hidx_lt_take : i + (ℓ + 1) < ((basisRows rows).take k).length := by
      rw [htakelen]; omega
    have hidx_lt_basis' : ℓ + 1 + i < (basisRows rows).length := by
      have hcomm : ℓ + 1 + i = i + (ℓ + 1) := by omega
      rw [hcomm]; exact hidx_lt_basis
    have hbget' :
        b = (basisRows rows)[ℓ + 1 + i]'hidx_lt_basis' := by
      rw [← hbget, List.getElem_drop, List.getElem_take]
    have hbget!_eq :
        b = (basisRows rows)[ℓ + 1 + i]! := by
      rw [hbget']
      simp [hidx_lt_basis']
    rw [hbget!_eq]
    apply gapH39 rows ℓ (ℓ + 1 + i) hℓlen
    ·
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    · omega
  rw [hinner]
  exact gapH104 rows ℓ hℓlen
private theorem gapH31
    (basisRev basisRev' : List (Vector Rat m)) (row acc : Vector Rat m)
    (hzero : ∀ b ∈ basisRev, reduceAgainstBasis basisRev' b = 0)
    (haccZero : reduceAgainstBasis basisRev' acc = 0) :
    reduceAgainstBasis basisRev' (projectionCombination row basisRev acc) = 0 := by
  induction basisRev generalizing acc with
  | nil =>
      simp [projectionCombination]
      exact haccZero
  | cons b rest ih =>
      show reduceAgainstBasis basisRev'
          (projectionCombination row (b :: rest) acc) = 0
      simp only [projectionCombination, List.foldl_cons]
      change reduceAgainstBasis basisRev'
          (projectionCombination row rest
            (acc + projectionCoeff row b • b)) = 0
      apply ih
      · intro b' hb'
        exact hzero b' (by simp [hb'])
      · rw [gapH50, haccZero, gapH79,
          hzero b (by simp), gapH448, gapH461]
private theorem gapH32
    (rows : List (Vector Rat m)) (j k : Nat)
    (hjk : j < k) (hk : k ≤ rows.length) :
    reduceAgainstBasis ((basisRows rows).take k).reverse rows[j]! = 0 := by
  have hjlen : j < rows.length := Nat.lt_of_lt_of_le hjk hk
  have hjbasis : j < (basisRows rows).length := by simpa [basisRows_length]
  have hrec :=
    basisRows_get!_eq_reduceAgainstBasis_forward (rows := rows) (k := j) hjlen
  rw [hrec, gapH50]
  rw [gapH15 rows j k hjk hk, gapH461]
  apply gapH31
  · intro b hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hilen, hbget⟩ := hmem
    have htakelen : ((basisRows rows).take j).length = j := by
      rw [List.length_take]; omega
    rw [htakelen] at hilen
    have hi_lt_basis : i < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[i]'hi_lt_basis := by
      rw [← hbget, List.getElem_take]
    have hbget!_eq : b = (basisRows rows)[i]! := by
      rw [hbget']; simp [hi_lt_basis]
    rw [hbget!_eq]
    apply gapH15 rows i k _ hk
    omega
  · exact gapH82 _
private theorem gapH357
    (rows rows' : List (Vector Rat m)) (i : Nat)
    (hlen : rows'.length = rows.length)
    (hprefix : ∀ t, t < i → rows'[t]! = rows[t]!)
    (hi : i ≤ rows.length) :
    (basisRows rows').take i = (basisRows rows).take i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ rows.length := Nat.le_of_succ_le hi
    have ihtake := ih (by
      intro t ht
      exact hprefix t (Nat.lt_trans ht (Nat.lt_succ_self i))) hi'
    have hi_lt : i < rows.length := hi
    have hi_lt_rows' : i < rows'.length := by rw [hlen]; exact hi_lt
    have hb1_len : (basisRows rows').length = rows.length := by
      rw [basisRows_length, hlen]
    have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
    have hi_lt_b1 : i < (basisRows rows').length := by rw [hb1_len]; exact hi_lt
    have hi_lt_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi_lt
    rw [List.take_succ_eq_append_getElem hi_lt_b1,
        List.take_succ_eq_append_getElem hi_lt_b2,
        ihtake]
    congr 1
    have hge1 : (basisRows rows')[i] = (basisRows rows')[i]! :=
      (getElem!_pos _ i hi_lt_b1).symm
    have hge2 : (basisRows rows)[i] = (basisRows rows)[i]! :=
      (getElem!_pos _ i hi_lt_b2).symm
    rw [hge1, hge2]
    congr 1
    rw [basisRows_get!_eq_reduceAgainstBasis_take rows' i hi_lt_rows',
        basisRows_get!_eq_reduceAgainstBasis_take rows i hi_lt,
        ihtake,
        hprefix i (Nat.lt_succ_self i)]
private theorem gapH303
    (rows rows' : List (Vector Rat m)) (i : Nat)
    (hlen : rows'.length = rows.length)
    (hprefix : ∀ t, t ≤ i → rows'[t]! = rows[t]!)
    (hi : i < rows.length) :
    (basisRows rows')[i]! = (basisRows rows)[i]! := by
  have htake :=
    gapH357 rows rows' (i + 1) hlen
      (by
        intro t ht
        exact hprefix t (Nat.le_of_lt_succ ht))
      (Nat.succ_le_of_lt hi)
  have hb1_len : (basisRows rows').length = rows.length := by
    rw [basisRows_length, hlen]
  have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
  have hi_b1 : i < (basisRows rows').length := by rw [hb1_len]; exact hi
  have hi_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi
  have hget :=
    congrArg (fun xs : List (Vector Rat m) => xs[i]?) htake
  simp [hi_b1, hi_b2] at hget
  simp [hget, hi_b1, hi_b2]
private theorem gapH85
    (rows : List (Vector Rat m)) (km1 k : Nat)
    (hkm1 : km1 + 1 = k) (hk : k < rows.length) :
    reduceAgainstBasis ((basisRows rows).take km1).reverse rows[k]! =
      (basisRows rows)[k]! +
        projectionCoeff rows[k]! (basisRows rows)[km1]! • (basisRows rows)[km1]! := by
  have hh544 : km1 < k := by omega
  have hkm1_lt_rows : km1 < rows.length := Nat.lt_trans hh544 hk
  have hbasis_k_len : k < (basisRows rows).length := by simpa [basisRows_length]
  have hbasis_km1_len : km1 < (basisRows rows).length := by
    simpa [basisRows_length] using hkm1_lt_rows
  have hrec :=
    basisRows_get!_eq_reduceAgainstBasis_forward (rows := rows) (k := k) hk
  have htake :
      (basisRows rows).take k =
        (basisRows rows).take km1 ++ [(basisRows rows)[km1]!] := by
    rw [← hkm1, List.take_succ_eq_append_getElem hbasis_km1_len]
    congr 1
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hbasis_km1_len]
  have hbasis_k :
      reduceAgainstBasis ((basisRows rows).take km1).reverse (basisRows rows)[k]! =
        (basisRows rows)[k]! := by
    apply gapH106
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, hbget⟩ := hmem
    have hh559 : ((basisRows rows).take km1).length = km1 := by
      rw [List.length_take]
      omega
    have hidx_km1 : idx < km1 := by
      rw [hh559] at hidx
      exact hidx
    have hh538 : idx < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[idx]! := by
      rw [← hbget, List.getElem_take]
      simp [hh538]
    rw [hbget']
    exact gapH39 rows k idx hk
      (by omega) (by omega)
  have hproj_prefix :
      reduceAgainstBasis ((basisRows rows).take km1).reverse
        (projectionCombination rows[k]! ((basisRows rows).take km1) 0) = 0 := by
    apply gapH31
    · intro b hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨idx, hidx, hbget⟩ := hmem
      have hh559 : ((basisRows rows).take km1).length = km1 := by
        rw [List.length_take]
        omega
      have hidx_km1 : idx < km1 := by
        rw [hh559] at hidx
        exact hidx
      have hh538 : idx < (basisRows rows).length := by
        have : (basisRows rows).length = rows.length := basisRows_length rows
        omega
      have hbget' : b = (basisRows rows)[idx]! := by
        rw [← hbget, List.getElem_take]
        simp [hh538]
      rw [hbget']
      apply gapH15 rows idx km1 hidx_km1
      omega
    · exact gapH82 _
  have hbasis_km1 :
      reduceAgainstBasis ((basisRows rows).take km1).reverse (basisRows rows)[km1]! =
      (basisRows rows)[km1]! := by
    apply gapH106
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, hbget⟩ := hmem
    have hh559 : ((basisRows rows).take km1).length = km1 := by
      rw [List.length_take]
      omega
    have hidx_km1 : idx < km1 := by
      rw [hh559] at hidx
      exact hidx
    have hh538 : idx < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[idx]! := by
      rw [← hbget, List.getElem_take]
      simp [hh538]
    rw [hbget']
    exact gapH39 rows km1 idx hkm1_lt_rows
      (by omega) (by omega)
  conv => lhs; rw [hrec]
  rw [htake, projectionCombination_append, projectionCombination_singleton]
  repeat rw [gapH50]
  rw [hbasis_k, hproj_prefix, gapH79, hbasis_km1]
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_add, Vector.getElem_add, Vector.getElem_zero]
  grind
private theorem gapH316
    (rows : List (Vector Rat m)) (j k : Nat) (c : Rat)
    (hjk : j < k) (hk : k < rows.length) (i : Nat) (hi : i ≤ rows.length) :
    (basisRows (rows.set k (rows[k]! + c • rows[j]!))).take i =
      (basisRows rows).take i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ rows.length := Nat.le_of_succ_le hi
    have ihtake := ih hi'
    have hi_lt : i < rows.length := hi
    have hrows'_len :
        (rows.set k (rows[k]! + c • rows[j]!)).length = rows.length := by simp
    have hi_lt_rows' : i < (rows.set k (rows[k]! + c • rows[j]!)).length := by
      rw [hrows'_len]; exact hi_lt
    have hb1_len :
        (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length = rows.length := by
      rw [basisRows_length, hrows'_len]
    have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
    have hi_lt_b1 :
        i < (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length := by
      rw [hb1_len]; exact hi_lt
    have hi_lt_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi_lt
    rw [List.take_succ_eq_append_getElem hi_lt_b1,
        List.take_succ_eq_append_getElem hi_lt_b2,
        ihtake]
    congr 1
    have hge1 :
        (basisRows (rows.set k (rows[k]! + c • rows[j]!)))[i] =
          (basisRows (rows.set k (rows[k]! + c • rows[j]!)))[i]! :=
      (getElem!_pos _ i hi_lt_b1).symm
    have hge2 : (basisRows rows)[i] = (basisRows rows)[i]! :=
      (getElem!_pos _ i hi_lt_b2).symm
    rw [hge1, hge2]
    congr 1
    rw [basisRows_get!_eq_reduceAgainstBasis_take
          (rows.set k (rows[k]! + c • rows[j]!)) i hi_lt_rows',
        basisRows_get!_eq_reduceAgainstBasis_take rows i hi_lt,
        ihtake]
    by_cases hik : i = k
    ·
      have hrows'_get_eq :
          (rows.set k (rows[k]! + c • rows[j]!))[i]! = rows[k]! + c • rows[j]! := by
        rw [hik]
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hk]
      rw [hrows'_get_eq, gapH50,
          gapH79]
      have hsrc :
          reduceAgainstBasis ((basisRows rows).take i).reverse rows[j]! = 0 := by
        rw [hik]
        exact gapH32 rows j k hjk
            (Nat.le_of_lt hk)
      rw [hsrc]
      have hrhs_get :
          reduceAgainstBasis ((basisRows rows).take i).reverse rows[i]! =
            reduceAgainstBasis ((basisRows rows).take i).reverse rows[k]! := by
        rw [hik]
      rw [hrhs_get, gapH448]
      apply Vector.ext
      intro idx hidx
      rw [Vector.getElem_add, Vector.getElem_zero]
      grind
    ·
      have hne : k ≠ i := Ne.symm hik
      have hrows'_get_eq :
          (rows.set k (rows[k]! + c • rows[j]!))[i]! = rows[i]! := by
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]
      rw [hrows'_get_eq]
private theorem gapH386
    (rows : List (Vector Rat m)) (j k : Nat) (c : Rat)
    (hjk : j < k) (hk : k < rows.length) :
    basisRows (rows.set k (rows[k]! + c • rows[j]!)) = basisRows rows := by
  have h :=
    gapH316 rows j k c hjk hk rows.length (Nat.le_refl _)
  have hlen1 :
      (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length = rows.length := by
    rw [basisRows_length, List.length_set]
  have hlen2 : (basisRows rows).length = rows.length := basisRows_length rows
  rw [List.take_of_length_le (Nat.le_of_eq hlen1),
      List.take_of_length_le (Nat.le_of_eq hlen2)] at h
  exact h
private theorem gapH423
    (b : Matrix Rat n m) (src dst : Fin n) (c : Rat) (h : src.val < dst.val) :
    basisMatrix (Matrix.rowAdd b src dst c) = basisMatrix b := by
  unfold basisMatrix
  have hsrc_toList : b.rows.toList[src.val]! = b[src] := by
    simp [Hex.Matrix.getRow]
  have hdst_toList : b.rows.toList[dst.val]! = b[dst] := by
    simp [Hex.Matrix.getRow]
  have htoList :
      (Matrix.rowAdd b src dst c).rows.toList =
        b.rows.toList.set dst.val
          (b.rows.toList[dst.val]! + c • b.rows.toList[src.val]!) := by
    rw [Matrix.rowAdd_eq_set, Matrix.rows_setRow]
    rw [Vector.toList_set]
    congr 1
    rw [hsrc_toList, hdst_toList]
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_ofFn, Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [htoList, gapH386 b.rows.toList src.val dst.val c h
    (by rw [Vector.length_toList]; exact dst.isLt)]
private theorem gapH203
    (b : Matrix Rat n m) (km1 k : Fin n) (t : Nat)
    (hkm1k : km1.val < k.val) (ht : t < km1.val) :
    (Matrix.rowSwap b km1 k).rows.toList[t]! = b.rows.toList[t]! := by
  have ht_n : t < n := Nat.lt_trans ht km1.isLt
  let r : Fin n := ⟨t, ht_n⟩
  have hrk : r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    change t = k.val at hval
    omega
  have hrkm1 : r ≠ km1 := by
    intro h
    have hval := congrArg Fin.val h
    change t = km1.val at hval
    omega
  have hleft :
      (Matrix.rowSwap b km1 k).rows.toList[t]! = (Matrix.rowSwap b km1 k).row r := by
    have hget :
        (Matrix.rowSwap b km1 k).rows.toList[t]! =
          (Matrix.rowSwap b km1 k).rows.toList[t]'(by simp [ht_n]) :=
      getElem!_pos _ t (by simp [ht_n])
    simpa [Matrix.row, Vector.getElem_toList, r, Hex.Matrix.getRow, Fin.getElem_fin] using hget
  have hright : b.rows.toList[t]! = b.row r := by
    have hget : b.rows.toList[t]! = b.rows.toList[t]'(by simp [ht_n]) :=
      getElem!_pos _ t (by simp [ht_n])
    simpa [Matrix.row, Vector.getElem_toList, r, Hex.Matrix.getRow, Fin.getElem_fin] using hget
  rw [hleft, hright]
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[r][cc] = b[r][cc]
  rw [Matrix.getElem_rowSwap]
  simp [hrk, hrkm1]
private theorem gapH325
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1k : km1.val ≠ k.val) :
    (Matrix.rowSwap b km1 k).rows.toList[km1.val]! = b.rows.toList[k.val]! := by
  have hleft :
      (Matrix.rowSwap b km1 k).rows.toList[km1.val]! =
        (Matrix.rowSwap b km1 k).row km1 := by
    simp [Matrix.row, Hex.Matrix.getRow]
  have hright : b.rows.toList[k.val]! = b.row k := by
    simp [Matrix.row, Hex.Matrix.getRow]
  rw [hleft, hright]
  have hne : km1 ≠ k := by
    intro h
    exact hkm1k (congrArg Fin.val h)
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[km1][cc] = b[k][cc]
  rw [Matrix.getElem_rowSwap]
  simp [hne]
private theorem gapH401
    (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row i = (basisMatrix b).row i := by
  rw [basisMatrix_row_eq_basisRows_get!, basisMatrix_row_eq_basisRows_get!]
  apply gapH303
  · simp
  · intro t ht
    exact gapH203 b km1 k t hkm1k (Nat.lt_of_le_of_lt ht hi)
  · simp
private theorem gapH231
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row km1 =
      (basisMatrix b).row k +
        projectionCoeff (b.row k) ((basisMatrix b).row km1) • (basisMatrix b).row km1 := by
  rw [basisMatrix_row_eq_basisRows_get!, basisMatrix_row_eq_basisRows_get!,
    basisMatrix_row_eq_basisRows_get!]
  have hswap_row :
      (Matrix.rowSwap b km1 k).rows.toList[km1.val]! = b.rows.toList[k.val]! := by
    apply gapH325
    omega
  have hprefix :
      ((basisRows (Matrix.rowSwap b km1 k).rows.toList).take km1.val) =
        ((basisRows b.rows.toList).take km1.val) := by
    apply gapH357
    · simp
    · intro t ht
      exact gapH203 b km1 k t (by omega) ht
    · simp
  have hlen_swap : (Matrix.rowSwap b km1 k).rows.toList.length = b.rows.toList.length := by simp
  have hkm1_lt_len : km1.val < b.rows.toList.length := by simp [km1.isLt]
  have hkm1_lt_swap : km1.val < (Matrix.rowSwap b km1 k).rows.toList.length := by
    rw [hlen_swap]; exact hkm1_lt_len
  rw [basisRows_get!_eq_reduceAgainstBasis_take
        (Matrix.rowSwap b km1 k).rows.toList km1.val hkm1_lt_swap,
      hprefix, hswap_row]
  have hreduce :=
    gapH85
      (rows := b.rows.toList) (km1 := km1.val) (k := k.val) hkm1 (by simp [k.isLt])
  simpa [Matrix.row, Hex.Matrix.getRow, Fin.getElem_fin] using hreduce
private theorem gapH341 (a b c : Vector Rat m) :
    a.dotProduct (b + c) = a.dotProduct b + a.dotProduct c := by
  rw [dot_comm_rat, gapH382, dot_comm_rat b a, dot_comm_rat c a]
private theorem gapH309 (s : Rat) (a b : Vector Rat m) :
    a.dotProduct (s • b) = s * a.dotProduct b := by
  rw [dot_comm_rat, gapH342, dot_comm_rat b a]
private theorem gapH412 (a : Vector Rat m) :
    a.dotProduct 0 = 0 := by
  unfold Vector.dotProduct
  change (List.finRange m).foldl
      (fun acc i => acc + a[i] * (0 : Vector Rat m)[i]) 0 = 0
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hterm : a[i] * (0 : Vector Rat m)[i] = 0 := by
        change a[i] * (0 : Vector Rat m)[i.val] = 0
        rw [Vector.getElem_zero]
        grind
      rw [hterm, show (0 : Rat) + 0 = 0 by grind]
      exact ih
private theorem gapH456
    (acc row : Vector Rat m) (c : Rat)
    (horth : acc.dotProduct row = 0) :
    (acc + c • row).normSq =
      acc.normSq + c * c * row.normSq := by
  change (acc + c • row).dotProduct (acc + c • row) =
    acc.dotProduct acc + c * c * row.dotProduct row
  rw [gapH382, gapH341 acc acc (c • row), gapH309, gapH342,
    gapH341 row acc (c • row), gapH309, horth]
  have horth' : row.dotProduct acc = 0 := by
    rw [dot_comm_rat]
    exact horth
  rw [horth']
  grind
private theorem gapH404 {α : Type v}
    (xs : List α) (f : α → Rat) (acc : Rat) :
    xs.foldl (fun total x => total + f x) acc =
      acc + xs.foldl (fun total x => total + f x) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp <;> grind
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc
      xs.foldl (fun total x => total + f x) (acc + f x) =
          (acc + f x) + xs.foldl (fun total x => total + f x) 0 := ih (acc + f x)
      _ = acc + ((0 + f x) + xs.foldl (fun total x => total + f x) 0) := by grind
      _ = acc + xs.foldl (fun total x => total + f x) (0 + f x) := by
          rw [ih (0 + f x)]
private theorem gapH229
    (xs : List (Fin n)) (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (acc : Vector Rat m)
    (hnodup : xs.Nodup)
    (hacc : ∀ i ∈ xs, acc.dotProduct (rows.row i) = 0)
    (horth : ∀ i ∈ xs, ∀ j ∈ xs, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0) :
    Vector.normSq
        (xs.foldl (fun acc i => acc + coeffs[i] • rows.row i) acc) =
      acc.normSq +
        xs.foldl
          (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp <;> grind
  | cons i rest ih =>
    simp only [List.foldl_cons]
    have hnodup_tail : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hi_not_mem : i ∉ rest := (List.nodup_cons.mp hnodup).1
    let acc' := acc + coeffs[i] • rows.row i
    have hacc' : ∀ j ∈ rest, acc'.dotProduct (rows.row j) = 0 := by
      intro j hj
      have hij : i ≠ j := by
        intro h
        subst h
        exact hi_not_mem hj
      have hrow : (rows.row i).dotProduct (rows.row j) = 0 :=
        horth i (by simp) j (by simp [hj]) hij
      simp only [acc']
      rw [gapH382, gapH342, hacc j (by simp [hj]), hrow]
      grind
    have horth' : ∀ a ∈ rest, ∀ b ∈ rest, a ≠ b →
        (rows.row a).dotProduct (rows.row b) = 0 := by
      intro a ha b hb hab
      exact horth a (by simp [ha]) b (by simp [hb]) hab
    rw [ih (acc := acc') hnodup_tail hacc' horth',
      gapH456 acc (rows.row i) coeffs[i] (hacc i (by simp))]
    rw [gapH404 rest
      (fun j => coeffs[j] * coeffs[j] * (rows.row j).normSq)
      (0 + coeffs[i] * coeffs[i] * (rows.row i).normSq)]
    grind
private theorem gapH159
    (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (horth : ∀ i j : Fin n, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0) :
    Vector.normSq
        (Fin.foldl n (fun acc i => acc + coeffs[i] • rows.row i) 0) =
      Fin.foldl n
        (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  have hacc : ∀ i ∈ List.finRange n, (0 : Vector Rat m).dotProduct (rows.row i) = 0 := by
    intro i _hi
    rw [dot_comm_rat]
    exact gapH412 (rows.row i)
  have horth' : ∀ i ∈ List.finRange n, ∀ j ∈ List.finRange n, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0 := by
    intro i _hi j _hj hij
    exact horth i j hij
  have h :=
    gapH229 (xs := List.finRange n)
      (rows := rows) (coeffs := coeffs) (acc := (0 : Vector Rat m))
      (List.nodup_finRange n) hacc horth'
  have hzero : (0 : Vector Rat m).normSq = 0 := by
    have hfold :
        ∀ xs : List (Fin m), ∀ acc : Rat,
          xs.foldl (fun acc _ => acc + 0) acc = acc := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          simp
      | cons _ rest ih =>
          intro acc
          simp only [List.foldl_cons]
          have hacc : acc + 0 = acc := by grind
          rw [hacc]
          exact ih acc
    simpa [Vector.normSq, Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using
      hfold (List.finRange m) 0
  rw [hzero] at h
  have hzero_add :
      (0 : Rat) +
          (List.finRange n).foldl
            (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 =
        (List.finRange n).foldl
            (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
    grind
  rw [hzero_add] at h
  exact h
theorem normSq_vecMul_of_orthogonal
    (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (horth : ∀ i j : Fin n, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0) :
    Vector.normSq (Matrix.vecMul coeffs rows) =
      Fin.foldl n
        (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
  rw [vecMul_eq_foldl_rows]
  exact gapH159 rows coeffs horth
end GramSchmidt
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt.Rat
@[grind =]
theorem basis_orthogonal (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((basis b).row ⟨i, hi⟩).dotProduct ((basis b).row ⟨j, hj⟩) = 0 := by
  rw [basis, GramSchmidt.basisMatrix_row_eq_basisRows_get!,
    GramSchmidt.basisMatrix_row_eq_basisRows_get!]
  exact GramSchmidt.gapH190 b i j hi hj hij
theorem coeffs_lower (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs b) i j =
      GramSchmidt.projectionCoeff (b.row i) ((basis b).row j) := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
    Matrix.row, show j < i from hji]
theorem coeffs_lower_projection (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs b) i j =
      (if ((basis b).row j).dotProduct ((basis b).row j) = 0 then 0
       else
        (b.row i).dotProduct ((basis b).row j) /
          ((basis b).row j).dotProduct ((basis b).row j)) := by
  rw [coeffs_lower (b := b) hji]
  rfl
@[grind =]
theorem basis_rowAdd (b : Matrix Rat n m) (src dst : Fin n) (c : Rat)
    (hsrcdst : src.val < dst.val) :
    basis (Matrix.rowAdd b src dst c) = basis b := by
  simpa [basis] using
    GramSchmidt.gapH423 (b := b) (src := src) (dst := dst) (c := c) hsrcdst
@[grind =]
theorem basis_rowSwap_of_before (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis] using
    GramSchmidt.gapH401 (b := b) (km1 := km1) (k := k)
      (i := i) hkm1k hi
@[grind =]
theorem basis_rowSwap_adjacent_prev (b : Matrix Rat n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val) :
    (basis (Matrix.rowSwap b km1 k)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  have hraw :=
    GramSchmidt.gapH231 (b := b) (km1 := km1) (k := k) hkm1
  have hlt : km1.val < k.val := by omega
  have hcoeff :
      GramSchmidt.projectionCoeff (b.row k) ((GramSchmidt.basisMatrix b).row km1) =
        GramSchmidt.entry (coeffs b) k km1 := by
    simpa [basis] using (coeffs_lower (b := b) hlt).symm
  simpa [basis, hcoeff] using hraw
private theorem gapH367 (b : Matrix Rat n m) (i j r : Fin n)
    (hri : r ≠ i) (hrj : r ≠ j) :
    (Matrix.rowSwap b i j).row r = b.row r := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[r][c] = b[r][c]
  rw [Matrix.getElem_rowSwap (M := b) (i := i) (j := j) (r := r) (k := c)]
  simp [hri, hrj]
@[grind =]
theorem coeffs_rowAdd_other_row (b : Matrix Rat n m) (src dst : Fin n) (c : Rat)
    (hsrcdst : src.val < dst.val) (row : Fin n) (hrow : row ≠ dst) :
    (coeffs (Matrix.rowAdd b src dst c)).row row = (coeffs b).row row := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  apply Vector.ext
  intro col hcol
  let colFin : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) row colFin =
    GramSchmidt.entry (coeffs b) row colFin
  simp only [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hbasis]
  rw [show (Matrix.rowAdd b src dst c).getRow row = b.getRow row from
    Matrix.row_rowAdd_of_ne b src c hrow]
@[grind =]
theorem coeffs_rowSwap_adjacent_before (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : i.val < km1.val) (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply gapH367
    · intro h
      have : i.val = km1.val := congrArg Fin.val h
      omega
    · intro h
      have : i.val = k.val := congrArg Fin.val h
      omega
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k
      (Nat.lt_trans hji hi)
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji,
    coeffs_lower_projection (b := b) (i := i) (j := j) hji, hrow, hbasis]
end GramSchmidt.Rat
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt.Int
@[grind =]
theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((basis b).row ⟨i, hi⟩).dotProduct ((basis b).row ⟨j, hj⟩) = 0 := by
  simpa [basis, GramSchmidt.Rat.basis] using
    GramSchmidt.Rat.basis_orthogonal (b := GramSchmidt.castIntMatrix b) i j hi hj hij
theorem basis_decomposition (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩) =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs, GramSchmidt.castIntMatrix, GramSchmidt.Rat.basis,
    GramSchmidt.Rat.coeffs, Matrix.row] using
      GramSchmidt.Rat.basis_decomposition (b := GramSchmidt.castIntMatrix b) i hi
@[simp, grind =]
theorem coeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]
@[grind =]
theorem coeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]
private theorem gapH25 (b : Matrix Int n m) (r : Fin n) (k : Fin m) :
    (GramSchmidt.castIntMatrix b)[r][k] = (b[r][k] : Rat) := by
  simp [GramSchmidt.castIntMatrix]
private theorem gapH137 (b : Matrix Int n m) (src dst : Fin n) (c : Int) :
    GramSchmidt.castIntMatrix (Matrix.rowAdd b src dst c) =
      Matrix.rowAdd (GramSchmidt.castIntMatrix b) src dst (c : Rat) := by
  apply Hex.Matrix.ext_getElem
  intro r k
  rw [gapH25, Matrix.getElem_rowAdd, Matrix.getElem_rowAdd,
    gapH25, gapH25]
  by_cases hdst : r = dst
  · simp only [hdst, ite_true]
    push_cast
    rfl
  · simp only [hdst, ite_false, gapH25]
private theorem gapH24 (b : Matrix Int n m) (i j : Fin n) :
    GramSchmidt.castIntMatrix (Matrix.rowSwap b i j) =
      Matrix.rowSwap (GramSchmidt.castIntMatrix b) i j := by
  apply Hex.Matrix.ext_getElem
  intro r k
  rw [gapH25, Matrix.getElem_rowSwap, Matrix.getElem_rowSwap,
    gapH25, gapH25, gapH25]
  by_cases hrj : r = j
  · simp [hrj]
  · by_cases hri : r = i <;> simp [hrj, hri]
@[grind =]
theorem basis_rowAdd (b : Matrix Int n m) (src dst : Fin n) (c : Int)
    (hsrcdst : src.val < dst.val) :
    basis (Matrix.rowAdd b src dst c) = basis b := by
  simpa [basis, GramSchmidt.Rat.basis, gapH137] using
    GramSchmidt.Rat.basis_rowAdd
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) (c := (c : Rat))
      hsrcdst
@[grind =]
theorem basis_rowSwap_of_before (b : Matrix Int n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis, GramSchmidt.Rat.basis, gapH24] using
    GramSchmidt.Rat.basis_rowSwap_of_before
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) hkm1k hi
@[grind =]
theorem basis_rowSwap_adjacent_prev (b : Matrix Int n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val) :
    (basis (Matrix.rowSwap b km1 k)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs,
    gapH24] using
    GramSchmidt.Rat.basis_rowSwap_adjacent_prev
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) hkm1
@[grind =]
theorem coeffs_rowSwap_adjacent_before (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : i.val < km1.val) (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH24] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_before
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hji
@[grind =]
theorem coeffs_rowAdd_other_row (b : Matrix Int n m) (src dst : Fin n) (c : Int)
    (hsrcdst : src.val < dst.val) (row : Fin n) (hrow : row ≠ dst) :
    (coeffs (Matrix.rowAdd b src dst c)).row row = (coeffs b).row row := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH137] using
    GramSchmidt.Rat.coeffs_rowAdd_other_row
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) (c := (c : Rat))
      hsrcdst row hrow
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {α : Type u}
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {α : Type u}
private theorem gapH288 {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} (xs : List β) (f : β → R) :
    xs.foldl (fun acc x => acc * f x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hzero : (0 : R) * f x = 0 := by grind
      simpa [hzero] using ih
private theorem gapH269 {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hzero : f i = 0) :
    xs.foldl (fun acc x => acc * f x) z = 0 := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [hzero]
        have hz : z * (0 : R) = 0 := by grind
        simpa [hz] using gapH288 xs f
      · have htail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) htail
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {α : Type u}
theorem detProduct_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detProduct (principalSubmatrix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n] := by
  unfold detProduct
  simp only [getElem_pair_eq_nested]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              M[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
        Fin.foldl n
          (fun acc i => acc * (principalSubmatrix M n (Nat.le_succ n))[i][v[i]]) 1 := by
    congr
    funext acc i
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    simp only [hget, getElem_principalSubmatrix]
    rfl
  have hlast :
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
        Fin.last n := by
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
  rw [hfold]
  simp [hlast]
theorem detTerm_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detSign (R := R) v *
        (detProduct (principalSubmatrix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_insertAt_last]
private theorem gapH217
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  unfold detProduct
  simp only [getElem_pair_eq_nested]
  rw [Fin.foldl_eq_finRange_foldl]
  apply gapH269
    (List.finRange (n + 1)) (Fin.last n)
    (fun r => M[r][(insertAt (Fin.last n) (v.map Fin.castSucc) i)[r]]) 1
    (List.mem_finRange (Fin.last n))
  have hiVal : i.val < n := by
    have hne : i.val ≠ n := by
      intro hval
      exact hi (Fin.ext hval)
    omega
  have hcolVal :
      ((insertAt (Fin.last n) (v.map Fin.castSucc) i)[Fin.last n]).val < n := by
    unfold insertAt
    simp [List.getElem_insertIdx_of_gt, hiVal, Vector.toList]
  exact hrow ((insertAt (Fin.last n) (v.map Fin.castSucc) i)[Fin.last n]) hcolVal
private theorem gapH259
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  unfold detTerm
  rw [gapH217 M v i hi hrow]
  grind
private theorem gapH227
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (z : R)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detSign (R := R) v *
        (detProduct (principalSubmatrix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  rw [← Fin.foldl_eq_finRange_foldl, Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_finRange_foldl]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply List.foldl_add_congr
          intro i _hmem
          rw [gapH259 M v i.castSucc
            (by
              intro hlast
              have hval := congrArg Fin.val hlast
              simp at hval
              exact (Nat.ne_of_lt i.isLt) hval)
            hrow]
      _ = z := by
          exact List.foldl_add_zero (List.finRange n) z
  rw [hprefix, detTerm_insertAt_last]
theorem det_eq_principalSubmatrix_mul_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1))
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    det M = det (principalSubmatrix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
  unfold det
  rw [permutationVectors_succ, List.foldl_add_flatMap]
  calc
    (permutationVectors n).foldl
        (fun acc v =>
          (List.map (fun i => insertAt (Fin.last n) (Vector.map Fin.castSucc v) i)
              (List.finRange (n + 1))).foldl
            (fun acc perm => acc + detTerm M perm) acc) 0 =
      (permutationVectors n).foldl
        (fun acc v =>
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) acc) 0 := by
        apply List.foldl_congr
        intro acc v _hmem
        simp only [List.foldl_map]
    _ =
      (permutationVectors n).foldl
        (fun acc v =>
          acc + detSign (R := R) v *
            (detProduct (principalSubmatrix M n (Nat.le_succ n)) v *
              M[Fin.last n][Fin.last n])) 0 := by
        apply List.foldl_congr
        intro acc v _hmem
        exact gapH227 M v acc hrow
    _ =
      (permutationVectors n).foldl
          (fun acc v => acc + detTerm (principalSubmatrix M n (Nat.le_succ n)) v) 0 *
        M[Fin.last n][Fin.last n] := by
        unfold detTerm
        calc
          (permutationVectors n).foldl
              (fun acc v =>
                acc + detSign (R := R) v *
                  (detProduct (principalSubmatrix M n (Nat.le_succ n)) v *
                    M[Fin.last n][Fin.last n])) 0 =
            (permutationVectors n).foldl
              (fun acc v =>
                acc + (detSign (R := R) v *
                  detProduct (principalSubmatrix M n (Nat.le_succ n)) v) *
                    M[Fin.last n][Fin.last n]) 0 := by
              apply List.foldl_add_congr
              intro v _hmem
              grind
          _ =
            (permutationVectors n).foldl
                (fun acc v =>
                  acc + detSign (R := R) v *
                    detProduct (principalSubmatrix M n (Nat.le_succ n)) v) 0 *
              M[Fin.last n][Fin.last n] := by
              exact List.foldl_add_mul_right_zero
                (permutationVectors n)
                (fun v => detSign (R := R) v *
                  detProduct (principalSubmatrix M n (Nat.le_succ n)) v)
                M[Fin.last n][Fin.last n]
    _ = det (principalSubmatrix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
        rfl
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {α : Type u}






























end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {α : Type u}




























attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast in
@[reducible] private def detMathlibCommRing {R : Type u} (s : Lean.Grind.CommRing R) : CommRing R :=
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ n := Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one, Lean.Grind.Semiring.natCast_succ] }

private theorem det_eq_mathlib_native {R : Type u} [s : Lean.Grind.CommRing R] {n : ℕ}
    (M : Matrix R n n) :
    letI := detMathlibCommRing s
    M.det = (HexMatrixTheory.matrixEquiv M).det := by
  letI := detMathlibCommRing s
  have h := HexMatrixTheory.det_eq M
  change M.det = (HexMatrixTheory.matrixEquiv M).det
  exact h

theorem det_rowSwap {R : Type u} [s : Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (rowSwap M i j) = -det M := by
  letI := detMathlibCommRing s
  rw [det_eq_mathlib_native, det_eq_mathlib_native]
  let A := HexMatrixTheory.matrixEquiv M
  have hswap : HexMatrixTheory.matrixEquiv (rowSwap M i j) =
      A.submatrix (Equiv.swap i j) id := by
    ext r c
    simp only [A, HexMatrixTheory.matrixEquiv_apply, getElem_rowSwap, _root_.Matrix.submatrix_apply,
      id_eq, Equiv.swap_apply_def]
    by_cases hi : r = i <;> by_cases hj : r = j <;> simp_all
  rw [hswap, _root_.Matrix.det_permute, Equiv.Perm.sign_swap h]
  simp [A]

theorem det_rowAdd {R : Type u} [s : Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (rowAdd M src dst c) = det M := by
  letI := detMathlibCommRing s
  rw [det_eq_mathlib_native, det_eq_mathlib_native]
  let A := HexMatrixTheory.matrixEquiv M
  have hadd : HexMatrixTheory.matrixEquiv (rowAdd M src dst c) =
      A.updateRow dst (A dst + c • A src) := by
    ext i j
    simp only [A, HexMatrixTheory.matrixEquiv_apply, getElem_rowAdd,
      _root_.Matrix.updateRow_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  erw [hadd]
  exact _root_.Matrix.det_updateRow_add_smul_self A h.symm c

theorem det_transpose {R : Type u} [s : Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) : det M.transpose = det M := by
  letI := detMathlibCommRing s
  rw [det_eq_mathlib_native, det_eq_mathlib_native]
  have htranspose : HexMatrixTheory.matrixEquiv M.transpose =
      (HexMatrixTheory.matrixEquiv M).transpose := by
    ext i j
    rw [HexMatrixTheory.matrixEquiv_apply, _root_.Matrix.transpose_apply,
      HexMatrixTheory.matrixEquiv_apply, getElem_transpose]
  rw [htranspose, _root_.Matrix.det_transpose]

theorem det_colAdd {R : Type u} [s : Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (colAdd M src dst c) = det M := by
  letI := detMathlibCommRing s
  rw [det_eq_mathlib_native, det_eq_mathlib_native]
  let A := HexMatrixTheory.matrixEquiv M
  have hadd : HexMatrixTheory.matrixEquiv (colAdd M src dst c) =
      A.updateCol dst (fun i => A i dst + c • A i src) := by
    ext i j
    simp only [A, HexMatrixTheory.matrixEquiv_apply, getElem_colAdd,
      _root_.Matrix.updateCol_apply, smul_eq_mul]
    split <;> simp_all only [HexMatrixTheory.matrixEquiv_apply]
  erw [hadd]
  exact _root_.Matrix.det_updateCol_add_smul_self A h.symm c
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {α : Type u}
private theorem matrixEquiv_setCol {R : Type u} {n : ℕ} (M : Matrix R n n)
    (dst : Fin n) (v : Fin n → R) :
    HexMatrixTheory.matrixEquiv (setCol M dst v) = (HexMatrixTheory.matrixEquiv M).updateCol dst v := by
  ext i j
  simp only [HexMatrixTheory.matrixEquiv_apply, getElem_setCol, _root_.Matrix.updateCol_apply]

theorem det_setCol_add {R : Type u} [s : Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (setCol M dst (fun r => v r + w r)) =
      det (setCol M dst v) + det (setCol M dst w) := by
  letI := detMathlibCommRing s
  simp only [det_eq_mathlib_native, matrixEquiv_setCol]
  exact _root_.Matrix.det_updateCol_add _ _ _ _

theorem det_setCol_smul {R : Type u} [s : Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R) :
    det (setCol M dst (fun r => c * v r)) =
      c * det (setCol M dst v) := by
  letI := detMathlibCommRing s
  simp only [det_eq_mathlib_native, matrixEquiv_setCol]
  exact _root_.Matrix.det_updateCol_smul _ _ _ _
theorem det_setCol_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    det (setCol M dst (fun _ => (0 : R))) = 0 := by
  have h := det_setCol_smul M dst (0 : R) (fun _ => (1 : R))
  have hcol : (fun r : Fin n => (0 : R) * (1 : R)) = fun _ => (0 : R) := by
    funext r
    grind
  rw [hcol] at h
  grind
theorem det_setCol_sum_list {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) {β : Type v} (xs : List β)
    (coeff : β → R) (source : β → Fin n → R) :
    det (setCol M dst
        (fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0)) =
      xs.foldl
        (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
  induction xs with
  | nil =>
      exact det_setCol_zero M dst
  | cons x xs ih =>
      simp only [List.foldl_cons]
      let tail : Fin n → R :=
        fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0
      have hcol :
          (fun r : Fin n =>
              xs.foldl (fun acc x => acc + coeff x * source x r)
                (0 + coeff x * source x r)) =
            fun r => coeff x * source x r + tail r := by
        funext r
        rw [List.foldl_add_eq_add_foldl]
        simp [tail]
        grind
      calc
        det (setCol M dst
            (fun r => xs.foldl (fun acc x => acc + coeff x * source x r)
              (0 + coeff x * source x r))) =
          det (setCol M dst (fun r => coeff x * source x r + tail r)) := by
            rw [hcol]
        _ =
          det (setCol M dst (fun r => coeff x * source x r)) +
            det (setCol M dst tail) := by
            exact det_setCol_add M dst (fun r => coeff x * source x r) tail
        _ =
          coeff x * det (setCol M dst (source x)) +
            xs.foldl (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
            rw [det_setCol_smul]
            simp [tail]
            rw [ih]
        _ =
          xs.foldl (fun acc x => acc + coeff x * det (setCol M dst (source x)))
            (0 + coeff x * det (setCol M dst (source x))) := by
            have hstart :=
              (List.foldl_add_eq_add_foldl (R := R) xs
                (fun x => coeff x * det (setCol M dst (source x)))
                (0 + coeff x * det (setCol M dst (source x)))).symm
            calc
              coeff x * det (setCol M dst (source x)) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 =
                (0 + coeff x * det (setCol M dst (source x))) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
                  grind
              _ =
                xs.foldl
                  (fun acc x => acc + coeff x * det (setCol M dst (source x)))
                  (0 + coeff x * det (setCol M dst (source x))) := hstart
theorem det_setCol_sum_finRange {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (M : Matrix R n n) (dst : Fin n) (coeff : Fin m → R)
    (source : Fin m → Fin n → R) :
    det (setCol M dst
        (fun r => (List.finRange m).foldl
          (fun acc x => acc + coeff x * source x r) 0)) =
      (List.finRange m).foldl
        (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 :=
  det_setCol_sum_list M dst (List.finRange m) coeff source
theorem det_eq_zero_of_col_eq {R : Type u} [s : Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    det M = 0 := by
  letI := detMathlibCommRing s
  rw [det_eq_mathlib_native]
  apply _root_.Matrix.det_zero_of_column_eq h
  simpa only [HexMatrixTheory.matrixEquiv_apply] using hcol
theorem det_setCol_existing_col_eq_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst src : Fin n) (hsrcdst : src ≠ dst) :
    det (setCol M dst (fun r => M[r][src])) = 0 := by
  apply det_eq_zero_of_col_eq (setCol M dst (fun r => M[r][src])) src dst hsrcdst
  intro r
  rw [getElem_setCol, getElem_setCol, if_neg hsrcdst, if_pos rfl]
theorem det_setCol_add_otherCols {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (sources : List (Fin n)) (coeff : Fin n → R)
    (hsrc : ∀ s ∈ sources, s ≠ dst) :
    det (setCol M dst
        (fun r => M[r][dst] +
          sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = det M := by
  rw [det_setCol_add M dst (fun r => M[r][dst])
    (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)]
  rw [setCol_self M dst]
  have hcomb : det (setCol M dst
        (fun r => sources.foldl (fun acc s => acc + coeff s * M[r][s]) 0)) = 0 := by
    rw [det_setCol_sum_list M dst sources coeff (fun s r => M[r][s])]
    have hzero_each : ∀ s ∈ sources, coeff s * det (setCol M dst (fun r => M[r][s])) = 0 := by
      intro s hs
      have hne : s ≠ dst := hsrc s hs
      rw [det_setCol_existing_col_eq_zero M dst s hne]
      grind
    have hfoldl : sources.foldl
        (fun acc s => acc + coeff s * det (setCol M dst (fun r => M[r][s]))) 0 = 0 := by
      clear hzero_each
      induction sources with
      | nil => rfl
      | cons s ss ih =>
          simp only [List.foldl_cons]
          have hs : coeff s * det (setCol M dst (fun r => M[r][s])) = 0 := by
            have hne : s ≠ dst := hsrc s (by simp)
            rw [det_setCol_existing_col_eq_zero M dst s hne]
            grind
          rw [hs]
          have hsrc' : ∀ s' ∈ ss, s' ≠ dst := fun s' hs' => hsrc s' (by simp [hs'])
          have hzero_acc : (0 : R) + 0 = 0 := by grind
          rw [hzero_acc]
          exact ih hsrc'
    exact hfoldl
  rw [hcomb]
  grind
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {α : Type u}
theorem det_upperTriangular_eq_finFoldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0) :
    det M = Fin.foldl n (fun acc i => acc * M[i][i]) 1 := by
  induction n with
  | zero =>
      simp only [Fin.foldl_zero]
      simp [det, permutationVectors, detTerm, detSign, detProduct,
        inversionCount]
      grind
  | succ n ih =>
      have hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0 := by
        intro j hj
        exact hzero (Fin.last n) j hj
      rw [det_eq_principalSubmatrix_mul_last M hrow]
      have hprefixZero :
          ∀ i j : Fin n, j.val < i.val →
            (principalSubmatrix M n (Nat.le_succ n))[i][j] = 0 := by
        intro i j hij
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        let jj : Fin (n + 1) := ⟨j.val, by omega⟩
        have hentry : (principalSubmatrix M n (Nat.le_succ n))[i][j] = M[ii][jj] :=
          getElem_principalSubmatrix M n (Nat.le_succ n) i j
        rw [hentry]
        exact hzero ii jj hij
      rw [ih (principalSubmatrix M n (Nat.le_succ n)) hprefixZero]
      rw [Fin.foldl_succ_last]
      have hcongr :
          Fin.foldl n
              (fun acc i => acc * (principalSubmatrix M n (Nat.le_succ n))[i][i]) 1 =
            Fin.foldl n (fun acc i => acc * M[i.castSucc][i.castSucc]) 1 := by
        rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
        apply List.foldl_congr
        intro acc i _hmem
        have hentry : (principalSubmatrix M n (Nat.le_succ n))[i][i] = M[i.castSucc][i.castSucc] :=
          getElem_principalSubmatrix M n (Nat.le_succ n) i i
        rw [hentry]
      rw [hcongr]
theorem det_lowerTriangular_eq_finFoldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, i.val < j.val → M[i][j] = 0) :
    det M = Fin.foldl n (fun acc i => acc * M[i][i]) 1 := by
  rw [← det_transpose M]
  have htransposeZero :
      ∀ i j : Fin n, j.val < i.val → M.transpose[i][j] = 0 := by
    intro i j hij
    have hentry : M.transpose[i][j] = M[j][i] := getElem_transpose M i j
    rw [hentry]
    exact hzero j i hij
  rw [det_upperTriangular_eq_finFoldl_diag M.transpose htransposeZero]
  have hdiag : ∀ i : Fin n, M.transpose[i][i] = M[i][i] := by
    intro i
    exact getElem_transpose M i i
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  apply List.foldl_congr
  intro acc i _hmem
  rw [hdiag]
theorem det_lowerTriangular_eq_foldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, i.val < j.val → M[i][j] = 0) :
    det M = (List.finRange n).foldl (fun acc i => acc * M[i][i]) 1 := by
  rw [det_lowerTriangular_eq_finFoldl_diag M hzero, Fin.foldl_eq_finRange_foldl]
end Matrix
end Hex
end
end
section
section
namespace Hex
universe u
namespace Matrix
variable {R : Type u} {n : Nat}
namespace BareissData
@[grind =]
theorem det_succ_eq [Zero R] [One R] [Neg R] [Mul R]
    {k : Nat} (data : BareissData R (k + 1))
    (h : data.singularStep = none) :
    data.det = data.sign *
      data.matrix[(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] := by
  unfold det
  rw [h, ← Matrix.getElem_pair_eq_nested]
  rfl
@[grind =]
theorem det_zero_eq [Zero R] [One R] [Neg R] [Mul R] (data : BareissData R 0)
    (h : data.singularStep = none) :
    data.det = data.sign := by
  unfold det
  rw [h]
  rfl
end BareissData
theorem findPivotAux_ge_start [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat) {pivot : Fin n}
    (hfind : findPivotAux M col start fuel = some pivot) :
    start ≤ pivot.val := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux] at hfind
  | succ fuel ih =>
      by_cases hstart : start < n
      · simp [findPivotAux, hstart] at hfind
        split at hfind
        · exact Nat.le_trans (Nat.le_succ start) (ih (start + 1) hfind)
        · cases hfind
          exact Nat.le_refl _
      · simp [findPivotAux, hstart] at hfind
@[grind →]
theorem findPivot?_ge_start [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat) {pivot : Fin n}
    (hfind : findPivot? M col start = some pivot) :
    start ≤ pivot.val :=
  findPivotAux_ge_start M col start (n - start) hfind
theorem findPivotAux_eq_zero_of_none [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat) (hfind : findPivotAux M col start fuel = none)
    (i : Fin n) (hstart : start ≤ i.val) (hfuel : i.val < start + fuel) :
    M[i][col] = 0 := by
  induction fuel generalizing start with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases hlt : start < n
      · by_cases hi : i.val = start
        · have hentry : M[(⟨start, hlt⟩ : Fin n)][col] = 0 := by
            by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
            · exact hzero
            · have hzeroNat : ¬ M[start][col.val] = 0 := by
                simpa using hzero
              simp only [findPivotAux, hlt, dif_pos] at hfind
              rw [if_neg (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
              simp at hfind
          have hiFin : i = (⟨start, hlt⟩ : Fin n) := Fin.ext hi
          rw [hiFin]
          exact hentry
        · have hentry : M[(⟨start, hlt⟩ : Fin n)][col] = 0 := by
            by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
            · exact hzero
            · have hzeroNat : ¬ M[start][col.val] = 0 := by
                simpa using hzero
              simp only [findPivotAux, hlt, dif_pos] at hfind
              rw [if_neg (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
              simp at hfind
          have hnext : findPivotAux M col (start + 1) fuel = none := by
            have hentryNat : M[start][col.val] = 0 := by
              simpa using hentry
            simp only [findPivotAux, hlt, dif_pos] at hfind
            rw [if_pos (by simpa [getRow, Fin.getElem_fin] using hentry)] at hfind
            exact hfind
          have hstart' : start + 1 ≤ i.val := by omega
          have hfuel' : i.val < start + 1 + fuel := by omega
          exact ih (start + 1) hnext hstart' hfuel'
      · omega
@[grind]
theorem findPivot?_eq_zero_of_none [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat) (hfind : findPivot? M col start = none)
    (i : Fin n) (hstart : start ≤ i.val) :
    M[i][col] = 0 := by
  apply findPivotAux_eq_zero_of_none M col start (n - start) hfind i hstart
  omega
theorem findPivotAux_eq_none_of_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat)
    (hzero : ∀ i : Fin n, start ≤ i.val → i.val < start + fuel → M[i][col] = 0) :
    findPivotAux M col start fuel = none := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux]
  | succ fuel ih =>
      by_cases hstart : start < n
      · have hentry : M[(⟨start, hstart⟩ : Fin n)][col] = 0 :=
          hzero ⟨start, hstart⟩ (Nat.le_refl _)
            (show (⟨start, hstart⟩ : Fin n).val < start + (fuel + 1) by
              simp)
        simp only [findPivotAux, hstart, dif_pos]
        rw [if_pos (by simpa [getRow, Fin.getElem_fin] using hentry)]
        apply ih
        intro i hle hlt
        exact hzero i (by omega) (by omega)
      · simp [findPivotAux, hstart]
theorem findPivot?_eq_none_of_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat)
    (hzero : ∀ i : Fin n, start ≤ i.val → M[i][col] = 0) :
    findPivot? M col start = none := by
  apply findPivotAux_eq_none_of_zero M col start (n - start)
  intro i hle _hlt
  exact hzero i hle
theorem findPivotAux_some_ne_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start fuel : Nat) {pivot : Fin n}
    (hfind : findPivotAux M col start fuel = some pivot) :
    M[pivot][col] ≠ 0 := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux] at hfind
  | succ fuel ih =>
      by_cases hlt : start < n
      · by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
        · simp only [findPivotAux, hlt, dif_pos] at hfind
          rw [if_pos (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
          exact ih (start + 1) hfind
        · simp only [findPivotAux, hlt, dif_pos] at hfind
          rw [if_neg (by simpa [getRow, Fin.getElem_fin] using hzero)] at hfind
          simp only [Option.some.injEq] at hfind
          subst hfind
          exact hzero
      · simp [findPivotAux, hlt] at hfind
@[grind →]
theorem findPivot?_some_ne_zero [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n)
    (start : Nat) {pivot : Fin n}
    (hfind : findPivot? M col start = some pivot) :
    M[pivot][col] ≠ 0 :=
  findPivotAux_some_ne_zero M col start (n - start) hfind
@[grind =]
theorem stepMatrixWith_diag_of_le
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i : Fin n)
    (hi : i.val ≤ k) :
    (stepMatrixWith quot M k pivot prevPivot)[i][i] = M[i][i] := by
  apply stepMatrixWith_eq_of_not_update
  · intro htrail
    exact Nat.not_lt_of_ge hi htrail.1
  · intro hcol
    exact Nat.not_lt_of_ge hi hcol.1
@[grind =]
theorem getEntry_matrixToRows [Zero R] (M : Matrix R n n) (i j : Fin n) :
    getEntry (matrixToRows M) i.val j.val = M[i][j] := by
  simp [getEntry, matrixToRows]
@[grind =]
theorem rowsToMatrix_matrixToRows [Zero R] (M : Matrix R n n) :
    rowsToMatrix (matrixToRows M) n = M := by
  apply Matrix.ext_getElem
  intro i j
  unfold rowsToMatrix
  rw [Matrix.getElem_ofFn]
  exact getEntry_matrixToRows M i j
section GenericBareiss
variable [Zero R] [One R] [Neg R] [Sub R] [Mul R] [DecidableEq R]
variable {quot : R → R → R}
omit [One R] [Neg R] in
@[grind]
theorem pivotLoopWith_zero_fuel (state : BareissState R n) :
    pivotLoopWith quot 0 state = state := by
  rfl
omit [One R] [Neg R] in
@[grind]
theorem pivotLoopWith_done (fuel : Nat) (state : BareissState R n)
    (hDone : ¬ state.step + 1 < n) :
    pivotLoopWith quot (fuel + 1) state = state := by
  simp [pivotLoopWith, hDone]
omit [One R] [Neg R] in
@[grind]
theorem pivotLoopWith_of_regular_no_swap (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    pivotLoopWith quot (fuel + 1) state =
      pivotLoopWith quot fuel
        { step := state.step + 1
          matrix := stepMatrixWith quot state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp_all [pivotLoopWith, getRow, Fin.getElem_fin]
omit [One R] [Neg R] in
@[grind]
theorem pivotLoopWith_of_singular_no_pivot (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    pivotLoopWith quot (fuel + 1) state =
      { state with singularStep := some state.step } := by
  simp_all [pivotLoopWith]
omit [One R] [Neg R] in
@[grind]
theorem pivotLoopWith_of_regular_swap (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0) {pivot : Fin n}
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot)
    (hp :
      (rowSwap state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)[state.step][state.step] ≠ 0) :
    pivotLoopWith quot (fuel + 1) state =
      pivotLoopWith quot fuel
        { step := state.step + 1
          matrix := stepMatrixWith quot
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)
            state.step
            ((rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step])
            state.prevPivot
          prevPivot :=
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step]
          rowSwaps := state.rowSwaps + 1
          singularStep := none } := by
  simp_all [pivotLoopWith]
omit [One R] [Neg R] in
@[grind =]
theorem noPivotLoopWith_diag_of_le_step (fuel : Nat) (state : BareissState R n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoopWith quot fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoopWith_matrix_entry_of_row_le_or_col_lt (quot := quot) fuel state i i (Or.inl hi)
omit [One R] [Neg R] in
@[grind =]
theorem noPivotLoopWith_rowSwaps (fuel : Nat) (state : BareissState R n) :
    (noPivotLoopWith quot fuel state).rowSwaps = state.rowSwaps := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoopWith]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoopWith_of_singular (quot := quot) fuel state hDone hp]
        · rw [noPivotLoopWith_of_regular (quot := quot) fuel state hDone]
          · let next : BareissState R n :=
              { step := state.step + 1
                matrix := stepMatrixWith quot state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoopWith quot fuel next).rowSwaps = state.rowSwaps
            rw [ih next]
          · simpa [k] using hp
      · simp [noPivotLoopWith_done (quot := quot) fuel state hDone]
omit [One R] [Neg R] in
theorem pivotLoopWith_eq_noPivotLoopWith_of_no_singular {n : Nat}
    (fuel : Nat) (state : BareissState R n)
    (hh509 : (noPivotLoopWith quot fuel state).singularStep = none) :
    pivotLoopWith quot fuel state = noPivotLoopWith quot fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        ·
          rw [noPivotLoopWith_of_singular (quot := quot) f state hDone hp] at hh509
          simp at hh509
        ·
          let next : BareissState R n :=
            { step := state.step + 1
              matrix := stepMatrixWith quot state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          rw [noPivotLoopWith_of_regular (quot := quot) f state hDone hp,
            pivotLoopWith_of_regular_no_swap (quot := quot) f state hDone hp]
          show pivotLoopWith quot f next = noPivotLoopWith quot f next
          apply ih
          show (noPivotLoopWith quot f next).singularStep = none
          rw [← noPivotLoopWith_of_regular (quot := quot) f state hDone hp]
          exact hh509
      · rw [pivotLoopWith_done (quot := quot) f state hDone]
        rw [noPivotLoopWith_done (quot := quot) f state hDone]
omit [Neg R] in
theorem bareissDataWith_eq_finish_pivotLoopWith (M : Matrix R n n) :
    bareissDataWith quot M = finish (pivotLoopWith quot n (noPivotInitialState M)) := by
  simp [bareissDataWith, bareissArrayStateWith, noPivotInitialState, finish,
    rowsToMatrix_matrixToRows]
theorem bareissWith_eq_noPivotLoopWith_last_of_no_singular {k : Nat}
    (M : Matrix R (k + 1) (k + 1))
    (hh509 :
      (noPivotLoopWith quot k (noPivotInitialState M)).singularStep = none)
    (hone : ∀ x : R, 1 * x = x) :
    bareissWith quot M =
      (noPivotLoopWith quot k (noPivotInitialState M)).matrix[Fin.last k][Fin.last k] := by
  let init := noPivotInitialState M
  let stateK := noPivotLoopWith quot k init
  have h_step : stateK.step = k := by
    have h := noPivotLoopWith_step_eq_add_of_singularStep_none (quot := quot) k init rfl
      (by simp [init, noPivotInitialState]) hh509
    simpa [stateK, init, noPivotInitialState] using h
  have hDone_stateK : ¬ stateK.step + 1 < k + 1 := by omega
  have h_full_nopivot : noPivotLoopWith quot (k + 1) init = stateK := by
    rw [noPivotLoopWith_add (quot := quot) k 1 init]
    exact noPivotLoopWith_id_at_done (quot := quot) 1 stateK hDone_stateK
  have h_full_sing : (noPivotLoopWith quot (k + 1) init).singularStep = none := by
    rw [h_full_nopivot]
    exact hh509
  have hpivot := pivotLoopWith_eq_noPivotLoopWith_of_no_singular (quot := quot) (k + 1) init h_full_sing
  rw [bareissWith_eq_bareissDataWith_det (quot := quot), bareissDataWith_eq_finish_pivotLoopWith (quot := quot), hpivot, h_full_nopivot]
  have hdet := BareissData.det_succ_eq (finish stateK) hh509
  rw [hdet]
  simp [finish, BareissData.sign, stateK, init, noPivotInitialState,
    noPivotLoopWith_rowSwaps (quot := quot), hone,
    getRow, Fin.getElem_fin]
end GenericBareiss
@[grind =]
theorem stepMatrix_diag_of_le (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i : Fin n) (hi : i.val ≤ k) :
    (stepMatrix M k pivot prevPivot)[i][i] = M[i][i] :=
  stepMatrixWith_diag_of_le exactDiv M k pivot prevPivot i hi
@[grind]
theorem pivotLoop_of_regular_no_swap (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    pivotLoop (fuel + 1) state =
      pivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } :=
  pivotLoopWith_of_regular_no_swap (quot := exactDiv) fuel state hDone hp
@[grind]
theorem pivotLoop_of_singular_no_pivot (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    pivotLoop (fuel + 1) state =
      { state with singularStep := some state.step } :=
  pivotLoopWith_of_singular_no_pivot (quot := exactDiv) fuel state hDone hp0 hfind
@[grind =]
theorem noPivotLoop_diag_of_le_step (fuel : Nat) (state : BareissState Int n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoop fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoopWith_diag_of_le_step (quot := exactDiv) fuel state i hi
theorem bareissNoPivotData_eq_finish (M : Matrix Int n n) :
    bareissNoPivotData M = finish (noPivotLoop n (noPivotInitialState M)) :=
  rfl
theorem bareissData_eq_finish_pivotLoop (M : Matrix Int n n) :
    bareissData M = finish (pivotLoop n (noPivotInitialState M)) :=
  bareissDataWith_eq_finish_pivotLoopWith (quot := exactDiv) M
theorem bareiss_eq_bareissData_det (M : Matrix Int n n) :
    bareiss M = (bareissData M).det :=
  bareissWith_eq_bareissDataWith_det (quot := exactDiv) M
theorem bareiss_eq_noPivotLoop_last_of_no_singular {k : Nat}
    (M : Matrix Int (k + 1) (k + 1))
    (hh509 :
      (noPivotLoop k (noPivotInitialState M)).singularStep = none) :
    bareiss M =
      (noPivotLoop k (noPivotInitialState M)).matrix[Fin.last k][Fin.last k] :=
  bareissWith_eq_noPivotLoopWith_last_of_no_singular
    (quot := exactDiv) M hh509 Int.one_mul
end Matrix
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
theorem leadingGramMatrixInt_eq_principalSubmatrix_gram
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    leadingGramMatrixInt b k hk =
      Matrix.principalSubmatrix (Matrix.gramMatrix b) k hk := by
  apply Hex.Matrix.ext_getElem
  intro i j
  simp only [leadingGramMatrixInt, Matrix.getElem_ofFn,
    Matrix.getElem_principalSubmatrix, Matrix.getElem_gramMatrix, liftFinLE]
end GramSchmidt
namespace GramSchmidt.Int
private theorem gapH134
    (data : Matrix.BareissData Int n) (s r : Nat) (hr : r < n)
    (hsing : data.singularStep = some s) (hs : s < r + 1) :
    gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
  simp [gramDetVecEntry, hsing, hs]
theorem gramDetVecEntry_noPivot_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (s r : Nat) (hr : r < n)
    (hsing : (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).singularStep = some s)
    (hs : s < r + 1) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 :=
  gapH134
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)) s r hr hsing hs
private theorem gapH67 (b : Matrix Int n m) (i j : Fin n) :
    getArrayEntry (gramRows b) i.val j.val = (Matrix.gramMatrix b)[i][j] := by
  rw [Matrix.getElem_gramMatrix]
  simp [getArrayEntry, gramRows, Vector.dotProduct]
private theorem gapH192 (b : Matrix Int n m) :
    rowsToMatrix (gramRows b) n = Matrix.gramMatrix b := by
  apply Hex.Matrix.ext_getElem
  intro i j
  rw [rowsToMatrix, Matrix.getElem_ofFn, gapH67]
private theorem gapH127 {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]
private theorem gapH252 {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.set! i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.set!
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]
private theorem gapH4
    (rows : Array (Array Int)) (row col r c : Nat) (value : Int) (hr : r ≠ row) :
    getArrayEntry (setArrayEntry rows row col value) r c = getArrayEntry rows r c := by
  grind [getArrayEntry, setArrayEntry]
private theorem gapH1
    (rows : Array (Array Int)) (row col c : Nat) (value : Int) (hc : c ≠ col) :
    getArrayEntry (setArrayEntry rows row col value) row c = getArrayEntry rows row c := by
  grind [getArrayEntry, setArrayEntry]
private theorem gapH28
    (rows : Array (Array Int)) (row col : Nat) (value : Int)
    (hrow : row < rows.size) (hcol : col < rows[row]!.size) :
    getArrayEntry (setArrayEntry rows row col value) row col = value := by
  unfold getArrayEntry setArrayEntry
  rw [gapH127 rows hrow (rows[row]!.set! col value)]
  exact gapH127 rows[row]! hcol value
private theorem gapH183 (rows : Array (Array Int)) (row col : Nat) (value : Int) :
    (setArrayEntry rows row col value).size = rows.size := by
  simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
private theorem gapH88
    (rows : Array (Array Int)) (row col r : Nat) (value : Int) :
    (setArrayEntry rows row col value)[r]!.size = rows[r]!.size := by
  unfold setArrayEntry
  by_cases hrow : r = row
  · subst r
    by_cases hbound : row < rows.size
    · rw [gapH127 _ hbound]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    · simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hbound]
  · simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.set!_eq_setIfInBounds]
    have hne : row ≠ r := fun h => hrow h.symm
    by_cases hbound : row < rows.size
    · simp [hne]
    · simp [Array.setIfInBounds, hbound]
private theorem gapH146
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k i j : Nat)
    (hxs : ∀ x ∈ xs, k < x) (hi : i ≤ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        i j =
      getArrayEntry coeffs i j := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : k < x := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, k < y := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs',
        gapH4]
      omega
private theorem gapH118
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat)
    (hr : r ∉ xs) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hrx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hrxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hrxs,
        gapH4]
      exact hrx
private theorem gapH147
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat) (hc : c ≠ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k))]
      by_cases hrow : r = x
      · subst x
        rw [gapH1 _ _ _ _ _ hc]
      · rw [gapH4]
        exact hrow
private theorem gapH140
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r : Nat)
    (hrmem : r ∈ xs) (hnodup : xs.Nodup)
    (hrow : r < coeffs.size) (hcol : k < coeffs[r]!.size) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r k =
      getArrayEntry rows r k := by
  induction xs generalizing coeffs with
  | nil =>
      exact absurd hrmem (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hrmem with hr_eq | hr_in
      · subst x
        rw [gapH118]
        · exact gapH28 coeffs r k
            (getArrayEntry rows r k) hrow hcol
        · exact hxnotmem
      · have hr_ne_x : r ≠ x := by
          intro h
          subst r
          exact hxnotmem hr_in
        have hrow' : r < (setArrayEntry coeffs x k (getArrayEntry rows x k)).size := by
          simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
        have hcol' :
            k < (setArrayEntry coeffs x k (getArrayEntry rows x k))[r]!.size := by
          unfold setArrayEntry
          rw [gapH252 _ hr_ne_x]
          exact hcol
        exact ih (setArrayEntry coeffs x k (getArrayEntry rows x k))
          hr_in hnodup' hrow' hcol'
private theorem gapH57
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      grind
private theorem gapH197
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [gapH57 _ _ _ _ hxnotmem]
        grind
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.set! x (f x arr[x]!)).size := by
          simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hbound]
        rw [ih _ hr_in hnodup' hbound']
        grind
private theorem gapH425
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
private theorem gapH365
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    arr.modify i f = arr.set! i (f arr[i]!) := by
  grind
private theorem gapH340
    {α : Type} [Inhabited α] (arr : Array α) (i r : Nat) (f : α → α)
    (hr : r ≠ i) :
    (arr.modify i f)[r]! = arr[r]! := by
  rw [gapH365]
  grind
private theorem gapH394
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α)
    (hi : i < arr.size) :
    (arr.modify i f)[i]! = f arr[i]! := by
  rw [gapH365]
  grind
private theorem gapH472
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    (arr.modify i f).size = arr.size := by
  rw [gapH365]
  simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
private theorem gapH62
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      exact gapH340 arr x r (f x) hx
private theorem gapH94
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [gapH62 _ _ _ _ hxnotmem]
        exact gapH394 arr r (f r) hbound
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.modify x (f x)).size := by
          rw [gapH472]
          exact hbound
        rw [ih _ hr_in hnodup' hbound', gapH340 arr x r (f x) hr_ne_x]
private theorem gapH436
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.modify x (f x)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact gapH472 arr x (f x)
private theorem gapH36
    (coeffs rows : Array (Array Int)) (n k : Nat)
    (hrow : k < coeffs.size) (hcol : k < coeffs[k]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) k k =
      getArrayEntry rows k k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [gapH146]
  · rw [gapH28 _ _ _ _ hrow hcol]
  · intro x hx
    simp at hx
    omega
  · omega
private theorem gapH34
    (coeffs rows : Array (Array Int)) (n k i : Nat)
    (hki : k < i) (hi : i < n)
    (hrow : i < coeffs.size) (hcol : k < coeffs[i]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) i k =
      getArrayEntry rows i k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have hmem : i ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨i - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hrow' : i < (setArrayEntry coeffs k k (getArrayEntry rows k k)).size := by
    simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
  have hcol' :
      k < (setArrayEntry coeffs k k (getArrayEntry rows k k))[i]!.size := by
    unfold setArrayEntry
    rw [gapH252 _ (show i ≠ k by omega)]
    exact hcol
  exact gapH140
    (List.range' (k + 1) (n - (k + 1)))
    (setArrayEntry coeffs k k (getArrayEntry rows k k)) rows k i
    hmem hnodup hrow' hcol'
private theorem gapH2
    (coeffs rows : Array (Array Int)) (n k r c : Nat) (hc : c ≠ k) :
    getArrayEntry (writeScaledColumn coeffs rows n k) r c =
      getArrayEntry coeffs r c := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [gapH147 _ _ _ _ _ _ hc]
  by_cases hrow : r = k
  · subst r
    rw [gapH1 _ _ _ _ _ hc]
  · rw [gapH4]
    exact hrow
private theorem gapH339
    (xs : List Nat) (init rows : Array (Array Int)) (k : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init).size =
      init.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact gapH183 _ _ _ _
private theorem gapH271
    (xs : List Nat) (init rows : Array (Array Int)) (k r : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init)[r]!.size =
      init[r]!.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact gapH88 _ _ _ _ _
private theorem gapH262
    (coeffs rows : Array (Array Int)) (n k : Nat) :
    (writeScaledColumn coeffs rows n k).size = coeffs.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [gapH339]
  exact gapH183 _ _ _ _
private theorem gapH173
    (coeffs rows : Array (Array Int)) (n k r : Nat) :
    (writeScaledColumn coeffs rows n k)[r]!.size = coeffs[r]!.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [gapH271]
  exact gapH88 _ _ _ _ _
private theorem gapH205 (j : Nat) :
    (default : Array Int)[j]! = 0 := by
  rfl
section StepScaledRowsBookkeeping
private theorem gapH164
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hr : r ≤ k) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      ((stepScaledRows rows n k pivot prevPivot)[r]!)[c]! =
        (rows[r]!)[c]!
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hnot : r ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hri⟩ := hmem
    omega
  rw [gapH62 _ _ _ _ hnot]
private theorem gapH70
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size) :
    (stepScaledRows rows n k pivot prevPivot)[r]! =
      (List.range' (k + 1) (n - (k + 1))).foldl
        (fun nextRow j =>
          nextRow.set! j
            (Matrix.exactDiv
              (pivot * nextRow[j]! - (rows[r]!)[k]! * getArrayEntry rows k j)
              prevPivot))
        (rows[r]!.set! k 0) := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hmem : r ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨r - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  rw [gapH94 _ _ _ _ hmem hnodup hrows]
  simp [getArrayEntry]
private theorem gapH162
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size)
    (hk_row : k < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r k = 0 := by
  show ((stepScaledRows rows n k pivot prevPivot)[r]!)[k]! = 0
  rw [gapH70 rows n k pivot prevPivot r hk hr hrows]
  have hnot : k ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hki⟩ := hmem
    omega
  rw [gapH57
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - (rows[r]!)[k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  grind
private theorem gapH178
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hkc : k < c) (hc : c < n)
    (hrows : r < rows.size) (hcols : c < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      Matrix.exactDiv
        (pivot * (rows[r]!)[c]! - (rows[r]!)[k]! * getArrayEntry rows k c)
        prevPivot := by
  show
      ((stepScaledRows rows n k pivot prevPivot)[r]!)[c]! =
        Matrix.exactDiv
          (pivot * (rows[r]!)[c]! - (rows[r]!)[k]! * getArrayEntry rows k c)
          prevPivot
  rw [gapH70 rows n k pivot prevPivot r hkr hr hrows]
  have hmem : c ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨c - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hbound : c < (rows[r]!.set! k 0).size := by
    simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hcols]
  rw [gapH197
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - (rows[r]!)[k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hmem hnodup hbound]
  have hck : c ≠ k := by omega
  grind
private theorem gapH166
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hc : c < k)
    (hrows : r < rows.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      ((stepScaledRows rows n k pivot prevPivot)[r]!)[c]! = (rows[r]!)[c]!
  rw [gapH70 rows n k pivot prevPivot r hkr hr hrows]
  have hnot : c ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hci⟩ := hmem
    omega
  rw [gapH57
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - (rows[r]!)[k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  have hck : c ≠ k := by omega
  grind
private theorem gapH314
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int) :
    (stepScaledRows rows n k pivot prevPivot).size = rows.size := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  exact gapH436 _ _ _
private theorem gapH218
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ r, r < n → rows[r]!.size = n) :
    ∀ r, r < n → (stepScaledRows rows n k pivot prevPivot)[r]!.size = n := by
  intro r hr
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  let xs := List.range' (k + 1) (n - (k + 1))
  let f : Nat → Array Int → Array Int := fun i sourceRow =>
    (List.range' (k + 1) (n - (k + 1))).foldl
      (fun nextRow j =>
        nextRow.set! j
          (Matrix.exactDiv
            (pivot * nextRow[j]! - sourceRow[k]! * (rows[k]!)[j]!)
            prevPivot))
      (sourceRow.set! k 0)
  by_cases hmem : r ∈ xs
  · have hnodup : xs.Nodup := by
      dsimp [xs]
      exact List.nodup_range'
    have hbound : r < rows.size := by
      rw [hsize]
      exact hr
    rw [gapH94 xs rows f r hmem hnodup hbound]
    dsimp [f]
    have hinner_size :=
      gapH425
        (List.range' (k + 1) (n - (k + 1)))
        (rows[r]!.set! k 0)
        (fun j nextEntry =>
          Matrix.exactDiv
            (pivot * nextEntry - (rows[r]!)[k]! * getArrayEntry rows k j)
            prevPivot)
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      hrowsize r hr] at hinner_size ⊢
    exact hinner_size
  · rw [gapH62 xs rows f r hmem]
    exact hrowsize r hr
private theorem gapH101
    {n : Nat} (rows : Array (Array Int)) (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int)
    (hentry : ∀ a b : Fin n, getArrayEntry rows a.val b.val = M[a][b])
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n)
    (i j : Fin n) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val =
      (Matrix.stepMatrix M k pivot prevPivot)[i][j] := by
  rcases Nat.lt_or_ge k i.val with hki | hki
  · rcases Nat.lt_or_ge k j.val with hkj | hkj
    ·
      have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
      have hcols : j.val < rows[i.val]!.size := by
        rw [hrowsize i.val i.isLt]; exact j.isLt
      have hij_eq : getArrayEntry rows i.val j.val = M[i][j] := hentry i j
      have hcol_eq :
          getArrayEntry rows i.val k =
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] := by
        simpa using hentry i ⟨k, Nat.lt_trans hki i.isLt⟩
      have hrow_eq :
          getArrayEntry rows k j.val =
            M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j] := by
        simpa using hentry ⟨k, Nat.lt_trans hkj j.isLt⟩ j
      rw [gapH178 rows n k pivot prevPivot
            i.val j.val hki i.isLt hkj j.isLt hrows hcols]
      rw [Matrix.stepMatrix_update_eq M k pivot prevPivot i j hki hkj]
      change Matrix.exactDiv
          (pivot * getArrayEntry rows i.val j.val -
            getArrayEntry rows i.val k * getArrayEntry rows k j.val) prevPivot =
        Matrix.exactDiv
          (pivot * M[i][j] -
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] *
              M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j]) prevPivot
      rw [hij_eq, hcol_eq, hrow_eq]
    ·
      rcases Nat.lt_or_eq_of_le hkj with hkj_lt | hkj_eq
      ·
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        rw [gapH166 rows n k pivot prevPivot
              i.val j.val hki i.isLt hkj_lt hrows]
        rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
              (fun h => Nat.not_lt_of_ge hkj h.2)
              (fun h => Nat.ne_of_lt hkj_lt h.2)]
        exact hentry i j
      ·
        have hjk : j.val = k := hkj_eq
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        have hk_row : k < rows[i.val]!.size := by
          rw [hrowsize i.val i.isLt]
          exact Nat.lt_of_lt_of_le hki (Nat.le_of_lt i.isLt)
        have hLHS :
            getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val = 0 := by
          rw [hjk]
          exact gapH162 rows n k pivot prevPivot
            i.val hki i.isLt hrows hk_row
        have hRHS :
            (Matrix.stepMatrix M k pivot prevPivot)[i][j] = 0 :=
          Matrix.stepMatrix_pivot_col_below M k pivot prevPivot i j hki hjk
        rw [hLHS]
        exact hRHS.symm
  ·
    rw [gapH164 rows n k pivot prevPivot
          i.val j.val hki]
    rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
          (fun h => Nat.not_lt_of_ge hki h.1)
          (fun h => Nat.not_lt_of_ge hki h.1)]
    exact hentry i j
private theorem gapH128
    {n : Nat} (rows : Array (Array Int)) (k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n) :
    rowsToMatrix (stepScaledRows rows n k pivot prevPivot) n =
      Matrix.stepMatrix (rowsToMatrix rows n) k pivot prevPivot := by
  apply Hex.Matrix.ext_getElem
  intro i j
  have hentry : ∀ a b : Fin n,
      getArrayEntry rows a.val b.val = (rowsToMatrix rows n)[a][b] := by
    intro a b
    rw [rowsToMatrix, Matrix.getElem_ofFn]
  rw [rowsToMatrix, Matrix.getElem_ofFn]
  exact gapH101 rows (rowsToMatrix rows n)
    k pivot prevPivot hentry hsize hrowsize i j
end StepScaledRowsBookkeeping
private theorem gapH107 (n i j : Nat) :
    getArrayEntry (zeroRows n) i j = 0 := by
  by_cases hi : i < n
  · by_cases hj : j < n <;> simp [zeroRows, getArrayEntry, hi, hj]
  · simp [zeroRows, getArrayEntry, hi, gapH205]
private theorem gapH343 (b : Matrix Int n m) : (gramRows b).size = n := by
  simp [gramRows]
private theorem gapH285 (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    (gramRows b)[r]!.size = n := by
  simp [gramRows, hr]
private theorem gapH302 (n : Nat) : (zeroRows n).size = n := by
  simp [zeroRows]
private theorem gapH153 (n : Nat) (r : Nat) (hr : r < n) :
    (zeroRows n)[r]!.size = n := by
  simp [zeroRows, hr]
private theorem gapH49
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hj : j < state.step) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state).coeffs i j =
      getArrayEntry state.coeffs i j := by
  induction fuel generalizing state with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [scaledCoeffArrayLoop]
      by_cases hstep : state.step < n
      · simp only [hstep, ↓reduceIte]
        by_cases hnext : state.step + 1 < n
        · simp only [hnext, ↓reduceIte]
          by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [hpivot, ↓reduceIte]
            rw [gapH2]
            omega
          · simp only [hpivot, ↓reduceIte]
            rw [ih]
            · rw [gapH2]
              omega
            · show j < state.step + 1
              omega
        · simp only [hnext, ↓reduceIte]
          rw [gapH2]
          omega
      · simp only [hstep, ↓reduceIte]
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt.Int
theorem scaledCoeffs_entry_eq_getArrayEntry
    (b : Matrix Int n m) (i j : Fin n) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      getArrayEntry (scaledCoeffRowsSchur b) i.val j.val := by
  simp only [GramSchmidt.entry, Matrix.getElem_row, scaledCoeffs, data,
    rowsToMatrix, Matrix.getElem_ofFn]
private theorem gapH233
    {n K : Nat} (M : Matrix Int n n) (hK : K ≤ n)
    (k : Nat) (pivot prevPivot : Int) :
    Matrix.principalSubmatrix (Matrix.stepMatrix M k pivot prevPivot) K hK =
      Matrix.stepMatrix (Matrix.principalSubmatrix M K hK) k pivot prevPivot := by
  apply Hex.Matrix.ext_getElem
  intro iK jK
  let i := iK.val
  let j := jK.val
  have hi : i < K := iK.isLt
  have hj : j < K := jK.isLt
  let iN : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hK⟩
  let jN : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hK⟩
  show (Matrix.principalSubmatrix (Matrix.stepMatrix M k pivot prevPivot) K hK)[iK][jK] =
      (Matrix.stepMatrix (Matrix.principalSubmatrix M K hK) k pivot prevPivot)[iK][jK]
  simp only [Matrix.getElem_principalSubmatrix]
  show (Matrix.stepMatrix M k pivot prevPivot)[iN][jN] =
      (Matrix.stepMatrix (Matrix.principalSubmatrix M K hK) k pivot prevPivot)[iK][jK]
  by_cases htrail : k < i ∧ k < j
  · have hki_n : k < iN.val := htrail.1
    have hkj_n : k < jN.val := htrail.2
    have hki_K : k < iK.val := htrail.1
    have hkj_K : k < jK.val := htrail.2
    rw [Matrix.stepMatrix_update_eq M k pivot prevPivot iN jN hki_n hkj_n]
    rw [Matrix.stepMatrix_update_eq (Matrix.principalSubmatrix M K hK) k pivot prevPivot
      iK jK hki_K hkj_K]
    simp only [Matrix.getElem_principalSubmatrix]
    rfl
  · by_cases hbelow : k < i ∧ j = k
    · have hki_n : k < iN.val := hbelow.1
      have hjk_n : jN.val = k := hbelow.2
      have hki_K : k < iK.val := hbelow.1
      have hjk_K : jK.val = k := hbelow.2
      rw [Matrix.stepMatrix_pivot_col_below M k pivot prevPivot iN jN hki_n hjk_n]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.principalSubmatrix M K hK) k
        pivot prevPivot iK jK hki_K hjk_K]
    · have hnot_n : ¬ (k < iN.val ∧ k < jN.val) := htrail
      have hnot_n' : ¬ (k < iN.val ∧ jN.val = k) := hbelow
      have hnot_K : ¬ (k < iK.val ∧ k < jK.val) := htrail
      have hnot_K' : ¬ (k < iK.val ∧ jK.val = k) := hbelow
      rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot iN jN hnot_n hnot_n']
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.principalSubmatrix M K hK) k
        pivot prevPivot iK jK hnot_K hnot_K']
      simp only [Matrix.getElem_principalSubmatrix]
      rfl
private theorem gapH265
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[(if h : i_bm.val < k then ⟨i_bm.val, Nat.lt_trans h hk⟩ else row)][
        (if h : j_bm.val < k then ⟨j_bm.val, Nat.lt_trans h hk⟩ else col)] := by
  by_cases hi_lt : i_bm.val < k
  · by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_lt_lt M k hk row col i_bm j_bm hi_lt hj_lt
      simp [hi_lt, hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_lt_last M k hk row col i_bm hi_lt
      rw [hjFin]
      simp [hi_lt] at h ⊢
      exact h
  · have hi_eq : i_bm.val = k := by
      have := i_bm.isLt
      omega
    have hiFin : i_bm = Fin.last k := Fin.ext (by simp [hi_eq])
    by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_last_lt M k hk row col j_bm hj_lt
      rw [hiFin]
      simp [hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_last_last M k hk row col
      rw [hiFin, hjFin]
      simp at h ⊢
      exact h
private theorem gapH170 {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val < k) :
    liftBorderedIdx hk anchor x = ⟨x.val, Nat.lt_trans h hk⟩ := by
  simp [liftBorderedIdx, h]
private theorem gapH131 {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val = k) :
    liftBorderedIdx hk anchor x = anchor := by
  have : ¬ x.val < k := fun h' => Nat.lt_irrefl _ (h ▸ h')
  simp [liftBorderedIdx, this]
private theorem gapH223 {n k : Nat} (hk : k < n) (anchor : Fin n)
    {k_step : Nat} (hkstep : k_step < k) (hh549 : k_step < n)
    (hh548 : k_step < k + 1) :
    liftBorderedIdx hk anchor ⟨k_step, hh548⟩ = ⟨k_step, hh549⟩ := by
  show (if h : k_step < k then (⟨k_step, Nat.lt_trans h hk⟩ : Fin n) else anchor) =
    ⟨k_step, hh549⟩
  simp [hkstep]
private theorem gapH295
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[liftBorderedIdx hk row i_bm][liftBorderedIdx hk col j_bm] := by
  rw [gapH265 M k hk row col i_bm j_bm]
  rfl
private theorem gapH292
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val)
    (k_step : Nat) (hkstep : k_step < k) (pivot prevPivot : Int) :
    Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col =
      Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot := by
  apply Hex.Matrix.ext_getElem
  intro i_bm j_bm
  let iN : Fin n := liftBorderedIdx hk row i_bm
  let jN : Fin n := liftBorderedIdx hk col j_bm
  have hi_iff : k_step < i_bm.val ↔ k_step < iN.val := by
    by_cases hi_lt : i_bm.val < k
    · have : iN = ⟨i_bm.val, Nat.lt_trans hi_lt hk⟩ :=
        gapH170 hk row i_bm hi_lt
      rw [show iN.val = i_bm.val from congrArg Fin.val this]
    · have hi_eq : i_bm.val = k := by have := i_bm.isLt; omega
      have : iN = row := gapH131 hk row i_bm hi_eq
      rw [show iN.val = row.val from congrArg Fin.val this, hi_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hrow
      · intro _; exact hkstep
  have hj_iff : k_step < j_bm.val ↔ k_step < jN.val := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        gapH170 hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := gapH131 hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hcol
      · intro _; exact hkstep
  have hj_eq_iff : j_bm.val = k_step ↔ jN.val = k_step := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        gapH170 hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := gapH131 hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro h; omega
      · intro h; exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le hkstep hcol))
  have h_entry : ∀ (M' : Matrix Int n n) (r : Fin (k + 1)) (c : Fin (k + 1)),
      (Matrix.borderedMinor M' k hk row col)[r][c] =
        M'[liftBorderedIdx hk row r][liftBorderedIdx hk col c] :=
    fun M' r c => gapH295 M' k hk row col r c
  show (Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col)[i_bm][j_bm] =
       (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm]
  rw [h_entry (Matrix.stepMatrix M k_step pivot prevPivot) i_bm j_bm]
  by_cases hh560 : k_step < i_bm.val ∧ k_step < j_bm.val
  · have htrail_N : k_step < iN.val ∧ k_step < jN.val :=
      ⟨hi_iff.mp hh560.1, hj_iff.mp hh560.2⟩
    have hh548 : k_step < k + 1 := Nat.lt_succ_of_lt hkstep
    have hh549 : k_step < n := Nat.lt_trans hkstep hk
    let colK_bm : Fin (k + 1) := ⟨k_step, hh548⟩
    let colK_N : Fin n := ⟨k_step, hh549⟩
    have hcolK_row : liftBorderedIdx hk row colK_bm = colK_N :=
      gapH223 hk row hkstep hh549 hh548
    have hcolK_col : liftBorderedIdx hk col colK_bm = colK_N :=
      gapH223 hk col hkstep hh549 hh548
    have h_iK : (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] = M[iN][colK_N] := by
      rw [h_entry M i_bm colK_bm]
      show M[iN][liftBorderedIdx hk col colK_bm] = M[iN][colK_N]
      exact congrArg (fun (x : Fin n) => M[iN][x]) hcolK_col
    have h_Kj : (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm] = M[colK_N][jN] := by
      rw [h_entry M colK_bm j_bm]
      show M[liftBorderedIdx hk row colK_bm][jN] = M[colK_N][jN]
      exact congrArg (fun (x : Fin n) => M[x][jN]) hcolK_row
    have hLHS :
        (Matrix.stepMatrix M k_step pivot prevPivot)[iN][jN] =
          Matrix.exactDiv (pivot * M[iN][jN] -
            M[iN][colK_N] * M[colK_N][jN]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq M k_step pivot prevPivot iN jN htrail_N.1 htrail_N.2]
    have hRHS :
        (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm] =
          Matrix.exactDiv (pivot * (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] -
            (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] *
            (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot
        i_bm j_bm hh560.1 hh560.2]
    rw [hLHS, hRHS, h_entry M i_bm j_bm, h_iK, h_Kj]
  · by_cases hh527 : k_step < i_bm.val ∧ j_bm.val = k_step
    · have hi_N : k_step < iN.val := hi_iff.mp hh527.1
      have hj_N : jN.val = k_step := hj_eq_iff.mp hh527.2
      rw [Matrix.stepMatrix_pivot_col_below M k_step pivot prevPivot iN jN hi_N hj_N]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm hh527.1 hh527.2]
    ·
      have hnot_trail_N : ¬ (k_step < iN.val ∧ k_step < jN.val) := by
        intro h
        exact hh560 ⟨hi_iff.mpr h.1, hj_iff.mpr h.2⟩
      have hnot_below_N : ¬ (k_step < iN.val ∧ jN.val = k_step) := by
        intro h
        exact hh527 ⟨hi_iff.mpr h.1, hj_eq_iff.mpr h.2⟩
      rw [Matrix.stepMatrix_eq_of_not_update M k_step pivot prevPivot iN jN
        hnot_trail_N hnot_below_N]
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm hh560 hh527]
      exact (h_entry M i_bm j_bm).symm
private theorem gapH214
    {n : Nat} (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState Int n) (state_bm : Matrix.BareissState Int (k + 1)),
      state_full.step = state_bm.step →
      state_full.prevPivot = state_bm.prevPivot →
      state_full.rowSwaps = state_bm.rowSwaps →
      state_full.singularStep = state_bm.singularStep →
      Matrix.borderedMinor state_full.matrix k hk row col = state_bm.matrix →
      fuel + state_full.step < k + 1 →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_bm).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_bm).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_bm).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_bm).singularStep ∧
      Matrix.borderedMinor (Matrix.noPivotLoop fuel state_full).matrix k hk row col =
          (Matrix.noPivotLoop fuel state_bm).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_k1 : state_full.step + 1 < k + 1 := by omega
      have h_step_lt_k : state_full.step < k := by omega
      have hh521 : state_full.step < n := Nat.lt_trans h_step_lt_k hk
      have hh502 : state_full.step + 1 < n := by
        have hk_le : k + 1 ≤ n := Nat.succ_le_of_lt hk
        omega
      have h_bm_done : state_bm.step + 1 < k + 1 := h_step ▸ h_step_lt_k1
      have h_bm_step_lt_k : state_bm.step < k := h_step ▸ h_step_lt_k
      let k_full : Fin n := ⟨state_full.step, hh521⟩
      let k_bm : Fin (k + 1) := ⟨state_bm.step, Nat.lt_succ_of_lt h_bm_step_lt_k⟩
      have hh507 : k_bm.val < k := h_bm_step_lt_k
      have hh514 :
          state_full.matrix[k_full][k_full] = state_bm.matrix[k_bm][k_bm] := by
        have hcongr :
            (Matrix.borderedMinor state_full.matrix k hk row col)[k_bm][k_bm] =
              state_bm.matrix[k_bm][k_bm] := by rw [h_mat]
        have h_bm_entry :=
          Matrix.borderedMinor_entry_lt_lt state_full.matrix k hk row col k_bm k_bm
            hh507 hh507
        simp only at h_bm_entry
        rw [h_bm_entry, Matrix.getElem_pair_eq_nested] at hcongr
        have h_idx : k_full = (⟨k_bm.val, Nat.lt_trans hh507 hk⟩ : Fin n) :=
          Fin.ext h_step
        calc state_full.matrix[k_full][k_full]
            = state_full.matrix[(⟨k_bm.val, Nat.lt_trans hh507 hk⟩ : Fin n)][
                (⟨k_bm.val, Nat.lt_trans hh507 hk⟩ : Fin n)] :=
              congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
          _ = state_bm.matrix[k_bm][k_bm] := hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      ·
        have hp_bm : state_bm.matrix[k_bm][k_bm] = 0 := by
          rw [← hh514]; exact hp_full
        rw [Matrix.noPivotLoop_of_singular f state_full hh502 hp_full,
          Matrix.noPivotLoop_of_singular f state_bm h_bm_done hp_bm]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      ·
        have hp_bm : state_bm.matrix[k_bm][k_bm] ≠ 0 := by
          rw [← hh514]; exact hp_full
        rw [Matrix.noPivotLoop_of_regular f state_full hh502 hp_full,
          Matrix.noPivotLoop_of_regular f state_bm h_bm_done hp_bm]
        have h_new_mat :
            Matrix.borderedMinor
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) k hk row col =
              Matrix.stepMatrix state_bm.matrix state_bm.step
                state_bm.matrix[k_bm][k_bm] state_bm.prevPivot := by
          rw [gapH292 state_full.matrix k hk row col hrow hcol
              state_full.step h_step_lt_k state_full.matrix[k_full][k_full]
              state_full.prevPivot, h_mat, h_step, h_prev, hh514]
        apply ih
        ·
          simp [h_step]
        ·
          exact hh514
        ·
          exact h_rows
        ·
          rfl
        ·
          exact h_new_mat
        ·
          simp; omega
theorem noPivotLoop_full_eq_borderedMinor_at_trailing
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) :
    let BM := Matrix.borderedMinor M k hk row col
    let s_full := Matrix.noPivotLoop k (Matrix.noPivotInitialState M)
    let s_bm := Matrix.noPivotLoop k (Matrix.noPivotInitialState BM)
    s_full.matrix[row][col] = s_bm.matrix[Fin.last k][Fin.last k] ∧
      s_full.singularStep = s_bm.singularStep := by
  intro BM s_full s_bm
  have h_sync :=
    gapH214 k hk row col hrow hcol k
      (Matrix.noPivotInitialState M) (Matrix.noPivotInitialState BM)
      rfl rfl rfl rfl rfl
      (show k + (Matrix.noPivotInitialState M).step < k + 1 by
        simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  have hcongr :
      (Matrix.borderedMinor s_full.matrix k hk row col)[Fin.last k][Fin.last k] =
        s_bm.matrix[Fin.last k][Fin.last k] := by rw [h_mat]
  rw [Matrix.borderedMinor_entry_last_last] at hcongr
  exact hcongr
private theorem gapH344
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState Int n) :
    (Matrix.noPivotLoop fuel state).step ≤ state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step + 0
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_of_singular f state hDone hp]
          show state.step ≤ state.step + (f + 1)
          omega
        · rw [Matrix.noPivotLoop_of_regular f state hDone hp]
          calc (Matrix.noPivotLoop f
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }).step
              ≤ state.step + 1 + f := ih _
            _ = state.step + (f + 1) := by omega
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step + (f + 1)
        omega
private theorem gapH58
    {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState Int n),
      (∀ a b : Fin n, state.step ≤ a.val → state.step ≤ b.val →
        state.matrix[a][b] = state.matrix[b][a]) →
      ∀ (a b : Fin n),
        (Matrix.noPivotLoop fuel state).step ≤ a.val →
        (Matrix.noPivotLoop fuel state).step ≤ b.val →
        (Matrix.noPivotLoop fuel state).matrix[a][b] =
          (Matrix.noPivotLoop fuel state).matrix[b][a] := by
  induction fuel with
  | zero =>
      intros state h_sym a b ha hb
      change state.matrix[a][b] = state.matrix[b][a]
      change state.step ≤ a.val at ha
      change state.step ≤ b.val at hb
      exact h_sym a b ha hb
  | succ f ih =>
      intros state h_sym a b ha hb
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        ·
          rw [Matrix.noPivotLoop_of_singular f state hDone hp] at ha hb ⊢
          change state.matrix[a][b] = state.matrix[b][a]
          change state.step ≤ a.val at ha
          change state.step ≤ b.val at hb
          exact h_sym a b ha hb
        ·
          rw [Matrix.noPivotLoop_of_regular f state hDone hp] at ha hb ⊢
          let kFin : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
          have h_sym_new : ∀ (a' b' : Fin n),
              state.step + 1 ≤ a'.val → state.step + 1 ≤ b'.val →
              (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[a'][b']
                = (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[b'][a'] := by
            intros a' b' ha' hb'
            have ha'_lt : state.step < a'.val := ha'
            have hb'_lt : state.step < b'.val := hb'
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot a' b' ha'_lt hb'_lt]
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot b' a' hb'_lt ha'_lt]
            have h_ab : state.matrix[a'][b'] = state.matrix[b'][a'] :=
              h_sym a' b' (Nat.le_of_lt ha'_lt) (Nat.le_of_lt hb'_lt)
            have h_ak : state.matrix[a'][kFin] = state.matrix[kFin][a'] :=
              h_sym a' kFin (Nat.le_of_lt ha'_lt) (Nat.le_refl _)
            have h_bk : state.matrix[b'][kFin] = state.matrix[kFin][b'] :=
              h_sym b' kFin (Nat.le_of_lt hb'_lt) (Nat.le_refl _)
            change Matrix.exactDiv (_ * state.matrix[a'][b']
                - state.matrix[a'][kFin] * state.matrix[kFin][b']) _
              = Matrix.exactDiv (_ * state.matrix[b'][a']
                - state.matrix[b'][kFin] * state.matrix[kFin][a']) _
            rw [h_ab, h_ak, h_bk]
            congr 1
            grind
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            (by
              intros a' b' ha' hb'
              exact h_sym_new a' b' ha' hb')
            a b ha hb
      ·
        rw [Matrix.noPivotLoop_done f state hDone] at ha hb ⊢
        change state.matrix[a][b] = state.matrix[b][a]
        change state.step ≤ a.val at ha
        change state.step ≤ b.val at hb
        exact h_sym a b ha hb
private theorem gapH125
    {n : Nat} (M : Matrix Int n n)
    (h_sym : ∀ a b : Fin n, M[a][b] = M[b][a])
    (k : Nat) (hk : k < n) (i j : Fin n)
    (hki : k ≤ i.val) (hkj : k ≤ j.val) :
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk i j))).matrix[Fin.last k][Fin.last k] =
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk j i))).matrix[Fin.last k][Fin.last k] := by
  have h_ij :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk i j hki hkj).1
  have h_ji :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk j i hkj hki).1
  rw [← h_ij, ← h_ji]
  have h_step_le := gapH344 k (Matrix.noPivotInitialState M)
  have h_step0 : (Matrix.noPivotInitialState M).step = 0 := rfl
  have h_step_bound :
      (Matrix.noPivotLoop k (Matrix.noPivotInitialState M)).step ≤ k := by
    rw [h_step0] at h_step_le
    simpa using h_step_le
  have h_init_sym :
      ∀ a b : Fin n, (Matrix.noPivotInitialState M).step ≤ a.val →
        (Matrix.noPivotInitialState M).step ≤ b.val →
        (Matrix.noPivotInitialState M).matrix[a][b] =
          (Matrix.noPivotInitialState M).matrix[b][a] := by
    intros a b _ _
    exact h_sym a b
  exact gapH58 k
    (Matrix.noPivotInitialState M) h_init_sym i j
    (Nat.le_trans h_step_bound hki) (Nat.le_trans h_step_bound hkj)
private theorem gapH65
    {n K : Nat} (hK : K ≤ n) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState Int n) (state_pref : Matrix.BareissState Int K),
      state_full.step = state_pref.step →
      state_full.prevPivot = state_pref.prevPivot →
      state_full.rowSwaps = state_pref.rowSwaps →
      state_full.singularStep = state_pref.singularStep →
      Matrix.principalSubmatrix state_full.matrix K hK = state_pref.matrix →
      fuel + state_full.step < K →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_pref).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_pref).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_pref).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_pref).singularStep ∧
      Matrix.principalSubmatrix (Matrix.noPivotLoop fuel state_full).matrix K hK =
          (Matrix.noPivotLoop fuel state_pref).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_K : state_full.step + 1 < K := by omega
      have hh502 : state_full.step + 1 < n :=
        Nat.lt_of_lt_of_le h_step_lt_K hK
      have h_pref_done : state_pref.step + 1 < K := h_step ▸ h_step_lt_K
      have hh521 : state_full.step < n := Nat.lt_of_succ_lt hh502
      have h_step_lt_K_strict : state_full.step < K :=
        Nat.lt_of_succ_lt h_step_lt_K
      have h_pref_step_lt_K : state_pref.step < K := h_step ▸ h_step_lt_K_strict
      let k_full : Fin n := ⟨state_full.step, hh521⟩
      let k_pref : Fin K := ⟨state_pref.step, h_pref_step_lt_K⟩
      let k_full' : Fin K := ⟨state_full.step, h_step_lt_K_strict⟩
      have h_k_eq : k_full' = k_pref := Fin.ext h_step
      have hh514 : state_full.matrix[k_full][k_full] =
          state_pref.matrix[k_pref][k_pref] := by
        have hcongr := congrArg (fun (M : Matrix Int K K) => M[k_pref][k_pref]) h_mat
        simp only [Matrix.getElem_principalSubmatrix] at hcongr
        have h_idx :
            k_full = (⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n) :=
          Fin.ext h_step
        have h_diag :
            state_full.matrix[k_full][k_full] =
              state_full.matrix[(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)][(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)] :=
          congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
        exact h_diag.trans hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      ·
        have hp_pref : state_pref.matrix[k_pref][k_pref] = 0 := by
          rw [← hh514]; exact hp_full
        rw [Matrix.noPivotLoop_of_singular f state_full hh502 hp_full,
          Matrix.noPivotLoop_of_singular f state_pref h_pref_done hp_pref]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      ·
        have hp_pref : state_pref.matrix[k_pref][k_pref] ≠ 0 := by
          rw [← hh514]; exact hp_full
        rw [Matrix.noPivotLoop_of_regular f state_full hh502 hp_full,
          Matrix.noPivotLoop_of_regular f state_pref h_pref_done hp_pref]
        have h_new_mat :
            Matrix.principalSubmatrix
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) K hK =
              Matrix.stepMatrix state_pref.matrix state_pref.step
                state_pref.matrix[k_pref][k_pref] state_pref.prevPivot := by
          rw [gapH233, h_mat, h_step, h_prev, hh514]
        apply ih
        ·
          simp [h_step]
        ·
          exact hh514
        ·
          exact h_rows
        ·
          rfl
        ·
          exact h_new_mat
        ·
          simp; omega
theorem noPivotLoop_singularStep_lt
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop fuel state).singularStep = some s) :
    s < state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      rw [Matrix.noPivotLoop_zero_fuel, h_init] at h_sing
      nomatch h_sing
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_of_singular f state hDone hp] at h_sing
          simp at h_sing
          omega
        · rw [Matrix.noPivotLoop_of_regular f state hDone hp] at h_sing
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            rfl h_sing
          change s < state.step + 1 + f at h_ih
          show s < state.step + (f + 1)
          omega
      · rw [Matrix.noPivotLoop_done f state hDone] at h_sing
        rw [h_init] at h_sing
        nomatch h_sing
private theorem noPivotLoop_step_eq_add_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (hh509 : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [Matrix.noPivotLoop_of_singular f state hDone hp] at hh509
        simp at hh509
      · rw [Matrix.noPivotLoop_of_regular f state hDone hp] at hh509
        rw [Matrix.noPivotLoop_of_regular f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          rfl h_next_room hh509
        rw [h_next_step]
        show state.step + 1 + f = state.step + (f + 1)
        omega
theorem noPivotLoop_step_monotone
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState Int n) :
    state.step ≤ (Matrix.noPivotLoop fuel state).step := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · have hStepLt : state.step < n := Nat.lt_of_succ_lt hDone
        by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_of_singular f state hDone hp]
        · rw [Matrix.noPivotLoop_of_regular f state hDone hp]
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          exact Nat.le_trans (Nat.le_succ _) h_ih
      · rw [Matrix.noPivotLoop_done f state hDone]
private theorem gapH222
    {n : Nat} (a b : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_prefix : (Matrix.noPivotLoop a state).singularStep = some s) :
    (Matrix.noPivotLoop (a + b) state).singularStep = some s := by
  rw [noPivotLoop_add a b state]
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, h_step, h_zero, h_bound⟩
  · rw [h_none] at h_prefix
    nomatch h_prefix
  · have hs : s = k.val := by
      rw [h_sing] at h_prefix
      injection h_prefix with h
      exact h.symm
    have hDone :
        (Matrix.noPivotLoop a state).step + 1 < n := by
      rw [h_step]
      exact h_bound
    have hidx :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step
    have hp :
        (Matrix.noPivotLoop a state).matrix[
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)][
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
      have h_lift := congrArg
        (fun (idx : Fin n) => (Matrix.noPivotLoop a state).matrix[idx][idx])
        hidx
      exact h_lift.trans h_zero
    have hsing_state :
        (Matrix.noPivotLoop a state).singularStep =
          some (Matrix.noPivotLoop a state).step := by
      rw [h_sing, h_step]
    rw [noPivotLoop_id_at_singular_fixedpoint b _ hDone hp hsing_state, hs]
    exact h_sing
private theorem gapH406
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    let GM := Matrix.gramMatrix b
    let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
    let LP := Matrix.principalSubmatrix GM (r + 1) hK
    let s_full := Matrix.noPivotLoop r (Matrix.noPivotInitialState GM)
    let s_pref := Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)
    s_full.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        s_pref.matrix[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))]
      ∧ s_full.singularStep = s_pref.singularStep := by
  intro GM hK LP s_full s_pref
  have h_sync := gapH65 hK r
    (Matrix.noPivotInitialState GM) (Matrix.noPivotInitialState LP)
    rfl rfl rfl rfl rfl
    (show r + (Matrix.noPivotInitialState GM).step < r + 1 by
      simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  have hcongr := congrArg
    (fun (M : Matrix Int (r + 1) (r + 1)) =>
      M[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))])
    h_mat
  simp only [Matrix.getElem_principalSubmatrix] at hcongr
  exact hcongr
theorem bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
    (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (hh510 :
      (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
      Matrix.bareiss
        (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr)) := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let fullAtR := Matrix.noPivotLoop r init
  let LP := Matrix.principalSubmatrix GM (r + 1) (Nat.succ_le_of_lt hr)
  have h_step_r : fullAtR.step = r := by
    have h_room : init.step + r + 1 ≤ n := by
      simp [init, Matrix.noPivotInitialState]
      omega
    have h := noPivotLoop_step_eq_add_of_singularStep_none r init rfl h_room hh510
    simpa [fullAtR, init, Matrix.noPivotInitialState] using h
  have h_factor :
      Matrix.noPivotLoop n init = Matrix.noPivotLoop (n - r) fullAtR := by
    have h_add := noPivotLoop_add r (n - r) init
    have h_split : r + (n - r) = n := by omega
    simpa [fullAtR, h_split] using h_add
  have h_final_diag :
      (Matrix.noPivotLoop n init).matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
    rw [h_factor]
    have h_le : (⟨r, hr⟩ : Fin n).val ≤ fullAtR.step := by
      change r ≤ fullAtR.step
      rw [h_step_r]
    exact Matrix.noPivotLoop_diag_of_le_step (n - r) fullAtR (⟨r, hr⟩ : Fin n) h_le
  obtain ⟨h_diag, h_sing⟩ :=
    gapH406 (b := b) r hr
  have h_pref_nonsing :
      (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).singularStep = none := by
    rw [← h_sing]
    exact hh510
  have h_bareiss :=
    Matrix.bareiss_eq_noPivotLoop_last_of_no_singular (M := LP) h_pref_nonsing
  calc
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
          rw [Matrix.bareissNoPivotData_eq_finish]
          simpa [Matrix.finish, GM, init, fullAtR] using h_final_diag
    _ =
        (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).matrix[
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))] := by
          exact h_diag
    _ = Matrix.bareiss LP := by
          simpa [LP, Fin.last] using h_bareiss.symm
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt.Int
private theorem gapH27
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (hh515 :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.noPivotLoop s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s := by
  have h_room :
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + s + 1 ≤ n := by
    simp [Matrix.noPivotInitialState]
    omega
  have h_step :=
    Matrix.noPivotLoop_step_eq_add_of_singularStep_none s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_room hh515
  simpa [Matrix.noPivotInitialState] using h_step
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt.Int
private theorem gapH168
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : StepWitness b)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ i.val) :
    ∃ v : Vector Int m,
      (∃ c : Vector Int n,
        (∀ k : Fin n, i.val < k.val → (c)[k] = 0) ∧
          v = Matrix.vecMul c b) ∧
        ∀ j : Fin n,
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] =
            v.dotProduct (b.row j) := by
  let hinv :=
    bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  refine ⟨Matrix.vecMul (hinv.coeff i) b, ?_, ?_⟩
  · exact ⟨hinv.coeff i, fun k hik => hinv.coeff_supp i k hi hik, rfl⟩
  · intro j
    exact hinv.entry_eq_dot i j hi
private theorem gapH232 (x : Int) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using
    (Lean.Grind.OrderedRing.sq_nonneg (a := x))
private theorem gapH257 (x : Int) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := gapH232 x
  have hsquare : x * x = 0 := Int.le_antisymm h hnonneg
  rcases Int.mul_eq_zero.mp hsquare with h0 | h0 <;> exact h0
private theorem gapH298 (xs : List (Fin m)) (v : Vector Int m)
    (acc : Int) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := gapH232 v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Int.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)
private theorem gapH230 (xs : List (Fin m))
    (v : Vector Int m) (acc : Int) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := gapH232 v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero : acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          gapH298 (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply gapH257
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h
private theorem gapH330 (v : Vector Int m)
    (hzero : v.dotProduct v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by simp
  exact gapH230 (xs := List.finRange m) (v := v)
    (acc := 0) (by decide)
    (by simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using hzero) i hmem
private theorem gapH177 (u v : Vector Int m)
    (hzero : v.dotProduct v = 0) :
    v.dotProduct u = 0 := by
  unfold Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [gapH330 v hzero i]
      have hzero_mul : (0 : Int) * u[i] = 0 := by grind
      rw [hzero_mul]
      have hadd_zero : (0 : Int) + 0 = 0 := by grind
      rw [hadd_zero]
      exact ih
private theorem gapH327 {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind
private theorem gapH410 {n' : Nat} (u v : Vector Int n') :
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using
    gapH327 (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl
private theorem gapH21 {α : Type v}
    (xs : List α) (f g : α → Int) (acc : Int)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs
private theorem gapH415
    {n m : Nat} (b : Matrix Int n m) (c : Vector Int n) (j : Fin m) :
    (Matrix.vecMul c b)[j] =
      Fin.foldl n (fun acc k => acc + b[k][j] * (c)[k]) 0 := by
  rw [Fin.foldl_eq_finRange_foldl]
  show (Matrix.transpose b * c)[j] = _
  rw [Matrix.getElem_mulVec]
  unfold Vector.dotProduct
  apply gapH21
  intro k _hk
  simp [Matrix.col]
private theorem gapH274 {α : Type v}
    (xs : List α) (f : α → Int) (x acc : Int) :
    x * xs.foldl (fun acc y => acc + f y) acc =
      xs.foldl (fun acc y => acc + x * f y) (x * acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + f y)]
      have : x * (acc + f y) = x * acc + x * f y := by grind
      rw [this]
private theorem gapH405
    {n m : Nat} (b : Matrix Int n m) (u : Vector Int m) (c : Vector Int n) :
    u.dotProduct (Matrix.vecMul c b) =
      Fin.foldl n
        (fun acc k => acc + (c)[k] * u.dotProduct (b.row k)) 0 := by
  rw [Fin.foldl_eq_finRange_foldl]
  have h_lhs :
      u.dotProduct (Matrix.vecMul c b) =
        (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * (c)[k]) 0) 0 := by
    unfold Vector.dotProduct
    apply gapH21
    intro j _hj
    rw [gapH415 (b := b) (c := c) j, Fin.foldl_eq_finRange_foldl]
  rw [h_lhs]
  have h_distrib :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * (c)[k]) 0) 0 =
        (List.finRange m).foldl
          (fun accj j => accj +
            (List.finRange n).foldl
              (fun acck k => acck + u[j] * (b[k][j] * (c)[k])) 0) 0 := by
    apply gapH21
    intro j _hj
    have h_mul := gapH274 (List.finRange n)
      (fun k : Fin n => b[k][j] * (c)[k]) u[j] 0
    have h_zero : u[j] * (0 : Int) = 0 := by grind
    rw [h_zero] at h_mul
    exact h_mul
  rw [h_distrib]
  have h_swap :=
    List.foldl_add_comm (R := Int)
      (xs := List.finRange m) (ys := List.finRange n)
      (fun (j : Fin m) (k : Fin n) => u[j] * (b[k][j] * (c)[k]))
  rw [h_swap]
  apply gapH21
  intro k _hk
  have h_body :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] * (b[k][j] * (c)[k])) 0 =
        (List.finRange m).foldl
          (fun accj j => accj + (c)[k] * (u[j] * b[k][j])) 0 := by
    apply gapH21
    intro j _hj
    have : u[j] * (b[k][j] * (c)[k]) = (c)[k] * (u[j] * b[k][j]) := by grind
    exact this
  rw [h_body]
  have h_pull := gapH274 (List.finRange m)
    (fun j : Fin m => u[j] * b[k][j]) (c)[k] 0
  have h_zero : (c)[k] * (0 : Int) = 0 := by grind
  rw [h_zero] at h_pull
  rw [← h_pull]
  have h_dot_eq :
      u.dotProduct (b.row k) =
        (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0 := by
    unfold Vector.dotProduct
    apply gapH21
    intro j _hj
    simp [Matrix.row]
  rw [h_dot_eq]
private theorem foldl_add_zero {α : Type v}
    (xs : List α) (f : α → Int)
    (h : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) (0 : Int) = 0 := by
  have h_aux : ∀ (xs : List α) (acc : Int),
      (∀ x ∈ xs, f x = 0) →
        xs.foldl (fun acc x => acc + f x) acc = acc := by
    intro xs
    induction xs with
    | nil => intros acc _h; rfl
    | cons y rest ih =>
        intros acc h_terms
        simp only [List.foldl_cons]
        have hy : f y = 0 := h_terms y (by simp)
        have hxs : ∀ x ∈ rest, f x = 0 :=
          fun x hx => h_terms x (List.mem_cons_of_mem _ hx)
        rw [hy]
        have h_add : acc + (0 : Int) = acc := by grind
        rw [h_add]
        exact ih (acc) hxs
  exact h_aux xs 0 h
private theorem gapH37
    {n m : Nat} (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (hquot : StepWitness b)
    (hh515 :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_zero :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    ∀ i : Fin n, s + 1 ≤ i.val →
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0 := by
  intro i hi
  let sFin : Fin n := ⟨s, Nat.lt_of_succ_lt hs⟩
  have h_step :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s :=
    gapH27 b s hs hh515
  have h_state_step_le_sFin :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ sFin.val := by
    rw [h_step]
  obtain ⟨v, ⟨c, h_coeff_supp_above, hv_def⟩, h_dot_eq_matrix⟩ :=
    gapH168 b s hquot sFin h_state_step_le_sFin
  have h_dot_zero_le : ∀ k : Fin n, k.val ≤ s →
      v.dotProduct (b.row k) = 0 := by
    intro k hks
    rw [← h_dot_eq_matrix k]
    by_cases hk_eq : k.val = s
    · have h_k_eq_sFin : k = sFin := Fin.ext hk_eq
      rw [h_k_eq_sFin]
      exact h_zero
    ·
      have hk_lt : k.val < s := Nat.lt_of_le_of_ne hks hk_eq
      have h_init_step_le :
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ k.val := by
        show 0 ≤ k.val
        exact Nat.zero_le _
      have h_k_lt_result :
          k.val < (Matrix.noPivotLoop s
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step := by
        rw [h_step]
        exact hk_lt
      have h_k_lt_sFin : k.val < sFin.val := hk_lt
      exact noPivotLoop_matrix_processed_col_eq_zero s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) hh515
        k.val h_init_step_le h_k_lt_result k rfl sFin h_k_lt_sFin
  have h_dot_self_zero : v.dotProduct v = 0 := by
    have h_expand_aux :
        v.dotProduct (Matrix.vecMul c b) =
          (List.finRange n).foldl
            (fun acc k => acc + (c)[k] * v.dotProduct (b.row k))
            0 := by
      have h := gapH405 b v c
      rwa [Fin.foldl_eq_finRange_foldl] at h
    rw [← hv_def] at h_expand_aux
    rw [h_expand_aux]
    apply foldl_add_zero
    intro k _hk
    by_cases hks : k.val ≤ s
    ·
      rw [h_dot_zero_le k hks]
      grind
    ·
      have hk_gt : sFin.val < k.val := by show s < k.val; omega
      rw [h_coeff_supp_above k hk_gt]
      grind
  have h_init_sym :
      ∀ a c : Fin n,
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ a.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ c.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[a][c] =
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[c][a] := by
    intros a c _ha _hc
    show (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a]
    rw [Matrix.getElem_gramMatrix, Matrix.getElem_gramMatrix]
    exact gapH410 (Matrix.row b a) (Matrix.row b c)
  have h_symm :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][sFin] =
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[sFin][i] := by
    apply gapH58 s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_init_sym i sFin
    · rw [h_step]; omega
    · rw [h_step]
  rw [h_symm, h_dot_eq_matrix i]
  exact gapH177 (b.row i) v h_dot_self_zero
private theorem gapH122 {n : Nat} (M : Matrix Int n n)
    {i j : Fin n} (h : i = j) :
    M[i][i] = M[j][j] := by
  subst h; rfl
private theorem gapH108
    {n : Nat} (state : Matrix.BareissState Int n) (a b : Nat) (k : Fin n)
    (h_sing_a : (Matrix.noPivotLoop a state).singularStep = some k.val)
    (h_step_a : (Matrix.noPivotLoop a state).step = k.val)
    (h_zero_a : (Matrix.noPivotLoop a state).matrix[k][k] = 0)
    (hk : k.val + 1 < n) :
    Matrix.noPivotLoop (a + b) state = Matrix.noPivotLoop a state := by
  rw [Matrix.noPivotLoop_add a b state]
  have hDone : (Matrix.noPivotLoop a state).step + 1 < n := by
    rw [h_step_a]; exact hk
  have hp_zero :
      (Matrix.noPivotLoop a state).matrix[
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
    have h_fin :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step_a
    exact (gapH122 (Matrix.noPivotLoop a state).matrix h_fin).trans h_zero_a
  have h_sing_step : (Matrix.noPivotLoop a state).singularStep =
      some (Matrix.noPivotLoop a state).step := by
    rw [h_sing_a, h_step_a]
  exact Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) b
    (Matrix.noPivotLoop a state) hDone hp_zero h_sing_step
private theorem gapH75
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).singularStep = none ∧
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s ∧
      (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState M)).matrix[
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] = 0 := by
  have hh505 : (Matrix.noPivotInitialState M).singularStep = none := rfl
  have hh506 : (Matrix.noPivotInitialState M).step = 0 := rfl
  have hsfuel : s < fuel := by
    have := noPivotLoop_singularStep_lt (n := n) fuel
      (Matrix.noPivotInitialState M) hh505 s h_sing
    rw [hh506] at this
    omega
  rcases noPivotLoop_singular_inv (n := n) s
      (Matrix.noPivotInitialState M) hh505
    with h_none | ⟨k', h_sing_s, h_step_s, h_zero_s, h_klt⟩
  · have hS_step : (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s := by
      have h_room :
          (Matrix.noPivotInitialState M).step + s + 1 ≤ n := by
        rw [hh506]; omega
      have h_step := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        (n := n) s (Matrix.noPivotInitialState M) hh505 h_room h_none
      rw [h_step, hh506]; omega
    refine ⟨h_none, hS_step, ?_⟩
    rcases noPivotLoop_singular_inv (n := n) fuel
        (Matrix.noPivotInitialState M) hh505
      with h_full_none | ⟨k, h_sing_full, h_step_full, h_zero_full, h_klt_full⟩
    · rw [h_full_none] at h_sing; nomatch h_sing
    · have hk_eq : k.val = s := by
        rw [h_sing_full] at h_sing
        exact Option.some.inj h_sing
      have hsn : s < n := Nat.lt_of_succ_le hs
      have hh503 :
          Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) := by
        congr 1; omega
      have h_split :
          Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) := by
        rw [← hh503,
          Matrix.noPivotLoop_add s (fuel - s) (Matrix.noPivotInitialState M)]
      have h_diag_preserved :
          (Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
        Matrix.noPivotLoop_diag_of_le_step (fuel - s)
          (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))
          (⟨s, hsn⟩ : Fin n)
          (by rw [hS_step])
      have h_full_diag_eq :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] := by
        rw [h_split]; exact h_diag_preserved
      have h_fin : k = (⟨s, hsn⟩ : Fin n) := Fin.ext hk_eq
      have hh504 :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
            (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] = 0 :=
        (gapH122
            (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix h_fin).symm.trans
          h_zero_full
      exact h_full_diag_eq.symm.trans hh504
  · have h_klt' : k'.val < s := by
      have := noPivotLoop_singularStep_lt (n := n) s
        (Matrix.noPivotInitialState M) hh505 k'.val h_sing_s
      rw [hh506] at this
      omega
    have hh512 :
        Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
          Matrix.noPivotLoop s (Matrix.noPivotInitialState M) :=
      gapH108 (Matrix.noPivotInitialState M) s (fuel - s) k'
        h_sing_s h_step_s h_zero_s h_klt
    have h_fuel_eq : s + (fuel - s) = fuel := by omega
    rw [h_fuel_eq] at hh512
    rw [hh512] at h_sing
    rw [h_sing_s] at h_sing
    have hk'_eq : k'.val = s := Option.some.inj h_sing
    omega
private theorem gapH291
    {n : Nat} :
    ∀ (a : Nat) (fuel : Nat) (state : Matrix.BareissState Int n)
      (result : Matrix.BareissState Int n)
      (_h_partial : Matrix.noPivotLoop a state = result),
      state.singularStep = none →
      a + 1 ≤ fuel →
      result.singularStep = none →
      (hh520 : result.step + 1 < n) →
      result.matrix[(⟨result.step, Nat.lt_of_succ_lt hh520⟩ : Fin n)][
        (⟨result.step, Nat.lt_of_succ_lt hh520⟩ : Fin n)] = 0 →
      Matrix.findPivot? result.matrix
        (⟨result.step, Nat.lt_of_succ_lt hh520⟩ : Fin n) (result.step + 1) = none →
      (Matrix.pivotLoop fuel state).singularStep = some result.step := by
  intro a
  induction a with
  | zero =>
      intro fuel state result h_partial _h_init_sing hfuel _h_part_none hStepLt hp_zero
          h_find_none
      have h_state_eq : state = result := by
        rw [show state = Matrix.noPivotLoop 0 state from rfl, h_partial]
      subst h_state_eq
      rcases fuel with _ | fuel'
      · omega
      exact (Matrix.pivotLoop_of_singular_no_pivot fuel' state hStepLt hp_zero h_find_none
        ▸ rfl)
  | succ a' ih =>
      intro fuel state result h_partial hh505 hfuel h_part_none hStepLt hp_zero
          h_find_none
      have hDone_state : state.step + 1 < n := by
        have hmono := noPivotLoop_step_monotone (a' + 1) state
        rw [h_partial] at hmono
        omega
      by_cases hp0_state : state.matrix[state.step][state.step] = 0
      ·
        exfalso
        have h_sing_branch :
            Matrix.noPivotLoop (a' + 1) state =
              { state with singularStep := some state.step } :=
          Matrix.noPivotLoop_of_singular a' state hDone_state hp0_state
        rw [h_sing_branch] at h_partial
        rw [← h_partial] at h_part_none
        simp at h_part_none
      ·
        have h_unfold_noPiv : Matrix.noPivotLoop (a' + 1) state =
            Matrix.noPivotLoop a'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.noPivotLoop_of_regular a' state hDone_state hp0_state
        rcases fuel with _ | fuel'
        · omega
        have h_fuel' : a' + 1 ≤ fuel' := by omega
        have h_unfold_piv : Matrix.pivotLoop (fuel' + 1) state =
            Matrix.pivotLoop fuel'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.pivotLoop_of_regular_no_swap fuel' state hDone_state hp0_state
        rw [h_unfold_piv]
        have h_next_partial :
            Matrix.noPivotLoop a'
              ({ step := state.step + 1
                 matrix := Matrix.stepMatrix state.matrix state.step
                   state.matrix[state.step][state.step] state.prevPivot
                 prevPivot := state.matrix[state.step][state.step]
                 rowSwaps := state.rowSwaps
                 singularStep := none } : Matrix.BareissState Int n) = result := by
          rw [← h_unfold_noPiv]; exact h_partial
        exact ih fuel'
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          result h_next_partial rfl h_fuel' h_part_none hStepLt hp_zero h_find_none
private theorem gapH109
    {n m : Nat} (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (hquot : StepWitness b)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    (Matrix.bareiss
      (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
        (Nat.succ_le_of_lt hr))).toNat = 0 := by
  let GM := Matrix.gramMatrix b
  let initGM := Matrix.noPivotInitialState GM
  let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
  let LP := Matrix.principalSubmatrix GM (r + 1) hK
  let initLP := Matrix.noPivotInitialState LP
  have hsr : s < r := by
    have h := noPivotLoop_singularStep_lt (n := n) r initGM rfl s h_sing
    change s < initGM.step + r at h
    have : initGM.step = 0 := rfl
    omega
  have hs1n : s + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hsr) hr
  have hsn : s < n := Nat.lt_of_succ_lt hs1n
  have hsucc_n : s + 1 ≤ n := Nat.le_of_lt hs1n
  obtain ⟨h_full_none, h_full_step, hh504⟩ :=
    gapH75 GM r s hsucc_n h_sing
  have h_full_col_zero :
      ∀ i : Fin n, s + 1 ≤ i.val →
        (Matrix.noPivotLoop s initGM).matrix[i][(⟨s, hsn⟩ : Fin n)] = 0 :=
    gapH37
      (b := b) s hs1n hquot h_full_none hh504
  have h_sync :=
    gapH65 (n := n) (K := r + 1) hK s
      initGM initLP rfl rfl rfl rfl
      (by
        show Matrix.principalSubmatrix initGM.matrix (r + 1) hK = initLP.matrix
        rfl)
      (show s + initGM.step < r + 1 by
        change s + 0 < r + 1; omega)
  obtain ⟨h_step_sync, _h_prev_sync, _h_rows_sync, h_sing_sync, h_mat_sync⟩ := h_sync
  have hs_lt_r1 : s < r + 1 := Nat.lt_succ_of_lt hsr
  have h_LP_col_zero :
      ∀ i' : Fin (r + 1), s + 1 ≤ i'.val →
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    intro i' hi'
    let iN : Fin n := ⟨i'.val, Nat.lt_of_lt_of_le i'.isLt hK⟩
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.principalSubmatrix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.getElem_principalSubmatrix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK i'
      (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have hi_iN : s + 1 ≤ iN.val := hi'
    have h_col_zero_iN := h_full_col_zero iN hi_iN
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[iN][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[iN][(⟨s, hsn⟩ : Fin n)] :=
      congrArg (fun (j : Fin n) => (Matrix.noPivotLoop s initGM).matrix[iN][j])
        (Fin.ext (rfl : (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n).val =
                        (⟨s, hsn⟩ : Fin n).val))
    exact h_entry_eq.trans h_col_zero_iN
  have h_LP_step : (Matrix.noPivotLoop s initLP).step = s := by
    rw [← h_step_sync]; exact h_full_step
  have h_LP_sing : (Matrix.noPivotLoop s initLP).singularStep = none := by
    rw [← h_sing_sync]; exact h_full_none
  have h_LP_zero_diag :
      (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
        (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.principalSubmatrix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.getElem_principalSubmatrix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK
      (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have h_idx_eq :
        (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n) =
          (⟨s, hsn⟩ : Fin n) := Fin.ext rfl
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
      gapH122 _ h_idx_eq
    exact h_entry_eq.trans hh504
  have h_LP_find_none :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (s + 1) = none :=
    Matrix.findPivot?_eq_none_of_zero _ _ _ h_LP_col_zero
  have hh495 : (Matrix.noPivotLoop s initLP).step + 1 < r + 1 := by
    rw [h_LP_step]; omega
  have h_idx_at_LP_step :
      (⟨(Matrix.noPivotLoop s initLP).step,
        Nat.lt_of_succ_lt hh495⟩ : Fin (r + 1)) =
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) :=
    Fin.ext h_LP_step
  have h_LP_zero_at_result :
      (Matrix.noPivotLoop s initLP).matrix[
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt hh495⟩ : Fin (r + 1))][
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt hh495⟩ : Fin (r + 1))] = 0 :=
    (gapH122 (n := r + 1)
      (Matrix.noPivotLoop s initLP).matrix h_idx_at_LP_step).trans h_LP_zero_diag
  have h_LP_find_at_result :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt hh495⟩ : Fin (r + 1))
        ((Matrix.noPivotLoop s initLP).step + 1) = none := by
    have h_step_plus_eq : (Matrix.noPivotLoop s initLP).step + 1 = s + 1 := by
      rw [h_LP_step]
    have h_step1 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨(Matrix.noPivotLoop s initLP).step,
              Nat.lt_of_succ_lt hh495⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) :=
      congrArg
        (fun (i : Fin (r + 1)) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix i
            ((Matrix.noPivotLoop s initLP).step + 1))
        h_idx_at_LP_step
    have h_step2 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            (s + 1) :=
      congrArg
        (fun (st : Nat) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1)) st)
        h_step_plus_eq
    exact (h_step1.trans h_step2).trans h_LP_find_none
  have h_pivot_sing : (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step :=
    gapH291
      s (r + 1) initLP (Matrix.noPivotLoop s initLP)
      rfl rfl (by omega) h_LP_sing hh495
      h_LP_zero_at_result h_LP_find_at_result
  have h_bareissData_sing :
      (Matrix.bareissData LP).singularStep =
        some (Matrix.noPivotLoop s initLP).step := by
    rw [Matrix.bareissData_eq_finish_pivotLoop]
    show (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step
    exact h_pivot_sing
  have h_bareiss_zero : Matrix.bareiss LP = 0 := by
    rw [Matrix.bareiss_eq_bareissData_det]
    unfold Matrix.BareissData.det
    rw [h_bareissData_sing]
  show (Matrix.bareiss LP).toNat = 0
  rw [h_bareiss_zero]
  rfl
private theorem gapH319 (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n (fuel + 1) state = state := by
  simp [scaledCoeffArrayLoop, hDone]
private theorem gapH249 (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ f => exact gapH319 f state hDone
private theorem gapH114 (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step = 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]
private theorem gapH129 (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : ¬ state.step + 1 < n) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with
        step := state.step + 1
        coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext]
private theorem gapH63 (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step ≠ 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      scaledCoeffArrayLoop n fuel
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]
private theorem gapH23
    (rows : Array (Array Int)) (i j : Fin n) :
    getArrayEntry rows i.val j.val = (rowsToMatrix rows n)[i][j] := by
  rw [rowsToMatrix, Matrix.getElem_ofFn]
private theorem gapH69
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hstep : state.step = j) (hji : j < i) (hin : i < n)
    (hh501 : state.coeffs.size = n)
    (hh500 : ∀ r, r < n → state.coeffs[r]!.size = n) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state).coeffs i j =
      getArrayEntry state.matrix i j := by
  have hh493 : state.step < n := by omega
  have hrow : i < state.coeffs.size := by
    rw [hh501]
    exact hin
  have hcol : j < state.coeffs[i]!.size := by
    rw [hh500 i hin]
    exact Nat.lt_trans hji hin
  by_cases hNext : state.step + 1 < n
  · by_cases hp : getArrayEntry state.matrix state.step state.step = 0
    · rw [gapH114 fuel state hh493 hNext hp]
      rw [hstep]
      exact gapH34 state.coeffs state.matrix n j i
        hji hin hrow hcol
    · rw [gapH63 fuel state hh493 hNext hp]
      let next : ScaledCoeffArrayState :=
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step }
      change getArrayEntry (scaledCoeffArrayLoop n fuel next).coeffs i j =
        getArrayEntry state.matrix i j
      rw [gapH49]
      · show getArrayEntry (writeScaledColumn state.coeffs state.matrix n state.step) i j =
          getArrayEntry state.matrix i j
        rw [hstep]
        exact gapH34 state.coeffs state.matrix n j i
          hji hin hrow hcol
      · show j < next.step
        simp [next, hstep]
  · rw [gapH129 fuel state hh493 hNext]
    rw [hstep]
    exact gapH34 state.coeffs state.matrix n j i
      hji hin hrow hcol
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt.Int
private theorem gapH93
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState Int n}
    (hh519 : state_array.step = state_matrix.step)
    (hh508 : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (hh497 : state_array.matrix.size = n)
    (hh496 : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (hh501 : state_array.coeffs.size = n)
    (hh500 : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + fuel)
    (hh523 :
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep = none) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val j.val =
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j] := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      omega
  | succ fuel' ih =>
      by_cases h_at_target : state_matrix.step = j.val
      · have h_array_step : state_array.step = j.val := by
          rw [hh519, h_at_target]
        rw [gapH69 n fuel' state_array
          i.val j.val h_array_step hji i.isLt hh501 hh500]
        have hdist : j.val - state_matrix.step = 0 := by omega
        rw [hdist, Matrix.noPivotLoop_zero_fuel,
          gapH23 state_array.matrix i j, hh508]
      · have h_step_lt_j : state_matrix.step < j.val :=
          Nat.lt_of_le_of_ne h_step_le_j h_at_target
        have hDone : state_matrix.step + 1 < n := by
          omega
        have hh521 : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hh493 : state_array.step < n := hh519 ▸ hh521
        have hh492 : state_array.step + 1 < n := hh519 ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, hh521⟩
        have hh513 :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [hh519]
          have := gapH23 (n := n) state_array.matrix kFin kFin
          rw [this, hh508]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [hdist, Matrix.noPivotLoop_of_singular _ state_matrix hDone hp] at hh523
          simp at hh523
        · have hp_array :
              getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [hh513]
            exact hp
          rw [gapH63 fuel' state_array hh493 hh492 hp_array]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState Int n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          change getArrayEntry (scaledCoeffArrayLoop n fuel' new_array).coeffs i.val j.val =
            (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j]
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [hh519]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [gapH128 _ _ _ _ hh497
              hh496, hh508, hh513, hh519, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := hh513
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [gapH314, hh497]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact gapH218 state_array.matrix n state_array.step _ _
              hh497 hh496 r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [gapH262]
            exact hh501
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [gapH173]
            exact hh500 r hr
          have h_step_le_j_new : new_matrix.step ≤ j.val := by
            show state_matrix.step + 1 ≤ j.val
            omega
          have h_fuel_new : j.val < new_matrix.step + fuel' := by
            show j.val < state_matrix.step + 1 + fuel'
            omega
          have h_target_nonsing_new :
              (Matrix.noPivotLoop (j.val - new_matrix.step) new_matrix).singularStep = none := by
            have hdist :
                j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
              omega
            rw [hdist, Matrix.noPivotLoop_of_regular _ state_matrix hDone hp] at hh523
            simpa [new_matrix] using hh523
          have h_capture := ih h_step_new h_matrix_new h_prev_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_step_le_j_new h_fuel_new h_target_nonsing_new
          have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [h_capture, hdist, Matrix.noPivotLoop_of_regular _ state_matrix hDone hp]
          rfl
private theorem gapH103
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState Int n}
    (hh519 : state_array.step = state_matrix.step)
    (hh508 : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (hh509 : state_matrix.singularStep = none)
    (hh497 : state_array.matrix.size = n)
    (hh496 : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (hh501 : state_array.coeffs.size = n)
    (hh500 : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (hh499 : ∀ j (_hjs : j < state_matrix.step) (hjn : j < n),
      getArrayEntry state_array.coeffs j j =
        state_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)])
    (h_coeffs_unwritten : ∀ j (_hjs : state_matrix.step ≤ j) (_hjn : j < n),
      getArrayEntry state_array.coeffs j j = 0)
    (fuel : Nat) (i : Fin n)
    (h_fuel : i.val < state_matrix.step + fuel ∨ i.val < state_matrix.step) :
    ((Matrix.noPivotLoop fuel state_matrix).singularStep = none ∧
      getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
        (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]) ∨
    (∃ s : Nat,
      (Matrix.noPivotLoop fuel state_matrix).singularStep = some s ∧
      ((s ≤ i.val ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val = 0) ∨
       (i.val < s ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
          (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]))) := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      left
      refine ⟨hh509, ?_⟩
      have h_ilt : i.val < state_matrix.step := by
        rcases h_fuel with hor1 | hor2
        · simpa using hor1
        · exact hor2
      exact hh499 i.val h_ilt i.isLt
  | succ fuel' ih =>
      by_cases hDone : state_matrix.step + 1 < n
      ·
        have hh521 : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hh493 : state_array.step < n := hh519 ▸ hh521
        have hh492 : state_array.step + 1 < n := hh519 ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, hh521⟩
        have hh513 :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [hh519]
          have := gapH23 (n := n) state_array.matrix kFin kFin
          rw [this, hh508]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        ·
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
            rw [hh513]; exact hp
          rw [gapH114 fuel' state_array hh493 hh492 hp_array,
            Matrix.noPivotLoop_of_singular fuel' state_matrix hDone hp]
          right
          refine ⟨state_matrix.step, rfl, ?_⟩
          by_cases h_ilt : i.val < state_matrix.step
          · right
            refine ⟨h_ilt, ?_⟩
            change getArrayEntry
              (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
              state_matrix.matrix[i][i]
            rw [gapH2 _ _ _ _ _ _
              (show i.val ≠ state_array.step by rw [hh519]; omega)]
            exact hh499 i.val h_ilt i.isLt
          · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
            by_cases h_ieq : i.val = state_matrix.step
            · left
              refine ⟨Nat.le_of_eq h_ieq.symm, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              have hh498 : state_array.step = i.val := by
                rw [hh519]; exact h_ieq.symm
              rw [hh498]
              have hrow : i.val < state_array.coeffs.size := by
                rw [hh501]; exact i.isLt
              have hcol : i.val < state_array.coeffs[i.val]!.size := by
                rw [hh500 i.val i.isLt]; exact i.isLt
              rw [gapH36 _ _ _ _ hrow hcol]
              rw [← hh498]
              exact hp_array
            · have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              left
              refine ⟨Nat.le_of_lt h_igt, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              rw [gapH2 _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [hh519]; omega)]
              exact h_coeffs_unwritten i.val (Nat.le_of_lt h_igt) i.isLt
        ·
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [hh513]; exact hp
          rw [gapH63 fuel' state_array hh493 hh492 hp_array,
            Matrix.noPivotLoop_of_regular fuel' state_matrix hDone hp]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState Int n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [hh519]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [gapH128 _ _ _ _ hh497
              hh496, hh508, hh513, hh519, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := hh513
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [gapH314, hh497]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact gapH218 state_array.matrix n state_array.step _ _
              hh497 hh496 r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [gapH262]; exact hh501
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [gapH173]; exact hh500 r hr
          have h_coeffs_processed_new :
              ∀ j (_hjs : j < new_matrix.step) (hjn : j < n),
                getArrayEntry new_array.coeffs j j =
                  new_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)] := by
            intro j hjs hjn
            let jFin : Fin n := ⟨j, hjn⟩
            change getArrayEntry (writeScaledColumn _ _ _ _) j j =
              (Matrix.stepMatrix state_matrix.matrix _ _ state_matrix.prevPivot)[jFin][jFin]
            have hj_le : jFin.val ≤ state_matrix.step := Nat.le_of_lt_succ hjs
            rw [Matrix.stepMatrix_diag_of_le _ _ _ _ _ hj_le]
            by_cases hj_eq : j = state_matrix.step
            ·
              have h_array_step_eq_j : state_array.step = j := hh519.trans hj_eq.symm
              have h_write_eq :
                  getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) j j =
                    getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n j) j j := by
                rw [h_array_step_eq_j]
              rw [h_write_eq]
              have hrow : j < state_array.coeffs.size := by
                rw [hh501]; exact hjn
              have hcol : j < state_array.coeffs[j]!.size := by
                rw [hh500 j hjn]; exact hjn
              rw [gapH36 _ _ _ _ hrow hcol]
              rw [gapH23 state_array.matrix jFin jFin, hh508]
            · have hj_lt : j < state_matrix.step := Nat.lt_of_le_of_ne hj_le hj_eq
              rw [gapH2 _ _ _ _ _ _
                (show j ≠ state_array.step by rw [hh519]; omega)]
              exact hh499 j hj_lt hjn
          have h_coeffs_unwritten_new :
              ∀ j (_hjs : new_matrix.step ≤ j) (_hjn : j < n),
                getArrayEntry new_array.coeffs j j = 0 := by
            intro j hjs hjn
            show getArrayEntry (writeScaledColumn _ _ _ _) j j = 0
            have hj_gt : state_matrix.step < j := hjs
            rw [gapH2 _ _ _ _ _ _
              (show j ≠ state_array.step by rw [hh519]; omega)]
            exact h_coeffs_unwritten j (Nat.le_of_lt hj_gt) hjn
          have h_fuel_new : i.val < new_matrix.step + fuel' ∨ i.val < new_matrix.step := by
            show i.val < state_matrix.step + 1 + fuel' ∨ i.val < state_matrix.step + 1
            rcases h_fuel with hor1 | hor2
            · left; omega
            · right; omega
          exact ih h_step_new h_matrix_new h_prev_new h_no_sing_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_coeffs_processed_new h_coeffs_unwritten_new h_fuel_new
      ·
        rw [Matrix.noPivotLoop_done fuel' state_matrix hDone]
        left
        refine ⟨hh509, ?_⟩
        by_cases hh493 : state_array.step < n
        · have hh492 : ¬ state_array.step + 1 < n := hh519 ▸ hDone
          rw [gapH129 fuel' state_array hh493 hh492]
          by_cases h_ieq : i.val = state_matrix.step
          · have hh498 : state_array.step = i.val := by
              rw [hh519]; exact h_ieq.symm
            change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
            have h_rewrite_step :
                getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                  getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n i.val) i.val i.val := by
              rw [hh498]
            rw [h_rewrite_step]
            have hrow : i.val < state_array.coeffs.size := by
              rw [hh501]; exact i.isLt
            have hcol : i.val < state_array.coeffs[i.val]!.size := by
              rw [hh500 i.val i.isLt]; exact i.isLt
            rw [gapH36 _ _ _ _ hrow hcol,
              gapH23 state_array.matrix i i, hh508]
          · by_cases h_ilt : i.val < state_matrix.step
            · change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
              rw [gapH2 _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [hh519]; omega)]
              exact hh499 i.val h_ilt i.isLt
            · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
              have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              have hDone : ¬ state_matrix.step + 1 < n := hDone
              omega
        · rw [gapH249 (fuel' + 1) state_array hh493]
          have hArrayStep' : n ≤ state_array.step := Nat.le_of_not_lt hh493
          have h_ilt : i.val < state_matrix.step := by
            rw [← hh519]; exact Nat.lt_of_lt_of_le i.isLt hArrayStep'
          exact hh499 i.val h_ilt i.isLt
private theorem gapH111
    (b : Matrix Int n m) (hquot : StepWitness b) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      (Matrix.bareiss
        (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr))).toNat := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let data := Matrix.bareissNoPivotData GM
  let i : Fin n := ⟨r, hr⟩
  by_cases h_prefix :
      (Matrix.noPivotLoop r init).singularStep = none
  · have hdiag :=
      bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
        (b := b) r hr (by simpa [GM, init] using h_prefix)
    have h_step_r : (Matrix.noPivotLoop r init).step = r := by
      have h_room : init.step + r + 1 ≤ n := by
        simp [init, Matrix.noPivotInitialState]
        omega
      have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        r init rfl h_room h_prefix
      simpa [init, Matrix.noPivotInitialState] using h
    have h_entry_diag :
        gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
      have h_split : r + (n - r) = n := by omega
      have h_full :
          Matrix.noPivotLoop n init =
            Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init) := by
        simpa [h_split] using Matrix.noPivotLoop_add r (n - r) init
      rcases noPivotLoop_singular_inv (n := n) (n - r)
          (Matrix.noPivotLoop r init) h_prefix with h_none | h_sing
      · have hdata : data.singularStep = none := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_none
        simp [gramDetVecEntry, data, hdata, i]
        simp [bareissDiagNat]
      · rcases h_sing with ⟨k, h_sing_full, h_step_full, h_zero_full, _hk_bound⟩
        have hdata : data.singularStep = some k.val := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_sing_full
        have hmono := noPivotLoop_step_monotone (n - r) (Matrix.noPivotLoop r init)
        have hr_le_k : r ≤ k.val := by
          rw [h_step_r, h_step_full] at hmono
          exact hmono
        by_cases hkr : k.val = r
        · have hlt : k.val < r + 1 := by omega
          have hdata_matrix :
              data.matrix[i][i] =
                (Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init)).matrix[i][i] := by
            simp [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full]
          have hzero_i : data.matrix[i][i] = 0 := by
            have hi_eq : i = k := Fin.ext hkr.symm
            rw [hdata_matrix]
            simpa [hi_eq] using h_zero_full
          simp [gramDetVecEntry, data, hdata, i, hlt]
          simpa [data, i] using (congrArg Int.toNat hzero_i).symm
        · have hlt : ¬ k.val < r + 1 := by omega
          simp [gramDetVecEntry, data, hdata, i, hlt]
          simp [bareissDiagNat]
    calc
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
          ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
            simpa [data, GM, i] using h_entry_diag
      _ = (Matrix.bareiss
            (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat := by
            exact congrArg Int.toNat (by simpa [data, GM, i] using hdiag)
  · rcases noPivotLoop_singular_inv (n := n) r init rfl with h_none | h_sing
    · exact False.elim (h_prefix h_none)
    · rcases h_sing with ⟨k, h_sing_r, h_step_r, h_zero_r, h_klt⟩
      have hsr : k.val < r + 1 := by
        have h := noPivotLoop_singularStep_lt (n := n) r init rfl k.val h_sing_r
        simp [init, Matrix.noPivotInitialState] at h
        omega
      have hh503 :
          Matrix.noPivotLoop n init = Matrix.noPivotLoop r init := by
        have h_split : n = r + (n - r) := by omega
        have hext :=
          gapH108 init r (n - r) k
            h_sing_r h_step_r h_zero_r h_klt
        exact (congrArg (fun fuel => Matrix.noPivotLoop fuel init) h_split).trans hext
      have hdata : data.singularStep = some k.val := by
        simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, hh503] using h_sing_r
      have hleft :
          gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
        simp [gramDetVecEntry, data, hdata, hsr]
      have hright :
          (Matrix.bareiss
            (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat = 0 :=
        gapH109
          (b := b) r hr hquot k.val (by simpa [GM, init] using h_sing_r)
      rw [hright]
      simpa [data, GM] using hleft
theorem gramDetVecEntry_eq_gramDet
    (b : Matrix Int n m) (hquot : StepWitness b) (k : Nat) (hk : k ≤ n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨k, Nat.lt_succ_of_le hk⟩ =
      gramDet b k hk := by
  cases k with
  | zero =>
      rw [show hk = Nat.zero_le n from Subsingleton.elim _ _]
      rfl
  | succ r =>
      have hr : r < n := Nat.lt_of_succ_le hk
      calc
        gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
            ⟨r + 1, Nat.lt_succ_of_le hk⟩ =
          gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
            ⟨r + 1, Nat.succ_lt_succ hr⟩ := by
              rfl
        _ = (Matrix.bareiss
              (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
                (Nat.succ_le_of_lt hr))).toNat :=
              gapH111 (b := b) hquot r hr
        _ = gramDet b (r + 1) hk := by
              simp [gramDet, GramSchmidt.leadingGramMatrixInt_eq_principalSubmatrix_gram]
private theorem gapH113
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (getArrayEntry (scaledCoeffRows b) i i).toNat =
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨i + 1, Nat.succ_lt_succ hi⟩ := by
  let iFin : Fin n := ⟨i, hi⟩
  have hdiag :=
    gapH103
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (gapH192 b) (by rfl) (by rfl)
      (gapH343 b) (gapH285 b)
      (gapH302 n) (gapH153 n)
      (by
        intro j hjs _hjn
        simp [Matrix.noPivotInitialState] at hjs)
      (by
        intro j _hjs _hjn
        exact gapH107 n j j)
      n iFin (by
        left
        simp [Matrix.noPivotInitialState, iFin, hi])
  show (getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i).toNat =
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
      ⟨i + 1, Nat.succ_lt_succ hi⟩
  rcases hdiag with ⟨h_sing, h_eq⟩ | ⟨s, h_sing, h_cases⟩
  · simp only [Matrix.bareissNoPivotData, gramDetVecEntry, Matrix.finish,
      bareissDiagNat, Matrix.getElem_pair_eq_nested, h_sing]
    exact congrArg Int.toNat h_eq
  · simp only [Matrix.bareissNoPivotData, gramDetVecEntry, Matrix.finish,
      bareissDiagNat, Matrix.getElem_pair_eq_nested, h_sing]
    rcases h_cases with ⟨hsi, h_zero⟩ | ⟨his, h_eq⟩
    · have hsi' : s ≤ i := by
        simpa [iFin] using hsi
      have hs_lt : s < i + 1 := by omega
      rw [if_pos hs_lt]
      exact congrArg Int.toNat h_zero
    · have his' : i < s := by
        simpa [iFin] using his
      have hs_not_lt : ¬ s < i + 1 := by omega
      rw [if_neg hs_not_lt]
      exact congrArg Int.toNat h_eq
private theorem gapH179
    (b : Matrix Int n m) (hquot : StepWitness b) (i : Nat) (hi : i < n) :
    (getArrayEntry (scaledCoeffRows b) i i).toNat =
      gramDet b (i + 1) (Nat.succ_le_of_lt hi) := by
  rw [gapH113 (b := b) i hi,
    gramDetVecEntry_eq_gramDet (b := b) hquot (i + 1) (Nat.succ_le_of_lt hi)]
@[simp, grind =] theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := by
  rfl
private theorem gapH334 {α : Type u}
    (xs : List α) (f : α → Rat) (acc : Rat)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hacc : acc + (0 : Rat) = acc := by grind
      rw [hacc]
      exact ih acc hxs
private theorem gapH123
    {n : Nat} (k : Fin n) (f : Fin n → Rat) (acc : Rat)
    (hzero : ∀ j : Fin n, k.val < j.val → f j = 0) :
    Fin.foldl n (fun acc j => acc + f j) acc =
      Fin.foldl (k.val + 1)
        (fun acc j =>
          acc + f ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩) acc := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  induction n generalizing acc with
  | zero =>
      exact Fin.elim0 k
  | succ n ih =>
      cases k using Fin.cases with
      | zero =>
          have htail : ∀ j ∈ (List.finRange n).map Fin.succ, f j = 0 := by
            intro j hj
            rcases List.mem_map.mp hj with ⟨i, _hi, rfl⟩
            exact hzero (Fin.succ i) (Nat.succ_pos i.val)
          have htailFold :
              ((List.finRange n).map Fin.succ).foldl (fun acc j => acc + f j)
                  (acc + f 0) = acc + f 0 :=
            gapH334 ((List.finRange n).map Fin.succ) (fun j => f j)
              (acc + f 0) htail
          simpa [List.finRange_succ] using htailFold
      | succ k =>
          have hzero_tail : ∀ j : Fin n, k.val < j.val → f (Fin.succ j) = 0 := by
            intro j hj
            exact hzero (Fin.succ j) (Nat.succ_lt_succ hj)
          have htail := ih k (fun j => f (Fin.succ j)) (acc + f 0) hzero_tail
          have htail' :
              ((List.finRange n).map Fin.succ).foldl (fun acc j => acc + f j)
                  (acc + f 0) =
                ((List.finRange (k.val + 1)).map Fin.succ).foldl
                  (fun acc j =>
                    acc + f ⟨j.val,
                      Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt (Fin.succ k).isLt)⟩)
                  (acc + f 0) := by
            simpa [List.foldl_map] using htail
          simpa [List.finRange_succ, Nat.succ_eq_add_one, Nat.add_assoc] using htail'
private theorem gapH167
    {n : Nat} (k : Fin n) (f : Fin n → Rat)
    (hzero : ∀ j : Fin n, k.val < j.val → f j = 0) :
    Fin.foldl n (fun acc j => acc + f j) 0 =
      Fin.foldl (k.val + 1)
        (fun acc j =>
          acc + f ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩) 0 :=
  gapH123 k f 0 hzero
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt.Int
private theorem gapH335 {n' : Nat}
    (xs : List (Fin n')) (g h : Fin n' → Int) (acc : Int) :
    ((xs.foldl (fun a i => a + g i * h i) acc : Int) : Rat) =
      xs.foldl
        (fun a i => a + ((g i : Rat)) * ((h i : Rat)))
        (acc : Rat) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hpush : ((acc + g i * h i : Int) : Rat) =
          (acc : Rat) + (g i : Rat) * (h i : Rat) := by
        push_cast
        rfl
      have := ih (acc := acc + g i * h i)
      rw [this, hpush]
private theorem gapH413
    (b : Matrix Int n m) (c : Vector Int n) (col : Fin m) :
    (Matrix.vecMul c b)[col] =
      Fin.foldl n
        (fun (acc : Int) (i : Fin n) => acc + b[i][col] * (c)[i]) 0 := by
  rw [Fin.foldl_eq_finRange_foldl]
  show (Matrix.transpose b * c)[col] = _
  rw [Matrix.getElem_mulVec]
  show ((Matrix.transpose b).row col).dotProduct c = _
  rw [Matrix.row_transpose]
  simp [Vector.dotProduct, Matrix.col]
@[simp, grind =] theorem coeffs_mul_basis_eq_castIntMatrix (b : Matrix Int n m) :
    coeffs b * basis b = castIntMatrix b := by
  apply Hex.Matrix.ext_getElem
  intro ii jj
  let i := ii.val
  have hi : i < n := ii.isLt
  let j := jj.val
  have hj : j < m := jj.isLt
  have hdec := basis_decomposition b i hi
  have hentry :
      ((basis b).row ii)[jj] +
        (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] =
      ((castIntMatrix b).row ii)[jj] := by
    have hdecj := congrArg (fun v : Vector Rat m => v[jj]) hdec
    simpa [castIntMatrix, Matrix.row, Vector.getElem_add] using hdecj.symm
  show (coeffs b * basis b)[ii][jj] = (castIntMatrix b)[ii][jj]
  rw [Matrix.getElem_mul]
  unfold Vector.dotProduct
  let f : Fin n → Rat := fun k => ((coeffs b).row ii)[k] * ((basis b).col jj)[k]
  have hzero : ∀ k : Fin n, i < k.val → f k = 0 := by
    intro k hk
    have hcoeff :
        GramSchmidt.entry (coeffs b) ii k = 0 :=
      coeffs_upper b i k.val hi k.isLt hk
    change ((coeffs b).row ii)[k] * ((basis b).col jj)[k] = 0
    rw [show ((coeffs b).row ii)[k] = 0 from hcoeff]
    grind
  have htrunc := gapH167 ii f hzero
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl] at htrunc
  change (List.finRange n).foldl (fun acc k => acc + f k) 0 =
    (castIntMatrix b)[ii][jj]
  rw [htrunc, List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hprefix :
      (List.finRange i).foldl
        (fun acc (x : Fin i) =>
          acc + f ⟨(Fin.castSucc x).val,
            Nat.lt_of_lt_of_le (Fin.castSucc x).isLt (Nat.succ_le_of_lt hi)⟩) 0 =
      (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] := by
    unfold GramSchmidt.prefixCombination GramSchmidt.entry
    rw [Fin.foldl_eq_finRange_foldl]
    let lift : Fin i → Fin n := fun x => ⟨x.val, Nat.lt_trans x.isLt hi⟩
    have hfold :
        ∀ xs : List (Fin i), ∀ accR : Rat, ∀ accV : Vector Rat m,
          accR = accV[jj] →
          xs.foldl
              (fun acc (x : Fin i) =>
                acc + f ⟨(Fin.castSucc x).val,
                  Nat.lt_of_lt_of_le (Fin.castSucc x).isLt (Nat.succ_le_of_lt hi)⟩)
              accR =
            (xs.foldl
              (fun acc (x : Fin i) =>
                acc + GramSchmidt.entry (coeffs b) ii (lift x) • (basis b).row (lift x))
              accV)[jj] := by
      intro xs
      induction xs with
      | nil =>
          intro accR accV hacc
          simp [hacc]
      | cons x xs ih =>
          intro accR accV hacc
          simp only [List.foldl_cons]
          apply ih
          have hstep :
              (accV + GramSchmidt.entry (coeffs b) ii (lift x) •
                  (basis b).row (lift x))[jj] =
                accV[jj] + GramSchmidt.entry (coeffs b) ii (lift x) *
                  ((basis b).row (lift x))[jj] := by
            change (accV + GramSchmidt.entry (coeffs b) ii (lift x) •
                (basis b).row (lift x))[jj.val]'jj.isLt =
              accV[jj.val]'jj.isLt + GramSchmidt.entry (coeffs b) ii (lift x) *
                ((basis b).row (lift x))[jj.val]'jj.isLt
            rw [Vector.getElem_add, Vector.getElem_smul]
            change accV[jj.val]'jj.isLt +
                GramSchmidt.entry (coeffs b) ii (lift x) *
                  ((basis b).row (lift x))[jj.val]'jj.isLt =
              accV[jj.val]'jj.isLt + GramSchmidt.entry (coeffs b) ii (lift x) *
                ((basis b).row (lift x))[jj.val]'jj.isLt
            rfl
          rw [hstep]
          simp [f, lift, GramSchmidt.entry, Matrix.row, Matrix.col, hacc, Hex.Matrix.getRow, Fin.getElem_fin]
    exact hfold (List.finRange i) 0 0 (by simp)
  rw [hprefix]
  have hdiag :
      ((coeffs b).row ii)[ii] = 1 := by
    exact coeffs_diag b i hi
  change (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] +
      ((coeffs b).row ii)[ii] * ((basis b).col jj)[ii] =
    (castIntMatrix b)[ii][jj]
  rw [hdiag]
  simp [Matrix.col]
  have hentry' :
      (basis b)[ii][jj] + (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] =
        (castIntMatrix b)[ii][jj] := by
    simpa [Matrix.row] using hentry
  change (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] +
      (basis b)[ii][jj] = (castIntMatrix b)[ii][jj]
  rw [← hentry']
  exact Lean.Grind.Semiring.add_comm _ _
theorem row_reconstruction (b : Matrix Int n m) (i : Fin n) :
    Vector.map (fun x : Int => (x : Rat)) (b.row i) =
      Matrix.vecMul ((coeffs b).row i) (basis b) := by
  have hmat := coeffs_mul_basis_eq_castIntMatrix b
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  have hentry := congrArg (fun M : Matrix Rat n m => M[i][jj]) hmat
  rw [Matrix.getElem_mul] at hentry
  have hcoord : ((b.row i)[jj] : Rat) =
      (Matrix.vecMul ((coeffs b).row i) (basis b))[jj] := by
    rw [Matrix.vecMul, Matrix.getElem_mulVec, Matrix.row_transpose]
    simpa [castIntMatrix, Matrix.row, Vector.dotProduct_comm] using hentry.symm
  simpa [Vector.getElem_map] using hcoord
theorem vecMul_basis_coeffs_reconstruction
    (b : Matrix Int n m) (c : Vector Int n) :
    Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b) =
      Matrix.vecMul (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b)) (basis b) := by
  have hcoeff : coeffs b * basis b = castIntMatrix b :=
    coeffs_mul_basis_eq_castIntMatrix b
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b))[jj] =
    (Matrix.vecMul (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b)) (basis b))[jj]
  have hmap :
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b))[jj] =
        ((Matrix.vecMul c b)[jj] : Rat) :=
    Vector.getElem_map _ _
  rw [hmap, gapH413 b c jj, Fin.foldl_eq_finRange_foldl]
  rw [gapH335 (List.finRange n)
    (fun i : Fin n => b[i][jj]) (fun i : Fin n => (c)[i]) 0]
  have hleft :
      (List.finRange n).foldl
        (fun acc i => acc + ((b[i][jj] : Int) : Rat) *
          (((c)[i] : Int) : Rat)) ((0 : Int) : Rat) =
      (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (castIntMatrix b))[jj] := by
    rw [show ((0 : Int) : Rat) = 0 by norm_cast]
    show _ = (Matrix.transpose (castIntMatrix b) *
        Vector.map (fun x : Int => (x : Rat)) c)[jj]
    rw [Matrix.getElem_mulVec, Matrix.row_transpose]
    simp [Vector.dotProduct, Matrix.col, castIntMatrix]
  rw [hleft, ← hcoeff]
  change ((Matrix.transpose (coeffs b * basis b)) *
      Vector.map (fun x : Int => (x : Rat)) c)[jj] =
    (Matrix.transpose (basis b) *
      (Matrix.transpose (coeffs b) *
        Vector.map (fun x : Int => (x : Rat)) c))[jj]
  rw [Matrix.transpose_mul_of_mul_comm, Matrix.mul_assoc_vec]
@[simp, grind =] theorem normSq_map_intCast (v : Vector Int m) :
    (Vector.map (fun x : Int => (x : Rat)) v).normSq =
      ((v.normSq : Int) : Rat) := by
  simpa [Vector.normSq, Vector.dotProduct, Fin.foldl_eq_finRange_foldl]
    using (gapH335 (List.finRange m)
      (fun i : Fin m => v[i]) (fun i : Fin m => v[i]) 0).symm
private theorem gapH414 {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind
private theorem gapH324 {n' : Nat} (u v : Vector Int n') :
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using
    gapH414 (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl
private theorem gapH326 (b : Matrix Int n m) (a c : Fin n) :
    (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a] := by
  rw [Matrix.getElem_gramMatrix, Matrix.getElem_gramMatrix]
  exact gapH324 _ _
theorem scaledCoeffMatrix_eq_borderedMinor
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.scaledCoeffMatrix b i j hji =
      Matrix.borderedMinor (Matrix.gramMatrix b) j.val
        (Nat.lt_trans hji i.isLt)
        ⟨j.val, Nat.lt_trans hji i.isLt⟩ i := by
  apply Hex.Matrix.ext_getElem
  intro pp cc
  by_cases hcj : cc.val < j.val
  ·
    by_cases hrj : pp.val < j.val
    · have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩) := by
        have hcc_ne : cc.val ≠ j.val := Nat.ne_of_lt hcj
        simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn]
        simp [GramSchmidt.liftFinLE, hcc_ne]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[
            (⟨pp.val, Nat.lt_trans hrj (Nat.lt_trans hji i.isLt)⟩ : Fin n)][
            (⟨cc.val, Nat.lt_trans hcj (Nat.lt_trans hji i.isLt)⟩ : Fin n)] := by
        rw [Matrix.borderedMinor_entry_lt_lt (Matrix.gramMatrix b) j.val
          (Nat.lt_trans hji i.isLt) ⟨j.val, Nat.lt_trans hji i.isLt⟩ i pp cc hrj hcj]
        simp [Hex.Matrix.getElem_pair_eq_nested]
      rw [h_sc, h_bm, Matrix.getElem_gramMatrix]
    ·
      have hpr : pp.val = j.val :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp pp.isLt) (Nat.le_of_not_lt hrj)
      have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩) := by
        have hcc_ne : cc.val ≠ j.val := Nat.ne_of_lt hcj
        simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn]
        simp [GramSchmidt.liftFinLE, hcc_ne]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[(⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n)][
            (⟨cc.val, Nat.lt_trans hcj (Nat.lt_trans hji i.isLt)⟩ : Fin n)] := by
        have hpr_not : ¬ pp.val < j.val := Nat.not_lt.mpr (Nat.le_of_eq hpr.symm)
        simp only [Matrix.borderedMinor, Matrix.getElem_ofFn]
        simp [hpr_not, hcj]
      rw [h_sc, h_bm, Matrix.getElem_gramMatrix]
      have hrow : (⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
          (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩ : Fin n)
          = ⟨j.val, Nat.lt_trans hji i.isLt⟩ := Fin.ext hpr
      rw [hrow]
  ·
    have hcj_eq : cc.val = j.val :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp cc.isLt) (Nat.le_of_not_lt hcj)
    by_cases hrj : pp.val < j.val
    · have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b i) := by
        simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn]
        simp [GramSchmidt.liftFinLE, hcj_eq]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[
            (⟨pp.val, Nat.lt_trans hrj (Nat.lt_trans hji i.isLt)⟩ : Fin n)][i] := by
        simp only [Matrix.borderedMinor, Matrix.getElem_ofFn]
        simp [hrj, hcj]
      rw [h_sc, h_bm, Matrix.getElem_gramMatrix]
    ·
      have hpr_eq : pp.val = j.val :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp pp.isLt) (Nat.le_of_not_lt hrj)
      have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b i) := by
        simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn]
        simp [GramSchmidt.liftFinLE, hcj_eq]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[(⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n)][i] := by
        have hpr_not : ¬ pp.val < j.val := hrj
        simp only [Matrix.borderedMinor, Matrix.getElem_ofFn]
        simp [hpr_not, hcj]
      rw [h_sc, h_bm, Matrix.getElem_gramMatrix]
      have hrow : (⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
          (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩ : Fin n)
          = ⟨j.val, Nat.lt_trans hji i.isLt⟩ := Fin.ext hpr_eq
      rw [hrow]
private theorem gapH234
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
          Fin.last j.val][Fin.last j.val] =
    (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt) i j))).matrix[
          Fin.last j.val][Fin.last j.val] := by
  rw [scaledCoeffMatrix_eq_borderedMinor b i j hji]
  exact gapH125
    (Matrix.gramMatrix b) (gapH326 (b := b))
    j.val (Nat.lt_trans hji i.isLt)
    ⟨j.val, Nat.lt_trans hji i.isLt⟩ i
    (Nat.le_refl _) (Nat.le_of_lt hji)
theorem scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (hh510 :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    getArrayEntry (scaledCoeffRows b) i.val j.val =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
        Fin.last j.val][Fin.last j.val] := by
  have hh523 :
      (Matrix.noPivotLoop (j.val - 0)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
    simpa using hh510
  have h_lower :=
    gapH93
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (gapH192 b) (by rfl)
      (gapH343 b) (gapH285 b)
      (gapH302 n) (gapH153 n)
      n i j (Nat.zero_le _) hji
      (by have := i.isLt; omega) hh523
  have h_state_level :
      getArrayEntry (scaledCoeffRows b) i.val j.val =
        (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] := by
    show getArrayEntry
        (scaledCoeffArrayLoop n n
            { step := 0, matrix := gramRows b, coeffs := zeroRows n,
              prevPivot := 1 }).coeffs i.val j.val = _
    have hh519 : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = 0 := rfl
    have h_sub : j.val - (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = j.val := by
      rw [hh519]; omega
    rw [h_lower, h_sub]
  rw [h_state_level]
  have h_bm :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val
      (Nat.lt_trans hji i.isLt) i j (Nat.le_of_lt hji) (Nat.le_refl _)).1
  rw [h_bm]
  exact
    (gapH234 b i j hji).symm
private theorem scaledCoeffArrayLoop_preserves_after_singular
    {n : Nat} {arrayState : ScaledCoeffArrayState}
    {matrixState : Matrix.BareissState Int n}
    (hstep : arrayState.step = matrixState.step)
    (hmatrix : rowsToMatrix arrayState.matrix n = matrixState.matrix)
    (hpast : arrayState.prevPivot = matrixState.prevPivot)
    (hnone : matrixState.singularStep = none)
    (hsize : arrayState.matrix.size = n)
    (hrows : ∀ r, r < n → arrayState.matrix[r]!.size = n)
    (fuel i j s : Nat) (hs : s < j)
    (hsing : (Matrix.noPivotLoop fuel matrixState).singularStep = some s) :
    matrixState.step ≤ s ∧
      getArrayEntry (scaledCoeffArrayLoop n fuel arrayState).coeffs i j =
        getArrayEntry arrayState.coeffs i j := by
  induction fuel generalizing arrayState matrixState with
  | zero =>
    rw [Matrix.noPivotLoop_zero_fuel, hnone] at hsing
    contradiction
  | succ fuel ih =>
    by_cases hroom : matrixState.step + 1 < n
    · have hk : matrixState.step < n := by omega
      have har : arrayState.step < n := by omega
      have hnext : arrayState.step + 1 < n := by omega
      let k : Fin n := ⟨matrixState.step, hk⟩
      have hpivot :
          getArrayEntry arrayState.matrix arrayState.step arrayState.step =
            matrixState.matrix[k][k] := by
        rw [hstep, gapH23 (n := n) arrayState.matrix k k, hmatrix]
      by_cases hp : matrixState.matrix[k][k] = 0
      · rw [Matrix.noPivotLoop_of_singular fuel matrixState hroom hp] at hsing
        have hstop : matrixState.step = s := Option.some.inj hsing
        rw [gapH114 fuel arrayState har hnext (hpivot.trans hp)]
        exact ⟨hstop.le, gapH2 _ _ _ _ _ _ (by omega)⟩
      · have hp' : getArrayEntry arrayState.matrix arrayState.step arrayState.step ≠ 0 :=
          fun h => hp (hpivot.symm.trans h)
        rw [Matrix.noPivotLoop_of_regular fuel matrixState hroom hp] at hsing
        rw [gapH63 fuel arrayState har hnext hp']
        let nextArray : ScaledCoeffArrayState :=
          { step := arrayState.step + 1
            matrix := stepScaledRows arrayState.matrix n arrayState.step
              (getArrayEntry arrayState.matrix arrayState.step arrayState.step) arrayState.prevPivot
            coeffs := writeScaledColumn arrayState.coeffs arrayState.matrix n arrayState.step
            prevPivot := getArrayEntry arrayState.matrix arrayState.step arrayState.step }
        let nextMatrix : Matrix.BareissState Int n :=
          { step := matrixState.step + 1
            matrix := Matrix.stepMatrix matrixState.matrix matrixState.step
              matrixState.matrix[k][k] matrixState.prevPivot
            prevPivot := matrixState.matrix[k][k]
            rowSwaps := matrixState.rowSwaps
            singularStep := none }
        have hstep' : nextArray.step = nextMatrix.step := by
          simpa [nextArray, nextMatrix, hstep]
        have hmatrix' : rowsToMatrix nextArray.matrix n = nextMatrix.matrix := by
          dsimp only [nextArray, nextMatrix]
          rw [gapH128 _ _ _ _ hsize hrows, hmatrix, hpivot, hstep, hpast]
        have hsize' : nextArray.matrix.size = n := by
          dsimp only [nextArray]
          rw [gapH314, hsize]
        have hrows' : ∀ r, r < n → nextArray.matrix[r]!.size = n :=
          gapH218 arrayState.matrix n arrayState.step _ _ hsize hrows
        have ⟨hs', hread⟩ :=
          ih (arrayState := nextArray) (matrixState := nextMatrix)
            hstep' hmatrix' hpivot rfl hsize' hrows' hsing
        have hstop : matrixState.step ≤ s := Nat.le_of_succ_le hs'
        exact ⟨hstop, hread.trans (gapH2 _ _ _ _ _ _ (by omega))⟩
    · rw [Matrix.noPivotLoop_done fuel matrixState hroom, hnone] at hsing
      contradiction
theorem getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
    {n m : Nat} (b : Matrix Int n m) (hquot : StepWitness b)
    (i j : Nat) (hi : i < n) (hji : j ≤ i)
    (s : Nat) (hsj : s < j)
    (h_sing : (Matrix.noPivotLoop j
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    getArrayEntry (scaledCoeffRowsSchur b) i j = 0 := by
  have hsing :
      (Matrix.noPivotLoop n
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s := by
    have hadd : j + (n - j) = n := by omega
    simpa only [hadd] using
      gapH222 j (n-j) (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_sing
  rw [getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
  exact (scaledCoeffArrayLoop_preserves_after_singular
    (arrayState := {step := 0, matrix := gramRows b, coeffs := zeroRows n, prevPivot := 1})
    (matrixState := Matrix.noPivotInitialState (Matrix.gramMatrix b))
    rfl (gapH192 b) rfl rfl (gapH343 b) (gapH285 b)
    n i j s hsj hsing).2.trans (gapH107 n i j)
theorem gramDetVec_eq_gramDet (b : Matrix Int n m) (hquot : StepWitness b)
    (k : Nat) (hk : k ≤ n) :
    (gramDetVec b).get ⟨k, Nat.lt_succ_of_le hk⟩ = gramDet b k hk := by
  rcases k with _ | r
  · show (gramDetVec b).get ⟨0, _⟩ = gramDet b 0 hk
    have h_one : (gramDetVec b).get ⟨0, Nat.zero_lt_succ n⟩ = 1 := by
      unfold gramDetVec data
      dsimp only
      change (gramDetVecFromScaledCoeffRows (scaledCoeffRowsSchur b))[0] = 1
      unfold gramDetVecFromScaledCoeffRows
      rw [Vector.getElem_ofFn]
    rw [show (gramDetVec b).get ⟨0, Nat.lt_succ_of_le hk⟩
          = (gramDetVec b).get ⟨0, Nat.zero_lt_succ n⟩ from rfl, h_one]
    exact (gramDet_zero b).symm
  · have hr : r < n := Nat.lt_of_succ_le hk
    show (gramDetVec b).get ⟨r + 1, _⟩ = gramDet b (r + 1) hk
    have hget :
        (gramDetVec b).get ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (getArrayEntry (scaledCoeffRowsSchur b) r r).toNat := by
      unfold gramDetVec data
      dsimp only
      change (gramDetVecFromScaledCoeffRows (scaledCoeffRowsSchur b))[r + 1] = _
      unfold gramDetVecFromScaledCoeffRows
      rw [Vector.getElem_ofFn]
    rw [hget, getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
    exact gapH179 (b := b) hquot r hr
theorem scaledCoeffs_lower_eq_noPivotLoop_scaledCoeffMatrix
    (b : Matrix Int n m) (hquot : StepWitness b)
    (i j : Fin n) (hji : j.val < i.val)
    (hh510 :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
        Fin.last j.val][Fin.last j.val] := by
  rw [scaledCoeffs_entry_eq_getArrayEntry,
    getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
  exact scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix b i j hji hh510
end GramSchmidt.Int
namespace GramSchmidt.Rat
end GramSchmidt.Rat
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
end GramSchmidt
namespace GramSchmidt.Int
theorem basis_sizeReduce (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int) :
    basis (sizeReduce b j k r) = basis b := by
  simpa [sizeReduce] using basis_rowAdd (b := b) (src := j) (dst := k) (c := -r) hjk
theorem coeffs_sizeReduce_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (i : Fin n) (hik : i ≠ k) :
    (coeffs (sizeReduce b j k r)).row i = (coeffs b).row i := by
  simpa [sizeReduce] using
    coeffs_rowAdd_other_row (b := b) (src := j) (dst := k) (c := -r) hjk i hik
theorem basis_adjacentSwap_of_lt (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hi : i.val + 1 < k.val) :
    (basis (adjacentSwap b k hk)).row i = (basis b).row i := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1k : km1.val < k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hikm1 : i.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.basis_rowSwap_of_before
      (b := b) (km1 := km1) (k := k) (i := i) hkm1k hikm1
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
namespace Internal
namespace LLLState
private theorem gapH283
    {n : Nat} (xs : List (Fin n))
    (base outerK outerJ : Vector Int n) (r : Int) (l : Fin n) :
    (xs.foldl
        (fun (row : Vector Int n) (i : Fin n) =>
          row.set i (outerK.get i - r * outerJ.get i))
        base).get l =
      if (∃ i ∈ xs, i.val = l.val) then
        outerK.get l - r * outerJ.get l
      else
        base.get l := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases h_xs : ∃ i ∈ xs, i.val = l.val
    · simp [h_xs]
    · by_cases h_xl : x.val = l.val
      · have h_cons : ∃ i ∈ x :: xs, i.val = l.val :=
          ⟨x, List.mem_cons.mpr (Or.inl rfl), h_xl⟩
        have h_xeq : x = l := Fin.eq_of_val_eq h_xl
        subst h_xeq
        simp only [h_xs, ↓reduceIte, h_cons]
        change (base.set x.val (outerK.get x - r * outerJ.get x) x.isLt)[x.val] = _
        exact Vector.getElem_set_self x.isLt
      · have h_cons : ¬ ∃ i ∈ x :: xs, i.val = l.val := by
          rintro ⟨i, hi, hi_l⟩
          rcases List.mem_cons.mp hi with rfl | hxs
          · exact h_xl hi_l
          · exact h_xs ⟨i, hxs, hi_l⟩
        simp only [h_xs, ↓reduceIte, h_cons]
        change (base.set x.val (outerK.get x - r * outerJ.get x) x.isLt)[l.val] = base[l.val]
        exact Vector.getElem_set_ne x.isLt l.isLt h_xl
theorem foldl_finRange_set_outerSubMul_get_eq
    {n : Nat} (jVal : Nat) (hjn : jVal ≤ n)
    (base outerK outerJ : Vector Int n) (r : Int) (l : Fin n) :
    (Fin.foldl jVal
        (fun (row : Vector Int n) (l' : Fin jVal) =>
          let lFin : Fin n := ⟨l'.val, Nat.lt_of_lt_of_le l'.isLt hjn⟩
          row.set lFin (outerK.get lFin - r * outerJ.get lFin))
        base).get l =
      if l.val < jVal then
        outerK.get l - r * outerJ.get l
      else
        base.get l := by
  rw [Fin.foldl_eq_finRange_foldl]
  let cast : Fin jVal → Fin n :=
    fun l' => ⟨l'.val, Nat.lt_of_lt_of_le l'.isLt hjn⟩
  show ((List.finRange jVal).foldl
        (fun (row : Vector Int n) (l' : Fin jVal) =>
          row.set (cast l') (outerK.get (cast l') - r * outerJ.get (cast l')))
        base).get l = _
  rw [show ((List.finRange jVal).foldl
        (fun (row : Vector Int n) (l' : Fin jVal) =>
          row.set (cast l') (outerK.get (cast l') - r * outerJ.get (cast l')))
        base) =
      ((List.finRange jVal).map cast).foldl
        (fun (row : Vector Int n) (i : Fin n) =>
          row.set i (outerK.get i - r * outerJ.get i))
        base from
      (@List.foldl_map (Fin jVal) (Fin n) (Vector Int n) cast
        (fun row i => row.set i (outerK.get i - r * outerJ.get i))
        (List.finRange jVal) base).symm]
  rw [gapH283]
  by_cases hlj : l.val < jVal
  · have hex : ∃ i ∈ (List.finRange jVal).map cast, i.val = l.val := by
      refine ⟨⟨l.val, Nat.lt_of_lt_of_le hlj hjn⟩, ?_, rfl⟩
      rw [List.mem_map]
      exact ⟨⟨l.val, hlj⟩, List.mem_finRange _, rfl⟩
    rw [if_pos hex, if_pos hlj]
  · have hno : ¬ ∃ i ∈ (List.finRange jVal).map cast, i.val = l.val := by
      rintro ⟨i, hi_mem, hi_eq⟩
      rw [List.mem_map] at hi_mem
      obtain ⟨l', _, hl'⟩ := hi_mem
      have hcast : (cast l').val = l'.val := rfl
      have : l.val < jVal := by
        rw [← hi_eq, ← hl', hcast]
        exact l'.isLt
      exact hlj this
    rw [if_neg hno, if_neg hlj]
private theorem gapH429 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) :
    (s.sizeReduceColumn j k hjk).d = s.d := by
  unfold sizeReduceColumn
  by_cases hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · simp [hreduce]
  · simp [hreduce]
private theorem gapH366 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) :
    GramSchmidt.Int.basis (s.sizeReduceColumn j k hjk).b =
      GramSchmidt.Int.basis s.b := by
  unfold sizeReduceColumn
  by_cases hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · simp only [hreduce]
    exact GramSchmidt.Int.basis_sizeReduce s.b j k hjk
      (nearestQuotient ((s.ν.getRow k).get j)
        (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))
  · simp [hreduce]
private theorem gapH428 (s : LLLState n m) (k : Nat) (hk : k < n)
    (xs : List (Fin k)) :
    (xs.foldl
        (fun state j =>
          let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
          LLLState.sizeReduceColumn state jFin ⟨k, hk⟩ j.isLt)
        s).d = s.d := by
  induction xs generalizing s with
  | nil =>
      rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, gapH429]
private theorem gapH370 (s : LLLState n m) (k : Nat) (hk : k < n)
    (xs : List (Fin k)) :
    GramSchmidt.Int.basis
        (xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            LLLState.sizeReduceColumn state jFin ⟨k, hk⟩ j.isLt)
          s).b =
      GramSchmidt.Int.basis s.b := by
  induction xs generalizing s with
  | nil =>
      rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, gapH366]
@[grind =] theorem sizeReduce_d (s : LLLState n m) (k : Nat) :
    (s.sizeReduce k).d = s.d := by
  unfold sizeReduce
  by_cases hk : k < n
  · simpa [hk, Fin.foldr_eq_finRange_foldr] using
      gapH428 (s := s) (k := k) (hk := hk) (xs := (List.finRange k).reverse)
  · simp [hk]
@[grind =] theorem sizeReduce_basis (s : LLLState n m) (k : Nat) :
    GramSchmidt.Int.basis (s.sizeReduce k).b = GramSchmidt.Int.basis s.b := by
  unfold sizeReduce
  by_cases hk : k < n
  · simpa [hk, Fin.foldr_eq_finRange_foldr] using
      gapH370 (s := s) (k := k) (hk := hk) (xs := (List.finRange k).reverse)
  · simp [hk]
end LLLState
end Internal
open Hex.Internal
namespace Internal
end Internal
end Hex
end
end
section
section
namespace Hex
namespace Internal.LLLCore
end Internal.LLLCore
open Hex.Internal
namespace Internal.LLLCore
private theorem gapH376 (x : Rat) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using (Lean.Grind.OrderedRing.sq_nonneg (a := x))
private theorem gapH488 {α : Type} (xs : List α) (f : α → Rat)
    (acc : Rat) (hacc : 0 ≤ acc) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ xs.foldl (fun sum x => sum + f x) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (acc + f x) (Rat.add_nonneg hacc (hf x))
theorem basisNormSq_nonneg (basis : Matrix Rat n m) (i : Fin n) :
    0 ≤ basisNormSq basis i := by
  simp only [basisNormSq, Vector.normSq, Vector.dotProduct]
  exact gapH488 (List.finRange m) (fun j => (basis.row i)[j] * (basis.row i)[j]) 0
    (by grind) (fun j => gapH376 ((basis.row i)[j]))
private theorem gapH460 (δ η μ N Np : Rat)
    (hN : 0 ≤ N) (hsize : μ * μ ≤ η * η)
    (hlov : δ * N ≤ Np + μ * μ * N) :
    (δ - η * η) * N ≤ Np := by
  have hcoef : δ - η * η ≤ δ - μ * μ := by grind
  have hleft : (δ - η * η) * N ≤ (δ - μ * μ) * N :=
    Rat.mul_le_mul_of_nonneg_right hcoef hN
  have hlov' : (δ - μ * μ) * N ≤ Np := by
    have hsub : δ * N - μ * μ * N ≤ (Np + μ * μ * N) - μ * μ * N := by
      grind
    calc
      (δ - μ * μ) * N = δ * N - μ * μ * N := by grind
      _ ≤ (Np + μ * μ * N) - μ * μ * N := hsub
      _ = Np := by grind
  exact Rat.le_trans hleft hlov'
private theorem gapH480 (d N Np : Rat) (hd : 0 < d)
    (h : d * N ≤ Np) :
    N ≤ (1 / d) * Np := by
  have hdne : d ≠ 0 := by grind
  have hinv_pos : 0 < (1 / d : Rat) := by
    rw [Rat.div_def]
    simpa using (Rat.inv_pos.mpr hd)
  have hinv_nonneg : 0 ≤ (1 / d : Rat) := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_left h hinv_nonneg
  have hleft : (1 / d : Rat) * (d * N) = N := by
    rw [Rat.div_def, show (1 : Rat) * d⁻¹ = d⁻¹ by grind,
      ← Rat.mul_assoc, Rat.inv_mul_cancel d hdne]
    grind
  change (1 / d : Rat) * (d * N) ≤ (1 / d : Rat) * Np at hmul
  rwa [hleft] at hmul
private theorem gapH389 (a : Rat) (ha : 0 ≤ a) (k : Nat) :
    0 ≤ a ^ k := by
  induction k with
  | zero =>
      rw [Lean.Grind.Semiring.pow_zero]
      grind
  | succ k ih =>
      rw [Lean.Grind.Semiring.pow_succ]
      exact Rat.mul_nonneg ih ha
theorem stepBound (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (_hδη : η * η < δ)
    (i : Nat) (hi : i + 1 < n) :
    (δ - η * η) *
        basisNormSq (GramSchmidt.Int.basis b)
          ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ ≤
      basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩ := by
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  let iFin : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
  let ip1Fin : Fin n := ⟨i + 1, hi⟩
  let μ := coeffs[ip1Fin][iFin]
  rcases hred with ⟨hsize, hlov⟩
  have hsize' : μ * μ ≤ η * η := by
    simpa [basis, coeffs, iFin, ip1Fin, μ] using
      hsize (i + 1) i hi (Nat.lt_succ_self i)
  have hlov' :
      δ * basisNormSq basis iFin ≤
        basisNormSq basis ip1Fin + μ * μ * basisNormSq basis iFin := by
    simpa [basis, coeffs, iFin, ip1Fin, μ] using hlov i hi
  exact gapH460 δ η μ (basisNormSq basis iFin) (basisNormSq basis ip1Fin)
    (basisNormSq_nonneg basis iFin) hsize' hlov'
theorem stepAlpha (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (hδη : η * η < δ)
    (i : Nat) (hi : i + 1 < n) :
    basisNormSq (GramSchmidt.Int.basis b)
        ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ ≤
      (1 / (δ - η * η)) *
        basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩ := by
  have hpos : 0 < δ - η * η := by grind
  exact gapH480 (δ - η * η)
    (basisNormSq (GramSchmidt.Int.basis b)
      ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
    (basisNormSq (GramSchmidt.Int.basis b) ⟨i + 1, hi⟩)
    hpos (stepBound b hred hδη i hi)
theorem teleBoundAdd (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (hδη : η * η < δ)
    (j d : Nat) (hi : j + d < n) :
    basisNormSq (GramSchmidt.Int.basis b)
        ⟨j, Nat.lt_of_le_of_lt (Nat.le_add_right j d) hi⟩ ≤
      (1 / (δ - η * η)) ^ d *
        basisNormSq (GramSchmidt.Int.basis b) ⟨j + d, hi⟩ := by
  let α : Rat := 1 / (δ - η * η)
  have hα_nonneg : 0 ≤ α := by
    have hpos : 0 < δ - η * η := by grind
    have hα_pos : 0 < α := by
      dsimp [α]
      rw [Rat.div_def]
      simpa using (Rat.inv_pos.mpr hpos)
    grind
  induction d with
  | zero =>
      simp only [Nat.add_zero, Lean.Grind.Semiring.pow_zero]
      grind
  | succ d ih =>
      have hiprev : j + d < n := by omega
      have hchain := ih hiprev
      have hstep := stepAlpha b hred hδη (j + d) (by omega : j + d + 1 < n)
      have hmul := Rat.mul_le_mul_of_nonneg_left hstep
        (gapH389 α hα_nonneg d)
      calc
        basisNormSq (GramSchmidt.Int.basis b)
            ⟨j, Nat.lt_of_le_of_lt (Nat.le_add_right j (d + 1)) hi⟩
            ≤ α ^ d * basisNormSq (GramSchmidt.Int.basis b)
                ⟨j + d, hiprev⟩ := by simpa [α] using hchain
        _ ≤ α ^ d * (α * basisNormSq (GramSchmidt.Int.basis b)
                ⟨j + d + 1, by omega⟩) := by
              simpa [α] using hmul
        _ = α ^ (d + 1) * basisNormSq (GramSchmidt.Int.basis b)
                ⟨j + (d + 1), hi⟩ := by
              have hfin :
                  (⟨j + d + 1, by omega⟩ : Fin n) = ⟨j + (d + 1), hi⟩ :=
                Fin.ext rfl
              rw [hfin]
              rw [Lean.Grind.Semiring.pow_succ]
              grind
private theorem gapH352 {α : Rat} (hα : 1 ≤ α) :
    ∀ {i j : Nat}, i ≤ j → α ^ i ≤ α ^ j := by
  intro i j hij
  induction j with
  | zero =>
      have hi : i = 0 := Nat.le_zero.mp hij
      subst hi
      exact Rat.le_refl
  | succ k ih =>
      by_cases hi : i ≤ k
      · have hih := ih hi
        have hα_nn : (0 : Rat) ≤ α := by grind
        have hpow_k : 0 ≤ α ^ k := gapH389 α hα_nn k
        have hstep : α ^ k ≤ α ^ (k + 1) := by
          rw [Lean.Grind.Semiring.pow_succ]
          have h1 : α ^ k * 1 ≤ α ^ k * α :=
            Rat.mul_le_mul_of_nonneg_left hα hpow_k
          simpa using h1
        exact Rat.le_trans hih hstep
      · have hi' : i = k + 1 :=
          Nat.le_antisymm hij (Nat.succ_le_of_lt (Nat.lt_of_not_ge hi))
        subst hi'
        exact Rat.le_refl
private theorem gapH299 {α : Type} (l : List α)
    (f : α → Rat) (C acc : Rat) (hf : ∀ x ∈ l, f x ≤ C) :
    l.foldl (fun acc x => acc + f x) acc ≤ acc + (l.length : Rat) * C := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      have htail := ih (acc := acc + f x) (fun y hy => hf y (by simp [hy]))
      have hx := hf x (by simp)
      calc
        xs.foldl (fun acc x => acc + f x) (acc + f x)
            ≤ acc + f x + (xs.length : Rat) * C := htail
        _ ≤ acc + C + (xs.length : Rat) * C := by grind
        _ = acc + ((xs.length + 1 : Nat) : Rat) * C := by
          push_cast
          grind
theorem rowNormSq_le_basisNormSq (b : Matrix Int n m) {δ η : Rat}
    (hred : isLLLReduced b δ η) (hηsq : η * η ≤ 1)
    (hδη : η * η < δ) (hδ' : δ ≤ 1)
    (j i : Fin n) (hji : j.val ≤ i.val) :
    (((b.row j).normSq : Int) : Rat) ≤
      (n : Rat) * (1 / (δ - η * η)) ^ (n - 1) *
        basisNormSq (GramSchmidt.Int.basis b) i := by
  let α : Rat := 1 / (δ - η * η)
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  have hpos : 0 < δ - η * η := by grind
  have hαpos : 0 < α := by
    dsimp [α]
    rw [Rat.div_def]
    simpa using (Rat.inv_pos.mpr hpos)
  have hαnn : 0 ≤ α := by grind
  have hden_le_one : δ - η * η ≤ 1 := by
    have hsqnn : 0 ≤ η * η := gapH376 η
    grind
  have hden_ne : δ - η * η ≠ 0 := by grind
  have hα_one : 1 ≤ α := by
    have hunit : α * (δ - η * η) = 1 := by
      dsimp [α]
      rw [Rat.div_def, show (1 : Rat) * (δ - η * η)⁻¹ =
        (δ - η * η)⁻¹ by grind, Rat.inv_mul_cancel _ hden_ne]
    have hmul := Rat.mul_le_mul_of_nonneg_left hden_le_one hαnn
    rw [hunit] at hmul
    simpa using hmul
  have horth : ∀ k l : Fin n, k ≠ l →
      (basis.row k).dotProduct (basis.row l) = 0 := by
    intro k l hkl
    exact GramSchmidt.Int.basis_orthogonal b k.val l.val k.isLt l.isLt
      (fun h => hkl (Fin.ext h))
  have hreconstruct := GramSchmidt.Int.row_reconstruction b j
  have hnorm := congrArg Vector.normSq hreconstruct
  rw [GramSchmidt.Int.normSq_map_intCast,
    GramSchmidt.normSq_vecMul_of_orthogonal basis (coeffs.row j) horth,
    Fin.foldl_eq_finRange_foldl] at hnorm
  rw [hnorm]
  have hfold := gapH299 (List.finRange n)
    (fun k : Fin n =>
      (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq)
    (α ^ (n - 1) * basisNormSq basis i) 0 (by
      intro k _hk
      by_cases hkj : k.val ≤ j.val
      · have hki : k.val ≤ i.val := Nat.le_trans hkj hji
        have hcoeff : (coeffs.row j)[k] * (coeffs.row j)[k] ≤ 1 := by
          rcases Nat.lt_or_eq_of_le hkj with hlt | heq
          · have hsize := hred.1 j.val k.val j.isLt hlt
            exact Rat.le_trans hsize hηsq
          · have hfin : k = j := Fin.ext heq
            rw [hfin]
            have hdiag : (coeffs.row j)[j] = 1 := by
              simpa [coeffs, GramSchmidt.entry] using
                GramSchmidt.Int.coeffs_diag b j.val j.isLt
            rw [hdiag]
            grind
        have hbasisnn : 0 ≤ basisNormSq basis k := basisNormSq_nonneg basis k
        have hfirst :
            (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq ≤
              basisNormSq basis k := by
          have hmul := Rat.mul_le_mul_of_nonneg_right hcoeff hbasisnn
          simpa [basisNormSq, basis] using hmul
        have htele := teleBoundAdd b hred hδη k.val (i.val - k.val) (by omega)
        have hadd : k.val + (i.val - k.val) = i.val := Nat.add_sub_of_le hki
        have hkfin :
            (⟨k.val, Nat.lt_of_le_of_lt (Nat.le_add_right k.val (i.val - k.val))
              (by omega)⟩ : Fin n) = k := Fin.ext rfl
        have hifin : (⟨k.val + (i.val - k.val), by omega⟩ : Fin n) = i :=
          Fin.ext hadd
        rw [hkfin, hifin] at htele
        have hpow : α ^ (i.val - k.val) ≤ α ^ (n - 1) :=
          gapH352 hα_one (by omega)
        have hibasisnn : 0 ≤ basisNormSq basis i := basisNormSq_nonneg basis i
        have hpowmul := Rat.mul_le_mul_of_nonneg_right hpow hibasisnn
        exact Rat.le_trans hfirst (Rat.le_trans (by simpa [α, basis] using htele)
          (by simpa [α, basis] using hpowmul))
      · have hjk : j.val < k.val := Nat.lt_of_not_ge hkj
        have hzero : (coeffs.row j)[k] = 0 := by
          simpa [coeffs, GramSchmidt.entry] using
            GramSchmidt.Int.coeffs_upper b j.val k.val j.isLt k.isLt hjk
        rw [hzero]
        have hnonneg : 0 ≤ α ^ (n - 1) * basisNormSq basis i :=
          Rat.mul_nonneg (gapH389 α hαnn (n - 1))
            (basisNormSq_nonneg basis i)
        grind)
  have hfold' :
      (List.finRange n).foldl
        (fun acc k => acc +
          (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq) 0
        ≤ (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := by
    calc
      _ ≤ 0 + (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := by
        simpa using hfold
      _ = (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := by grind
  calc
    (List.finRange n).foldl
        (fun acc k => acc +
          (coeffs.row j)[k] * (coeffs.row j)[k] * (basis.row k).normSq) 0
        ≤ (n : Rat) * (α ^ (n - 1) * basisNormSq basis i) := hfold'
    _ = (n : Rat) * (1 / (δ - η * η)) ^ (n - 1) *
          basisNormSq (GramSchmidt.Int.basis b) i := by
          dsimp [α, basis]
          grind
end Internal.LLLCore
namespace Internal
end Internal
end Hex
end
end
section
section
open Matrix
namespace HexMatrixTheory
universe u
section RowOps
variable [Semiring R]
end RowOps
section RowAdd
variable [CommRing R]
end RowAdd
end HexMatrixTheory
end
end
section
section
open Matrix
namespace HexMatrixTheory
universe u
variable {R : Type u} {n m : Nat}
@[simp, grind =] theorem vectorEquiv_apply (v : Vector R n) (i : Fin n) :
    vectorEquiv v i = v[i] :=
  rfl
theorem foldl_finRange_eq_sum [AddCommMonoid R] (f : Fin n → R) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 = ∑ i, f i := by
  rw [← List.foldl_map]
  rw [← List.sum_eq_foldl]
  rw [← List.sum_toFinset f (List.nodup_finRange n)]
  rw [List.toFinset_finRange]
theorem dotProduct_eq [NonUnitalNonAssocSemiring R] (u v : Vector R n) :
    u.dotProduct v = dotProduct (vectorEquiv u) (vectorEquiv v) := by
  unfold Vector.dotProduct dotProduct
  rw [foldl_finRange_eq_sum]
  rfl
end HexMatrixTheory
end
end
section
section
namespace HexMatrixTheory
universe u v
variable {R : Type u} {n : Nat}
namespace PermutationVector
end PermutationVector
theorem matrixEquiv_borderedMinor
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    matrixEquiv (Hex.Matrix.borderedMinor M k hk i j) =
      (matrixEquiv M).submatrix
        (fun r : Fin (k + 1) =>
          if hr : r.val < k then ⟨r.val, Nat.lt_trans hr hk⟩ else i)
        (fun c : Fin (k + 1) =>
          if hc : c.val < k then ⟨c.val, Nat.lt_trans hc hk⟩ else j) := by
  ext r c
  simp only [Hex.Matrix.borderedMinor, matrixEquiv_apply, Matrix.submatrix_apply]
  rw [Hex.Matrix.getElem_ofFn]
  exact Hex.Matrix.getElem_pair_eq_nested M _ _
namespace OrderedFourShift
variable {n : Nat}
end OrderedFourShift
end HexMatrixTheory
end
end
section
section
namespace HexMatrixTheory
universe u
variable {R : Type u} [CommRing R] [DecidableEq R] {n : Nat}
variable {quot : R → R → R}
variable {hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a}
theorem bareissPivotInvariant_regular_no_swap
    {R : Type u} [CommRing R]
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissNoPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    BareissNoPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrixWith quot state.matrix state.step
          state.matrix[state.step][state.step] state.prevPivot
        prevPivot := state.matrix[state.step][state.step]
        rowSwaps := state.rowSwaps
        singularStep := none } :=
  bareissNoPivotInvariant_step quot hquot source state hinv hDone hp
theorem bareissPivotNoPivot_column_eq_zero
    (state : Hex.Matrix.BareissState R n) (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    ∀ i : Fin n, state.step ≤ i.val →
      state.matrix[i][
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)] =
        0 := by
  intro i hi
  by_cases heq : i.val = state.step
  · have hiFin :
        i = (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ :
          Fin n) :=
      Fin.ext heq
    rw [hiFin]
    simpa using hp0
  · have hstart : state.step + 1 ≤ i.val := by omega
    exact Hex.Matrix.findPivot?_eq_zero_of_none state.matrix
      (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
      (state.step + 1) hfind i hstart
private theorem gapH185
    (state : Hex.Matrix.BareissState R n) (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    pivot ≠ (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n) := by
  intro hpivot
  have hge :
      state.step + 1 ≤ pivot.val :=
    Hex.Matrix.findPivot?_ge_start state.matrix
      (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
      (state.step + 1) hfind
  have hval : pivot.val = state.step := by
    simpa using congrArg Fin.val hpivot
  omega
private theorem gapH195 {R : Type u}
    (M : Hex.Matrix R n n) (k : Nat) (hk : k ≤ n)
    (kFin pivot : Fin n) (hkF : k ≤ kFin.val) (hp : k ≤ pivot.val) :
    Hex.Matrix.principalSubmatrix (Hex.Matrix.rowSwap M kFin pivot) k hk =
      Hex.Matrix.principalSubmatrix M k hk := by
  apply Hex.Matrix.ext_getElem
  intro r c
  have hr := r.isLt
  have hr_lt : r.val < n := Nat.lt_of_lt_of_le hr hk
  have h_r_ne_kFin : (⟨r.val, hr_lt⟩ : Fin n) ≠ kFin := by
    intro h
    have hval : r.val = kFin.val := by simpa using congrArg Fin.val h
    omega
  have h_r_ne_pivot : (⟨r.val, hr_lt⟩ : Fin n) ≠ pivot := by
    intro h
    have hval : r.val = pivot.val := by simpa using congrArg Fin.val h
    omega
  rw [Hex.Matrix.getElem_principalSubmatrix, Hex.Matrix.getElem_principalSubmatrix]
  simp only [Hex.Matrix.getElem_rowSwap, if_neg h_r_ne_pivot, if_neg h_r_ne_kFin]
private theorem gapH384 {R : Type u}
    (M : Hex.Matrix R n n) (kFin pivot r : Fin n) (c : Fin n)
    (hr_ne_kFin : r ≠ kFin) (hr_ne_pivot : r ≠ pivot) :
    (Hex.Matrix.rowSwap M kFin pivot)[r][c] = M[r][c] := by
  rw [Hex.Matrix.getElem_rowSwap, if_neg hr_ne_pivot, if_neg hr_ne_kFin]
private theorem gapH349 {R : Type u}
    (M : Hex.Matrix R n n) (kFin pivot r : Fin n) (c : Fin n) :
    (Hex.Matrix.rowSwap M kFin pivot)[r][c] =
      M[if r = pivot then kFin else if r = kFin then pivot else r][c] := by
  rw [Hex.Matrix.getElem_rowSwap]
  by_cases hrp : r = pivot
  · simp only [if_pos hrp]
  · by_cases hrk : r = kFin
    · simp only [if_neg hrp, if_pos hrk]
    · simp only [if_neg hrp, if_neg hrk]
private theorem gapH240 {R : Type u}
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n)
    (kFin pivot : Fin n) (hkF : kFin.val = k) (hp : k + 1 ≤ pivot.val)
    (i j : Fin n) :
    Hex.Matrix.borderedMinor (Hex.Matrix.rowSwap M kFin pivot) k hk i j =
      Hex.Matrix.borderedMinor M k hk
        (if i = pivot then kFin else if i = kFin then pivot else i) j := by
  apply Hex.Matrix.ext_getElem
  intro r c
  simp only [Hex.Matrix.borderedMinor]
  rw [Hex.Matrix.getElem_ofFn, Hex.Matrix.getElem_ofFn]
  simp only [Hex.Matrix.getElem_pair_eq_nested]
  by_cases hrk : r.val < k
  · simp only [dif_pos hrk]
    have hr_lt : r.val < n := Nat.lt_trans hrk hk
    have h_r_ne_kFin : (⟨r.val, hr_lt⟩ : Fin n) ≠ kFin := by
      intro h
      have hval : r.val = kFin.val := by simpa using congrArg Fin.val h
      omega
    have h_r_ne_pivot : (⟨r.val, hr_lt⟩ : Fin n) ≠ pivot := by
      intro h
      have hval : r.val = pivot.val := by simpa using congrArg Fin.val h
      omega
    exact gapH384 M kFin pivot ⟨r.val, hr_lt⟩ _ h_r_ne_kFin h_r_ne_pivot
  · simp only [dif_neg hrk]
    exact gapH349 M kFin pivot i _
theorem bareissPivotInvariant_regular_swap
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissNoPivotInvariant source state)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    BareissNoPivotInvariant
      (Hex.Matrix.rowSwap source
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)
      { state with
          matrix := Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot
          rowSwaps := state.rowSwaps + 1 } := by
  have hk : state.step < n := Nat.lt_of_succ_lt hDone
  set kFin : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
  have hkF_val : kFin.val = state.step := rfl
  have hp_ge :
      state.step + 1 ≤ pivot.val :=
    Hex.Matrix.findPivot?_ge_start state.matrix kFin (state.step + 1) hfind
  refine
    { singular_none := hinv.singular_none
      step_le := hinv.step_le
      prevPivot_eq := ?_
      prevPivot_ne := hinv.prevPivot_ne
      trailing_eq := ?_ }
  ·
    have hkF_ge : state.step ≤ kFin.val := Nat.le_of_eq hkF_val.symm
    have hp_le : state.step ≤ pivot.val := Nat.le_of_succ_le hp_ge
    rw [gapH195 source state.step hinv.step_le kFin pivot
      hkF_ge hp_le]
    exact hinv.prevPivot_eq
  · intro hnext i j hi hj
    rw [Hex.Matrix.getElem_rowSwap]
    rw [gapH240 source state.step hk kFin pivot hkF_val
      hp_ge i j]
    by_cases hip : i = pivot
    · simp only [if_pos hip]
      have hkFin_le : state.step ≤ kFin.val := Nat.le_of_eq hkF_val.symm
      exact hinv.trailing_eq hk kFin j hkFin_le hj
    · by_cases hik : i = kFin
      · simp only [if_neg hip, if_pos hik]
        have hp_step : state.step ≤ pivot.val := Nat.le_of_succ_le hp_ge
        exact hinv.trailing_eq hk pivot j hp_step hj
      · simp only [if_neg hip, if_neg hik]
        exact hinv.trailing_eq hk i j hi hj
private theorem gapH450 {R : Type u} [CommRing R] (swaps : Nat) :
    (if (swaps + 1) % 2 = 0 then (1 : R) else -1) =
      -(if swaps % 2 = 0 then (1 : R) else -1) := by
  by_cases h : swaps % 2 = 0
  · have hs : (swaps + 1) % 2 ≠ 0 := by omega
    simp [h, hs]
  · have hs : (swaps + 1) % 2 = 0 := by omega
    simp [h, hs]
theorem bareissPivotInvariant_initial {R : Type u} [CommRing R]
    (M : Hex.Matrix R n n) (h1 : (1 : R) ≠ 0) :
    BareissPivotInvariant M (Hex.Matrix.noPivotInitialState M) :=
  ⟨M, by simp [bareissStateSign, Hex.Matrix.noPivotInitialState],
    bareissNoPivotInvariant_initialWith M h1⟩
theorem bareissPivotInvariant_regular_no_swap_step
    {R : Type u} [CommRing R]
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    BareissPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrixWith quot state.matrix state.step
          state.matrix[state.step][state.step] state.prevPivot
        prevPivot := state.matrix[state.step][state.step]
        rowSwaps := state.rowSwaps
        singularStep := none } := by
  rcases hinv with ⟨logicalSource, hdet, hnopiv⟩
  exact ⟨logicalSource, hdet,
    bareissPivotInvariant_regular_no_swap quot hquot logicalSource state hnopiv hDone hp⟩
private theorem gapH220
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    BareissPivotInvariant source
      { state with
          matrix := Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot
          rowSwaps := state.rowSwaps + 1 } := by
  rcases hinv with ⟨logicalSource, hdet, hnopiv⟩
  set kFin : Fin n :=
    ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
  have hpivot_ne : pivot ≠ kFin :=
    gapH185 state hDone hfind
  refine ⟨Hex.Matrix.rowSwap logicalSource kFin pivot, ?_, ?_⟩
  · have hswap :
        Hex.Matrix.det (Hex.Matrix.rowSwap logicalSource kFin pivot) =
          -Hex.Matrix.det logicalSource :=
      Hex.Matrix.det_rowSwap logicalSource kFin pivot hpivot_ne.symm
    rw [hswap]
    simpa [bareissStateSign, gapH450, neg_mul, mul_neg, neg_neg] using hdet
  · simpa [kFin] using
      bareissPivotInvariant_regular_swap logicalSource state hnopiv hDone hfind
private theorem gapH26
    (state : Hex.Matrix.BareissState R n)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    (Hex.Matrix.rowSwap state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)[state.step][state.step] ≠ 0 := by
  set kFin : Fin n :=
    ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
  have hpivot_ne : pivot ≠ kFin :=
    gapH185 state hDone hfind
  have hpivot :
      state.matrix[pivot][kFin] ≠ 0 :=
    Hex.Matrix.findPivot?_some_ne_zero state.matrix kFin (state.step + 1) hfind
  have hentry :
      (Hex.Matrix.rowSwap state.matrix kFin pivot)[kFin][kFin] =
        state.matrix[pivot][kFin] := by
    rw [Hex.Matrix.getElem_rowSwap]
    simp [hpivot_ne.symm]
  simpa [kFin] using hentry ▸ hpivot
theorem bareissPivotInvariant_regular_swap_step
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    BareissPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrixWith quot
          (Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot)
          state.step
          ((Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot)[state.step][state.step])
          state.prevPivot
        prevPivot :=
          (Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot)[state.step][state.step]
        rowSwaps := state.rowSwaps + 1
        singularStep := none } := by
  have hswapped :=
    gapH220 source state hinv hDone hfind
  exact bareissPivotInvariant_regular_no_swap_step quot hquot source
    { state with
        matrix := Hex.Matrix.rowSwap state.matrix
          (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
          pivot
        rowSwaps := state.rowSwaps + 1 }
    hswapped hDone (gapH26 state hDone hfind)
theorem pivotLoop_invariant_of_singularStep_eq_none
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissPivotInvariant source state)
    (hregular : (Hex.Matrix.pivotLoopWith quot fuel state).singularStep = none) :
    BareissPivotInvariant source (Hex.Matrix.pivotLoopWith quot fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simpa only [Hex.Matrix.pivotLoopWith_zero_fuel (quot := quot)] using hinv
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              have hloop :=
                Hex.Matrix.pivotLoopWith_of_singular_no_pivot (quot := quot) fuel state hDone hp0
                  (by simpa [kFin] using hfind)
              rw [hloop] at hregular
              simp at hregular
          | some pivot =>
              have hp :=
                gapH26 state hDone (by simpa [kFin] using hfind)
              rw [Hex.Matrix.pivotLoopWith_of_regular_swap (quot := quot) fuel state hDone hp0
                (by simpa [kFin] using hfind) hp]
              apply ih
              · exact bareissPivotInvariant_regular_swap_step hquot source state hinv hDone
                  (by simpa [kFin] using hfind)
              · simpa [Hex.Matrix.pivotLoopWith_of_regular_swap (quot := quot) fuel state hDone hp0
                  (by simpa [kFin] using hfind) hp] using hregular
        · rw [Hex.Matrix.pivotLoopWith_of_regular_no_swap (quot := quot) fuel state hDone hp0]
          apply ih
          · exact bareissPivotInvariant_regular_no_swap_step quot hquot source state hinv hDone hp0
          · simpa [Hex.Matrix.pivotLoopWith_of_regular_no_swap (quot := quot) fuel state hDone hp0]
              using hregular
      · simpa [Hex.Matrix.pivotLoopWith_done (quot := quot) fuel state hDone] using hinv
private theorem gapH351 {R : Type u}
    (M : Hex.Matrix R n n) (h : n ≤ n) :
    Hex.Matrix.principalSubmatrix M n h = M := by
  apply Hex.Matrix.ext_getElem
  intro i j
  rw [Hex.Matrix.getElem_principalSubmatrix]
private theorem gapH289
    {R : Type u} [CommRing R]
    (k : Nat) (M : Hex.Matrix R (k + 1) (k + 1))
    (state : Hex.Matrix.BareissState R (k + 1))
    (hinv : BareissNoPivotInvariant M state)
    (hstep : state.step = k) :
    state.matrix[(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] = Hex.Matrix.det M := by
  obtain ⟨step', matrix', prev', swaps', sing'⟩ := state
  change step' = k at hstep
  subst hstep
  have hk' : step' < step' + 1 := Nat.lt_succ_self step'
  have h_trail :=
    hinv.trailing_eq hk' ⟨step', hk'⟩ ⟨step', hk'⟩ (Nat.le_refl _) (Nat.le_refl _)
  change matrix'[(⟨step', hk'⟩ : Fin (step' + 1))][
      (⟨step', hk'⟩ : Fin (step' + 1))] = Hex.Matrix.det M
  change matrix'[(⟨step', hk'⟩ : Fin (step' + 1))][
      (⟨step', hk'⟩ : Fin (step' + 1))] =
    Hex.Matrix.det
      (Hex.Matrix.borderedMinor M step' hk' ⟨step', hk'⟩ ⟨step', hk'⟩) at h_trail
  rw [h_trail, borderedMinor_corner_eq_principalSubmatrix M step' hk',
    gapH351 M (Nat.succ_le_of_lt hk')]
theorem failedBareissColumn_above_pivot
    {R : Type u} [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n)
    (c : Fin n) (hc : k < c.val) :
    failedBareissColumn source k hk c = 0 := by
  show (if h : c.val ≤ k then _ else (0 : R)) = 0
  rw [dif_neg (Nat.not_le_of_lt hc)]
private theorem gapH130
    {R : Type u}
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n)
    (s : Fin k) (c : Fin (k + 1)) (hc : c.val < k) :
    failedBareissTopBlock source k hk s c =
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n)
        (⟨c.val, Nat.lt_trans hc hk⟩ : Fin n) := by
  show (if h : c.val < k then _ else _) = _
  rw [dif_pos hc]
private theorem gapH235
    {R : Type u}
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n)
    (s : Fin k) :
    failedBareissTopBlock source k hk s (Fin.last k) =
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n) ⟨k, hk⟩ := by
  show (if h : (Fin.last k : Fin (k + 1)).val < k then _ else _) = _
  simp only [Fin.val_last]
  rw [dif_neg (Nat.lt_irrefl k)]
private theorem gapH180
    {R : Type u}
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) :
    (failedBareissTopBlock source k hk).submatrix id (Fin.last k).succAbove =
      matrixEquiv (Hex.Matrix.principalSubmatrix source k (Nat.le_of_lt hk)) := by
  ext s t
  show failedBareissTopBlock source k hk s ((Fin.last k).succAbove t) = _
  rw [Fin.succAbove_last]
  have ht : (t.castSucc : Fin (k + 1)).val < k := by
    show t.val < k; exact t.isLt
  rw [gapH130 source k hk s t.castSucc ht]
  show matrixEquiv source _ _ = matrixEquiv (Hex.Matrix.principalSubmatrix _ _ _) _ _
  rw [matrixEquiv_apply, matrixEquiv_apply, Hex.Matrix.getElem_principalSubmatrix]
  rfl
theorem failedBareissColumn_at_pivot
    {R : Type u} [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) :
    failedBareissColumn source k hk ⟨k, hk⟩ =
      Hex.Matrix.det (Hex.Matrix.principalSubmatrix source k (Nat.le_of_lt hk)) := by
  show (if hc : (⟨k, hk⟩ : Fin n).val ≤ k then
      (-1) ^ (k + (⟨k, hk⟩ : Fin n).val) *
        Matrix.det ((failedBareissTopBlock source k hk).submatrix id
          (⟨(⟨k, hk⟩ : Fin n).val, Nat.lt_succ_of_le hc⟩ : Fin (k + 1)).succAbove)
      else 0) = _
  rw [dif_pos (le_refl k)]
  have hsign : (-1 : R) ^ (k + k) = 1 := by
    rw [← Nat.two_mul, pow_mul]; norm_num
  show (-1 : R) ^ (k + k) *
      Matrix.det ((failedBareissTopBlock source k hk).submatrix id
        (Fin.last k).succAbove) = _
  rw [hsign, one_mul, gapH180, ← det_eq]
private theorem gapH184
    {R : Type u}
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (r : Fin n)
    (c' : Fin (k + 1)) :
    ((matrixEquiv source).submatrix
        (fun r' : Fin (k + 1) =>
          if hr : r'.val < k then (⟨r'.val, Nat.lt_trans hr hk⟩ : Fin n) else r)
        (fun c'' : Fin (k + 1) =>
          if hc : c''.val < k then (⟨c''.val, Nat.lt_trans hc hk⟩ : Fin n) else
            ⟨k, hk⟩))
        (Fin.last k) c' =
      matrixEquiv source r
        (⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n) := by
  show matrixEquiv source
      (if hr : (Fin.last k : Fin (k + 1)).val < k then _ else r)
      (if hc : c'.val < k then (⟨c'.val, Nat.lt_trans hc hk⟩ : Fin n) else
        ⟨k, hk⟩) = _
  simp only [Fin.val_last]
  rw [dif_neg (Nat.lt_irrefl k)]
  by_cases hcv : c'.val < k
  · rw [dif_pos hcv]
  · have hc_eq : c'.val = k :=
      Nat.le_antisymm (Nat.le_of_lt_succ c'.isLt) (Nat.not_lt.mp hcv)
    rw [dif_neg hcv]
    show matrixEquiv source r (⟨k, hk⟩ : Fin n) =
      matrixEquiv source r (⟨c'.val, Nat.lt_of_le_of_lt
        (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n)
    rw [show (⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n) =
        (⟨k, hk⟩ : Fin n) from Fin.ext hc_eq]
private theorem gapH83
    {R : Type u}
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (r : Fin n)
    (c' : Fin (k + 1)) :
    ((matrixEquiv source).submatrix
        (fun r' : Fin (k + 1) =>
          if hr : r'.val < k then (⟨r'.val, Nat.lt_trans hr hk⟩ : Fin n) else r)
        (fun c'' : Fin (k + 1) =>
          if hc : c''.val < k then (⟨c''.val, Nat.lt_trans hc hk⟩ : Fin n) else
            ⟨k, hk⟩)).submatrix
        (Fin.last k).succAbove c'.succAbove =
      (failedBareissTopBlock source k hk).submatrix id c'.succAbove := by
  ext s t
  show matrixEquiv source
      (if hr : ((Fin.last k).succAbove s).val < k then
        (⟨((Fin.last k).succAbove s).val, Nat.lt_trans hr hk⟩ : Fin n) else r)
      (if hc : (c'.succAbove t).val < k then
        (⟨(c'.succAbove t).val, Nat.lt_trans hc hk⟩ : Fin n) else ⟨k, hk⟩) =
    failedBareissTopBlock source k hk s (c'.succAbove t)
  rw [Fin.succAbove_last]
  have hslt : (s.castSucc : Fin (k + 1)).val < k := s.isLt
  rw [dif_pos hslt]
  by_cases hctlt : (c'.succAbove t).val < k
  · rw [dif_pos hctlt]
    rw [gapH130 source k hk s (c'.succAbove t) hctlt]
    rfl
  · have hctlt' : k ≤ (c'.succAbove t).val := Nat.not_lt.mp hctlt
    have hct_eq : (c'.succAbove t).val = k := by
      have := (c'.succAbove t).isLt
      omega
    rw [dif_neg hctlt]
    have h_succAbove_eq : c'.succAbove t = Fin.last k := Fin.ext hct_eq
    rw [h_succAbove_eq, gapH235 source k hk s]
    rfl
private theorem gapH92
    {R : Type u} [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (r : Fin n) :
    ∑ c : Fin n, failedBareissColumn source k hk c * matrixEquiv source r c =
      Matrix.det
        (matrixEquiv (Hex.Matrix.borderedMinor source k hk r ⟨k, hk⟩)) := by
  let φ : Fin (k + 1) → Fin n :=
    fun c' => ⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩
  have hφ_apply : ∀ c' : Fin (k + 1), (φ c').val = c'.val := fun _ => rfl
  have hφ_inj : Function.Injective φ := by
    intro c₁ c₂ h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa [φ] using this
  have hLHS :
      ∑ c : Fin n, failedBareissColumn source k hk c * matrixEquiv source r c =
        ∑ c' : Fin (k + 1),
          failedBareissColumn source k hk (φ c') * matrixEquiv source r (φ c') := by
    have h_others_zero : ∀ c ∈ (Finset.univ : Finset (Fin n)),
        c ∉ (Finset.univ : Finset (Fin (k + 1))).image φ →
        failedBareissColumn source k hk c * matrixEquiv source r c = 0 := by
      intro c _ hcnotin
      have hck : k < c.val := by
        by_contra h
        apply hcnotin
        have h' : c.val ≤ k := Nat.not_lt.mp h
        exact Finset.mem_image.mpr
          ⟨⟨c.val, Nat.lt_succ_of_le h'⟩, Finset.mem_univ _, Fin.ext rfl⟩
      rw [failedBareissColumn_above_pivot source k hk c hck, zero_mul]
    rw [← Finset.sum_subset
        ((Finset.univ : Finset (Fin (k + 1))).image φ).subset_univ h_others_zero]
    rw [Finset.sum_image (fun a _ b _ h => hφ_inj h)]
  rw [hLHS]
  rw [matrixEquiv_borderedMinor source k hk r ⟨k, hk⟩,
      Matrix.det_succ_row _ (Fin.last k)]
  apply Finset.sum_congr rfl
  intro c' _
  have hφc'_le : (φ c').val ≤ k := Nat.le_of_lt_succ c'.isLt
  have hφc'_eq_c' : (⟨(φ c').val, Nat.lt_succ_of_le hφc'_le⟩ : Fin (k + 1)) = c' :=
    Fin.ext rfl
  have hα_eq :
      failedBareissColumn source k hk (φ c') =
        (-1) ^ (k + c'.val) *
          Matrix.det
            ((failedBareissTopBlock source k hk).submatrix id c'.succAbove) := by
    show (if hc : (φ c').val ≤ k then _ else (0 : R)) = _
    rw [dif_pos hφc'_le, hφc'_eq_c', hφ_apply]
  rw [hα_eq, gapH184 source k hk r c',
      gapH83 source k hk r c']
  show (-1 : R) ^ (k + c'.val) *
      Matrix.det ((failedBareissTopBlock source k hk).submatrix id c'.succAbove) *
      matrixEquiv source r (φ c') =
    (-1 : R) ^ ((Fin.last k : Fin (k + 1)).val + c'.val) *
      matrixEquiv source r
        (⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n) *
      Matrix.det ((failedBareissTopBlock source k hk).submatrix id c'.succAbove)
  simp only [Fin.val_last]
  show (-1 : R) ^ (k + c'.val) * _ * matrixEquiv source r (φ c') =
    (-1 : R) ^ (k + c'.val) * matrixEquiv source r (φ c') * _
  ring
private theorem gapH97
    {R : Type u} [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (r : Fin n) (hr : r.val < k) :
    Matrix.det
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk r ⟨k, hk⟩)) = 0 := by
  rw [matrixEquiv_borderedMinor source k hk r ⟨k, hk⟩]
  apply Matrix.det_zero_of_row_eq (i := (⟨r.val, Nat.lt_succ_of_lt hr⟩ : Fin (k + 1)))
    (j := Fin.last k)
  · intro h
    have hv : r.val = k := by simpa using congrArg Fin.val h
    omega
  funext c
  show matrixEquiv source
      (if h : (⟨r.val, Nat.lt_succ_of_lt hr⟩ : Fin (k + 1)).val < k then _ else r) _ =
    matrixEquiv source
      (if h : (Fin.last k : Fin (k + 1)).val < k then _ else r) _
  rw [dif_pos hr]
  simp only [Fin.val_last]
  rw [dif_neg (Nat.lt_irrefl k)]
theorem failed_bareiss_column_dependence
    {R : Type u} [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n)
    (hprev :
      Hex.Matrix.det (Hex.Matrix.principalSubmatrix source k (Nat.le_of_lt hk)) ≠ 0)
    (hcol :
      ∀ i : Fin n, k ≤ i.val →
        Hex.Matrix.det
          (Hex.Matrix.borderedMinor source k hk i (⟨k, hk⟩ : Fin n)) = 0) :
    ∃ α : Fin n → R,
      α ⟨k, hk⟩ ≠ 0 ∧
        (∀ c : Fin n, k < c.val → α c = 0) ∧
        (matrixEquiv source).mulVec α = 0 := by
  refine ⟨failedBareissColumn source k hk, ?_,
    fun c hc => failedBareissColumn_above_pivot source k hk c hc, ?_⟩
  · rw [failedBareissColumn_at_pivot source k hk]; exact hprev
  funext r
  show ∑ c : Fin n,
      matrixEquiv source r c * failedBareissColumn source k hk c = 0
  have h_comm :
      ∑ c : Fin n, matrixEquiv source r c * failedBareissColumn source k hk c =
        ∑ c : Fin n, failedBareissColumn source k hk c * matrixEquiv source r c := by
    apply Finset.sum_congr rfl
    intros c _
    exact mul_comm _ _
  rw [h_comm, gapH92 source k hk r]
  by_cases hrk : r.val < k
  · exact gapH97 source k hk r hrk
  · have hrk' : k ≤ r.val := Nat.not_lt.mp hrk
    rw [← det_eq]
    exact hcol r hrk'
theorem det_eq_zero_of_bareiss_failed_column
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0)
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n)
    (hprev :
      Hex.Matrix.det (Hex.Matrix.principalSubmatrix source k (Nat.le_of_lt hk)) ≠ 0)
    (hcol : ∀ i : Fin n, k ≤ i.val →
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i ⟨k, hk⟩) = 0) :
    Hex.Matrix.det source = 0 := by
  let _ : IsDomain R := isDomain_of_quot quot hquot h1
  obtain ⟨α, hα_ne, _hα_above, hmulvec⟩ :=
    failed_bareiss_column_dependence source k hk hprev hcol
  have hdet_zero : Matrix.det (matrixEquiv source) = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨α, ?_, hmulvec⟩
    intro hα_zero
    apply hα_ne
    simpa using congrFun hα_zero ⟨k, hk⟩
  exact (det_eq source).trans hdet_zero
theorem bareissPivotInvariant_singular_no_pivot_det_eq_zero
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    Hex.Matrix.det source = 0 := by
  rcases hinv with ⟨logicalSource, hdet, hnopiv⟩
  have hk : state.step < n := Nat.lt_of_succ_lt hDone
  have hprev :
      Hex.Matrix.det
          (Hex.Matrix.principalSubmatrix logicalSource state.step (Nat.le_of_lt hk)) ≠ 0 := by
    rw [← hnopiv.prevPivot_eq]
    exact hnopiv.prevPivot_ne
  have hzero_col := bareissPivotNoPivot_column_eq_zero state hDone hp0 hfind
  have hcol : ∀ i : Fin n, state.step ≤ i.val →
      Hex.Matrix.det
          (Hex.Matrix.borderedMinor logicalSource state.step hk i ⟨state.step, hk⟩) =
        0 := by
    intro i hi
    have hentry :
        state.matrix[i][(⟨state.step, hk⟩ : Fin n)] = 0 :=
      hzero_col i hi
    have htrail :
        state.matrix[i][(⟨state.step, hk⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor logicalSource state.step hk i ⟨state.step, hk⟩) :=
      hnopiv.trailing_eq hk i ⟨state.step, hk⟩ hi (Nat.le_refl _)
    rw [← htrail]
    exact hentry
  have hlogical_zero :
      Hex.Matrix.det logicalSource = 0 :=
    det_eq_zero_of_bareiss_failed_column quot hquot
      (Hex.one_ne_zero_of_nonzero hprev) logicalSource state.step hk hprev hcol
  rw [hlogical_zero, mul_zero] at hdet
  exact hdet
theorem pivotLoop_singularStep_ne_none_det_eq_zero
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissPivotInvariant source state)
    (hsing : (Hex.Matrix.pivotLoopWith quot fuel state).singularStep ≠ none) :
    Hex.Matrix.det source = 0 := by
  induction fuel generalizing state with
  | zero =>
      rcases hinv with ⟨_, _, hnopiv⟩
      simp only [Hex.Matrix.pivotLoopWith_zero_fuel (quot := quot), hnopiv.singular_none] at hsing
      exact (hsing rfl).elim
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              exact bareissPivotInvariant_singular_no_pivot_det_eq_zero quot hquot source state hinv
                hDone hp0 (by simpa [kFin] using hfind)
          | some pivot =>
              have hp :=
                gapH26 state hDone (by simpa [kFin] using hfind)
              apply ih
              · exact bareissPivotInvariant_regular_swap_step hquot source state hinv hDone
                  (by simpa [kFin] using hfind)
              · simpa [Hex.Matrix.pivotLoopWith_of_regular_swap (quot := quot) fuel state hDone hp0
                  (by simpa [kFin] using hfind) hp] using hsing
        · apply ih
          · exact bareissPivotInvariant_regular_no_swap_step quot hquot source state hinv hDone hp0
          · simpa [Hex.Matrix.pivotLoopWith_of_regular_no_swap (quot := quot) fuel state hDone hp0]
              using hsing
      · rcases hinv with ⟨_, _, hnopiv⟩
        simp [Hex.Matrix.pivotLoopWith_done (quot := quot) fuel state hDone, hnopiv.singular_none] at hsing
theorem pivotLoop_initial_singularStep_ne_none_det_eq_zero
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0)
    (M : Hex.Matrix R n n)
    (hsing :
      (Hex.Matrix.pivotLoopWith quot n (Hex.Matrix.noPivotInitialState M)).singularStep ≠ none) :
    Hex.Matrix.det M = 0 :=
  pivotLoop_singularStep_ne_none_det_eq_zero hquot M n (Hex.Matrix.noPivotInitialState M)
    (bareissPivotInvariant_initial M h1) hsing
theorem bareissData_singularStep_ne_none_det_eq_zero
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0)
    (M : Hex.Matrix R n n)
    (hsing : (Hex.Matrix.bareissDataWith quot M).singularStep ≠ none) :
    Hex.Matrix.det M = 0 := by
  apply pivotLoop_initial_singularStep_ne_none_det_eq_zero hquot h1 M
  intro hregular
  apply hsing
  simpa [Hex.Matrix.bareissDataWith_eq_finish_pivotLoopWith (quot := quot), Hex.Matrix.finish] using hregular
private theorem gapH360
    (fuel : Nat) (state : Hex.Matrix.BareissState R n) (h : state.step + 1 ≤ n) :
    (Hex.Matrix.pivotLoopWith quot fuel state).step + 1 ≤ n := by
  induction fuel generalizing state with
  | zero =>
      show state.step + 1 ≤ n
      exact h
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              rw [Hex.Matrix.pivotLoopWith_of_singular_no_pivot (quot := quot) fuel state hDone hp0
                (by simpa [kFin] using hfind)]
              exact h
          | some pivot =>
              have hp :=
                gapH26 state hDone (by simpa [kFin] using hfind)
              rw [Hex.Matrix.pivotLoopWith_of_regular_swap (quot := quot) fuel state hDone hp0
                (by simpa [kFin] using hfind) hp]
              apply ih
              show state.step + 1 + 1 ≤ n
              omega
        · rw [Hex.Matrix.pivotLoopWith_of_regular_no_swap (quot := quot) fuel state hDone hp0]
          apply ih
          show state.step + 1 + 1 ≤ n
          omega
      · rw [Hex.Matrix.pivotLoopWith_done (quot := quot) fuel state hDone]
        exact h
private theorem gapH224
    (fuel : Nat) (state : Hex.Matrix.BareissState R n)
    (hregular : (Hex.Matrix.pivotLoopWith quot fuel state).singularStep = none)
    (hfuel : n ≤ state.step + fuel + 1) :
    n ≤ (Hex.Matrix.pivotLoopWith quot fuel state).step + 1 := by
  induction fuel generalizing state with
  | zero =>
      show n ≤ state.step + 1
      omega
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              have hloop :=
                Hex.Matrix.pivotLoopWith_of_singular_no_pivot (quot := quot) fuel state hDone hp0
                  (by simpa [kFin] using hfind)
              rw [hloop] at hregular
              simp at hregular
          | some pivot =>
              have hp :=
                gapH26 state hDone (by simpa [kFin] using hfind)
              rw [Hex.Matrix.pivotLoopWith_of_regular_swap (quot := quot) fuel state hDone hp0
                (by simpa [kFin] using hfind) hp]
              apply ih
              · simpa [Hex.Matrix.pivotLoopWith_of_regular_swap (quot := quot) fuel state hDone hp0
                  (by simpa [kFin] using hfind) hp] using hregular
              · show n ≤ state.step + 1 + fuel + 1
                omega
        · rw [Hex.Matrix.pivotLoopWith_of_regular_no_swap (quot := quot) fuel state hDone hp0]
          apply ih
          · simpa [Hex.Matrix.pivotLoopWith_of_regular_no_swap (quot := quot) fuel state hDone hp0]
              using hregular
          · show n ≤ state.step + 1 + fuel + 1
            omega
      · rw [Hex.Matrix.pivotLoopWith_done (quot := quot) fuel state hDone]
        show n ≤ state.step + 1
        omega
private theorem gapH160
    (M : Hex.Matrix R (k + 1) (k + 1))
    (hregular :
      (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M)).singularStep =
        none) :
    (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M)).step = k := by
  have hle :
      (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M)).step + 1 ≤
        k + 1 :=
    gapH360 (k + 1) (Hex.Matrix.noPivotInitialState M)
      (by show 0 + 1 ≤ k + 1; omega)
  have hge :
      k + 1 ≤
        (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M)).step + 1 :=
    gapH224 (k + 1) (Hex.Matrix.noPivotInitialState M)
      hregular (by show k + 1 ≤ 0 + (k + 1) + 1; omega)
  omega
private theorem gapH112
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (M : Hex.Matrix R n n) :
    (Hex.Matrix.bareissDataWith quot M).det = Matrix.det (matrixEquiv M) := by
  by_cases hregular : (Hex.Matrix.bareissDataWith quot M).singularStep = none
  · have hpiv :
        BareissPivotInvariant M
          (Hex.Matrix.pivotLoopWith quot n (Hex.Matrix.noPivotInitialState M)) := by
      apply pivotLoop_invariant_of_singularStep_eq_none hquot M n
        (Hex.Matrix.noPivotInitialState M) (bareissPivotInvariant_initial M h1)
      simpa [Hex.Matrix.bareissDataWith_eq_finish_pivotLoopWith (quot := quot), Hex.Matrix.finish] using hregular
    rcases hpiv with ⟨logicalSource, hdet, hnopiv⟩
    match n, M, logicalSource, hdet, hnopiv, hregular with
    | 0, M, logicalSource, hdet, hnopiv, hregular =>
        have hdata_sign : (Hex.Matrix.bareissDataWith quot M).sign =
            bareissStateSign (Hex.Matrix.pivotLoopWith quot 0 (Hex.Matrix.noPivotInitialState M)) := by
          simp [Hex.Matrix.bareissDataWith_eq_finish_pivotLoopWith (quot := quot), Hex.Matrix.finish,
            Hex.Matrix.BareissData.sign, bareissStateSign]
        have hlogical_det : Hex.Matrix.det logicalSource = 1 := by
          exact (det_eq logicalSource).trans (by rw [Matrix.det_isEmpty])
        have hsource_det : Hex.Matrix.det M = (Hex.Matrix.bareissDataWith quot M).sign := by
          rw [hdet, hlogical_det, mul_one]
          exact hdata_sign.symm
        rw [Hex.Matrix.BareissData.det_zero_eq _ hregular, ← hsource_det]
        exact det_eq M
    | k + 1, M, logicalSource, hdet, hnopiv, hregular =>
        have hloop_regular :
            (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M)).singularStep =
              none := by
          simpa [Hex.Matrix.bareissDataWith_eq_finish_pivotLoopWith (quot := quot), Hex.Matrix.finish] using hregular
        have hstep :
            (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M)).step = k :=
          gapH160 M hloop_regular
        have hentry :
            (Hex.Matrix.pivotLoopWith quot (k + 1)
                (Hex.Matrix.noPivotInitialState M)).matrix[
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] =
              Hex.Matrix.det logicalSource :=
          gapH289 k logicalSource
            (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M))
            hnopiv hstep
        have hsign :
            (Hex.Matrix.bareissDataWith quot M).sign =
              bareissStateSign
                (Hex.Matrix.pivotLoopWith quot (k + 1) (Hex.Matrix.noPivotInitialState M)) := by
          simp [Hex.Matrix.bareissDataWith_eq_finish_pivotLoopWith (quot := quot), Hex.Matrix.finish,
            Hex.Matrix.BareissData.sign, bareissStateSign]
        have hdata_entry :
            (Hex.Matrix.bareissDataWith quot M).matrix[
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] =
              Hex.Matrix.det logicalSource := by
          simpa [Hex.Matrix.bareissDataWith_eq_finish_pivotLoopWith (quot := quot), Hex.Matrix.finish] using hentry
        rw [Hex.Matrix.BareissData.det_succ_eq _ hregular, hdata_entry, hsign, ← hdet]
        exact det_eq M
  · have hdata_zero : (Hex.Matrix.bareissDataWith quot M).det = 0 := by
      unfold Hex.Matrix.BareissData.det
      split
      · rfl
      · contradiction
    have hhex_zero : Hex.Matrix.det M = 0 :=
      bareissData_singularStep_ne_none_det_eq_zero hquot h1 M hregular
    rw [hdata_zero, ← hhex_zero]
    exact det_eq M
private theorem gapH143
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (M : Hex.Matrix R n n) :
    Hex.Matrix.bareissWith quot M = Matrix.det (matrixEquiv M) := by
  rw [Hex.Matrix.bareissWith_eq_bareissDataWith_det (quot := quot) M]
  exact gapH112 quot hquot h1 M
theorem bareissWith_eq_mathlib_det
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (M : Hex.Matrix R n n) :
    Hex.Matrix.bareissWith quot M = Matrix.det (matrixEquiv M) := by
  by_cases h1 : (1 : R) = 0
  · have hz : ∀ x : R, x = 0 := by
      intro x
      rw [← one_mul x, h1, zero_mul]
    exact (hz _).trans (hz _).symm
  · exact gapH143 quot hquot h1 M
theorem bareiss_eq_mathlib_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M) :=
  bareissWith_eq_mathlib_det Hex.Matrix.exactDiv Int.mul_ediv_cancel M
end HexMatrixTheory
end
end
section
section
namespace HexMatrixTheory
universe u
variable {n : Nat}
end HexMatrixTheory
end
end
section
section
namespace Hex
namespace GramSchmidt
namespace Int
private theorem gapH215 {S : Type v} {n' m' : Nat} (f : Fin n' → Fin m' → S)
    (i : Fin n') :
    Hex.Matrix.getRow (Matrix.ofFn f) i = Vector.ofFn (f i) := by
  apply Vector.ext
  intro j hj
  show (Matrix.ofFn f)[i][(⟨j, hj⟩ : Fin m')] = (Vector.ofFn (f i))[j]'hj
  rw [Matrix.getElem_ofFn]
  simp
theorem leadingGramMatrixInt_det_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) := by
  let rowPrefix : Matrix Int t m :=
    Matrix.ofFn fun i j =>
      (b.row ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩)[j]
  have hrow : ∀ p : Fin t, Matrix.row rowPrefix p =
      b.row (GramSchmidt.liftFinLE p ht) := by
    intro p
    apply Vector.ext
    intro q hq
    show (Matrix.row rowPrefix p)[(⟨q, hq⟩ : Fin m)] =
      (b.row (GramSchmidt.liftFinLE p ht))[(⟨q, hq⟩ : Fin m)]
    rw [Matrix.getElem_row]
    simp only [rowPrefix, Matrix.getElem_ofFn]
    rfl
  have hgram :
      GramSchmidt.leadingGramMatrixInt b t ht =
        Matrix.gramMatrix rowPrefix := by
    apply Hex.Matrix.ext_getElem
    intro i j
    rw [Matrix.getElem_gramMatrix, hrow i, hrow j]
    simp only [GramSchmidt.leadingGramMatrixInt, Matrix.getElem_ofFn]
  rw [hgram]
  exact Matrix.det_gramMatrix_nonneg rowPrefix
theorem gramDet_pos (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      exact hli ⟨r, hrn⟩
private theorem gapH276 {α : Type v}
    (xs : List α) (f : α → Int) (acc : Int) :
    ((xs.foldl (fun acc x => acc + f x) acc : Int) : Rat) =
      xs.foldl (fun (acc' : Rat) x => acc' + ((f x : Int) : Rat)) ((acc : Rat)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hi := ih (acc := acc + f x)
      simpa [Rat.intCast_add] using hi
private theorem gapH373 {α : Type v}
    (xs : List α) (f : α → Int) (acc : Int) :
    ((xs.foldl (fun acc x => acc * f x) acc : Int) : Rat) =
      xs.foldl (fun (acc' : Rat) x => acc' * ((f x : Int) : Rat)) ((acc : Rat)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hi := ih (acc := acc * f x)
      simpa [Rat.intCast_mul] using hi
private theorem gapH459 {k : Nat} (perm : Vector (Fin k) k) :
    ((Matrix.detSign perm : Int) : Rat) = (Matrix.detSign perm : Rat) := by
  unfold Matrix.detSign
  by_cases h : Matrix.inversionCount perm.toList % 2 = 0
  · simp [h]
  · simp [h]
@[simp] private theorem gapH144 {k : Nat}
    (M : Matrix Int k k) (i j : Fin k) :
    (castIntDetMatrix M)[i][j] = ((M[i][j] : Int) : Rat) := by
  simp [castIntDetMatrix, gapH215]
private theorem gapH165 {α : Type v} {R : Type w} [Mul R]
    (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc * f x) acc =
      xs.foldl (fun acc x => acc * g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      rw [hx]
      exact ih (acc * g x) (fun y hy => h y (by simp [hy]))
private theorem gapH416 {k : Nat}
    (M : Matrix Int k k) (perm : Vector (Fin k) k) :
    ((Matrix.detProduct M perm : Int) : Rat) =
      Matrix.detProduct (castIntDetMatrix M) perm := by
  unfold Matrix.detProduct
  simp only [Fin.foldl_eq_finRange_foldl]
  rw [gapH373 (xs := List.finRange k)
    (f := fun i => M[(i, perm[i])]) (acc := 1)]
  rw [show ((1 : Int) : Rat) = (1 : Rat) from rfl]
  apply gapH165
  intro i _hi
  simp [castIntDetMatrix, gapH215, Fin.getElem_fin]
private theorem gapH462 {k : Nat}
    (M : Matrix Int k k) (perm : Vector (Fin k) k) :
    ((Matrix.detTerm M perm : Int) : Rat) =
      Matrix.detTerm (castIntDetMatrix M) perm := by
  unfold Matrix.detTerm
  rw [Rat.intCast_mul, gapH459, gapH416]
private theorem gapH30 {α : Type v} {R : Type w} [Add R]
    (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      rw [hx]
      exact ih (acc + g x) (fun y hy => h y (by simp [hy]))
private theorem gapH452 {k : Nat} (M : Matrix Int k k) :
    ((Matrix.det M : Int) : Rat) = Matrix.det (castIntDetMatrix M) := by
  unfold Matrix.det
  rw [gapH276 (xs := Matrix.permutationVectors k)
    (f := fun perm => Matrix.detTerm M perm) (acc := 0)]
  rw [show ((0 : Int) : Rat) = (0 : Rat) from rfl]
  apply gapH30
  intro perm _hperm
  exact gapH462 M perm
theorem dot_add_right_rat {m' : Nat} (u v w : Vector Rat m') :
    u.dotProduct (v + w) = u.dotProduct v + u.dotProduct w := by
  unfold Vector.dotProduct
  have h :
      ∀ (xs : List (Fin m')) (accV accW : Rat),
        xs.foldl (fun acc i => acc + u[i] * (v + w)[i]) (accV + accW) =
          xs.foldl (fun acc i => acc + u[i] * v[i]) accV +
            xs.foldl (fun acc i => acc + u[i] * w[i]) accW := by
    intro xs
    induction xs with
    | nil => intro accV accW; simp
    | cons i xs ih =>
        intro accV accW
        have hentry : (v + w)[i] = v[i] + w[i] := by
          change (v + w)[i.val] = v[i.val] + w[i.val]
          rw [Vector.getElem_add]
        simp only [List.foldl_cons]
        have hstart :
            accV + accW + u[i] * (v + w)[i] =
              (accV + u[i] * v[i]) + (accW + u[i] * w[i]) := by
          rw [hentry]
          grind
        rw [hstart]
        exact ih (accV + u[i] * v[i]) (accW + u[i] * w[i])
  have hzero : (0 : Rat) + 0 = 0 := by grind
  simpa [hzero] using h (List.finRange m') 0 0
theorem dot_smul_right_rat {m' : Nat} (s : Rat) (u v : Vector Rat m') :
    u.dotProduct (s • v) = s * u.dotProduct v := by
  unfold Vector.dotProduct
  have h :
      ∀ (xs : List (Fin m')) (acc : Rat),
        xs.foldl (fun acc i => acc + u[i] * (s • v)[i]) (s * acc) =
          s * xs.foldl (fun acc i => acc + u[i] * v[i]) acc := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons i xs ih =>
        intro acc
        have hentry : (s • v)[i] = s * v[i] := by
          change (s • v)[i.val] = s * v[i.val]
          rw [Vector.getElem_smul]
          rfl
        simp only [List.foldl_cons]
        have hstart :
            s * acc + u[i] * (s • v)[i] = s * (acc + u[i] * v[i]) := by
          rw [hentry]
          grind
        rw [hstart]
        exact ih (acc + u[i] * v[i])
  have hzero : s * (0 : Rat) = 0 := by grind
  simpa [hzero] using h (List.finRange m') 0
private theorem gapH331 {m' : Nat} (u : Vector Rat m') :
    u.dotProduct (0 : Vector Rat m') = 0 := by
  unfold Vector.dotProduct
  have h : ∀ (xs : List (Fin m')) (acc : Rat),
      xs.foldl (fun acc i => acc + u[i] * (0 : Vector Rat m')[i]) acc = acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        have hzero : (0 : Vector Rat m')[i] = 0 := by
          change (0 : Vector Rat m')[i.val] = 0
          rw [Vector.getElem_zero]
        rw [hzero]
        have : acc + u[i] * 0 = acc := by grind
        rw [this]
        exact ih acc
  exact h (List.finRange m') 0
private theorem gapH157 {α : Type v}
    (xs : List α) (f : α → Rat) (acc : Rat) :
    xs.foldl (fun acc x => acc + f x) acc =
      acc + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x), ih (acc := (0 : Rat) + f x)]
      grind
private theorem dot_comm_rat {m' : Nat} (u v : Vector Rat m') :
    u.dotProduct v = v.dotProduct u := by
  unfold Vector.dotProduct
  have h : ∀ (xs : List (Fin m')) (accU accV : Rat),
      accU = accV →
        xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
          xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
    intro xs
    induction xs with
    | nil => intro accU accV h; exact h
    | cons i xs ih =>
        intro accU accV h
        simp only [List.foldl_cons]
        apply ih
        rw [h]
        grind
  exact h (List.finRange m') 0 0 rfl
private theorem gapH18
    (coeffs : Matrix Rat n n) (basisM : Matrix Rat n m)
    (i : Nat) (hi : i < n) (u : Vector Rat m) :
    u.dotProduct (GramSchmidt.prefixCombination coeffs basisM i hi) =
      (List.finRange i).foldl
        (fun (acc : Rat) (j : Fin i) =>
          acc +
            GramSchmidt.entry coeffs ⟨i, hi⟩
                ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
              u.dotProduct
                (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
  unfold GramSchmidt.prefixCombination
  rw [Fin.foldl_eq_finRange_foldl]
  have hgen :
      ∀ (xs : List (Fin i)) (acc : Vector Rat m),
        u.dotProduct
            (xs.foldl
              (fun acc (j : Fin i) =>
                acc +
                  GramSchmidt.entry coeffs ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ •
                    basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)
              acc) =
          u.dotProduct acc +
            xs.foldl
              (fun (acc' : Rat) (j : Fin i) =>
                acc' +
                  GramSchmidt.entry coeffs ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
                    u.dotProduct
                      (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih, dot_add_right_rat, dot_smul_right_rat]
        rw [gapH157 xs _
          ((0 : Rat) + (GramSchmidt.entry coeffs ⟨i, hi⟩
              ⟨x.val, Nat.lt_trans x.isLt hi⟩ *
            u.dotProduct
              (basisM.row ⟨x.val, Nat.lt_trans x.isLt hi⟩)))]
        grind
  rw [hgen (List.finRange i) 0, gapH331]
  grind
private theorem gapH9
    (coeffs : Matrix Rat n n) (basisM : Matrix Rat n m)
    (i : Nat) (hi : i < n) (u : Vector Rat m)
    (h : ∀ (j : Fin i),
      u.dotProduct
          (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩) = 0) :
    u.dotProduct (GramSchmidt.prefixCombination coeffs basisM i hi) = 0 := by
  rw [gapH18]
  induction (List.finRange i) with
  | nil => rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [h j]
      have h0 : (0 : Rat) + GramSchmidt.entry coeffs ⟨i, hi⟩
          ⟨j.val, Nat.lt_trans j.isLt hi⟩ * 0 = 0 := by grind
      rw [h0]
      exact ih
private theorem gapH364 {R : Type v} (M : Matrix R n m) (i : Nat) (hi : i < n)
    (q : Fin (i + 1)) :
    (GramSchmidt.prefixRows M i hi).row q =
      M.row ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hi)⟩ := by
  show Hex.Matrix.getRow _ q = _
  rw [GramSchmidt.prefixRows, Hex.Matrix.getRow_ofRows]
  simp
private theorem gapH213 (b : Matrix Int n m) (i : Fin n) :
    (castIntMatrixRat b).row i = castIntRow b i := by
  show Hex.Matrix.getRow _ i = _
  rw [castIntMatrixRat, Hex.Matrix.getRow_ofRows]
  simp [castIntRow, Matrix.row]
private theorem gapH145
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Matrix.vecMul (originalProjectionCoords b i j hi hj) (GramSchmidt.prefixRows (castIntMatrixRat b) j hj) =
      basisPrefixProjection b i j hi hj := by
  exact Classical.choose_spec (basisPrefixProjection_mem_originalSpan b i j hi hj)
private theorem gapH332
    (M : Matrix Rat n m) (c : Vector Rat n) :
    Matrix.vecMul c M =
      (List.finRange n).foldl (fun acc j => acc + (c)[j] • M.row j) 0 := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
    ((List.finRange n).foldl (fun acc j => acc + (c)[j] • M.row j) 0)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
        (List.finRange n).foldl
          (fun acc j => acc + M[j.val][idxFin.val] * (c)[j])
          0 by
        have hcol : ∀ p : Fin n, (Matrix.col M idxFin)[p.val] =
            (Hex.Matrix.getRow M p)[idxFin.val] := by
          intro p
          show (Matrix.col M idxFin)[p] = M[p][idxFin]
          rw [Matrix.getElem_col]
        simp [Matrix.mulVec, Vector.dotProduct, hcol]]
  have hfold :
      ∀ xs : List (Fin n), ∀ accL : Rat, ∀ accR : Vector Rat m,
        accL = accR[idxFin] →
        xs.foldl (fun acc j => acc + M[j.val][idxFin.val] * (c)[j]) accL =
          (xs.foldl (fun acc j => acc + (c)[j] • M.row j) accR)[idxFin] := by
    intro xs
    induction xs with
    | nil =>
        intro accL accR hacc
        simp [hacc]
    | cons j rest ih =>
        intro accL accR hacc
        simp only [List.foldl_cons]
        apply ih
        change accL + M[j.val][idxFin.val] * (c)[j] =
          (accR + (c)[j] • M.row j)[idxFin.val]
        rw [Vector.getElem_add, Vector.getElem_smul, hacc]
        change accR[idx] + M[j.val][idx] * (c)[j] =
          accR[idx] + (c)[j] * M[j.val][idx]
        grind
  exact hfold (List.finRange n) 0 0 (by simp [Vector.getElem_zero])
private theorem gapH139
    (u : Vector Rat m) (M : Matrix Rat n m) (c : Vector Rat n) :
    u.dotProduct (Matrix.vecMul c M) =
      (List.finRange n).foldl
        (fun acc j => acc + (c)[j] * u.dotProduct (M.row j)) 0 := by
  rw [gapH332]
  have hgen :
      ∀ xs : List (Fin n), ∀ acc : Vector Rat m,
        u.dotProduct (xs.foldl (fun acc j => acc + (c)[j] • M.row j) acc) =
          u.dotProduct acc +
            xs.foldl (fun acc' j => acc' + (c)[j] * u.dotProduct (M.row j)) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp only [List.foldl_nil]
        grind
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih, dot_add_right_rat, dot_smul_right_rat]
        rw [gapH157 xs _
          ((0 : Rat) + (c)[x] * u.dotProduct (M.row x))]
        grind
  rw [hgen (List.finRange n) 0, gapH331]
  grind
private theorem gapH242
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n)
    (p : Fin (j + 1)) :
    Vector.dotProduct
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_of_lt hj)⟩)
        (basisPrefixProjection b i j hi hj) =
      (List.finRange (j + 1)).foldl
        (fun acc q =>
          acc + (originalProjectionCoords b i j hi hj)[q] *
            Vector.dotProduct
              (castIntRow b
                ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_of_lt hj)⟩)
              (castIntRow b
                ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hj)⟩)) 0 := by
  rw [← gapH145 b i j hi hj, gapH139]
  apply gapH30
  intro q _hq
  rw [gapH364, gapH213]
private theorem gapH388 (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (auxMatrix b k hk)[i][j] =
      (castIntRow b (GramSchmidt.liftFinLE i hk)).dotProduct
        ((basis b).row (GramSchmidt.liftFinLE j hk)) := by
  simp [auxMatrix, gapH215]
private theorem gapH20
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    castIntRow b ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  exact basis_decomposition (b := b) i hi
private theorem gapH393 (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) (hij : i.val < j.val) :
    (auxMatrix b k hk)[i][j] = 0 := by
  rw [gapH388]
  have hi' : i.val < n := Nat.lt_of_lt_of_le i.isLt hk
  have hj' : j.val < n := Nat.lt_of_lt_of_le j.isLt hk
  have hij' : i.val ≠ j.val := Nat.ne_of_lt hij
  rw [show GramSchmidt.liftFinLE i hk = ⟨i.val, hi'⟩ from rfl,
    show GramSchmidt.liftFinLE j hk = ⟨j.val, hj'⟩ from rfl, gapH20 b i.val hi',
    dot_comm_rat, dot_add_right_rat,
    dot_comm_rat ((basis b).row ⟨j.val, hj'⟩) ((basis b).row ⟨i.val, hi'⟩),
    basis_orthogonal b i.val j.val hi' hj' hij']
  have hprefix :
      ((basis b).row ⟨j.val, hj'⟩).dotProduct
          (GramSchmidt.prefixCombination (coeffs b) (basis b) i.val hi') = 0 := by
    apply gapH9
      (coeffs := coeffs b) (basisM := basis b) (i := i.val) (hi := hi')
      (u := (basis b).row ⟨j.val, hj'⟩)
    intro p
    have hp' : p.val < i.val := p.isLt
    have hpj : p.val ≠ j.val := Nat.ne_of_lt (Nat.lt_trans hp' hij)
    have hpj_lt : p.val < n := Nat.lt_trans hp' hi'
    exact basis_orthogonal b j.val p.val hj' hpj_lt fun h => hpj h.symm
  rw [hprefix]
  grind
private theorem gapH471 (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) :
    (auxMatrix b k hk)[i][i] =
      ((basis b).row (GramSchmidt.liftFinLE i hk)).normSq := by
  rw [gapH388]
  have hi' : i.val < n := Nat.lt_of_lt_of_le i.isLt hk
  rw [show GramSchmidt.liftFinLE i hk = ⟨i.val, hi'⟩ from rfl, gapH20 b i.val hi',
    dot_comm_rat, dot_add_right_rat]
  have hprefix :
      ((basis b).row ⟨i.val, hi'⟩).dotProduct
          (GramSchmidt.prefixCombination (coeffs b) (basis b) i.val hi') = 0 := by
    apply gapH9
      (coeffs := coeffs b) (basisM := basis b) (i := i.val) (hi := hi')
      (u := (basis b).row ⟨i.val, hi'⟩)
    intro p
    have hp' : p.val < i.val := p.isLt
    have hpi : p.val ≠ i.val := Nat.ne_of_lt hp'
    have hpi_lt : p.val < n := Nat.lt_trans hp' hi'
    exact basis_orthogonal b i.val p.val hi' hpi_lt fun h => hpi h.symm
  rw [hprefix]
  have hns :
      ((basis b).row ⟨i.val, hi'⟩).normSq =
        ((basis b).row ⟨i.val, hi'⟩).dotProduct ((basis b).row ⟨i.val, hi'⟩) := by
    rfl
  rw [hns]
  grind
private theorem gapH77 (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    Matrix.det (auxMatrix b k hk) = gramSchmidtNormProduct b k hk := by
  rw [Matrix.det_lowerTriangular_eq_foldl_diag (auxMatrix b k hk)
    (fun i j hij => gapH393 b k hk i j hij)]
  unfold gramSchmidtNormProduct
  rw [Fin.foldl_eq_finRange_foldl]
  apply gapH165
  intro i _hi
  rw [gapH471 b k hk i]
  rfl
private theorem gapH74 (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (s : Nat) (i j : Fin k) (hj : j.val < s) :
    (progressMatrix b k hk s)[i][j] =
      (castIntRow b (GramSchmidt.liftFinLE i hk)).dotProduct
        ((basis b).row (GramSchmidt.liftFinLE j hk)) := by
  simp [progressMatrix, gapH215, hj]
private theorem gapH120 (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (s : Nat) (i j : Fin k) (hj : ¬ j.val < s) :
    (progressMatrix b k hk s)[i][j] =
      (castIntRow b (GramSchmidt.liftFinLE i hk)).dotProduct
        (castIntRow b (GramSchmidt.liftFinLE j hk)) := by
  simp [progressMatrix, gapH215, hj]
private theorem gapH59 (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    progressMatrix b k hk k = auxMatrix b k hk := by
  apply Hex.Matrix.ext_getElem
  intro i j
  rw [gapH74 b k hk k i j j.isLt, gapH388]
private theorem gapH280 (k : Nat) (s : Nat) (hs : s < k)
    (src : Fin k) (hmem : src ∈ progressMatrixSources k s hs) :
    src ≠ ⟨s, hs⟩ := by
  unfold progressMatrixSources at hmem
  rw [List.mem_map] at hmem
  obtain ⟨p, _, hp⟩ := hmem
  intro h
  have hval := congrArg Fin.val h
  rw [← hp] at hval
  exact Nat.ne_of_lt p.isLt hval
private theorem gapH225
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s < k) :
    progressMatrix b k hk (s + 1) =
      Matrix.setCol (progressMatrix b k hk s) (⟨s, hs⟩ : Fin k)
        (fun i =>
          (progressMatrix b k hk s)[i][(⟨s, hs⟩ : Fin k)] +
          (progressMatrixSources k s hs).foldl
            (fun acc src =>
              acc + progressMatrixCoeff b k hk s hs src *
                (progressMatrix b k hk s)[i][src]) 0) := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  simp only [Hex.Matrix.getElem_rows]
  change (progressMatrix b k hk (s + 1))[ii][(⟨j, hj⟩ : Fin k)] =
    (Matrix.setCol (progressMatrix b k hk s) (⟨s, hs⟩ : Fin k)
      (fun i' =>
        (progressMatrix b k hk s)[i'][(⟨s, hs⟩ : Fin k)] +
        (progressMatrixSources k s hs).foldl
          (fun acc src =>
            acc + progressMatrixCoeff b k hk s hs src *
              (progressMatrix b k hk s)[i'][src]) 0))[ii][(⟨j, hj⟩ : Fin k)]
  rw [Matrix.getElem_setCol]
  by_cases hjs : (⟨j, hj⟩ : Fin k) = (⟨s, hs⟩ : Fin k)
  ·
    rw [if_pos hjs]
    have hjs_val : j = s := congrArg Fin.val hjs
    have hLHS_eq :
        (progressMatrix b k hk (s + 1))[ii][(⟨j, hj⟩ : Fin k)] =
          (progressMatrix b k hk (s + 1))[ii][(⟨s, hs⟩ : Fin k)] := by
      congr 1
    rw [hLHS_eq]
    have hjlt : (⟨s, hs⟩ : Fin k).val < s + 1 := Nat.lt_succ_self s
    rw [gapH74 b k hk (s + 1) ii (⟨s, hs⟩ : Fin k) hjlt]
    have hjnlt : ¬ (⟨s, hs⟩ : Fin k).val < s := Nat.lt_irrefl s
    rw [gapH120 b k hk s ii (⟨s, hs⟩ : Fin k) hjnlt]
    have hsn : s < n := Nat.lt_of_lt_of_le hs hk
    have hslift : GramSchmidt.liftFinLE (⟨s, hs⟩ : Fin k) hk = ⟨s, hsn⟩ := rfl
    rw [hslift]
    rw [gapH20 b s hsn, dot_add_right_rat]
    rw [gapH18 (coeffs := coeffs b) (basisM := basis b)
      (i := s) (hi := hsn)]
    have hfold_match :
        (List.finRange s).foldl
          (fun (acc : Rat) (jp : Fin s) =>
            acc +
              GramSchmidt.entry (coeffs b) ⟨s, hsn⟩
                  ⟨jp.val, Nat.lt_trans jp.isLt hsn⟩ *
                (castIntRow b (GramSchmidt.liftFinLE ii hk)).dotProduct
                  ((basis b).row ⟨jp.val, Nat.lt_trans jp.isLt hsn⟩)) 0 =
        - ((progressMatrixSources k s hs).foldl
          (fun acc src =>
            acc + progressMatrixCoeff b k hk s hs src *
              (progressMatrix b k hk s)[ii][src]) 0) := by
      unfold progressMatrixSources progressMatrixCoeff
      have hneg_foldl :
          - ((List.finRange s).map fun p =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)).foldl
            (fun acc src =>
              acc + (-GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩) *
                (progressMatrix b k hk s)[ii][src]) 0 =
            ((List.finRange s).map fun p =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)).foldl
            (fun acc src =>
              acc + GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩ *
                (progressMatrix b k hk s)[ii][src]) 0 := by
        generalize hmap : (List.finRange s).map (fun p : Fin s =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)) = lst
        clear hmap
        induction lst with
        | nil => simp
        | cons x xs ih =>
            simp only [List.foldl_cons]
            rw [gapH157 xs _
              ((0 : Rat) + (-GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨x.val, Nat.lt_of_lt_of_le x.isLt hk⟩) *
                (progressMatrix b k hk s)[ii][x])]
            rw [gapH157 xs _
              ((0 : Rat) + GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨x.val, Nat.lt_of_lt_of_le x.isLt hk⟩ *
                (progressMatrix b k hk s)[ii][x])]
            grind
      rw [hneg_foldl]
      rw [List.foldl_map]
      apply gapH30
      intro p _hp
      have hp_lt : p.val < s := p.isLt
      let pp : Fin k := ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩
      have hpp_lt_s : pp.val < s := hp_lt
      rw [gapH74 b k hk s ii pp hpp_lt_s]
      rfl
    grind
  ·
    rw [if_neg hjs]
    have hjs_ne : j ≠ s := fun h => hjs (Fin.ext h)
    by_cases hjlt : j < s
    ·
      have hjlt' : j < s + 1 := Nat.lt_succ_of_lt hjlt
      have hj_idx_lt_succ : (⟨j, hj⟩ : Fin k).val < s + 1 := hjlt'
      have hj_idx_lt : (⟨j, hj⟩ : Fin k).val < s := hjlt
      rw [gapH74 b k hk (s + 1) ii (⟨j, hj⟩ : Fin k) hj_idx_lt_succ,
        gapH74 b k hk s ii (⟨j, hj⟩ : Fin k) hj_idx_lt]
    ·
      have hjge : j ≥ s := Nat.le_of_not_lt hjlt
      have hjgt : j > s := Nat.lt_of_le_of_ne hjge fun h => hjs_ne h.symm
      have hj_idx_nlt_succ : ¬ (⟨j, hj⟩ : Fin k).val < s + 1 := by
        change ¬ j < s + 1; omega
      have hj_idx_nlt : ¬ (⟨j, hj⟩ : Fin k).val < s := hjlt
      rw [gapH120 b k hk (s + 1) ii (⟨j, hj⟩ : Fin k) hj_idx_nlt_succ,
        gapH120 b k hk s ii (⟨j, hj⟩ : Fin k) hj_idx_nlt]
private theorem gapH345
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s < k) :
    Matrix.det (progressMatrix b k hk (s + 1)) =
      Matrix.det (progressMatrix b k hk s) := by
  rw [gapH225 b k hk s hs]
  apply Matrix.det_setCol_add_otherCols
  exact gapH280 k s hs
private theorem gapH80
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s ≤ k) :
    Matrix.det (progressMatrix b k hk s) = Matrix.det (progressMatrix b k hk 0) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have hslt : s < k := Nat.lt_of_succ_le hs
      have hsle : s ≤ k := Nat.le_of_lt hslt
      rw [gapH345 b k hk s hslt]
      exact ih hsle
private theorem gapH105
    (b : Matrix Int n m) (i j : Fin n) :
    (castIntRow b i).dotProduct (castIntRow b j) =
      (((b.row i).dotProduct (b.row j) : Int) : Rat) := by
  unfold Vector.dotProduct
  rw [gapH276 (xs := List.finRange m)
    (f := fun k : Fin m => (b.row i)[k] * (b.row j)[k]) (acc := 0)]
  rw [show ((0 : Int) : Rat) = (0 : Rat) from rfl]
  apply gapH30
  intro k _hk
  unfold castIntRow
  have hi_entry : (Vector.map (fun x : Int => (x : Rat)) (b.row i))[k] = ((b.row i)[k] : Rat) := by
    change (Vector.map (fun x : Int => (x : Rat)) (b.row i))[k.val] = ((b.row i)[k.val] : Rat)
    rw [Vector.getElem_map]
  have hj_entry : (Vector.map (fun x : Int => (x : Rat)) (b.row j))[k] = ((b.row j)[k] : Rat) := by
    change (Vector.map (fun x : Int => (x : Rat)) (b.row j))[k.val] = ((b.row j)[k.val] : Rat)
    rw [Vector.getElem_map]
  rw [hi_entry, hj_entry, Rat.intCast_mul]
private theorem gapH141
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i)
    (p : Fin (j + 1)) :
    (castIntDetMatrix
        (GramSchmidt.leadingGramMatrixInt b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hj hi))) *
        originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[p] =
        Vector.dotProduct
          (castIntRow b
            ⟨p.val, Nat.lt_of_lt_of_le p.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
          (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) := by
  have hsys :=
    gapH242
      (b := b) (i := i) (j := j) (hi := hi)
      (hj := Nat.lt_trans hj hi) p
  change
    (Matrix.mulVec
        (castIntDetMatrix
          (GramSchmidt.leadingGramMatrixInt b (j + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))
        (originalProjectionCoords b i j hi (Nat.lt_trans hj hi)))[p] =
      Vector.dotProduct
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi))
  rw [hsys]
  unfold Matrix.mulVec Matrix.row
  simp only [Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [Vector.dotProduct]
  change
    (List.finRange (j + 1)).foldl
      (fun acc q =>
        acc +
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1)
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))[p][q] *
            (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[q]) 0 =
    (List.finRange (j + 1)).foldl
      (fun acc q =>
        acc +
          (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[q] *
            Vector.dotProduct
              (castIntRow b
                ⟨p.val, Nat.lt_of_lt_of_le p.isLt
                  (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
              (castIntRow b
                ⟨q.val, Nat.lt_of_lt_of_le q.isLt
                  (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)) 0
  apply gapH30
  intro q _hq
  rw [gapH144]
  simp [GramSchmidt.leadingGramMatrixInt, gapH215, GramSchmidt.liftFinLE]
  rw [← gapH105 b
    (⟨p.val, Nat.lt_of_lt_of_le p.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)
    (⟨q.val, Nat.lt_of_lt_of_le q.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)]
  grind
private theorem gapH154 (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    progressMatrix b k hk 0 =
      castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk) := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin k := ⟨j, hj⟩
  simp only [Hex.Matrix.getElem_rows]
  change (progressMatrix b k hk 0)[ii][jj] =
    (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk))[ii][jj]
  have hjnlt : ¬ jj.val < 0 := Nat.not_lt_zero _
  rw [gapH120 b k hk 0 ii jj hjnlt, gapH144]
  rw [gapH105]
  simp [GramSchmidt.leadingGramMatrixInt, gapH215]
private theorem gapH29 (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = Matrix.det (progressMatrix b k hk 0) := by
  have hdet_int :
      Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) =
        Int.ofNat (gramDet b k hk) := by
    rw [gramDet, HexMatrixTheory.bareiss_eq_mathlib_det, ← HexMatrixTheory.det_eq]
    exact (Int.toNat_of_nonneg (leadingGramMatrixInt_det_nonneg b k hk)).symm
  have hstep1 : ((gramDet b k hk : Int) : Rat) =
      ((Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) : Int) : Rat) := by
    rw [hdet_int]
    rfl
  have hstep2 : ((Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) : Int) : Rat) =
      Matrix.det (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk)) :=
    gapH452 (GramSchmidt.leadingGramMatrixInt b k hk)
  have hstep3 :
      Matrix.det (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk)) =
        Matrix.det (progressMatrix b k hk 0) := by
    rw [gapH154]
  have hcast_chain : ((gramDet b k hk : Nat) : Rat) =
      ((gramDet b k hk : Int) : Rat) := by
    push_cast; rfl
  rw [hcast_chain, hstep1, hstep2, hstep3]
theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  rw [gapH29 b k hk,
    ← gapH80 b k hk k (Nat.le_refl k), gapH59]
  exact (fun _ : independent b => gapH77 b k hk) hli
theorem gramSchmidtNormProduct_succ (b : Matrix Int n m)
    (k : Nat) (hk : k + 1 ≤ n) :
    gramSchmidtNormProduct b (k + 1) hk =
      gramSchmidtNormProduct b k (Nat.le_of_succ_le hk) *
        ((basis b).row ⟨k, Nat.lt_of_succ_le hk⟩).normSq := by
  unfold gramSchmidtNormProduct
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl,
    List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl
theorem basis_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    ((basis b).row ⟨k, hk⟩).normSq =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  have hk_le : k ≤ n := Nat.le_of_lt hk
  have hden_pos : 0 < (gramDet b k hk_le : Rat) := by
    rw [Rat.natCast_pos]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; rw [gramDet_zero]; decide
    · exact gramDet_pos b hli k hk_le hkpos
  have hprod_ne : gramSchmidtNormProduct b k hk_le ≠ 0 := by
    rw [← gramDet_eq_prod_normSq b hli k hk_le]
    exact Rat.ne_of_gt hden_pos
  rw [gramDet_eq_prod_normSq b hli (k + 1) (Nat.succ_le_of_lt hk),
    gramDet_eq_prod_normSq b hli k hk_le, gramSchmidtNormProduct_succ b k (Nat.succ_le_of_lt hk),
    Rat.mul_comm]
  exact (Rat.mul_div_cancel hprod_ne).symm
private theorem gapH41
    (b : Matrix Int n m) (p r : Nat) (hp : p < n) (hr : r < n) (hpr : p < r) :
    (castIntRow b ⟨p, hp⟩).dotProduct ((basis b).row ⟨r, hr⟩) = 0 := by
  rw [dot_comm_rat, gapH20 b p hp, dot_add_right_rat]
  have hbasis : ((basis b).row ⟨r, hr⟩).dotProduct ((basis b).row ⟨p, hp⟩) = 0 :=
    basis_orthogonal b r p hr hp (Nat.ne_of_gt hpr)
  have hprefix : ((basis b).row ⟨r, hr⟩).dotProduct
      (GramSchmidt.prefixCombination (coeffs b) (basis b) p hp) = 0 := by
    apply gapH9
      (coeffs := coeffs b) (basisM := basis b) (i := p) (hi := hp)
      (u := (basis b).row ⟨r, hr⟩)
    intro p'
    have hp'_lt_p : p'.val < p := p'.isLt
    have hp'_lt_r : p'.val < r := Nat.lt_trans hp'_lt_p hpr
    have hp'_lt_n : p'.val < n := Nat.lt_trans hp'_lt_p hp
    exact basis_orthogonal b r p'.val hr hp'_lt_n (Nat.ne_of_gt hp'_lt_r)
  rw [hbasis, hprefix]
  grind
private theorem gapH212
    {n : Nat} (body : ∀ (k : Nat), k < n → Rat) (acc : Rat) (k₀ : Nat)
    (h_zero : ∀ r : Nat, k₀ ≤ r → (hrn : r < n) → body r hrn = 0) :
    ∀ (m : Nat) (hk : m ≤ n) (hkk : k₀ ≤ m),
      (List.finRange m).foldl
          (fun (acc' : Rat) (r : Fin m) =>
            acc' + body r.val (Nat.lt_of_lt_of_le r.isLt hk)) acc =
        (List.finRange k₀).foldl
          (fun (acc' : Rat) (q : Fin k₀) =>
            acc' + body q.val (Nat.lt_of_lt_of_le q.isLt (Nat.le_trans hkk hk))) acc := by
  intro m
  induction m with
  | zero =>
      intro _ hkk
      have hk₀ : k₀ = 0 := Nat.eq_zero_of_le_zero hkk
      subst hk₀
      rfl
  | succ m ih =>
      intro hk hkk
      rcases Nat.lt_or_ge m k₀ with hmk | hkm
      · have hk_eq : k₀ = m + 1 := Nat.le_antisymm hkk (Nat.succ_le_of_lt hmk)
        subst hk_eq
        rfl
      · have hk' : m ≤ n := Nat.le_of_succ_le hk
        have h_last_lt : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk
        have h_last_zero : body m h_last_lt = 0 := h_zero m hkm h_last_lt
        rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
        simp only [List.foldl_cons, List.foldl_nil]
        have h_last :
            body (Fin.last m).val
                (Nat.lt_of_lt_of_le (Fin.last m).isLt hk) = 0 :=
          h_last_zero
        rw [h_last, Rat.add_zero]
        exact ih hk' hkm
private theorem gapH277
    (b : Matrix Int n m) (i j p : Nat) (hi : i < n) (hj : j < i)
    (hp_le_j : p ≤ j) (hp : p < n) :
    (castIntRow b ⟨p, hp⟩).dotProduct (castIntRow b ⟨i, hi⟩) =
      (castIntRow b ⟨p, hp⟩).dotProduct
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) := by
  obtain ⟨d, rfl⟩ : ∃ d, i = (j + 1) + d := ⟨i - (j + 1), by omega⟩
  have hkdn : (j + 1) + d ≤ n := Nat.le_of_lt hi
  rw [gapH20 b ((j + 1) + d) hi, dot_add_right_rat]
  rw [gapH41 b p ((j + 1) + d) hp hi
    (Nat.lt_of_le_of_lt hp_le_j hj)]
  rw [Rat.zero_add]
  rw [gapH18 (coeffs := coeffs b) (basisM := basis b)
    (i := (j + 1) + d) (hi := hi) (u := castIntRow b ⟨p, hp⟩)]
  unfold basisPrefixProjection
  rw [gapH139]
  let body : ∀ (k : Nat), k < n → Rat := fun k hk =>
    GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨k, hk⟩ *
      (castIntRow b ⟨p, hp⟩).dotProduct ((basis b).row ⟨k, hk⟩)
  have hRHS :
      (List.finRange (j + 1)).foldl
          (fun (acc' : Rat) (q : Fin (j + 1)) =>
            acc' +
              (projectionCoeffPrefix b ((j + 1) + d) j hi
                (Nat.lt_trans hj hi))[q] *
              (castIntRow b ⟨p, hp⟩).dotProduct
                ((GramSchmidt.prefixRows (basis b) j (Nat.lt_trans hj hi)).row q)) 0 =
        (List.finRange (j + 1)).foldl
          (fun (acc' : Rat) (q : Fin (j + 1)) =>
            acc' + body q.val (Nat.lt_of_lt_of_le q.isLt
              (Nat.le_trans (Nat.le_add_right (j + 1) d) hkdn))) 0 := by
    apply gapH30
    intro q _hq
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.le_trans (Nat.le_add_right (j + 1) d) hkdn)
    have hcoeff :
        (projectionCoeffPrefix b ((j + 1) + d) j hi (Nat.lt_trans hj hi))[q] =
          GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨q.val, hq_lt_n⟩ := by
      simp [projectionCoeffPrefix, Vector.getElem_ofFn]
    have hrow :
        (GramSchmidt.prefixRows (basis b) j (Nat.lt_trans hj hi)).row q =
          (basis b).row ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn]
    rw [hcoeff, hrow]
  rw [hRHS]
  exact gapH212 body 0 (j + 1)
    (by
      intro r hjr hrn
      show GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨r, hrn⟩ *
          (castIntRow b ⟨p, hp⟩).dotProduct ((basis b).row ⟨r, hrn⟩) = 0
      have hpr : p < r := Nat.lt_of_le_of_lt hp_le_j (Nat.lt_of_succ_le hjr)
      rw [gapH41 b p r hp hrn hpr]
      grind)
    ((j + 1) + d) hkdn (Nat.le_add_right (j + 1) d)
private theorem gapH60
    (k : Nat) (f : Fin (k + 1) → Rat)
    (h_zero : ∀ q : Fin (k + 1), q.val < k → f q = 0) :
    (List.finRange (k + 1)).foldl
        (fun (acc : Rat) (q : Fin (k + 1)) => acc + f q) 0 =
      f (Fin.last k) := by
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hfold_zero :
      (List.finRange k).foldl
          (fun (acc : Rat) (q : Fin k) => acc + f (Fin.castSucc q)) 0 = 0 := by
    have hgen : ∀ (xs : List (Fin k)) (acc : Rat),
        xs.foldl (fun acc' q => acc' + f (Fin.castSucc q)) acc = acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons q xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have hq : f (Fin.castSucc q) = 0 := h_zero (Fin.castSucc q) q.isLt
          rw [hq, Rat.add_zero]
          exact ih acc
    exact hgen (List.finRange k) 0
  rw [hfold_zero, Rat.zero_add]
private theorem gapH76
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((basis b).row ⟨j, Nat.lt_trans hj hi⟩).dotProduct
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ *
        ((basis b).row ⟨j, Nat.lt_trans hj hi⟩).normSq := by
  have hjlt : j < n := Nat.lt_trans hj hi
  unfold basisPrefixProjection
  rw [gapH139]
  rw [gapH60 j _ ?_]
  ·
    have hrow :
        (GramSchmidt.prefixRows (basis b) j hjlt).row (Fin.last j) =
          (basis b).row ⟨j, hjlt⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn, Fin.last]
    have hcoeff :
        (projectionCoeffPrefix b i j hi hjlt)[Fin.last j] =
          GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      simp [projectionCoeffPrefix, Vector.getElem_ofFn, Fin.last]
    rw [hcoeff, hrow]
    rfl
  ·
    intro q hqval
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hjlt)
    have hrow :
        (GramSchmidt.prefixRows (basis b) j hjlt).row q =
          (basis b).row ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn]
    rw [hrow, basis_orthogonal b j q.val hjlt hq_lt_n (Nat.ne_of_gt hqval)]
    grind
private theorem gapH48
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((basis b).row ⟨j, Nat.lt_trans hj hi⟩).dotProduct
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[Fin.last j] *
        ((basis b).row ⟨j, Nat.lt_trans hj hi⟩).normSq := by
  have hjlt : j < n := Nat.lt_trans hj hi
  rw [← gapH145 b i j hi hjlt, gapH139,
    gapH60 j _ ?_]
  ·
    have hrow :
        (GramSchmidt.prefixRows (castIntMatrixRat b) j hjlt).row (Fin.last j) =
          castIntRow b ⟨j, hjlt⟩ := by
      rw [gapH364, gapH213]
      rfl
    rw [hrow]
    rw [gapH20 b j hjlt, dot_add_right_rat]
    have hbasis_self :
        ((basis b).row ⟨j, hjlt⟩).dotProduct ((basis b).row ⟨j, hjlt⟩) =
          ((basis b).row ⟨j, hjlt⟩).normSq := rfl
    rw [hbasis_self]
    have hprefix :
        ((basis b).row ⟨j, hjlt⟩).dotProduct
            (GramSchmidt.prefixCombination (coeffs b) (basis b) j hjlt) = 0 := by
      apply gapH9
        (coeffs := coeffs b) (basisM := basis b) (i := j) (hi := hjlt)
        (u := (basis b).row ⟨j, hjlt⟩)
      intro r
      have hr_lt_j : r.val < j := r.isLt
      have hr_lt_n : r.val < n := Nat.lt_trans hr_lt_j hjlt
      exact basis_orthogonal b j r.val hjlt hr_lt_n (Nat.ne_of_gt hr_lt_j)
    rw [hprefix, Rat.add_zero]
  ·
    intro q hqval
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hjlt)
    have hrow :
        (GramSchmidt.prefixRows (castIntMatrixRat b) j hjlt).row q =
          castIntRow b ⟨q.val, hq_lt_n⟩ := by
      rw [gapH364, gapH213]
    rw [hrow, dot_comm_rat, gapH41 b q.val j hq_lt_n hjlt hqval]
    grind
theorem gramDet_succ_rat
    (b : Matrix Int n m) (j : Nat) (hjsuc : j + 1 ≤ n) :
    (gramDet b (j + 1) hjsuc : Rat) =
      gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
        ((basis b).row ⟨j, Nat.lt_of_succ_le hjsuc⟩).normSq := by
  have hgd_eq_gsnp :
      (gramDet b (j + 1) hjsuc : Rat) = gramSchmidtNormProduct b (j + 1) hjsuc := by
    rw [gapH29,
      ← gapH80 b (j + 1) hjsuc (j + 1) (Nat.le_refl _),
      gapH59]
    exact gapH77 b (j + 1) hjsuc
  rw [hgd_eq_gsnp]
  exact gramSchmidtNormProduct_succ b j hjsuc
end Int
end GramSchmidt
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
namespace Int
private theorem gapH45
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((Matrix.det
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) :
          Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  have hjlt : j < n := Nat.lt_trans hj hi
  have hjsuc : j + 1 ≤ n := Nat.succ_le_of_lt hjlt
  rw [gapH452]
  have hM_colReplace :
      castIntDetMatrix
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj) =
        Matrix.setCol
          (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
          (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
          (fun p : Fin (j + 1) =>
            Vector.dotProduct
              (castIntRow b ⟨p.val, Nat.lt_of_lt_of_le p.isLt hjsuc⟩)
              (castIntRow b ⟨i, hi⟩)) := by
    apply Hex.Matrix.ext_getElem
    intro pp cc
    change
      (castIntDetMatrix
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj))[pp][cc] =
        (Matrix.setCol _ _ _)[pp][cc]
    rw [Matrix.getElem_setCol, gapH144]
    by_cases hc_eq : cc = (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
    · rw [if_pos hc_eq]
      have hc_val : cc.val = j := congrArg Fin.val hc_eq
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Vector.dotProduct
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨i, hi⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, gapH215,
          GramSchmidt.liftFinLE, hc_val]
      rw [hsc, ← gapH105]
    · rw [if_neg hc_eq, gapH144]
      have hc_ne : cc.val ≠ j := fun h => hc_eq (Fin.ext h)
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Vector.dotProduct
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, gapH215,
          GramSchmidt.liftFinLE, hc_ne]
      have hG :
          (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc)[pp][cc] =
            Vector.dotProduct
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.leadingGramMatrixInt, gapH215,
          GramSchmidt.liftFinLE]
      rw [hsc, hG]
  rw [hM_colReplace]
  have hcol_lin_comb :
      (fun p : Fin (j + 1) =>
        Vector.dotProduct
          (castIntRow b ⟨p.val, Nat.lt_of_lt_of_le p.isLt hjsuc⟩)
          (castIntRow b ⟨i, hi⟩)) =
      (fun p : Fin (j + 1) =>
        (List.finRange (j + 1)).foldl
          (fun (acc : Rat) (q : Fin (j + 1)) =>
            acc + (originalProjectionCoords b i j hi hjlt)[q] *
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p][q]) 0) := by
    funext p
    rw [gapH277 b i j p.val hi hj
      (Nat.le_of_lt_succ p.isLt) (Nat.lt_of_lt_of_le p.isLt hjsuc)]
    rw [← gapH141 b i j hi hj p]
    change
      (Matrix.mulVec
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
          (originalProjectionCoords b i j hi hjlt))[p] = _
    unfold Matrix.mulVec Matrix.row
    simp only [Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
    unfold Vector.dotProduct
    apply gapH30
    intro q _hq
    grind
  rw [hcol_lin_comb]
  rw [Matrix.det_setCol_sum_finRange]
  rw [gapH60 j _ ?_]
  ·
    have hlast_self :
        Matrix.setCol
            (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
            (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
            (fun p : Fin (j + 1) =>
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p][Fin.last j]) =
          castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc) :=
      Matrix.setCol_self _ _
    rw [hlast_self]
    have hdetG :
        Matrix.det
            (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc)) =
          (gramDet b (j + 1) hjsuc : Rat) := by
      rw [← gapH452]
      have hdet_int :
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc) =
            Int.ofNat (gramDet b (j + 1) hjsuc) := by
        rw [gramDet, HexMatrixTheory.bareiss_eq_mathlib_det, ← HexMatrixTheory.det_eq]
        exact (Int.toNat_of_nonneg
          (leadingGramMatrixInt_det_nonneg b (j + 1) hjsuc)).symm
      rw [hdet_int]
      rfl
    rw [hdetG]
    have hcancel_normSq :
        ((basis b).row ⟨j, hjlt⟩).normSq *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
          ((basis b).row ⟨j, hjlt⟩).normSq *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      have hH2 := gapH76 b i j hi hj
      have hH3 := gapH48 b i j hi hj
      have heq := hH3.symm.trans hH2
      grind
    have hgd_succ := gramDet_succ_rat b j hjsuc
    rw [hgd_succ]
    have hgnp_ne_or_zero :
        gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              ((basis b).row ⟨j, hjlt⟩).normSq *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              ((basis b).row ⟨j, hjlt⟩).normSq *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      have h1 :
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              ((basis b).row ⟨j, hjlt⟩).normSq *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
            gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              (((basis b).row ⟨j, hjlt⟩).normSq *
                (originalProjectionCoords b i j hi hjlt)[Fin.last j]) := by
        grind
      have h2 :
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              ((basis b).row ⟨j, hjlt⟩).normSq *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ =
            gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              (((basis b).row ⟨j, hjlt⟩).normSq *
                GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩) := by
        grind
      rw [h1, h2, hcancel_normSq]
    rw [Rat.mul_comm (originalProjectionCoords b i j hi hjlt)[Fin.last j] _]
    exact hgnp_ne_or_zero
  ·
    intro q hqval
    have hq_ne :
        q ≠ (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) := by
      intro h
      exact Nat.ne_of_lt hqval (congrArg Fin.val h)
    rw [Matrix.det_setCol_existing_col_eq_zero _ _ _ hq_ne]
    grind
theorem scaledCoeffMatrix_det_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) (s : Nat)
    (h_sing : (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) = 0 := by
  have hsj : s < j.val := by
    have h := noPivotLoop_singularStep_lt j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
    change s < 0 + j.val at h
    omega
  have hjn : j.val < n := Nat.lt_trans hji i.isLt
  have hsucc : j.val + 1 ≤ n := Nat.succ_le_of_lt hjn
  have hjle : j.val ≤ n := Nat.le_of_lt hjn
  have h_init :
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)).singularStep = none := rfl
  have h_full_sing :
      (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).singularStep = some s := by
    rcases noPivotLoop_singular_inv j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_init
      with h_none | ⟨k, hsk, hstk, hpk, hk⟩
    · rw [h_none] at h_sing; nomatch h_sing
    ·
      have hks : k.val = s := by
        rw [hsk] at h_sing
        exact Option.some.inj h_sing
      have h_add : Matrix.noPivotLoop (j.val + (n - j.val))
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
        Matrix.noPivotLoop (n - j.val)
          (Matrix.noPivotLoop j.val
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))) :=
        Matrix.noPivotLoop_add j.val (n - j.val) _
      have hn_eq : j.val + (n - j.val) = n := Nat.add_sub_cancel' hjle
      have hh520 : (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
        rw [hstk]; exact hk
      have h_pivot_zero :
          (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨(Matrix.noPivotLoop j.val
                  (Matrix.noPivotInitialState
                    (Matrix.gramMatrix b))).step,
                Nat.lt_of_succ_lt hh520⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop j.val
                  (Matrix.noPivotInitialState
                    (Matrix.gramMatrix b))).step,
                Nat.lt_of_succ_lt hh520⟩ : Fin n)] = 0 := by
        have h_fin :
            (⟨(Matrix.noPivotLoop j.val
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step,
              Nat.lt_of_succ_lt hh520⟩ : Fin n) = k :=
          Fin.ext hstk
        simp only [h_fin]
        exact hpk
      have h_sing_step :
          (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep =
            some (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step := by
        rw [hsk, hstk]
      have h_fixed :
          Matrix.noPivotLoop (n - j.val)
            (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))) =
            Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) :=
        Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) (n - j.val) _
          hh520 h_pivot_zero h_sing_step
      have hh503 :
          Matrix.noPivotLoop n
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          Matrix.noPivotLoop j.val
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
        calc Matrix.noPivotLoop n
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))
            = Matrix.noPivotLoop (j.val + (n - j.val))
                (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
                  rw [hn_eq]
          _ = Matrix.noPivotLoop (n - j.val)
                (Matrix.noPivotLoop j.val
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))) := h_add
          _ = Matrix.noPivotLoop j.val
                (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := h_fixed
      show (Matrix.finish (Matrix.noPivotLoop n
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)))).singularStep = some s
      change (Matrix.noPivotLoop n
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s
      rw [hh503, hsk, hks]
  have h_gd_zero : gramDet b (j.val + 1) hsucc = 0 := by
    have h_vec_gd :=
      gramDetVecEntry_eq_gramDet (b := b) (StepWitness.ofGram b) (j.val + 1) hsucc
    have h_vec_zero :=
      gramDetVecEntry_noPivot_eq_zero_of_singularStep_lt b s j.val hjn h_full_sing
        (by omega)
    rw [← h_vec_gd, h_vec_zero]
  have h_cramer :=
    gapH45 (b := b) i.val j.val i.isLt hji
  rw [h_gd_zero] at h_cramer
  simp at h_cramer
  exact_mod_cast h_cramer
theorem scaledCoeffs_lower_eq_det_scaledCoeffMatrix
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      ((Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) : Int) : Rat) := by
  have hjn : j.val < n := Nat.lt_trans hji i.isLt
  cases h_sing : (Matrix.noPivotLoop j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
  | none =>
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j =
          Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
        rw [scaledCoeffs_lower_eq_noPivotLoop_scaledCoeffMatrix b (StepWitness.ofGram b)
          i j hji h_sing]
        have h_sync :=
          noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val hjn
            ⟨j.val, hjn⟩ i (Nat.le_refl j.val) (Nat.le_of_lt hji)
        have h_bm_nonsing :
            (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState
                (Matrix.borderedMinor (Matrix.gramMatrix b) j.val hjn
                  ⟨j.val, hjn⟩ i))).singularStep = none := by
          rw [← h_sync.2]; exact h_sing
        have h_sc_nonsing :
            (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState
                (GramSchmidt.scaledCoeffMatrix b i j hji))).singularStep = none := by
          rw [scaledCoeffMatrix_eq_borderedMinor]; exact h_bm_nonsing
        exact (Matrix.bareiss_eq_noPivotLoop_last_of_no_singular
          (GramSchmidt.scaledCoeffMatrix b i j hji) h_sc_nonsing).symm
      rw [h_lhs]
      exact_mod_cast (HexMatrixTheory.bareiss_eq_mathlib_det
          (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
        (HexMatrixTheory.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm
  | some s =>
      have hsj : s < j.val := by
        have h := noPivotLoop_singularStep_lt j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
        change s < 0 + j.val at h
        omega
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j = 0 := by
        rw [scaledCoeffs_entry_eq_getArrayEntry]
        exact getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
          b (StepWitness.ofGram b) i.val j.val i.isLt (Nat.le_of_lt hji) s hsj h_sing
      have h_det : Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) = 0 :=
        scaledCoeffMatrix_det_eq_zero_of_singularStep_lt b i j hji s h_sing
      rw [h_lhs, h_det]
theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    ((GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  rw [scaledCoeffs_lower_eq_det_scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj]
  exact gapH45 b i j hi hj
end Int
end GramSchmidt
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
namespace Int
private theorem gapH284 {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega
theorem dot_add_left_rat {m' : Nat} (u v w : Vector Rat m') :
    (u + v).dotProduct w = u.dotProduct w + v.dotProduct w := by
  rw [dot_comm_rat (u := u + v) (v := w), dot_add_right_rat (u := w) (v := u) (w := v),
    dot_comm_rat (u := w) (v := u), dot_comm_rat (u := w) (v := v)]
theorem dot_smul_left_rat {m' : Nat} (s : Rat) (u v : Vector Rat m') :
    (s • u).dotProduct v = s * u.dotProduct v := by
  rw [dot_comm_rat (u := s • u) (v := v), dot_smul_right_rat (s := s) (u := v) (v := u),
    dot_comm_rat (u := v) (v := u)]
theorem normSq_add_smul_orthogonal_rat {m' : Nat}
    (curr prev : Vector Rat m') (μ : Rat)
    (horth : curr.dotProduct prev = 0) :
    (curr + μ • prev).normSq =
      curr.normSq + μ ^ 2 * prev.normSq := by
  show (curr + μ • prev).dotProduct (curr + μ • prev) =
    curr.dotProduct curr + μ ^ 2 * prev.dotProduct prev
  rw [dot_add_left_rat (u := curr) (v := μ • prev) (w := curr + μ • prev),
    dot_add_right_rat (u := curr) (v := curr) (w := μ • prev),
    dot_add_right_rat (u := μ • prev) (v := curr) (w := μ • prev),
    dot_smul_right_rat (s := μ) (u := curr) (v := prev),
    dot_smul_left_rat (s := μ) (u := prev) (v := curr),
    dot_smul_left_rat (s := μ) (u := prev) (v := μ • prev),
    dot_smul_right_rat (s := μ) (u := prev) (v := prev)]
  have horth_swap : prev.dotProduct curr = 0 := by
    rw [dot_comm_rat]; exact horth
  rw [horth, horth_swap]
  grind
theorem gramSchmidtNormProduct_rowSwap_below
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val) :
    gramSchmidtNormProduct (Matrix.rowSwap b km1 k) km1.val
        (Nat.le_of_lt km1.isLt) =
      gramSchmidtNormProduct b km1.val (Nat.le_of_lt km1.isLt) := by
  unfold gramSchmidtNormProduct
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  apply gapH165
  intro j _hj
  have hh540 : j.val < km1.val := j.isLt
  congr 1
  exact basis_rowSwap_of_before b km1 k
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt km1.isLt)⟩ hkm1k hh540
theorem gramDet_eq_prod_normSq_uncond (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  rw [gapH29 b k hk,
    ← gapH80 b k hk k (Nat.le_refl k), gapH59]
  exact gapH77 b k hk
theorem gramDet_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramDet b j₁ h₁ = gramDet b j₂ h₂ := by
  subst he
  rfl
theorem gramSchmidtNormProduct_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramSchmidtNormProduct b j₁ h₁ = gramSchmidtNormProduct b j₂ h₂ := by
  subst he
  rfl
theorem gramDet_rowSwap_adjacent_pivot_product
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) *
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
        B ^ 2 := by
  intro B
  have hkm1k : km1.val < k.val := by omega
  have hh542 : km1.val ≤ n := Nat.le_of_lt km1.isLt
  have hk_le_n : k.val ≤ n := Nat.le_of_lt k.isLt
  have hk1_le_n : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hh546 : km1.val + 1 ≤ n := Nat.succ_le_of_lt km1.isLt
  let μ : Rat := GramSchmidt.entry (coeffs b) k km1
  let prev : Vector Rat m := (basis b).row km1
  let curr : Vector Rat m := (basis b).row k
  let G : Rat := gramSchmidtNormProduct b km1.val hh542
  let Nkm1 : Rat := prev.normSq
  let Nk : Rat := curr.normSq
  have hh532 : (gramDet b km1.val hh542 : Rat) = G :=
    gramDet_eq_prod_normSq_uncond b km1.val hh542
  have hdk_rat : (gramDet b k.val hk_le_n : Rat) = G * Nkm1 := by
    have h_succ := gramDet_succ_rat b km1.val hh546
    have hgd_eq :
        gramDet b (km1.val + 1) hh546 = gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    rw [← hgd_eq, h_succ]
  have hh533 : (gramDet b (k.val + 1) hk1_le_n : Rat) = G * Nkm1 * Nk := by
    have h_succ := gramDet_succ_rat b k.val hk1_le_n
    have hh535 :
        gramSchmidtNormProduct b k.val hk_le_n =
          gramSchmidtNormProduct b (km1.val + 1) hh546 :=
      gramSchmidtNormProduct_subst_val b _ _ _ _ hkm1.symm
    rw [h_succ, hh535,
        gramSchmidtNormProduct_succ b km1.val hh546]
  have horth : curr.dotProduct prev = 0 :=
    basis_orthogonal b k.val km1.val k.isLt km1.isLt (by omega)
  have hh526 :
      (basis (Matrix.rowSwap b km1 k)).row km1 = curr + μ • prev :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  have hdprime_rat :
      (gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n : Rat) =
        G * (Nk + μ ^ 2 * Nkm1) := by
    have h_succ :=
      gramDet_succ_rat (Matrix.rowSwap b km1 k) km1.val hh546
    have hgd_eq :
        gramDet (Matrix.rowSwap b km1 k) (km1.val + 1) hh546 =
          gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n :=
      gramDet_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1
    rw [← hgd_eq, h_succ,
        gramSchmidtNormProduct_rowSwap_below b km1 k hkm1k]
    show G * ((basis (Matrix.rowSwap b km1 k)).row
        ⟨km1.val, km1.isLt⟩).normSq = G * (Nk + μ ^ 2 * Nkm1)
    have hbasis_row :
        (basis (Matrix.rowSwap b km1 k)).row ⟨km1.val, km1.isLt⟩ =
          curr + μ • prev := hh526
    rw [hbasis_row, normSq_add_smul_orthogonal_rat curr prev μ horth]
  have hB_rat : ((B : Int) : Rat) = G * Nkm1 * μ := by
    show ((GramSchmidt.entry (scaledCoeffs b) k km1 : Int) : Rat) =
        G * Nkm1 * μ
    rw [scaledCoeffs_eq b k.val km1.val k.isLt hkm1k]
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hkm1k k.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show (gramDet b (km1.val + 1) _ : Rat) *
        GramSchmidt.entry (coeffs b) ⟨k.val, k.isLt⟩
          ⟨km1.val, Nat.lt_trans hkm1k k.isLt⟩ = G * Nkm1 * μ
    rw [hgd_eq, hdk_rat]
  apply gapH284
  push_cast
  rw [hdprime_rat, hdk_rat, hh533, hh532, hB_rat]
  grind
theorem leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n)
    (hdet : 0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht)) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) := by
  rw [gramDet, HexMatrixTheory.bareiss_eq_mathlib_det, ← HexMatrixTheory.det_eq]
  exact (Int.toNat_of_nonneg hdet).symm
theorem leadingGramMatrixInt_det_eq_gramDet_int
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) :=
  leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg b t ht
    (leadingGramMatrixInt_det_nonneg b t ht)
end Int
end GramSchmidt
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
namespace Int
private theorem gapH16 (b : Matrix Int n m) (t : Nat)
    (ht : t ≤ n) (p q : Fin t) :
    (GramSchmidt.leadingGramMatrixInt b t ht)[p][q] =
      (b[GramSchmidt.liftFinLE p ht]).dotProduct (b[GramSchmidt.liftFinLE q ht]) := by
  show (GramSchmidt.leadingGramMatrixInt b t ht)[p][q] =
    (b.row (GramSchmidt.liftFinLE p ht)).dotProduct (b.row (GramSchmidt.liftFinLE q ht))
  rw [GramSchmidt.leadingGramMatrixInt, Matrix.getElem_ofFn]
private theorem gapH55 {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (hr : r.val ≠ dst.val) :
    (Matrix.rowAdd M src dst c)[r] = M[r] := by
  rw [Matrix.rowAdd_eq_set]
  exact Hex.Matrix.setRow_row_ne M dst r _ (fun heq => hr (congrArg Fin.val heq))
theorem leadingGramMatrixInt_rowAdd_outside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hkt : t ≤ k.val) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      GramSchmidt.leadingGramMatrixInt b t ht := by
  apply Hex.Matrix.ext_getElem
  intro p q
  have hp_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le p.isLt hkt)
  have hq_ne : (GramSchmidt.liftFinLE q ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le q.isLt hkt)
  have hp_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
      b[GramSchmidt.liftFinLE p ht] :=
    gapH55 b j k (GramSchmidt.liftFinLE p ht) c hp_ne
  have hq_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht] =
      b[GramSchmidt.liftFinLE q ht] :=
    gapH55 b j k (GramSchmidt.liftFinLE q ht) c hq_ne
  rw [gapH16, gapH16, hp_eq, hq_eq]
private theorem gapH149
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t)
    (p q : Fin t) :
    (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
      (Matrix.colAdd
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
            ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)[p][q] := by
  let jt : Fin t := ⟨j.val, Nat.lt_trans hjk hkt⟩
  let kt : Fin t := ⟨k.val, hkt⟩
  let u : Fin t → Vector ℤ m := fun r => b.row (GramSchmidt.liftFinLE r ht)
  let v : Fin t → Vector ℤ m := fun r => (b.rowAdd j k c).row (GramSchmidt.liftFinLE r ht)
  let G := GramSchmidt.leadingGramMatrixInt b t ht
  have hL : (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
      (v p).dotProduct (v q) := by
    change (Matrix.ofFn (fun r s : Fin t => (v r).dotProduct (v s)))[p][q] = _
    exact Matrix.getElem_ofFn _ _ _
  rw [hL]
  change (v p).dotProduct (v q) = ((G.rowAdd jt kt c).colAdd jt kt c)[p][q]
  have hG (r s : Fin t) : G[r][s] = (u r).dotProduct (u s) := by
    change (Matrix.ofFn (fun r s : Fin t => (u r).dotProduct (u s)))[r][s] = _
    exact Matrix.getElem_ofFn _ _ _
  have hjkt : jt ≠ kt := fun h => Nat.ne_of_lt hjk (congrArg (fun x : Fin t => x.val) h)
  have he (r : Fin t) (hr : r ≠ kt) : v r = u r := by
    apply Matrix.row_rowAdd_of_ne
    intro h
    apply hr
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) h
  have hv : v kt = Vector.ofFn (fun i : Fin m => (u kt)[i] + c * (u jt)[i]) := by
    change (b.rowAdd j k c).row k = Vector.ofFn (fun i : Fin m => b[k][i] + c * b[j][i])
    exact Matrix.row_rowAdd_dst _ _ _ _
  have hLeft (w : Vector ℤ m) : (v kt).dotProduct w = (u kt).dotProduct w + c * (u jt).dotProduct w := by
    rw [hv, HexMatrixTheory.dotProduct_eq, HexMatrixTheory.dotProduct_eq, HexMatrixTheory.dotProduct_eq]
    simp only [dotProduct, HexMatrixTheory.vectorEquiv_apply, Fin.getElem_fin, Vector.getElem_ofFn, add_mul, mul_assoc,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have hRight (w : Vector ℤ m) : w.dotProduct (v kt) = w.dotProduct (u kt) + c * w.dotProduct (u jt) := by
    rw [hv, HexMatrixTheory.dotProduct_eq, HexMatrixTheory.dotProduct_eq, HexMatrixTheory.dotProduct_eq]
    simp only [dotProduct, HexMatrixTheory.vectorEquiv_apply, Fin.getElem_fin, Vector.getElem_ofFn, mul_add,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Matrix.getElem_colAdd]
  by_cases hq : q = kt
  · subst q
    rw [if_pos rfl, hRight, Matrix.getElem_rowAdd, Matrix.getElem_rowAdd]
    by_cases hp : p = kt
    · subst p
      rw [if_pos rfl, if_pos rfl, hLeft, hLeft]
      simp only [hG]
    · rw [if_neg hp, if_neg hp, he p hp]
      simp only [hG]
  · rw [if_neg hq, Matrix.getElem_rowAdd, he q hq]
    by_cases hp : p = kt
    · subst p
      rw [if_pos rfl, hLeft]
      simp only [hG]
    · rw [if_neg hp, he p hp, hG]
theorem leadingGramMatrixInt_rowAdd_inside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      Matrix.colAdd
        (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
        ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c := by
  apply Hex.Matrix.ext_getElem
  intro p q
  exact gapH149 b j k c t ht hjk hkt p q
theorem gramDet_rowAdd_earlier
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) :
    gramDet (Matrix.rowAdd b j k c) t ht = gramDet b t ht := by
  unfold gramDet
  congr 1
  by_cases hkt : k.val < t
  ·
    rw [leadingGramMatrixInt_rowAdd_inside b j k c t ht hjk hkt]
    have hh524 : ∀ (M : Hex.Matrix Int t t),
        Hex.Matrix.bareiss M = Hex.Matrix.det M := fun M =>
      (HexMatrixTheory.bareiss_eq_mathlib_det M).trans
        (HexMatrixTheory.det_eq M).symm
    rw [hh524, hh524]
    have hjt_ne_kt : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t) ≠ ⟨k.val, hkt⟩ := by
      intro h
      have hval : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t).val =
          (⟨k.val, hkt⟩ : Fin t).val :=
        congrArg Fin.val h
      exact Nat.ne_of_lt hjk hval
    rw [Matrix.det_colAdd _ _ _ _ hjt_ne_kt, Matrix.det_rowAdd _ _ _ _ hjt_ne_kt]
  ·
    have hkt' : t ≤ k.val := Nat.le_of_not_lt hkt
    rw [leadingGramMatrixInt_rowAdd_outside b j k c t ht hkt']
end Int
end GramSchmidt
end Hex
end
end
section
section
namespace HexMatrixTheory
universe u
variable {R : Type u} {n m : Nat}
theorem vectorEquiv_vecMul [CommRing R] (M : Hex.Matrix R n m) (c : Vector R n) :
    vectorEquiv (Hex.Matrix.vecMul c M) =
      Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c) := by
  funext j
  simp only [vectorEquiv_apply]
  unfold Hex.Matrix.vecMul
  change (Hex.Matrix.mulVec (Hex.Matrix.transpose M) c)[j.val] =
    (Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c)) j
  unfold Hex.Matrix.mulVec Hex.Matrix.row Vector.dotProduct Hex.Matrix.transpose
  rw [Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn j.isLt, foldl_finRange_eq_sum,
    Fintype.linearCombination_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [vectorEquiv_apply, matrixEquiv_apply, _root_.Matrix.row_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [← Hex.Matrix.getElem_eq_getRow, Hex.Matrix.getElem_ofFn,
    Hex.Matrix.getElem_pair_eq_nested]
end HexMatrixTheory
end
end
section
section
namespace HexLLLTheory
theorem LLLState.ofBasis_valid (b : Hex.Matrix Int n m) :
    (Hex.Internal.LLLState.ofBasis b).Valid := by
  let gs := Hex.GramSchmidt.Int.data b
  constructor
  · intro i j hi hj hji
    simp [Hex.Internal.LLLState.ofBasis,
      Hex.GramSchmidt.Int.scaledCoeffs]
  · intro i hi
    simpa [Hex.Internal.LLLState.ofBasis,
      Hex.GramSchmidt.Int.gramDetVec, gs] using
      Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b
        (Hex.GramSchmidt.Int.StepWitness.ofGram b) i (Nat.le_of_lt_succ hi)
theorem lllState_ν_eq_coeffs
    (s : Hex.Internal.LLLState n m) (hvalid : s.Valid)
    (i j : Nat) (hi : i < n) (hj : j < n) (hji : j < i) :
    (((s.ν.getRow ⟨i, hi⟩).get ⟨j, hj⟩ : Int) : Rat) =
      (s.d.get ⟨j + 1, Nat.succ_lt_succ hj⟩ : Rat) *
        (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨i, hi⟩).get ⟨j, hj⟩) := by
  have hν := hvalid.ν_eq i j hi hj hji
  have hd :
      s.d.get ⟨j + 1, Nat.succ_lt_succ hj⟩ =
        Hex.GramSchmidt.Int.gramDet s.b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hji hi)) :=
    hvalid.d_eq (j + 1) (Nat.succ_lt_succ hj)
  have hscaled :=
    Hex.GramSchmidt.Int.scaledCoeffs_eq s.b i j hi hji
  rw [hν, hd]
  exact hscaled
theorem lovasz_check_iff_isLLLReduced_pair
    (s : Hex.Internal.LLLState n m) (k : Nat) (hk : k < n) (hk0 : 0 < k)
    (hvalid : s.Valid) (hind : s.b.independent)
    {δ : Rat} (_hδ : (1 : Rat) / 4 < δ) (_hδ' : δ ≤ 1) :
    have hkm1lt : k - 1 < n :=
      Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk
    have hkm1ltN1 : k - 1 < n + 1 :=
      Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk)
    have hkltN1 : k < n + 1 := Nat.lt_succ_of_lt hk
    have hkSuccLt : k + 1 < n + 1 := Nat.succ_lt_succ hk
    Int.ofNat δ.den *
        (Int.ofNat (s.d.get ⟨k + 1, hkSuccLt⟩) *
            Int.ofNat (s.d.get ⟨k - 1, hkm1ltN1⟩) +
          ((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩) ^ 2) ≥
        δ.num * (Int.ofNat (s.d.get ⟨k, hkltN1⟩) ^ 2) ↔
      δ * Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b)
            ⟨k - 1, hkm1lt⟩ ≤
        Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b) ⟨k, hk⟩ +
          (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get
              ⟨k - 1, hkm1lt⟩) *
            (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get
              ⟨k - 1, hkm1lt⟩) *
            Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b)
              ⟨k - 1, hkm1lt⟩ := by
  intro hkm1lt hkm1ltN1 hkltN1 hkSuccLt
  have hdk_eq : s.d.get ⟨k, hkltN1⟩ =
      Hex.GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt_succ hkltN1) :=
    hvalid.d_eq k hkltN1
  have hh530 : s.d.get ⟨k - 1, hkm1ltN1⟩ =
      Hex.GramSchmidt.Int.gramDet s.b (k - 1) (Nat.le_of_lt_succ hkm1ltN1) :=
    hvalid.d_eq (k - 1) hkm1ltN1
  have hh529 : s.d.get ⟨k + 1, hkSuccLt⟩ =
      Hex.GramSchmidt.Int.gramDet s.b (k + 1) (Nat.le_of_lt_succ hkSuccLt) :=
    hvalid.d_eq (k + 1) hkSuccLt
  have hkm1ltK : k - 1 < k := Nat.sub_lt hk0 Nat.zero_lt_one
  have hsubAdd : k - 1 + 1 = k := Nat.sub_add_cancel hk0
  have hν :
      (((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int) : Rat) =
        (s.d.get ⟨k, hkltN1⟩ : Rat) *
          (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get
            ⟨k - 1, hkm1lt⟩) := by
    have h := lllState_ν_eq_coeffs s hvalid k (k - 1) hk hkm1lt hkm1ltK
    have hidx :
        (⟨k - 1 + 1, Nat.succ_lt_succ hkm1lt⟩ : Fin (n + 1)) =
          ⟨k, hkltN1⟩ :=
      Fin.ext hsubAdd
    rw [hidx] at h
    exact h
  set gd_k : Nat :=
    Hex.GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt_succ hkltN1) with hgd_k_def
  set gd_k1 : Nat :=
    Hex.GramSchmidt.Int.gramDet s.b (k + 1) (Nat.le_of_lt_succ hkSuccLt)
      with hgd_k1_def
  set gd_km1 : Nat :=
    Hex.GramSchmidt.Int.gramDet s.b (k - 1) (Nat.le_of_lt_succ hkm1ltN1)
      with hgd_km1_def
  set Nk : Rat :=
    Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b) ⟨k, hk⟩
      with hNk_def
  set Nkm1 : Rat :=
    Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b)
        ⟨k - 1, hkm1lt⟩ with hNkm1_def
  set μ : Rat :=
    ((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩
      with hμ_def
  have hgd_k_pos_nat : 0 < gd_k :=
    Hex.GramSchmidt.Int.gramDet_pos s.b hind k
      (Nat.le_of_lt_succ hkltN1) hk0
  have hgd_k1_pos_nat : 0 < gd_k1 :=
    Hex.GramSchmidt.Int.gramDet_pos s.b hind (k + 1)
      (Nat.le_of_lt_succ hkSuccLt) (Nat.succ_pos k)
  have hgd_km1_pos_nat : 0 < gd_km1 := by
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
    · show 0 < Hex.GramSchmidt.Int.gramDet s.b (k - 1) _
      rw [Hex.GramSchmidt.Int.gramDet_subst_val s.b (k - 1) 0
          (Nat.le_of_lt_succ hkm1ltN1) (Nat.zero_le n) h0,
        Hex.GramSchmidt.Int.gramDet_zero]
      exact Nat.zero_lt_one
    · exact Hex.GramSchmidt.Int.gramDet_pos s.b hind (k - 1)
        (Nat.le_of_lt_succ hkm1ltN1) hpos
  have hgd_k_pos : (0 : Rat) < (gd_k : Rat) := by exact_mod_cast hgd_k_pos_nat
  have hgd_k1_pos : (0 : Rat) < (gd_k1 : Rat) := by exact_mod_cast hgd_k1_pos_nat
  have hgd_km1_pos : (0 : Rat) < (gd_km1 : Rat) := by
    exact_mod_cast hgd_km1_pos_nat
  have hgd_k_ne : (gd_k : Rat) ≠ 0 := ne_of_gt hgd_k_pos
  have hgd_km1_ne : (gd_km1 : Rat) ≠ 0 := ne_of_gt hgd_km1_pos
  have hδden_pos : (0 : Rat) < (δ.den : Rat) := by
    exact_mod_cast δ.den_pos
  have hδden_ne : (δ.den : Rat) ≠ 0 := ne_of_gt hδden_pos
  have hNk_mul : (gd_k : Rat) * Nk = (gd_k1 : Rat) := by
    have hbn := Hex.GramSchmidt.Int.basis_normSq s.b hind k hk
    have hNk_val : Nk = (gd_k1 : Rat) / (gd_k : Rat) := by
      show ((Hex.GramSchmidt.Int.basis s.b).row ⟨k, hk⟩).normSq = _
      exact hbn
    rw [hNk_val, mul_div_cancel₀ _ hgd_k_ne]
  have hNkm1_mul : (gd_km1 : Rat) * Nkm1 = (gd_k : Rat) := by
    have hbn := Hex.GramSchmidt.Int.basis_normSq s.b hind (k - 1) hkm1lt
    have hNkm1_val :
        Nkm1 = (Hex.GramSchmidt.Int.gramDet s.b (k - 1 + 1)
            (Nat.succ_le_of_lt hkm1lt) : Rat) / (gd_km1 : Rat) := by
      show ((Hex.GramSchmidt.Int.basis s.b).row ⟨k - 1, hkm1lt⟩).normSq = _
      exact hbn
    have hgd_eq :
        Hex.GramSchmidt.Int.gramDet s.b (k - 1 + 1)
            (Nat.succ_le_of_lt hkm1lt) = gd_k :=
      Hex.GramSchmidt.Int.gramDet_subst_val s.b (k - 1 + 1) k
        (Nat.succ_le_of_lt hkm1lt) (Nat.le_of_lt_succ hkltN1) hsubAdd
    rw [hgd_eq] at hNkm1_val
    rw [hNkm1_val, mul_div_cancel₀ _ hgd_km1_ne]
  have hδmul : δ * (δ.den : Rat) = (δ.num : Rat) := Rat.mul_den_eq_num δ
  have hB_cast :
      (((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int) : Rat) =
        (gd_k : Rat) * μ := by
    rw [hν, hdk_eq]
  have hB_sq :
      ((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) ^ 2 : Rat) =
        (gd_k : Rat) ^ 2 * μ ^ 2 := by
    have hsq : (((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) : Rat)) ^ 2 =
        ((gd_k : Rat) * μ) ^ 2 := by rw [hB_cast]
    rw [show ((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) ^ 2 : Rat) =
          (((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) : Rat)) ^ 2 from by
        rfl, hsq]; ring
  have hcast_iff :
      (Int.ofNat δ.den *
          (Int.ofNat (s.d.get ⟨k + 1, hkSuccLt⟩) *
              Int.ofNat (s.d.get ⟨k - 1, hkm1ltN1⟩) +
            ((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩) ^ 2) ≥
        δ.num * (Int.ofNat (s.d.get ⟨k, hkltN1⟩) ^ 2)) ↔
      ((δ.den : Rat) *
          ((gd_k1 : Rat) * (gd_km1 : Rat) +
            (gd_k : Rat) ^ 2 * μ ^ 2) ≥
        (δ.num : Rat) * (gd_k : Rat) ^ 2) := by
    rw [ge_iff_le, ge_iff_le, ← @Int.cast_le ℚ, hdk_eq, hh530, hh529]
    push_cast
    rw [hB_sq]
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
  rw [hcast_iff]
  set P : Rat := (δ.den : Rat) * (gd_k : Rat) * (gd_km1 : Rat) with hP_def
  have hP_pos : 0 < P := by
    have : 0 < (δ.den : Rat) * (gd_k : Rat) := mul_pos hδden_pos hgd_k_pos
    exact mul_pos this hgd_km1_pos
  have hidentity :
      (δ.den : Rat) *
          ((gd_k1 : Rat) * (gd_km1 : Rat) + (gd_k : Rat) ^ 2 * μ ^ 2) -
        (δ.num : Rat) * (gd_k : Rat) ^ 2 =
      P * ((Nk + Nkm1 * μ * μ) - δ * Nkm1) := by
    have hμ_sq : μ ^ 2 = μ * μ := sq μ
    rw [hP_def, ← hNk_mul, ← hNkm1_mul, ← hδmul, hμ_sq]
    ring
  constructor
  · intro hint
    have hLHS_ge :
        0 ≤ (δ.den : Rat) *
              ((gd_k1 : Rat) * (gd_km1 : Rat) + (gd_k : Rat) ^ 2 * μ ^ 2) -
            (δ.num : Rat) * (gd_k : Rat) ^ 2 := by linarith
    rw [hidentity] at hLHS_ge
    have hdiff_nn :
        0 ≤ (Nk + Nkm1 * μ * μ) - δ * Nkm1 :=
      (mul_nonneg_iff_of_pos_left hP_pos).mp hLHS_ge
    linarith
  · intro hrat
    have hdiff_nn : 0 ≤ (Nk + Nkm1 * μ * μ) - δ * Nkm1 := by linarith
    have hLHS_ge :
        0 ≤ (δ.den : Rat) *
              ((gd_k1 : Rat) * (gd_km1 : Rat) + (gd_k : Rat) ^ 2 * μ ^ 2) -
            (δ.num : Rat) * (gd_k : Rat) ^ 2 := by
      rw [hidentity]
      exact mul_nonneg (le_of_lt hP_pos) hdiff_nn
    linarith
end HexLLLTheory
end
end
section
section
namespace Hex
namespace GramSchmidt.Int
theorem gramDet_sizeReduce (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val)
    (r : Int) (t : Nat) (ht : t ≤ n) :
    gramDet (sizeReduce b j k r) t ht = gramDet b t ht := by
  unfold sizeReduce
  exact gramDet_rowAdd_earlier b j k (-r) t ht hjk
private theorem gapH14 {n' m' : Nat}
    (b : Matrix Int n' m') (i j r : Fin n') (hri : r ≠ i) (hrj : r ≠ j) :
    (Matrix.rowSwap b i j)[r] = b[r] := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m' := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[r][c] = b[r][c]
  rw [Matrix.getElem_rowSwap]
  by_cases hrj' : r = j
  · exact absurd hrj' hrj
  · by_cases hri' : r = i
    · exact absurd hri' hri
    · simp [hri', hrj']
private theorem gapH181
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val)
    (t : Nat) (ht : t ≤ n) (htkm1 : t ≤ km1.val) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht =
      GramSchmidt.leadingGramMatrixInt b t ht := by
  rw [GramSchmidt.leadingGramMatrixInt_eq_principalSubmatrix_gram,
      GramSchmidt.leadingGramMatrixInt_eq_principalSubmatrix_gram]
  apply Hex.Matrix.ext
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  let pp : Fin t := ⟨p, hp⟩
  let qq : Fin t := ⟨q, hq⟩
  let pn : Fin n := ⟨p, Nat.lt_of_lt_of_le hp ht⟩
  let qn : Fin n := ⟨q, Nat.lt_of_lt_of_le hq ht⟩
  have hp_ne_km1 : pn ≠ km1 := by
    intro h
    have hv : p = km1.val := by simpa [pn] using congrArg Fin.val h
    omega
  have hp_ne_k : pn ≠ k := by
    intro h
    have hv : p = k.val := by simpa [pn] using congrArg Fin.val h
    omega
  have hq_ne_km1 : qn ≠ km1 := by
    intro h
    have hv : q = km1.val := by simpa [qn] using congrArg Fin.val h
    omega
  have hq_ne_k : qn ≠ k := by
    intro h
    have hv : q = k.val := by simpa [qn] using congrArg Fin.val h
    omega
  have hp_eq : (Matrix.rowSwap b km1 k)[pn] = b[pn] :=
    gapH14 b km1 k pn hp_ne_km1 hp_ne_k
  have hq_eq : (Matrix.rowSwap b km1 k)[qn] = b[qn] :=
    gapH14 b km1 k qn hq_ne_km1 hq_ne_k
  simp only [Hex.Matrix.getElem_rows]
  show (Matrix.principalSubmatrix (Matrix.gramMatrix (Matrix.rowSwap b km1 k)) t ht)[pp][qq] =
       (Matrix.principalSubmatrix (Matrix.gramMatrix b) t ht)[pp][qq]
  simp only [Matrix.getElem_principalSubmatrix]
  show (Matrix.gramMatrix (Matrix.rowSwap b km1 k))[pn][qn] =
       (Matrix.gramMatrix b)[pn][qn]
  have hentry_swap :
      (Matrix.gramMatrix (Matrix.rowSwap b km1 k))[pn][qn] =
        ((Matrix.rowSwap b km1 k)[pn]).dotProduct ((Matrix.rowSwap b km1 k)[qn]) := by
    rw [Matrix.getElem_gramMatrix]
    rfl
  have hentry_b :
      (Matrix.gramMatrix b)[pn][qn] =
        (b[pn]).dotProduct (b[qn]) := by
    rw [Matrix.getElem_gramMatrix]
    rfl
  rw [hentry_swap, hentry_b, hp_eq, hq_eq]
private theorem gapH200
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val)
    (t : Nat) (ht : t ≤ n) (hkt : k.val < t) :
    let km1' : Fin t := ⟨km1.val, Nat.lt_trans hkm1k hkt⟩
    let k' : Fin t := ⟨k.val, hkt⟩
    GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht =
      (Matrix.rowSwap
        ((Matrix.rowSwap (GramSchmidt.leadingGramMatrixInt b t ht) km1' k').transpose)
        km1' k').transpose := by
  intro km1' k'
  let swapIndex : Fin t → Fin t := fun p => if p = k' then km1' else if p = km1' then k' else p
  have hLift (p : Fin t) :
      (Matrix.rowSwap b km1 k)[GramSchmidt.liftFinLE p ht] = b[GramSchmidt.liftFinLE (swapIndex p) ht] := by
    ext j hj
    let col : Fin m := ⟨j, hj⟩
    change (Matrix.rowSwap b km1 k)[GramSchmidt.liftFinLE p ht][col] =
      b[GramSchmidt.liftFinLE (swapIndex p) ht][col]
    rw [Matrix.getElem_rowSwap]
    have hk' : GramSchmidt.liftFinLE p ht = k ↔ p = k' := by
      constructor
      · intro h; apply Fin.ext; exact congrArg (fun (r : Fin n) => r.val) h
      · intro h; apply Fin.ext; exact congrArg (fun (r : Fin t) => r.val) h
    have hkm1' : GramSchmidt.liftFinLE p ht = km1 ↔ p = km1' := by
      constructor
      · intro h; apply Fin.ext; exact congrArg (fun (r : Fin n) => r.val) h
      · intro h; apply Fin.ext; exact congrArg (fun (r : Fin t) => r.val) h
    have hpk : GramSchmidt.liftFinLE k' ht = k := Fin.ext rfl
    have hpp : GramSchmidt.liftFinLE km1' ht = km1 := Fin.ext rfl
    dsimp only [swapIndex]
    simp only [hk', hkm1']
    by_cases heK : p = k'
    · rw [if_pos heK, if_pos heK, hpp]
    · rw [if_neg heK, if_neg heK]
      by_cases heKm1 : p = km1'
      · rw [if_pos heKm1, if_pos heKm1, hpk]
      · rw [if_neg heKm1, if_neg heKm1]
  apply Hex.Matrix.ext_getElem
  intro p q
  let G := GramSchmidt.leadingGramMatrixInt b t ht
  have hentry (A : Matrix Int t t) (i j : Fin t) :
      (A.rowSwap km1' k')[i][j] = A[swapIndex i][j] := by
    rw [Matrix.getElem_rowSwap]
    unfold swapIndex
    by_cases hi : i = k'
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]
      by_cases hi' : i = km1'
      · rw [if_pos hi', if_pos hi']
      · rw [if_neg hi', if_neg hi']
  change (GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht)[p][q] =
    (((G.rowSwap km1' k').transpose).rowSwap km1' k').transpose[p][q]
  rw [Matrix.getElem_transpose, hentry, Matrix.getElem_transpose, hentry]
  change (GramSchmidt.leadingGramMatrixInt (Matrix.rowSwap b km1 k) t ht)[p][q] =
    (GramSchmidt.leadingGramMatrixInt b t ht)[swapIndex p][swapIndex q]
  rw [GramSchmidt.leadingGramMatrixInt, GramSchmidt.leadingGramMatrixInt,
    Matrix.getElem_ofFn, Matrix.getElem_ofFn]
  change ((Matrix.rowSwap b km1 k)[GramSchmidt.liftFinLE p ht]).dotProduct
      ((Matrix.rowSwap b km1 k)[GramSchmidt.liftFinLE q ht]) =
    (b[GramSchmidt.liftFinLE (swapIndex p) ht]).dotProduct
      (b[GramSchmidt.liftFinLE (swapIndex q) ht])
  rw [hLift, hLift]
private theorem gapH155
    {R : Type u} [Lean.Grind.CommRing R] {n' : Nat}
    (M : Matrix R n' n') (i j : Fin n') (h : i ≠ j) :
    Matrix.det
        ((Matrix.rowSwap ((Matrix.rowSwap M i j).transpose) i j).transpose) =
      Matrix.det M := by
  rw [Matrix.det_transpose, Matrix.det_rowSwap _ _ _ h,
      Matrix.det_transpose, Matrix.det_rowSwap _ _ _ h]
  grind
theorem gramDet_adjacentSwap_of_ne (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (t : Nat) (ht : t ≤ n) (htk : t ≠ k.val) :
    gramDet (adjacentSwap b k hk) t ht = gramDet b t ht := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1k : km1.val < k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  unfold adjacentSwap gramDet
  congr 1
  by_cases hkt : k.val < t
  · rw [gapH200 (b := b) (km1 := km1) (k := k) hkm1k t ht hkt]
    have hh524 : ∀ (M : Hex.Matrix Int t t),
        Hex.Matrix.bareiss M = Hex.Matrix.det M := fun M =>
      (HexMatrixTheory.bareiss_eq_mathlib_det M).trans
        (HexMatrixTheory.det_eq M).symm
    rw [hh524, hh524]
    apply gapH155
    intro h
    have : km1.val = k.val := by
      have := congrArg Fin.val h
      simpa using this
    omega
  · have htlt : t ≤ km1.val := by
      have ht_le : t ≤ k.val := Nat.le_of_not_lt hkt
      have htlt_k : t < k.val := Nat.lt_of_le_of_ne ht_le htk
      dsimp [km1, GramSchmidt.prevRow]
      omega
    rw [gapH181 (b := b) (km1 := km1) (k := k) hkm1k t ht htlt]
theorem gramDet_adjacentSwap_pivot (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (adjacentSwap b k hk) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) := by
  let km1 := GramSchmidt.prevRow k hk
  let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product
      (b := b) (km1 := km1) (k := k) hkm1
  have hdk_pos :
      ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ≠ 0 := by
    intro h
    apply hdet
    exact Int.ofNat.inj h
  show ((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      (((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2) /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)
  rw [← hprod]
  exact (Int.mul_ediv_cancel _ hdk_pos).symm
theorem adjacentSwap_gramDetNumerator_dvd (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val)
    (_hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    adjacentSwapDenom b k ∣ adjacentSwapGramDetNumerator b k hk := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product
      (b := b) (km1 := km1) (k := k) hkm1
  show ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ∣
      adjacentSwapGramDetNumerator b k hk
  show ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ∣
      ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
        (GramSchmidt.entry (scaledCoeffs b) k km1) ^ 2
  rw [← hprod]
  exact ⟨((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int),
    Int.mul_comm _ _⟩
end GramSchmidt.Int
end Hex
end
end
section
section
namespace Hex
open Hex.Internal
namespace Matrix
end Matrix
namespace Internal.LLLState
theorem sizeReduce_independent (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) (hvalid' : (s.sizeReduce k).Valid) :
    (s.sizeReduce k).b.independent := by
  intro i
  have hd_vec :
      (s.sizeReduce k).d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
        s.d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
    simpa using congrArg
      (fun d : Vector Nat (n + 1) => d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (sizeReduce_d s k)
  have hgram :
      GramSchmidt.Int.gramDet (s.sizeReduce k).b (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) =
        GramSchmidt.Int.gramDet s.b (i.val + 1) (Nat.succ_le_of_lt i.isLt) := by
    rw [← hvalid'.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt), hd_vec,
      hvalid.d_eq (i.val + 1) (Nat.succ_lt_succ i.isLt)]
  rw [hgram]
  exact hind i
theorem swapStep_b_eq (s : LLLState n m) (k : Nat) (hk : k < n) (hk0 : 0 < k) :
    (s.swapStep k).b = GramSchmidt.Int.adjacentSwap s.b ⟨k, hk⟩ hk0 := by
  unfold swapStep
  rw [dif_pos hk, dif_pos hk0]
theorem swapStep_valid (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) :
    (s.swapStep k).Valid := by
  exact (InfoLossLAR.WorstCase.NativeLLL.elementary_updates_preserve_validity s hvalid).2 hind k
theorem swapStep_independent (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (_hvalid : s.Valid) (hk0 : 0 < k) (hk : k < n) :
    (s.swapStep k).b.independent := by
  rw [swapStep_b_eq s k hk hk0]
  intro t
  let kFin : Fin n := ⟨k, hk⟩
  let km1 : Fin n := GramSchmidt.prevRow kFin hk0
  have hkFinVal : kFin.val = k := rfl
  have hkm1Val : km1.val = k - 1 := by
    show (GramSchmidt.prevRow kFin hk0).val = k - 1
    dsimp [GramSchmidt.prevRow]
  have hkm1 : km1.val + 1 = k := by omega
  have hh544 : km1.val < k := by omega
  have hdk_pos : 0 < GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
    have h := hind ⟨km1.val, Nat.lt_trans hh544 hk⟩
    rw [GramSchmidt.Int.gramDet_subst_val s.b k (km1.val + 1) (Nat.le_of_lt hk)
        (Nat.succ_le_of_lt (Nat.lt_trans hh544 hk)) hkm1.symm]
    exact h
  have hdkNext_pos :
      0 < GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := hind kFin
  have hdkm1_pos :
      0 < GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
    by_cases hh547 : km1.val = 0
    ·
      rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val 0 (Nat.le_of_lt km1.isLt)
          (Nat.zero_le n) hh547, GramSchmidt.Int.gramDet_zero]
      exact Nat.zero_lt_one
    · have hpos : 0 < km1.val := Nat.pos_of_ne_zero hh547
      have h := hind ⟨km1.val - 1, Nat.lt_trans
        (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt⟩
      rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val (km1.val - 1 + 1)
          (Nat.le_of_lt km1.isLt)
          (Nat.succ_le_of_lt (Nat.lt_trans (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt))
          (Nat.succ_pred_eq_of_pos hpos).symm]
      exact h
  by_cases hne : t.val + 1 = k
  ·
    have hh531 :
        GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp hdk_pos
    have hgramPivot :=
      GramSchmidt.Int.gramDet_adjacentSwap_pivot s.b kFin hk0 hh531
    have hdvd :=
      GramSchmidt.Int.adjacentSwap_gramDetNumerator_dvd s.b kFin hk0 hh531
    rw [GramSchmidt.Int.gramDet_subst_val (GramSchmidt.Int.adjacentSwap s.b ⟨k, hk⟩ hk0)
        (t.val + 1) k (Nat.succ_le_of_lt t.isLt) (Nat.le_of_lt hk) hne]
    suffices h : (0 : Int) < ((GramSchmidt.Int.gramDet
        (GramSchmidt.Int.adjacentSwap s.b kFin hk0) k
        (Nat.le_of_lt hk) : Nat) : Int) by
      exact_mod_cast h
    rw [hgramPivot]
    have hdenom_pos :
        (0 : Int) < ((GramSchmidt.Int.gramDet s.b kFin.val
            (Nat.le_of_lt kFin.isLt) : Nat) : Int) := by exact_mod_cast hdk_pos
    have hnum_pos :
        (0 : Int) < (((GramSchmidt.Int.gramDet s.b (kFin.val + 1)
              (Nat.succ_le_of_lt kFin.isLt) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
          GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2) := by
      have hprod_pos :
          (0 : Int) < ((GramSchmidt.Int.gramDet s.b (kFin.val + 1)
              (Nat.succ_le_of_lt kFin.isLt) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) :=
        Int.mul_pos (by exact_mod_cast hdkNext_pos) (by exact_mod_cast hdkm1_pos)
      have hsq_nn :
          (0 : Int) ≤ GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2 :=
        sq_nonneg _
      linarith
    rcases hdvd with ⟨q, hq⟩
    have hnum_eq :
        ((GramSchmidt.Int.gramDet s.b (kFin.val + 1)
              (Nat.succ_le_of_lt kFin.isLt) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
          GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2 =
        ((GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) : Nat) : Int) * q := by
      have := hq
      unfold GramSchmidt.Int.adjacentSwapGramDetNumerator
            GramSchmidt.Int.adjacentSwapDenom
            GramSchmidt.Int.adjacentSwapPivotCoeff at this
      exact this
    rw [hnum_eq, Int.mul_ediv_cancel_left _ (by linarith :
        ((GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) : Nat) : Int) ≠ 0)]
    have hdq_pos :
        (0 : Int) < ((GramSchmidt.Int.gramDet s.b kFin.val
            (Nat.le_of_lt kFin.isLt) : Nat) : Int) * q := by
      rw [← hnum_eq]; exact hnum_pos
    exact (mul_pos_iff_of_pos_left hdenom_pos).mp hdq_pos
  ·
    have hbridge := GramSchmidt.Int.gramDet_adjacentSwap_of_ne s.b kFin hk0 (t.val + 1)
      (Nat.succ_le_of_lt t.isLt) hne
    rw [hbridge]
    exact hind t
theorem swapStep_basisNormSq_below (s : LLLState n m) (k : Nat) (hk : k < n)
    (hk0 : 0 < k) (i : Nat) (hi : i + 1 < k) :
    LLLCore.basisNormSq (GramSchmidt.Int.basis (s.swapStep k).b)
        ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩ =
      LLLCore.basisNormSq (GramSchmidt.Int.basis s.b)
        ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩ := by
  rw [swapStep_b_eq s k hk hk0]
  unfold LLLCore.basisNormSq
  rw [GramSchmidt.Int.basis_adjacentSwap_of_lt s.b ⟨k, hk⟩ hk0
        ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩ hi]
theorem swapStep_coeffs_below (s : LLLState n m) (k : Nat) (hk : k < n)
    (hk0 : 0 < k) (i j : Nat) (hi : i + 1 < k) (hji : j < i) :
    (GramSchmidt.Int.coeffs (s.swapStep k).b)[(⟨i, Nat.lt_of_succ_lt
          (Nat.lt_trans hi hk)⟩ : Fin n)][(⟨j, Nat.lt_trans hji
            (Nat.lt_of_succ_lt (Nat.lt_trans hi hk))⟩ : Fin n)] =
      (GramSchmidt.Int.coeffs s.b)[(⟨i, Nat.lt_of_succ_lt
          (Nat.lt_trans hi hk)⟩ : Fin n)][(⟨j, Nat.lt_trans hji
            (Nat.lt_of_succ_lt (Nat.lt_trans hi hk))⟩ : Fin n)] := by
  rw [swapStep_b_eq s k hk hk0]
  set kFin : Fin n := ⟨k, hk⟩ with hkFin_def
  set km1 : Fin n := GramSchmidt.prevRow kFin hk0 with hkm1_def
  have hkm1_succ : km1.val + 1 = kFin.val := by
    simp [km1, GramSchmidt.prevRow, kFin]; omega
  have hikm1 : i < km1.val := by
    simp [km1, GramSchmidt.prevRow, kFin]; omega
  have hcoeff := GramSchmidt.Int.coeffs_rowSwap_adjacent_before
    s.b km1 kFin
    ⟨i, Nat.lt_of_succ_lt (Nat.lt_trans hi hk)⟩
    ⟨j, Nat.lt_trans hji (Nat.lt_of_succ_lt (Nat.lt_trans hi hk))⟩
    hkm1_succ hikm1 hji
  simpa [GramSchmidt.Int.adjacentSwap, GramSchmidt.entry, Matrix.row,
    kFin, km1] using hcoeff
end Internal.LLLState
theorem prefixLLLReduced.mono {b : Matrix Int n m} {k k' : Nat} {δ : Rat}
    (h : prefixLLLReduced b k δ) (hk : k' ≤ k) : prefixLLLReduced b k' δ := by
  refine ⟨?_, ?_⟩
  · intro i j hik' hin hji
    exact h.1 i j (Nat.lt_of_lt_of_le hik' hk) hin hji
  · intro i hik' hin
    exact h.2 i (Nat.lt_of_lt_of_le hik' hk) hin
theorem prefixLLLReduced.advance {b : Matrix Int n m} {k : Nat} (hk : k < n) {δ : Rat}
    (hpre : prefixLLLReduced b k δ)
    (hsize : ∀ (j : Nat) (hj : j < k),
      let kFin : Fin n := ⟨k, hk⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hj hk⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[kFin][jFin]
      4 * μ * μ ≤ 1)
    (hlovasz : (hk0 : 0 < k) →
      let kFin : Fin n := ⟨k, hk⟩
      let km1Fin : Fin n := ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[kFin][km1Fin]
      δ * LLLCore.basisNormSq (GramSchmidt.Int.basis b) km1Fin ≤
        LLLCore.basisNormSq (GramSchmidt.Int.basis b) kFin +
          μ * μ * LLLCore.basisNormSq (GramSchmidt.Int.basis b) km1Fin) :
    prefixLLLReduced b (k + 1) δ := by
  refine ⟨?_, ?_⟩
  ·
    intro i j hik' hin hji
    rcases Nat.lt_or_ge i k with hik | hik
    · exact hpre.1 i j hik hin hji
    · have hi_eq : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hik') hik
      have hj_lt_k : j < k := hi_eq ▸ hji
      have hg := hsize j hj_lt_k
      let iFin : Fin n := ⟨i, hin⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[iFin][jFin]
      show 4 * μ * μ ≤ 1
      have hi_fin : (⟨k, hk⟩ : Fin n) = iFin := Fin.ext hi_eq.symm
      have hj_fin : (⟨j, Nat.lt_trans hj_lt_k hk⟩ : Fin n) = jFin :=
        Fin.ext rfl
      have key := hg
      simp only [hi_fin, hj_fin] at key
      exact key
  ·
    intro i hik' hin
    rcases Nat.lt_or_ge (i + 1) k with hik | hik
    · exact hpre.2 i hik hin
    · have hip1_eq : i + 1 = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hik') hik
      have hk0 : 0 < k := by omega
      have hi_eq : i = k - 1 := by omega
      have hg := hlovasz hk0
      have hin_i : i < n := Nat.lt_of_succ_lt hin
      let iFin : Fin n := ⟨i, hin_i⟩
      let ip1Fin : Fin n := ⟨i + 1, hin⟩
      let μ : Rat := (GramSchmidt.Int.coeffs b)[ip1Fin][iFin]
      let N_i : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis b) iFin
      let N_ip1 : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis b) ip1Fin
      show δ * N_i ≤ N_ip1 + μ * μ * N_i
      have hi_fin : (⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk⟩ : Fin n) = iFin :=
        Fin.ext hi_eq.symm
      have hip1_fin : (⟨k, hk⟩ : Fin n) = ip1Fin :=
        Fin.ext (by show k = i + 1; omega)
      have key := hg
      simp only [hi_fin, hip1_fin] at key
      exact key
theorem prefixLLLReduced_one (b : Matrix Int n m) (δ : Rat) :
    prefixLLLReduced b 1 δ := by
  refine ⟨?_, ?_⟩
  · intro i j hi _ hji
    interval_cases i
    exact absurd hji (Nat.not_lt_zero j)
  · intro i hi _
    omega
theorem prefixLLLReduced_to_isLLLReduced (b : Matrix Int n m) (δ : Rat)
    (h : prefixLLLReduced b n δ) : isLLLReduced b δ (1 / 2) := by
  let coeffs := GramSchmidt.Int.coeffs b
  refine ⟨?_, ?_⟩
  · intro i j hi hji
    have h4 := h.1 i j hi hi hji
    let iFin : Fin n := ⟨i, hi⟩
    let jFin : Fin n := ⟨j, Nat.lt_trans hji hi⟩
    let μ : Rat := coeffs[iFin][jFin]
    show μ * μ ≤ (1 / 2 : Rat) * (1 / 2)
    have h4' : 4 * μ * μ ≤ 1 := h4
    have hhalf : (1 / 2 : Rat) * (1 / 2) = 1 / 4 := by grind
    grind
  · intro i hi
    exact h.2 i hi hi
namespace Internal.LLLState
theorem swapStep_prefixLLLReduced (s : LLLState n m) (k : Nat) (δ : Rat)
    (h : prefixLLLReduced s.b k δ) :
    prefixLLLReduced (s.swapStep k).b (max (k - 1) 1) δ := by
  rcases Nat.eq_zero_or_pos k with hk0_eq | hk0_pos
  ·
    subst hk0_eq
    refine ⟨fun i j hik' _ hji => ?_, fun i hik' _ => ?_⟩
    · simp at hik'; omega
    · simp at hik'
  · by_cases hk : k < n
    ·
      refine ⟨?_, ?_⟩
      · intro i j hik' hin hji
        have hi_pos : 0 < i := Nat.lt_of_le_of_lt (Nat.zero_le _) hji
        have hi_lt : i + 1 < k := by
          rcases Nat.lt_or_ge k 2 with hk_lt | hk_ge
          · interval_cases k
            simp at hik'; omega
          · have hmax_eq : max (k - 1) 1 = k - 1 := max_eq_left (by omega)
            rw [hmax_eq] at hik'; omega
        let iFin : Fin n := ⟨i, hin⟩
        let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
        let μ_swap : Rat := (GramSchmidt.Int.coeffs (s.swapStep k).b)[iFin][jFin]
        let μ : Rat := (GramSchmidt.Int.coeffs s.b)[iFin][jFin]
        show 4 * μ_swap * μ_swap ≤ 1
        have hcoeff : μ_swap = μ :=
          swapStep_coeffs_below s k hk hk0_pos i j hi_lt hji
        have hres : 4 * μ * μ ≤ 1 := h.1 i j (by omega) hin hji
        rw [hcoeff]; exact hres
      · intro i hik' hin
        have hi_lt : i + 2 < k := by
          rcases Nat.lt_or_ge k 3 with hk_lt | hk_ge
          · interval_cases k
            · simp at hik'
            · simp at hik'
          · have hmax_eq : max (k - 1) 1 = k - 1 := max_eq_left (by omega)
            rw [hmax_eq] at hik'; omega
        have hin_i : i < n := Nat.lt_of_succ_lt hin
        let iFin : Fin n := ⟨i, hin_i⟩
        let ip1Fin : Fin n := ⟨i + 1, hin⟩
        let N_swap_i : Rat :=
          LLLCore.basisNormSq (GramSchmidt.Int.basis (s.swapStep k).b) iFin
        let N_swap_ip1 : Rat :=
          LLLCore.basisNormSq (GramSchmidt.Int.basis (s.swapStep k).b) ip1Fin
        let N_i : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) iFin
        let N_ip1 : Rat := LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) ip1Fin
        let μ_swap : Rat := (GramSchmidt.Int.coeffs (s.swapStep k).b)[ip1Fin][iFin]
        let μ : Rat := (GramSchmidt.Int.coeffs s.b)[ip1Fin][iFin]
        show δ * N_swap_i ≤ N_swap_ip1 + μ_swap * μ_swap * N_swap_i
        have hb_i : N_swap_i = N_i :=
          swapStep_basisNormSq_below s k hk hk0_pos i (by omega)
        have hb_ip1 : N_swap_ip1 = N_ip1 :=
          swapStep_basisNormSq_below s k hk hk0_pos (i + 1) hi_lt
        have hcoeff : μ_swap = μ :=
          swapStep_coeffs_below s k hk hk0_pos (i + 1) i hi_lt (Nat.lt_succ_self i)
        have hres : δ * N_i ≤ N_ip1 + μ * μ * N_i := h.2 i (by omega) hin
        rw [hb_i, hb_ip1, hcoeff]; exact hres
    ·
      have hsw : s.swapStep k = s := by
        unfold swapStep; rw [dif_neg hk]
      rw [hsw]
      apply h.mono
      apply max_le <;> omega
private theorem gapH275 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) :
    (s.sizeReduceColumn j k hjk).d = s.d := by
  unfold sizeReduceColumn
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
  · rw [dif_neg hreduce]
private theorem gapH136 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    (r : Int)
    (hr : r = nearestQuotient ((s.ν.getRow k).get j)
      (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) :
    (s.sizeReduceColumn j k hjk).ν.getRow k =
      (Fin.foldl j.val
        (fun (row : Vector Int n) (l : Fin j.val) =>
          let lFin : Fin n := ⟨l.val, Nat.lt_trans l.isLt j.isLt⟩
          row.set lFin ((s.ν.getRow k).get lFin - r * (s.ν.getRow j).get lFin))
        (s.ν.getRow k)).set j ((s.ν.getRow k).get j -
          r * Int.ofNat (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) := by
  subst hr
  unfold sizeReduceColumn; rw [dif_pos hreduce]
  exact Hex.Matrix.setRow_get_self s.ν k _
theorem sizeReduceColumn_valid (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (hvalid : s.Valid) :
    (s.sizeReduceColumn j k hjk).Valid := by
  exact (InfoLossLAR.WorstCase.NativeLLL.elementary_updates_preserve_validity s hvalid).1 j k hjk
theorem sizeReduce_valid (s : LLLState n m) (k : Nat) (hvalid : s.Valid) :
    (s.sizeReduce k).Valid := by
  unfold sizeReduce
  by_cases hk : k < n
  · rw [dif_pos hk]
    suffices h : ∀ (xs : List (Fin k)) (s' : LLLState n m), s'.Valid →
        (xs.foldl
            (fun state j =>
              let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
              state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
            s').Valid from by
      simpa [Fin.foldr_eq_finRange_foldr] using h (List.finRange k).reverse s hvalid
    intro xs
    induction xs with
    | nil => intro s' hv; exact hv
    | cons j js ih =>
      intro s' hv
      simp only [List.foldl_cons]
      exact ih _ (sizeReduceColumn_valid s' _ _ _ hv)
  · rw [dif_neg hk]
    exact hvalid
private theorem gapH266 (νjk : Int) (dj1 : Nat)
    (hdpos : 0 < dj1) :
    2 * Int.natAbs (νjk - nearestQuotient νjk dj1 * Int.ofNat dj1) ≤ dj1 := by
  set q : Int := nearestQuotient νjk dj1 with hq_def
  unfold nearestQuotient at hq_def
  have hdj_pos_int : (0 : Int) < Int.ofNat dj1 := by
    show (0 : Int) < (dj1 : Int)
    exact_mod_cast hdpos
  have h2d_pos : (0 : Int) < 2 * Int.ofNat dj1 := by linarith
  set a : Int := 2 * νjk + Int.ofNat dj1 with ha_def
  have hqf : q = Int.fdiv a (2 * Int.ofNat dj1) := hq_def
  have hm_eq : Int.fmod a (2 * Int.ofNat dj1) = a - q * (2 * Int.ofNat dj1) := by
    rw [hqf, Int.fmod_def]; ring
  have hm_nn : (0 : Int) ≤ Int.fmod a (2 * Int.ofNat dj1) :=
    Int.fmod_nonneg_of_pos a h2d_pos
  have hm_lt : Int.fmod a (2 * Int.ofNat dj1) < 2 * Int.ofNat dj1 :=
    Int.fmod_lt_of_pos a h2d_pos
  have h2res : 2 * (νjk - q * Int.ofNat dj1) =
      Int.fmod a (2 * Int.ofNat dj1) - Int.ofNat dj1 := by
    rw [hm_eq, ha_def]; ring
  have hres_lb : -(Int.ofNat dj1) ≤ 2 * (νjk - q * Int.ofNat dj1) := by
    rw [h2res]; omega
  have hres_ub : 2 * (νjk - q * Int.ofNat dj1) ≤ Int.ofNat dj1 := by
    rw [h2res]; omega
  have hres_lb' : -(dj1 : Int) ≤ 2 * (νjk - q * (dj1 : Int)) := by
    have : (Int.ofNat dj1 : Int) = (dj1 : Int) := rfl
    rw [this] at hres_lb; exact hres_lb
  have hres_ub' : 2 * (νjk - q * (dj1 : Int)) ≤ (dj1 : Int) := by
    have : (Int.ofNat dj1 : Int) = (dj1 : Int) := rfl
    rw [this] at hres_ub; exact hres_ub
  show 2 * Int.natAbs (νjk - q * Int.ofNat dj1) ≤ dj1
  have : (Int.ofNat dj1 : Int) = (dj1 : Int) := rfl
  rw [this]
  omega
private theorem gapH307 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (t : Nat) (ht : t ≤ n) :
    GramSchmidt.Int.gramDet (s.sizeReduceColumn j k hjk).b t ht =
      GramSchmidt.Int.gramDet s.b t ht := by
  unfold sizeReduceColumn
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
    exact GramSchmidt.Int.gramDet_sizeReduce s.b j k hjk _ t ht
  · rw [dif_neg hreduce]
private theorem gapH286 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (hind : s.b.independent) :
    (s.sizeReduceColumn j k hjk).b.independent := by
  intro i
  rw [gapH307 s j k hjk]
  exact hind i
private theorem gapH260 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hdpos : 0 < s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :
    2 * Int.natAbs (((s.sizeReduceColumn j k hjk).ν.getRow k).get j) ≤
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [gapH136 s j k hjk hreduce _ rfl]
    rw [show ∀ (xs : Vector Int n) (x : Int),
            (xs.set j.val x j.isLt).get j = x from
          fun xs x => Vector.getElem_set_self j.isLt]
    exact gapH266 _ _ hdpos
  · have h_eq : s.sizeReduceColumn j k hjk = s := by
      unfold sizeReduceColumn; rw [dif_neg hreduce]
    rw [h_eq]
    exact Nat.le_of_not_lt hreduce
private theorem gapH207 (s : LLLState n m)
    (j k : Fin n) (hjk : j.val < k.val) (l : Fin n) (hjl : j.val < l.val) :
    ((s.sizeReduceColumn j k hjk).ν.getRow k).get l = (s.ν.getRow k).get l := by
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [gapH136 s j k hjk hreduce _ rfl]
    have hj_ne_l : j.val ≠ l.val := Nat.ne_of_lt hjl
    rw [show ∀ (xs : Vector Int n) (x : Int),
            (xs.set j.val x j.isLt).get l = xs.get l from
          fun xs x => Vector.getElem_set_ne j.isLt l.isLt hj_ne_l]
    rw [LLLState.foldl_finRange_set_outerSubMul_get_eq j.val
        (Nat.le_of_lt j.isLt) (s.ν.getRow k) (s.ν.getRow k) (s.ν.getRow j) _ l]
    rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hjl))]
  · have h_eq : s.sizeReduceColumn j k hjk = s := by
      unfold sizeReduceColumn; rw [dif_neg hreduce]
    rw [h_eq]
private theorem gapH358 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (i : Fin (n + 1)) :
    (s.sizeReduceColumn j k hjk).d.get i = s.d.get i := by
  rw [gapH275 s j k hjk]
private theorem gapH206 {n m : Nat}
    (k : Nat) (hk : k < n) (e : Fin n) :
    ∀ (xs : List (Fin k)) (s' : LLLState n m),
      (∀ l ∈ xs, l.val < e.val) →
      ((xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
          s').ν.getRow ⟨k, hk⟩).get e = (s'.ν.getRow ⟨k, hk⟩).get e := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons j js ih =>
    intro s' hxs
    have hj_lt_e : j.val < e.val := hxs j List.mem_cons_self
    have hjs_lt_e : ∀ l ∈ js, l.val < e.val := fun l hl =>
      hxs l (List.mem_cons.mpr (Or.inr hl))
    simp only [List.foldl_cons]
    rw [ih _ hjs_lt_e]
    let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
    exact gapH207 s' jFin ⟨k, hk⟩ j.isLt e hj_lt_e
private theorem gapH272 {n m : Nat}
    (k : Nat) (hk : k < n) :
    ∀ (xs : List (Fin k)),
      xs.Pairwise (fun a b : Fin k => b.val < a.val) →
      ∀ (s' : LLLState n m), s'.Valid → s'.b.independent →
        ∀ e ∈ xs,
          2 * Int.natAbs
              (((xs.foldl
                  (fun state j =>
                    let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
                    state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
                  s').ν.getRow ⟨k, hk⟩).get
                ⟨e.val, Nat.lt_trans e.isLt hk⟩) ≤
            s'.d.get ⟨e.val + 1, Nat.succ_lt_succ (Nat.lt_trans e.isLt hk)⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro _ s' _ _ e he
    exact absurd he List.not_mem_nil
  | cons j js ih =>
    intro hpairwise s' hvalid hind e he
    have hpairwise' : js.Pairwise (fun a b : Fin k => b.val < a.val) :=
      List.Pairwise.tail hpairwise
    have hj_gt_js : ∀ l ∈ js, l.val < j.val := by
      intro l hl
      have := List.rel_of_pairwise_cons hpairwise hl
      exact this
    simp only [List.foldl_cons]
    set jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩ with hjFin_def
    have hjFinLt : jFin.val < k := j.isLt
    set s'' : LLLState n m := s'.sizeReduceColumn jFin ⟨k, hk⟩ hjFinLt with hs''_def
    by_cases h_eq : e = j
    ·
      subst h_eq
      have hdpos :
          0 < s'.d.get ⟨jFin.val + 1, Nat.succ_lt_succ jFin.isLt⟩ := by
        have := hvalid.d_eq (jFin.val + 1) (Nat.succ_lt_succ jFin.isLt)
        rw [this]
        exact hind ⟨jFin.val, jFin.isLt⟩
      have hpivot :=
        gapH260 s' jFin ⟨k, hk⟩ hjFinLt hdpos
      have hpres :=
        gapH206 k hk
          (⟨e.val, Nat.lt_trans e.isLt hk⟩ : Fin n) js
          s'' hj_gt_js
      show 2 * Int.natAbs ((((js.foldl _ s'').ν.getRow ⟨k, hk⟩).get _)) ≤ _
      rw [hpres]
      exact hpivot
    ·
      have he_js : e ∈ js := by
        rcases List.mem_cons.mp he with h | h
        · exact absurd h h_eq
        · exact h
      have hd_step := gapH358 s' jFin ⟨k, hk⟩ hjFinLt
        ⟨e.val + 1, Nat.succ_lt_succ (Nat.lt_trans e.isLt hk)⟩
      rw [← hd_step]
      exact ih hpairwise' s''
        (sizeReduceColumn_valid s' jFin ⟨k, hk⟩ hjFinLt hvalid)
        (gapH286 s' jFin ⟨k, hk⟩ hjFinLt hind)
        e he_js
private theorem gapH282 (k : Nat) :
    ((List.finRange k).reverse).Pairwise (fun a b : Fin k => b.val < a.val) := by
  rw [List.pairwise_reverse, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_finRange] at hi hj
  rw [List.getElem_finRange (by rw [List.length_finRange]; exact hi),
    List.getElem_finRange (by rw [List.length_finRange]; exact hj)]
  exact hij
theorem sizeReduce_ν_bound (s : LLLState n m) (k : Nat) (hk : k < n)
    (hvalid : s.Valid) (hind : s.b.independent) :
    ∀ (j : Nat) (hj : j < k),
      let kFin : Fin n := ⟨k, hk⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hj hk⟩
      2 * Int.natAbs (((s.sizeReduce k).ν.getRow kFin).get jFin) ≤
        s.d.get ⟨j + 1, Nat.succ_lt_succ (Nat.lt_trans hj hk)⟩ := by
  intro j hj
  unfold sizeReduce
  rw [dif_pos hk]
  simpa [Fin.foldr_eq_finRange_foldr] using
    gapH272 k hk (List.finRange k).reverse
      (gapH282 k)
      s hvalid hind ⟨j, hj⟩ (List.mem_reverse.mpr (List.mem_finRange _))
theorem sizeReduce_size_reduced (s : LLLState n m) (k : Nat) (hk : k < n)
    (hvalid : s.Valid) (hind : s.b.independent) :
    ∀ (j : Nat) (hj : j < k),
      let kFin : Fin n := ⟨k, hk⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hj hk⟩
      let μ := GramSchmidt.entry (GramSchmidt.Int.coeffs (s.sizeReduce k).b)
        kFin jFin
      4 * μ * μ ≤ 1 := by
  intro j hj
  have hjn : j < n := Nat.lt_trans hj hk
  have hjsuc : j + 1 ≤ n := Nat.succ_le_of_lt hjn
  have hν_bound := sizeReduce_ν_bound s k hk hvalid hind j hj
  have hvalid' : (s.sizeReduce k).Valid := sizeReduce_valid s k hvalid
  have hgramDet_preserved :
      GramSchmidt.Int.gramDet (s.sizeReduce k).b (j + 1) hjsuc =
        GramSchmidt.Int.gramDet s.b (j + 1) hjsuc := by
    have h1 := hvalid'.d_eq (j + 1) (Nat.succ_lt_succ hjn)
    have h2 := hvalid.d_eq (j + 1) (Nat.succ_lt_succ hjn)
    have h3 : (s.sizeReduce k).d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩ =
        s.d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩ := by
      simpa using congrArg (fun d : Vector Nat (n + 1) =>
        d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩) (sizeReduce_d s k)
    rw [← h1, h3, h2]
  have hgd_pos : 0 < GramSchmidt.Int.gramDet (s.sizeReduce k).b (j + 1) hjsuc := by
    rw [hgramDet_preserved]
    exact hind ⟨j, hjn⟩
  have hsc := GramSchmidt.Int.scaledCoeffs_eq (s.sizeReduce k).b
    k j hk hj
  set kFin : Fin n := ⟨k, hk⟩
  set jFin : Fin n := ⟨j, hjn⟩
  set ν' : Int := ((s.sizeReduce k).ν.getRow kFin).get jFin with hν'_def
  set d_jp1 : Nat := s.d.get ⟨j + 1, Nat.succ_lt_succ hjn⟩ with hd_jp1_def
  set μ : Rat := GramSchmidt.entry (GramSchmidt.Int.coeffs (s.sizeReduce k).b)
    kFin jFin with hμ_def
  have hd_rat_pos : (0 : Rat) < (d_jp1 : Rat) := by
    have hd_nat_pos : 0 < d_jp1 := by
      rw [hd_jp1_def, hvalid.d_eq (j + 1) (Nat.succ_lt_succ hjn)]
      exact hind ⟨j, hjn⟩
    exact_mod_cast hd_nat_pos
  have hd_ne : (d_jp1 : Rat) ≠ 0 := ne_of_gt hd_rat_pos
  have hν'_bridge : (ν' : Rat) = (d_jp1 : Rat) * μ := by
    have hν_at : ν' =
        ((GramSchmidt.Int.scaledCoeffs (s.sizeReduce k).b).getRow kFin).get jFin :=
      hvalid'.ν_eq kFin.val jFin.val kFin.isLt jFin.isLt hj
    have hd_eq_rat : (d_jp1 : Rat) =
        ((GramSchmidt.Int.gramDet (s.sizeReduce k).b (j+1) hjsuc : Nat) : Rat) := by
      rw [hgramDet_preserved]
      show ((s.d.get _ : Nat) : Rat) = ((GramSchmidt.Int.gramDet s.b (j+1) hjsuc : Nat) : Rat)
      rw [hvalid.d_eq (j + 1) (Nat.succ_lt_succ hjn)]
    have hsc' : ((GramSchmidt.entry
        (GramSchmidt.Int.scaledCoeffs (s.sizeReduce k).b) kFin jFin : Int) : Rat) =
      ((GramSchmidt.Int.gramDet (s.sizeReduce k).b (j+1) hjsuc : Nat) : Rat) * μ := hsc
    have hν'_eq : ((ν' : Int) : Rat) =
        ((GramSchmidt.entry
          (GramSchmidt.Int.scaledCoeffs (s.sizeReduce k).b) kFin jFin : Int) : Rat) := by
      rw [hν_at]; rfl
    rw [hν'_eq, hsc', hd_eq_rat]
  have h_int_le : 2 * (ν' : Int).natAbs ≤ (d_jp1 : Nat) := hν_bound
  have habs2_int : |(2 * ν' : Int)| ≤ (d_jp1 : Int) := by
    rw [Int.abs_eq_natAbs, Int.natAbs_mul]
    show ((2 * ν'.natAbs : Nat) : Int) ≤ (d_jp1 : Int)
    exact_mod_cast h_int_le
  have habs2_rat : |(2 * ν' : Rat)| ≤ (d_jp1 : Rat) := by
    have h_cast : |((2 * ν' : Int) : Rat)| ≤ ((d_jp1 : Int) : Rat) := by
      exact_mod_cast habs2_int
    push_cast at h_cast
    exact h_cast
  have hsq_le : (2 * (ν' : Rat))^2 ≤ (d_jp1 : Rat)^2 := by
    have h := abs_le_abs habs2_rat (by linarith [abs_nonneg (2 * (ν' : Rat))])
    have : |(2 * (ν' : Rat))| ≤ |((d_jp1 : Rat))| := by
      rw [abs_of_nonneg (le_of_lt hd_rat_pos)]
      exact habs2_rat
    calc (2 * (ν' : Rat))^2 = |(2 * (ν' : Rat))|^2 := (sq_abs _).symm
      _ ≤ |((d_jp1 : Rat))|^2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (d_jp1 : Rat)^2 := sq_abs _
  show 4 * μ * μ ≤ 1
  have hμ_eq : μ = (ν' : Rat) / (d_jp1 : Rat) := by
    field_simp
    linarith [hν'_bridge]
  rw [hμ_eq]
  rw [show 4 * ((ν' : Rat) / (d_jp1 : Rat)) * ((ν' : Rat) / (d_jp1 : Rat)) =
      (2 * (ν' : Rat))^2 / (d_jp1 : Rat)^2 by ring]
  rw [div_le_one (by positivity)]
  exact hsq_le
theorem sizeReduce_potential (s : LLLState n m) (k : Nat) :
    (s.sizeReduce k).potential = s.potential := by
  unfold potential
  rw [sizeReduce_d]
theorem lllLoop_eq_b_at_n
    (s : LLLState n m) (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1)
    (hk : 1 ≤ n) (hkn : n ≤ n) (fuel : Nat) :
    lllLoop s n δ hδ hδ' hk hkn fuel = s.b := by
  cases fuel with
  | zero => rfl
  | succ f =>
    show (if hdone : n = n then s.b
          else _) = s.b
    rw [dif_pos rfl]
theorem lllLoop_succ_eq_body
    (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n) (hlt : k < n)
    (fuel : Nat) :
    lllLoop s k δ hδ hδ' hk hkn (fuel + 1) =
      lllLoopBody s k δ hδ hδ' hk hkn hlt fuel := by
  show (if hdone : k = n then s.b else _) = _
  rw [dif_neg (Nat.ne_of_lt hlt)]
  rfl
private theorem gapH221 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (i : Fin n) (hik : i ≠ k) :
    (GramSchmidt.Int.coeffs (s.sizeReduceColumn j k hjk).b).row i =
      (GramSchmidt.Int.coeffs s.b).row i := by
  unfold sizeReduceColumn
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
    exact GramSchmidt.Int.coeffs_sizeReduce_other_row s.b j k hjk _ i hik
  · rw [dif_neg hreduce]
private theorem gapH228 {n m : Nat}
    (k : Nat) (hk : k < n) (i : Fin n) (hik : i ≠ ⟨k, hk⟩) :
    ∀ (xs : List (Fin k)) (s' : LLLState n m),
      (GramSchmidt.Int.coeffs (xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            state.sizeReduceColumn jFin ⟨k, hk⟩ j.isLt)
          s').b).row i = (GramSchmidt.Int.coeffs s'.b).row i := by
  intro xs
  induction xs with
  | nil => intro s'; rfl
  | cons j js ih =>
    intro s'
    simp only [List.foldl_cons]
    rw [ih _]
    exact gapH221 s' _ _ j.isLt i hik
theorem sizeReduce_coeffs_row_of_ne (s : LLLState n m) (k : Nat) (i : Fin n)
    (hik : i.val ≠ k) :
    (GramSchmidt.Int.coeffs (s.sizeReduce k).b).row i =
      (GramSchmidt.Int.coeffs s.b).row i := by
  unfold sizeReduce
  by_cases hk : k < n
  · rw [dif_pos hk]
    have hik' : i ≠ ⟨k, hk⟩ := fun h => hik (by rw [h])
    simpa [Fin.foldr_eq_finRange_foldr] using
      gapH228 k hk i hik' (List.finRange k).reverse s
  · rw [dif_neg hk]
theorem sizeReduce_prefixLLLReduced (s : LLLState n m) (k : Nat) (δ : Rat)
    (h : prefixLLLReduced s.b k δ) :
    prefixLLLReduced (s.sizeReduce k).b k δ := by
  refine ⟨?_, ?_⟩
  ·
    intro i j hik hin hji
    have hi_ne_k : (⟨i, hin⟩ : Fin n).val ≠ k := Nat.ne_of_lt hik
    have hrow := sizeReduce_coeffs_row_of_ne s k ⟨i, hin⟩ hi_ne_k
    let iFin : Fin n := ⟨i, hin⟩
    let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
    let μ_sr : Rat := (GramSchmidt.Int.coeffs (s.sizeReduce k).b)[iFin][jFin]
    show 4 * μ_sr * μ_sr ≤ 1
    have hμ_eq : μ_sr =
        (GramSchmidt.Int.coeffs s.b)[iFin][jFin] := by
      show ((GramSchmidt.Int.coeffs (s.sizeReduce k).b).row iFin)[jFin] =
        ((GramSchmidt.Int.coeffs s.b).row iFin)[jFin]
      rw [hrow]
    rw [hμ_eq]
    exact h.1 i j hik hin hji
  ·
    intro i hik hin
    have hh525 := sizeReduce_basis s k
    have hip1_ne_k : (⟨i + 1, hin⟩ : Fin n).val ≠ k := Nat.ne_of_lt hik
    have hrow := sizeReduce_coeffs_row_of_ne s k ⟨i + 1, hin⟩ hip1_ne_k
    have hin_i : i < n := Nat.lt_of_succ_lt hin
    let iFin : Fin n := ⟨i, hin_i⟩
    let ip1Fin : Fin n := ⟨i + 1, hin⟩
    let N_sr_i : Rat :=
      LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) iFin
    let N_sr_ip1 : Rat :=
      LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) ip1Fin
    let μ_sr : Rat :=
      (GramSchmidt.Int.coeffs (s.sizeReduce k).b)[ip1Fin][iFin]
    show δ * N_sr_i ≤ N_sr_ip1 + μ_sr * μ_sr * N_sr_i
    have hb_i : N_sr_i = LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) iFin := by
      show LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) iFin = _
      rw [hh525]
    have hb_ip1 : N_sr_ip1 =
        LLLCore.basisNormSq (GramSchmidt.Int.basis s.b) ip1Fin := by
      show LLLCore.basisNormSq (GramSchmidt.Int.basis (s.sizeReduce k).b) ip1Fin = _
      rw [hh525]
    have hμ_eq : μ_sr = (GramSchmidt.Int.coeffs s.b)[ip1Fin][iFin] := by
      show ((GramSchmidt.Int.coeffs (s.sizeReduce k).b).row ip1Fin)[iFin] =
        ((GramSchmidt.Int.coeffs s.b).row ip1Fin)[iFin]
      rw [hrow]
    rw [hb_i, hb_ip1, hμ_eq]
    exact h.2 i hik hin
theorem lllLoop_independent
    (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1) :
    ∀ (fuel : Nat) (s : LLLState n m) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n),
      s.Valid → s.b.independent →
      Matrix.independent (lllLoop s k δ hδ hδ' hk hkn fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s _ _ _ _ hind
    exact hind
  | succ f ih =>
    intro s k hk hkn hvalid hind
    by_cases hkn_eq : k = n
    · subst hkn_eq
      rw [lllLoop_eq_b_at_n]
      exact hind
    · have hlt : k < n := Nat.lt_of_le_of_ne hkn hkn_eq
      have hh558 : (s.sizeReduce k).Valid := sizeReduce_valid s k hvalid
      have hsR_ind : (s.sizeReduce k).b.independent :=
        sizeReduce_independent s k hind hvalid hh558
      rw [lllLoop_succ_eq_body s k δ hδ hδ' hk hkn hlt]
      dsimp only [lllLoopBody]
      split_ifs
      · exact ih (s.sizeReduce k) (k + 1) (Nat.succ_pos k)
          (Nat.succ_le_of_lt hlt) hh558 hsR_ind
      · have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
        have hsS_valid : ((s.sizeReduce k).swapStep k).Valid :=
          swapStep_valid (s.sizeReduce k) k hsR_ind hh558
        have hsS_ind : ((s.sizeReduce k).swapStep k).b.independent :=
          swapStep_independent (s.sizeReduce k) k hsR_ind hh558 hk0 hlt
        have hk'n : max (k - 1) 1 ≤ n :=
          (Nat.max_le).2 ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩
        exact ih ((s.sizeReduce k).swapStep k) (max (k - 1) 1)
          (Nat.le_max_right (k - 1) 1) hk'n hsS_valid hsS_ind
end Internal.LLLState
end Hex
end
end
section
private theorem gapH176 {α : Type*} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.get i = v[i.1] := rfl
namespace Hex
open Hex.Internal
namespace Internal.LLLState
private theorem gapH417 {α : Type*} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun acc i => acc * f i) a =
      a * xs.foldl (fun acc i => acc * f i) 1 := by
  induction xs generalizing a with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih (a * f x), ih (1 * f x), Nat.one_mul, Nat.mul_assoc]
private theorem gapH445 {α : Type*} (xs : List α) (f : α → Nat) (a : Nat)
    (ha : 0 < a) (hpos : ∀ i ∈ xs, 0 < f i) :
    0 < xs.foldl (fun acc i => acc * f i) a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact Nat.mul_pos ha (hpos x List.mem_cons_self)
    · exact fun i hi => hpos i (List.mem_cons.mpr (Or.inr hi))
private theorem gapH318 {α : Type*} (xs : List α) (f g : α → Nat) (a : Nat)
    (heq : ∀ i ∈ xs, f i = g i) :
    xs.foldl (fun acc i => acc * f i) a = xs.foldl (fun acc i => acc * g i) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [heq x List.mem_cons_self]
    exact ih _ (fun i hi => heq i (List.mem_cons.mpr (Or.inr hi)))
private theorem gapH375 {α : Type*} {xs : List α} (hnd : xs.Nodup)
    {k : α} (hk : k ∈ xs) (f g : α → Nat)
    (hpos : ∀ i ∈ xs, 0 < f i)
    (heq : ∀ i ∈ xs, i ≠ k → f i = g i)
    (hlt : 4 * g k < 3 * f k) :
    ∀ a, 0 < a →
      4 * xs.foldl (fun acc i => acc * g i) a <
        3 * xs.foldl (fun acc i => acc * f i) a := by
  induction xs with
  | nil => exact absurd hk List.not_mem_nil
  | cons x rest ih =>
    intro a ha
    have hxnd : x ∉ rest := (List.nodup_cons.mp hnd).1
    have hrnd : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hpos_x : 0 < f x := hpos x List.mem_cons_self
    simp only [List.foldl_cons]
    by_cases hxk : x = k
    · subst hxk
      have heq_rest : ∀ i ∈ rest, f i = g i := fun i hi =>
        heq i (List.mem_cons.mpr (Or.inr hi)) (fun h => hxnd (h ▸ hi))
      have hpos_rest : ∀ i ∈ rest, 0 < f i := fun i hi =>
        hpos i (List.mem_cons.mpr (Or.inr hi))
      have hP_pos : 0 < rest.foldl (fun acc i => acc * f i) 1 :=
        gapH445 rest f 1 Nat.one_pos hpos_rest
      rw [gapH417 rest g (a * g x), gapH417 rest f (a * f x),
        ← gapH318 rest f g 1 heq_rest]
      have h_factor : a * (4 * g x) < a * (3 * f x) :=
        (Nat.mul_lt_mul_left ha).mpr hlt
      have h_total := (Nat.mul_lt_mul_right hP_pos).mpr h_factor
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h_total
    · have hk_rest : k ∈ rest := by
        rcases List.mem_cons.mp hk with rfl | h
        · exact absurd rfl hxk
        · exact h
      have heq_x : f x = g x := heq x List.mem_cons_self hxk
      rw [heq_x]
      apply ih hrnd hk_rest
      · exact fun i hi => hpos i (List.mem_cons.mpr (Or.inr hi))
      · exact fun i hi => heq i (List.mem_cons.mpr (Or.inr hi))
      · exact Nat.mul_pos ha (heq_x ▸ hpos_x)
theorem swapStep_potential_three_fourths (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid)
    (hk0 : 0 < k) (hk : k < n)
    (hfail :
      Int.ofNat 4 *
          (Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
              Int.ofNat (s.d.get ⟨k - 1,
                Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk)⟩) +
            ((s.ν.getRow ⟨k, hk⟩).get
                ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk⟩) ^ 2) <
        (3 : Int) * (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2) :
    4 * (s.swapStep k).potential < 3 * s.potential := by
  have hδden_pos : 0 < (4 : Nat) := by decide
  have hδ_le_one : (3 : Int) ≤ Int.ofNat 4 := by decide
  have hkm1lt : k - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk
  let kFin : Fin n := ⟨k, hk⟩
  let km1 : Fin n := ⟨k - 1, hkm1lt⟩
  have hh544 : km1.val < k := by show k - 1 < k; omega
  have hkm1Pred_eq : (GramSchmidt.prevRow kFin hk0) = km1 := by
    apply Fin.eq_of_val_eq
    show k - 1 = k - 1
    rfl
  have hdk_pos : 0 < GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
    have h := hind ⟨km1.val, Nat.lt_trans hh544 hk⟩
    have hkm1_succ : km1.val + 1 = k := by show k - 1 + 1 = k; omega
    rwa [GramSchmidt.Int.gramDet_subst_val s.b (km1.val + 1) k _ _ hkm1_succ] at h
  have hdkNext_pos :
      0 < GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := hind kFin
  have hdkm1_pos :
      0 < GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
    by_cases hh547 : km1.val = 0
    · rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val 0 (Nat.le_of_lt km1.isLt)
          (Nat.zero_le n) hh547, GramSchmidt.Int.gramDet_zero]
      exact Nat.zero_lt_one
    · have hpos : 0 < km1.val := Nat.pos_of_ne_zero hh547
      have h := hind ⟨km1.val - 1, Nat.lt_trans
        (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt⟩
      rw [GramSchmidt.Int.gramDet_subst_val s.b km1.val (km1.val - 1 + 1)
          (Nat.le_of_lt km1.isLt)
          (Nat.succ_le_of_lt (Nat.lt_trans (Nat.sub_lt hpos Nat.zero_lt_one) km1.isLt))
          (Nat.succ_pred_eq_of_pos hpos).symm]
      exact h
  have hdk_eq : s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ =
      GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
    have := hvalid.d_eq k (Nat.lt_succ_of_lt hk); simpa using this
  have hh530 : s.d.get ⟨k - 1, Nat.lt_succ_of_lt hkm1lt⟩ =
      GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
    have := hvalid.d_eq km1.val (Nat.lt_succ_of_lt km1.isLt); simpa using this
  have hh529 : s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩ =
      GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := by
    have := hvalid.d_eq (k + 1) (Nat.succ_lt_succ hk); simpa using this
  have hdk_nat_pos : 0 < s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ := hdk_eq ▸ hdk_pos
  have hδden_int_pos : (0 : Int) < Int.ofNat 4 := by
    show (0 : Int) < ((4 : Nat) : Int)
    exact_mod_cast hδden_pos
  have hsq_lt :
      Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
            Int.ofNat (s.d.get ⟨k - 1, Nat.lt_succ_of_lt hkm1lt⟩) +
          ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩) ^ 2 <
      (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 := by
    have hsq_nn : (0 : Int) ≤ (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 :=
      sq_nonneg _
    have h_bound :
        (3 : Int) * (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 ≤
          Int.ofNat 4 * (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2 :=
      Int.mul_le_mul_of_nonneg_right hδ_le_one hsq_nn
    exact Int.lt_of_mul_lt_mul_left (hfail.trans_le h_bound) (le_of_lt hδden_int_pos)
  have hvalid' : (s.swapStep k).Valid := swapStep_valid s k hind hvalid
  have hswap_d_at_k :
      ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Nat) =
        GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) k
          (Nat.le_of_lt hk) := by
    have := hvalid'.d_eq k (Nat.lt_succ_of_lt hk)
    simpa [swapStep_b_eq s k hk hk0] using this
  have hB_via_valid :
      ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩ : Int) =
        GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := by
    have h := hvalid.ν_eq kFin.val km1.val kFin.isLt km1.isLt
      (by show k - 1 < k; omega)
    simpa [GramSchmidt.entry, Matrix.row, gapH176] using h
  have hprod :=
    GramSchmidt.Int.gramDet_rowSwap_adjacent_pivot_product (b := s.b)
      (km1 := km1) (k := kFin) (by show k - 1 + 1 = k; omega)
  have hdk'_mul_dk :
      ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) *
        (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) =
      Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
            Int.ofNat (s.d.get ⟨k - 1, Nat.lt_succ_of_lt hkm1lt⟩) +
          ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩) ^ 2 := by
    have hprod' :
        ((GramSchmidt.Int.gramDet (Matrix.rowSwap s.b km1 kFin) k
            (Nat.le_of_lt hk) : Nat) : Int) *
          ((GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) : Nat) : Int) =
        ((GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) : Nat) : Int) *
            ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
          (GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1) ^ 2 := hprod
    show ((s.swapStep k).d.get _ : Nat) * ((s.d.get _ : Nat) : Int) =
      ((s.d.get _ : Nat) : Int) * ((s.d.get _ : Nat) : Int) +
        ((s.ν.getRow kFin).get _) ^ 2
    rw [hdk_eq, hh530, hh529]
    rw [show ((s.ν.getRow kFin).get ⟨k - 1, hkm1lt⟩ : Int) =
        GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 from
        hB_via_valid]
    rw [hswap_d_at_k]
    show ((GramSchmidt.Int.gramDet
        (Matrix.rowSwap s.b (GramSchmidt.prevRow kFin hk0) kFin) k
        (Nat.le_of_lt hk) : Nat) : Int) *
        ((GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) : Nat) : Int) = _
    rw [hkm1Pred_eq]
    exact hprod'
  have hdk_int_pos : (0 : Int) < Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩) := by
    show (0 : Int) < ((s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Nat) : Int)
    exact_mod_cast hdk_nat_pos
  simp only [Int.ofNat_eq_natCast] at hdk'_mul_dk hfail
  have hpivotInt :
      4 * ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) <
        3 * (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) := by
    have hprodFail :
        (4 * ((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int)) *
            (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) <
        (3 * (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int)) *
            (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) := by
      calc
        _ = 4 * (((s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) *
              (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int)) := by ring
        _ = 4 * _ := by rw [hdk'_mul_dk]
        _ < 3 * (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ : Int) ^ 2 := hfail
        _ = _ := by ring
    exact Int.lt_of_mul_lt_mul_right hprodFail (le_of_lt hdk_int_pos)
  have hpivot :
      4 * (s.swapStep k).d.get ⟨k, Nat.lt_succ_of_lt hk⟩ <
        3 * s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ := by
    exact_mod_cast hpivotInt
  have hd_off_pivot : ∀ (i : Nat) (hi : i < n + 1), i ≠ k →
      (s.swapStep k).d.get ⟨i, hi⟩ = s.d.get ⟨i, hi⟩ := by
    intro i hi hik
    unfold swapStep
    rw [dif_pos hk, dif_pos hk0]
    exact Vector.getElem_set_ne (Nat.lt_succ_of_lt hk) hi (fun h => hik h.symm)
  unfold potential
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  have hkm1_lt_nsub : k - 1 < n - 1 := by omega
  let i₀ : Fin (n - 1) := ⟨k - 1, hkm1_lt_nsub⟩
  have hi₀_mem : i₀ ∈ List.finRange (n - 1) := List.mem_finRange _
  have hi₀_plus : i₀.val + 1 = k := by show k - 1 + 1 = k; omega
  let g : Fin (n - 1) → Nat := fun i =>
    (s.swapStep k).d.get
      ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩
  let f : Fin (n - 1) → Nat := fun i =>
    s.d.get
      ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩
  have hfg_eq : ∀ i ∈ List.finRange (n - 1), i ≠ i₀ → f i = g i := by
    intro i _ hi
    have hindex_ne : i.val + 1 ≠ k := by
      intro h
      apply hi
      apply Fin.eq_of_val_eq
      show i.val = k - 1
      omega
    show s.d.get _ = (s.swapStep k).d.get _
    exact (hd_off_pivot (i.val + 1) _ hindex_ne).symm
  have hglt : 4 * g i₀ < 3 * f i₀ := by
    show 4 * (s.swapStep k).d.get _ < 3 * s.d.get _
    have hidx : (⟨i₀.val + 1,
        Nat.succ_lt_succ (Nat.lt_of_lt_of_le i₀.isLt (Nat.sub_le n 1))⟩ : Fin (n + 1)) =
      ⟨k, Nat.lt_succ_of_lt hk⟩ := Fin.eq_of_val_eq hi₀_plus
    rw [hidx]
    exact hpivot
  have hf_pos : ∀ i ∈ List.finRange (n - 1), 0 < f i := by
    intro i _
    show 0 < s.d.get _
    have hi_succ_le : i.val + 1 ≤ n := by have := i.isLt; omega
    have hdpos : 0 < GramSchmidt.Int.gramDet s.b (i.val + 1) hi_succ_le :=
      hind ⟨i.val, by omega⟩
    have h := hvalid.d_eq (i.val + 1)
      (Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)))
    rw [h]
    exact hdpos
  exact gapH375 (List.nodup_finRange _) hi₀_mem f g hf_pos hfg_eq hglt 1
    Nat.one_pos
theorem potential_pos (s : LLLState n m) (hind : s.b.independent) (hvalid : s.Valid) :
    0 < s.potential := by
  unfold potential
  rw [Fin.foldl_eq_finRange_foldl]
  apply gapH445 _ _ 1 (by decide)
  intro i _
  rw [hvalid.d_eq]
  exact hind ⟨i.val, by have := i.isLt; omega⟩
theorem two_mul_cube_lt_of_four_mul_lt_three_mul {a b : Nat} (h : 4 * a < 3 * b) :
    2 * a ^ 3 < b ^ 3 := by
  have hp : (4 * a) ^ 3 < (3 * b) ^ 3 := Nat.pow_lt_pow_left h (by decide)
  norm_num [mul_pow] at hp
  omega
theorem log2_lt_of_two_mul_lt {a b : Nat} (ha : 0 < a) (h : 2 * a < b) :
    a.log2 < b.log2 := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := by omega
  apply Nat.lt_of_succ_le
  apply (Nat.le_log2 hb0).mpr
  calc
    2 ^ (a.log2 + 1) = 2 * 2 ^ a.log2 := by rw [pow_succ, Nat.mul_comm]
    _ ≤ 2 * a := Nat.mul_le_mul_left 2 (Nat.log2_self_le ha0)
    _ ≤ b := Nat.le_of_lt h
theorem sizeReduce_logPotential (s : LLLState n m) (k : Nat) :
    (s.sizeReduce k).logPotential = s.logPotential := by
  simp only [logPotential, sizeReduce_potential]
theorem swapStep_logPotential_lt (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) (hk0 : 0 < k) (hk : k < n)
    (δ : Rat) (hδ : δ = 3 / 4)
    (hfail :
      Int.ofNat δ.den *
          (Int.ofNat (s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩) *
              Int.ofNat (s.d.get ⟨k - 1,
                Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk)⟩) +
            ((s.ν.getRow ⟨k, hk⟩).get
                ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk⟩) ^ 2) <
        δ.num * (Int.ofNat (s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩)) ^ 2) :
    (s.swapStep k).logPotential < s.logPotential := by
  subst δ
  have hn : (3 / 4 : Rat).num = 3 := by
    convert (Rat.num_div_eq_of_coprime (a := 3) (b := 4) (by norm_num) (by norm_num)) using 1 <;> norm_num
  have hd : (3 / 4 : Rat).den = 4 := by
    have h := Rat.den_div_eq_of_coprime (a := 3) (b := 4) (by norm_num) (by norm_num)
    norm_num at h ⊢
  rw [hn, hd] at hfail
  have hratio := swapStep_potential_three_fourths s k hind hvalid hk0 hk hfail
  have hswapValid := swapStep_valid s k hind hvalid
  have hswapIndependent := swapStep_independent s k hind hvalid hk0 hk
  have hpos := potential_pos (s.swapStep k) hswapIndependent hswapValid
  have hcubePos : 0 < (s.swapStep k).potential ^ 3 := Nat.pow_pos hpos
  have hlog := log2_lt_of_two_mul_lt hcubePos
    (two_mul_cube_lt_of_four_mul_lt_three_mul hratio)
  exact Nat.add_lt_add_right hlog 1
end Internal.LLLState
end Hex
end
section
namespace Hex
open Hex.Internal
namespace Internal.LLLState
theorem lllLoop_isLLLReduced_of_logMeasure
    (δ : Rat) (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hδfixed : δ = 3 / 4) :
    ∀ (fuel : Nat) (s : LLLState n m) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n),
      s.Valid → s.b.independent → prefixLLLReduced s.b k δ →
      s.logPotential * (n + 1) + (n - k) < fuel →
      isLLLReduced (lllLoop s k δ hδ hδ' hk hkn fuel) δ (1 / 2) := by
  intro fuel
  induction fuel with
  | zero =>
    intros _ _ _ _ _ _ _ hmeasure
    exact absurd hmeasure (Nat.not_lt_zero _)
  | succ f ih =>
    intros s k hk hkn hvalid hind hpre hmeasure
    by_cases hkn_eq : k = n
    · subst hkn_eq
      rw [lllLoop_eq_b_at_n]
      exact prefixLLLReduced_to_isLLLReduced s.b δ hpre
    · have hlt : k < n := Nat.lt_of_le_of_ne hkn hkn_eq
      have hh558 : (s.sizeReduce k).Valid := sizeReduce_valid s k hvalid
      have hsR_ind : (s.sizeReduce k).b.independent :=
        sizeReduce_independent s k hind hvalid hh558
      have hsR_pot : (s.sizeReduce k).logPotential = s.logPotential := sizeReduce_logPotential s k
      have hsR_pre : prefixLLLReduced (s.sizeReduce k).b k δ :=
        sizeReduce_prefixLLLReduced s k δ hpre
      have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      rw [lllLoop_succ_eq_body s k δ hδ hδ' hk hkn hlt]
      dsimp only [lllLoopBody]
      split_ifs with hcond
      ·
        have hpre_advance : prefixLLLReduced (s.sizeReduce k).b (k + 1) δ := by
          apply prefixLLLReduced.advance hlt hsR_pre
          · intro j hj
            exact sizeReduce_size_reduced s k hlt hvalid hind j hj
          · intro _hk0
            have hiff := HexLLLTheory.lovasz_check_iff_isLLLReduced_pair
              (s.sizeReduce k) k hlt hk0 hh558 hsR_ind hδ hδ'
            exact hiff.mp hcond
        apply ih (s.sizeReduce k) (k + 1) (Nat.succ_pos k) (Nat.succ_le_of_lt hlt)
          hh558 hsR_ind hpre_advance
        rw [hsR_pot]
        have : n - (k + 1) + 1 ≤ n - k := by omega
        omega
      ·
        push Not at hcond
        have hpot_lt :
            ((s.sizeReduce k).swapStep k).logPotential < (s.sizeReduce k).logPotential :=
          swapStep_logPotential_lt (s.sizeReduce k) k hsR_ind hh558 hk0 hlt
            δ hδfixed (by convert hcond using 2)
        have hsS_pot_lt : ((s.sizeReduce k).swapStep k).logPotential < s.logPotential := by
          rw [← hsR_pot]; exact hpot_lt
        have hsS_valid : ((s.sizeReduce k).swapStep k).Valid :=
          swapStep_valid (s.sizeReduce k) k hsR_ind hh558
        have hsS_ind : ((s.sizeReduce k).swapStep k).b.independent :=
          swapStep_independent (s.sizeReduce k) k hsR_ind hh558 hk0 hlt
        have hsS_pre :
            prefixLLLReduced ((s.sizeReduce k).swapStep k).b (max (k - 1) 1) δ :=
          swapStep_prefixLLLReduced (s.sizeReduce k) k δ hsR_pre
        have hk'n : max (k - 1) 1 ≤ n :=
          (Nat.max_le).2 ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩
        apply ih ((s.sizeReduce k).swapStep k) (max (k - 1) 1)
          (Nat.le_max_right (k - 1) 1) hk'n hsS_valid hsS_ind hsS_pre
        have hmeasure_le : s.logPotential * (n + 1) + (n - k) ≤ f := Nat.lt_succ_iff.mp hmeasure
        have hspot_pos : 0 < s.logPotential := by
          have : 0 ≤ ((s.sizeReduce k).swapStep k).logPotential := Nat.zero_le _
          omega
        have hmul_bound :
            ((s.sizeReduce k).swapStep k).logPotential * (n + 1) ≤
              (s.logPotential - 1) * (n + 1) :=
          Nat.mul_le_mul_right (n + 1)
            (by omega : ((s.sizeReduce k).swapStep k).logPotential ≤ s.logPotential - 1)
        have hsub_mul : (s.logPotential - 1) * (n + 1) + (n + 1) = s.logPotential * (n + 1) := by
          have hp : s.logPotential = (s.logPotential - 1) + 1 := by omega
          calc (s.logPotential - 1) * (n + 1) + (n + 1)
              = ((s.logPotential - 1) + 1) * (n + 1) := by ring
            _ = s.logPotential * (n + 1) := by rw [← hp]
        have h_fpos : 0 < f := by
          have h1 : 1 ≤ s.logPotential * (n + 1) := by
            calc 1 = 1 * (n + 1) - n := by omega
              _ ≤ s.logPotential * (n + 1) - n := by
                have := Nat.mul_le_mul_right (n + 1) hspot_pos
                omega
              _ ≤ s.logPotential * (n + 1) := Nat.sub_le _ _
          omega
        have hnk' : n - max (k - 1) 1 ≤ n := Nat.sub_le n _
        show ((s.sizeReduce k).swapStep k).logPotential * (n + 1) + (n - max (k - 1) 1) < f
        omega
theorem lllLoop_isLLLReduced_logarithmicFuel (s : LLLState n m) (hn : 1 ≤ n)
    (hvalid : s.Valid) (hind : s.b.independent)
    (hpre : prefixLLLReduced s.b 1 (3 / 4)) :
    isLLLReduced
      (lllLoop s 1 (3 / 4) (by norm_num) (by norm_num) (Nat.le_refl 1) hn
        s.logarithmicFuel) (3 / 4) (1 / 2) := by
  apply lllLoop_isLLLReduced_of_logMeasure _ _ _ rfl _ s 1 _ hn hvalid hind hpre
  unfold logarithmicFuel
  have hmul : (s.logPotential + 1) * (n + 1) =
      s.logPotential * (n + 1) + (n + 1) := by ring
  omega
end Internal.LLLState
end Hex
end
section
section
namespace HexLLLTheory
private theorem foldl_finRange_eq_sum {R : Type*} [AddCommMonoid R] {n : Nat}
    (f : Fin n → R) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 = ∑ i, f i := by
  rw [← List.foldl_map, ← List.sum_eq_foldl,
    ← List.sum_toFinset f (List.nodup_finRange n), List.toFinset_finRange]
@[simp]
theorem norm_sq_intRowToEuclidean (row : Vector Int m) :
    ‖intRowToEuclidean row‖ ^ 2 = ((row.normSq : Int) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [intRowToEuclidean, PiLp.toLp_apply]
  unfold Vector.normSq Vector.dotProduct
  rw [foldl_finRange_eq_sum]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i _
  ring
end HexLLLTheory
end
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.RationalGramSchmidt
open InnerProductSpace
open scoped BigOperators
noncomputable section
end
noncomputable section
theorem inputVectors_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (column : Fin dimension) :
    realVec (inputVectors basis column)=IntegerBasis.realBasis basis hdet column := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp [realVec,inputVectors]
theorem inputVectors_independent {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    LinearIndependent ℝ (fun position => realVec (inputVectors basis position)) := by
  simpa only [inputVectors_real basis hdet] using (IntegerBasis.realBasis basis hdet).linearIndependent
end
noncomputable section
end
end InfoLossLAR.WorstCase.RationalGramSchmidt
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.RationalGramSchmidt
open InnerProductSpace
open scoped BigOperators
noncomputable section
theorem prefixGram_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).map (fun value => (value : ℝ))=
      Matrix.gram ℝ (fun index => realVec (inputVectors basis (Fin.castLE hsteps index))) := by
  ext first second
  simp only [prefixGram,Matrix.map_apply,Matrix.gram_apply,realVec,inputVectors,PiLp.inner_apply,
    Real.inner_apply,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
theorem prefixGram_det_ne_zero {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).det ≠ 0 := by
  have independent : LinearIndependent ℝ
      (fun index : Fin steps => realVec (inputVectors basis (Fin.castLE hsteps index))) :=
    (inputVectors_independent basis hdet).comp (Fin.castLE hsteps) (Fin.castLE_injective hsteps)
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr independent
  rw [←prefixGram_real,←Int.cast_det] at h
  exact_mod_cast h
end
noncomputable section
end
end InfoLossLAR.WorstCase.RationalGramSchmidt
end
section
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n m : Nat}
theorem current_independent (b : Hex.Matrix Int n m) (hind : b.independent) :
    (current b).independent := by
  unfold current
  split_ifs with hn
  · exact LLLState.lllLoop_independent _ _ _ _ (LLLState.ofBasis b) 1 _ hn
      (HexLLLTheory.LLLState.ofBasis_valid b) hind
  · exact hind
theorem current_reduced (b : Hex.Matrix Int n m) (hn : 1 ≤ n) (hind : b.independent) :
    Hex.isLLLReduced (current b) (3 / 4) (1 / 2) := by
  unfold current
  rw [dif_pos hn]
  exact LLLState.lllLoop_isLLLReduced_logarithmicFuel _ hn
    (HexLLLTheory.LLLState.ofBasis_valid b) hind (Hex.prefixLLLReduced_one b _)
theorem input_leadingGram (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    HexMatrixTheory.matrixEquiv (Hex.GramSchmidt.leadingGramMatrixInt (input B) k hk) =
      RationalGramSchmidt.prefixGram B k hk := by
  ext i j
  simp only [HexMatrixTheory.matrixEquiv_apply, Hex.GramSchmidt.leadingGramMatrixInt,
    Hex.Matrix.getElem_ofFn, HexMatrixTheory.dotProduct_eq, dotProduct,
    RationalGramSchmidt.prefixGram, HexMatrixTheory.vectorEquiv_apply,
    Hex.Matrix.getElem_row, input, Hex.GramSchmidt.liftFinLE]
  apply Finset.sum_congr rfl
  intro row _
  rfl
theorem input_gramDet (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    (Hex.GramSchmidt.Int.gramDet (input B) k hk : ℤ) =
      (RationalGramSchmidt.prefixGram B k hk).det := by
  change Int.ofNat (Hex.GramSchmidt.Int.gramDet (input B) k hk) = _
  rw [←Hex.GramSchmidt.Int.leadingGramMatrixInt_det_eq_gramDet_int]
  have h := HexMatrixTheory.det_eq (Hex.GramSchmidt.leadingGramMatrixInt (input B) k hk)
  rw [input_leadingGram] at h
  simpa only [Hex.Matrix.det, Hex.Matrix.detTerm, Hex.Matrix.detSign, Hex.Matrix.detProduct] using h
theorem input_independent (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det ≠ 0) :
    (input B).independent := by
  intro i
  have hn0 := RationalGramSchmidt.prefixGram_det_ne_zero B hdet (i.val+1)
    (Nat.succ_le_of_lt i.isLt)
  have hnn := Hex.GramSchmidt.Int.leadingGramMatrixInt_det_nonneg
    (input B) (i.val+1) (Nat.succ_le_of_lt i.isLt)
  have hd := HexMatrixTheory.det_eq (Hex.GramSchmidt.leadingGramMatrixInt (input B) (i.val+1) (Nat.succ_le_of_lt i.isLt))
  rw [input_leadingGram] at hd
  have hd' : Hex.Matrix.det (Hex.GramSchmidt.leadingGramMatrixInt (input B) (i.val+1) (Nat.succ_le_of_lt i.isLt)) =
      (RationalGramSchmidt.prefixGram B (i.val+1) (Nat.succ_le_of_lt i.isLt)).det := by
    simpa only [Hex.Matrix.det, Hex.Matrix.detTerm, Hex.Matrix.detSign, Hex.Matrix.detProduct] using hd
  rw [hd'] at hnn
  have hpos : 0 < (RationalGramSchmidt.prefixGram B (i.val+1) _).det :=
    lt_of_le_of_ne hnn (Ne.symm hn0)
  have hc := input_gramDet B (i.val+1) (Nat.succ_le_of_lt i.isLt)
  have : (0 : ℤ) < (Hex.GramSchmidt.Int.gramDet (input B) (i.val+1) (Nat.succ_le_of_lt i.isLt) : ℤ) := by
    rw [hc]; exact hpos
  exact_mod_cast this
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n : Nat}
theorem input_basis (B : Matrix (Fin n) (Fin n) ℤ) : input (basis B) = current (input B) := by
  apply Hex.Matrix.ext_getElem
  intro i j
  simp only [input,Hex.Matrix.getElem_ofFn,basis,Matrix.transpose_apply,
    HexMatrixTheory.matrixEquiv_apply]
theorem vecMul_input (B : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    Hex.Matrix.vecMul (Vector.ofFn z) (input B) = Vector.ofFn (B.mulVec z) := by
  apply HexMatrixTheory.vectorEquiv.injective
  rw [HexMatrixTheory.vectorEquiv_vecMul]
  ext row
  simp only [Fintype.linearCombination_apply,Finset.sum_apply,Pi.smul_apply,
    HexMatrixTheory.matrixEquiv_apply,Hex.Matrix.getElem_row,input,
    Hex.Matrix.getElem_ofFn,HexMatrixTheory.vectorEquiv_apply,Vector.getElem_ofFn,
    zsmul_eq_mul,Matrix.row,Pi.mul_apply,Pi.intCast_apply,Fin.getElem_fin,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  change (z j : ℤ)*(Hex.Matrix.ofFn (fun i j => B j i))[j][row] = B row j*z j
  rw [Hex.Matrix.getElem_ofFn]
  exact mul_comm _ _
theorem rowToEuclidean_vecMul_input (B : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    HexLLLTheory.intRowToEuclidean (Hex.Matrix.vecMul (Vector.ofFn z) (input B)) =
      latVec B z := by
  rw [vecMul_input]
  ext row
  simp only [HexLLLTheory.intRowToEuclidean,latVec,WithLp.ofLp_toLp,Fin.getElem_fin,Vector.getElem_ofFn]
theorem prefixGram_full (B : Matrix (Fin n) (Fin n) ℤ) :
    RationalGramSchmidt.prefixGram B n (le_refl n) = B.transpose*B := by
  ext i j
  simp only [RationalGramSchmidt.prefixGram,Matrix.mul_apply,Matrix.transpose_apply]
  rfl
theorem det_ne_zero_of_input_independent (B : Matrix (Fin n) (Fin n) ℤ)
    (hind : (input B).independent) : B.det ≠ 0 := by
  cases n with
  | zero => simp
  | succ d =>
    have hpos := hind ⟨d,Nat.lt_succ_self d⟩
    have hc := input_gramDet B (d+1) (le_refl _)
    rw [prefixGram_full,Matrix.det_mul,Matrix.det_transpose] at hc
    intro hdet
    rw [hdet,zero_mul] at hc
    have hzero : Hex.GramSchmidt.Int.gramDet (input B) (d+1) (le_refl _) = 0 := by
      exact_mod_cast hc
    exact (Nat.ne_of_gt hpos) hzero
theorem basis_det_ne_zero (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det ≠ 0) :
    (basis B).det ≠ 0 := by
  apply det_ne_zero_of_input_independent
  rw [input_basis]
  exact current_independent _ (input_independent B hdet)
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n m : Nat}
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators Classical
noncomputable def gapGSCoordinates {n m : ℕ} (b : Hex.Matrix ℤ n m) (z : Vector ℤ n) : Vector ℚ n :=
  Hex.Matrix.vecMul (z.map (fun a : ℤ => (a : ℚ))) (Hex.GramSchmidt.Int.coeffs b)
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase.NativeLLL
open scoped BigOperators Classical
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.RegevSketch
theorem finiteGap_triangle_abs_bound {n : ℕ} {K : ℚ} (hK : 0 ≤ K)
    (z : Fin n → ℤ)
    (htri : ∀ i : Fin n, |(z i : ℚ)| ≤ K + ∑ j ∈ Finset.univ.filter (fun j => i < j), |(z j : ℚ)|) :
    ∀ i : Fin n, |(z i : ℚ)| ≤ K * ((n : ℚ) + 1)^n := by
  classical
  have hbase : 1 ≤ (n : ℚ) + 1 := le_add_of_nonneg_left (by positivity)
  have haux (d : ℕ) : ∀ i : Fin n, n - i.val = d →
      |(z i : ℚ)| ≤ K * ((n : ℚ) + 1)^d := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hi
      have hd : 0 < d := by omega
      have hcoeff (j : Fin n) (hj : j ∈ Finset.univ.filter (fun k => i < k)) :
          |(z j : ℚ)| ≤ K * ((n : ℚ) + 1)^(d - 1) := by
        have hj' : i.val < j.val := (Finset.mem_filter.mp hj).2
        have h1 : n - j.val < d := by omega
        have h2 : n - j.val ≤ d - 1 := by omega
        apply (ih (n - j.val) h1 j rfl).trans
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase h2) hK
      have hsum := Finset.sum_le_sum hcoeff
      have hcard : (Finset.univ.filter (fun j : Fin n => i < j)).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun j : Fin n => i < j))
      have hpow : 1 ≤ ((n : ℚ) + 1)^(d - 1) := one_le_pow₀ hbase
      have hK' := mul_le_mul_of_nonneg_left hpow hK
      have hterm : 0 ≤ K * ((n : ℚ) + 1)^(d - 1) := by positivity
      have hcard' : ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℚ) ≤ n := by exact_mod_cast hcard
      apply (htri i).trans
      calc
        K + ∑ j ∈ Finset.univ.filter (fun j => i < j), |(z j : ℚ)|
            ≤ K + (∑ _j ∈ Finset.univ.filter (fun j : Fin n => i < j), K * ((n : ℚ) + 1)^(d - 1)) :=
              add_le_add_right hsum K
        _ ≤ K * ((n : ℚ) + 1)^(d - 1) + n * (K * ((n : ℚ) + 1)^(d - 1)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact add_le_add (by simpa using hK') (mul_le_mul_of_nonneg_right hcard' hterm)
        _ = K * ((n : ℚ) + 1)^d := by
          conv_rhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
          ring
  intro i
  apply (haux (n - i.val) i rfl).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.sub_le n i.val)) hK
theorem finiteGap_size_reduced_coeff_bound {n : ℕ} {K : ℚ} (hK : 0 ≤ K)
    (z : Fin n → ℤ) (w : Fin n → ℚ) (μ : Fin n → Fin n → ℚ)
    (hw : ∀ i, |w i| ≤ K)
    (hμ : ∀ i j, i < j → |μ j i| ≤ 1)
    (hexp : ∀ i, w i = (z i : ℚ) + ∑ j ∈ Finset.univ.filter (fun j => i < j),
      (z j : ℚ) * μ j i) :
    ∀ i, |(z i : ℚ)| ≤ K * ((n : ℚ) + 1)^n := by
  apply finiteGap_triangle_abs_bound hK z
  intro i
  have hzi : (z i : ℚ) = w i - ∑ j ∈ Finset.univ.filter (fun j => i < j),
      (z j : ℚ) * μ j i := by linarith only [hexp i]
  rw [hzi]
  apply (abs_sub _ _).trans
  apply add_le_add (hw i)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hμ i j (Finset.mem_filter.mp hj).2)
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option autoImplicit false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.RegevSketch
theorem finiteGap_hex_coeff_expansion {n m : ℕ} (b : Hex.Matrix ℤ n m)
    (z : Fin n → ℤ) (i : Fin n) :
    (Hex.Matrix.vecMul (Vector.map (fun k : ℤ => (k : ℚ)) (Vector.ofFn z))
        (Hex.GramSchmidt.Int.coeffs b))[i] =
      (z i : ℚ) + ∑ j ∈ Finset.univ.filter (fun j => i < j),
        (z j : ℚ) * (Hex.GramSchmidt.Int.coeffs b)[j][i] := by
  classical
  let μ := Hex.GramSchmidt.Int.coeffs b
  have hsum : (Hex.Matrix.vecMul (Vector.map (fun k : ℤ => (k : ℚ)) (Vector.ofFn z)) μ)[i] =
      ∑ j : Fin n, (z j : ℚ) * μ[j][i] := by
    change HexMatrixTheory.vectorEquiv (Hex.Matrix.vecMul
      (Vector.map (fun k : ℤ => (k : ℚ)) (Vector.ofFn z)) μ) i = _
    rw [HexMatrixTheory.vectorEquiv_vecMul]
    rw [Fintype.linearCombination_apply, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, HexMatrixTheory.matrixEquiv_apply, HexMatrixTheory.vectorEquiv_apply,
      Vector.getElem_map, Vector.getElem_ofFn, smul_eq_mul, Fin.getElem_fin, Matrix.row]
  change (Hex.Matrix.vecMul _ μ)[i] = (z i : ℚ) + ∑ j ∈ Finset.univ.filter (fun j => i < j),
    (z j : ℚ) * μ[j][i]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdiag : μ[i][i] = 1 := Hex.GramSchmidt.Int.coeffs_diag b i.val i.isLt
  rw [hdiag, mul_one]
  congr 1
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_erase.mpr ⟨(ne_of_gt (Finset.mem_filter.mp hj).2), Finset.mem_univ _⟩
  · intro j hj hji
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hnlt : ¬ i < j := fun h => hji (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hnlt) hne
    have hzero : μ[j][i] = 0 := Hex.GramSchmidt.Int.coeffs_upper b j.val i.val j.isLt i.isLt hjlt
    rw [hzero, mul_zero]
theorem finiteGap_hex_coeff_bound {n m : ℕ} (b : Hex.Matrix ℤ n m)
    (hred : Hex.isLLLReduced b (3 / 4) (1 / 2)) {K : ℚ} (hK : 0 ≤ K) (z : Fin n → ℤ)
    (hw : ∀ i : Fin n, |(Hex.Matrix.vecMul (Vector.map (fun k : ℤ => (k : ℚ)) (Vector.ofFn z))
        (Hex.GramSchmidt.Int.coeffs b))[i]| ≤ K) :
    ∀ i, |(z i : ℚ)| ≤ K * ((n : ℚ) + 1)^n := by
  apply finiteGap_size_reduced_coeff_bound hK z
    (fun i => (Hex.Matrix.vecMul (Vector.map (fun k : ℤ => (k : ℚ)) (Vector.ofFn z))
      (Hex.GramSchmidt.Int.coeffs b))[i])
    (fun j i => (Hex.GramSchmidt.Int.coeffs b)[j][i]) hw
  · intro i j hij
    let c : ℚ := (Hex.GramSchmidt.Int.coeffs b)[j][i]
    change |c| ≤ 1
    have hsq : c * c ≤ (1 / 2 : ℚ) * (1 / 2 : ℚ) := hred.1 j.val i.val j.isLt hij
    have hhalf : |c| ≤ (1 / 2 : ℚ) := by
      apply (sq_le_sq₀ (abs_nonneg c) (by norm_num : (0 : ℚ) ≤ 1 / 2)).mp
      simpa [sq_abs, pow_two] using hsq
    norm_num at hhalf ⊢
    exact hhalf.trans (by norm_num)
  · exact finiteGap_hex_coeff_expansion b z
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.NativeLLL
open scoped BigOperators


set_option linter.all false
set_option maxHeartbeats 2000000
open InfoLossLAR.WorstCase.RegevSketch
namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection
namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
end InfoLossLAR.WorstCase.GaussianPoissonSeries


/- Helper module Solutions.RegevBridgeNativeLLLVendor.HexGramSchmidt.Basic.Rat. -/
section P2MDyadicModule1

set_option autoImplicit true

public section

namespace Hex

namespace GramSchmidt.Rat

/-- Lower coefficient entries, with the dot product oriented to match
Mathlib's projection coefficient numerator. -/
theorem coeffs_lower_projection_comm (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs b) i j =
      (if ((basis b).row j).dotProduct ((basis b).row j) = 0 then 0
       else
        ((basis b).row j).dotProduct (b.row i) /
          ((basis b).row j).dotProduct ((basis b).row j)) := by
  rw [coeffs_lower_projection (b := b) hji]
  by_cases hnorm : ((basis b).row j).dotProduct ((basis b).row j) = 0
  · simp [hnorm]
  · simp [hnorm, GramSchmidt.dot_comm_rat]

end GramSchmidt.Rat

end Hex

end

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule2

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

/-- The coefficient vector sent to the native program represents exactly
its target-defined lattice point `latVec basis value`. -/
theorem coefficient_point (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) :
    ((integerBasis basis hdet).equivFun.symm value : Space (dimension:=dimension))=latVec basis value := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,integerBasis_apply]
  ext row
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,latVec,Matrix.mulVec,dotProduct,
    Int.cast_sum,Int.cast_mul,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

/-- The Gaussian submodule is exactly the original worst-case target's
`L(B)=Bℤ^n`, with the original integer-basis convention. -/
theorem inputLattice_eq_target (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (inputLattice basis hdet : Set (Space (dimension:=dimension)))=InfoLossLAR.WorstCase.lattice basis := by
  ext point
  constructor
  · intro membership
    let value : inputLattice basis hdet := ⟨point,membership⟩
    refine ⟨(integerBasis basis hdet).equivFun value,?_⟩
    rw [←coefficient_point basis hdet,LinearEquiv.symm_apply_apply]
  · rintro ⟨value,rfl⟩
    rw [←coefficient_point basis hdet value]
    exact Subtype.prop _

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

theorem realVec_zero {dimension : ℕ} : realVec (0 : QVector dimension)=0 := by ext index;simp [realVec]

theorem realVec_add {dimension : ℕ} (left right : QVector dimension) : realVec (left+right)=realVec left+realVec right := by
  ext index
  exact Rat.cast_add _ _

theorem realVec_sub {dimension : ℕ} (left right : QVector dimension) : realVec (left-right)=realVec left-realVec right := by
  ext index
  exact Rat.cast_sub _ _

theorem realVec_smul {dimension : ℕ} (scalar : ℚ) (vector : QVector dimension) :
    realVec (scalar • vector)=(scalar : ℝ) • realVec vector := by
  ext index
  exact Rat.cast_mul _ _

theorem realVec_list_sum {dimension : ℕ} (vectors : List (QVector dimension)) :
    realVec vectors.sum=(vectors.map realVec).sum := by
  induction vectors with
  | nil => exact realVec_zero
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,realVec_add,ih]

theorem innerQ_real {dimension : ℕ} (left right : QVector dimension) :
    (innerQ left right : ℝ)=inner ℝ (realVec left) (realVec right) := by
  unfold innerQ realVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

def squaredNorm {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : ℚ := innerQ (orthogonal vectors index) (orthogonal vectors index)

noncomputable section

theorem projection_real {dimension : ℕ} (orthogonal current : QVector dimension) :
    realVec (projection orthogonal current)=
      (inner ℝ (realVec orthogonal) (realVec current)/‖realVec orthogonal‖^2) • realVec orthogonal := by
  rw [projection,realVec_smul,Rat.cast_div,innerQ_real,innerQ_real,real_inner_self_eq_norm_sq]

theorem orthogonalStep_real {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) :
    realVec (orthogonalStep previous current)=realVec current-
      ((previous.map realVec).map (fun orthogonal => (inner ℝ orthogonal (realVec current)/‖orthogonal‖^2) • orthogonal)).sum := by
  rw [orthogonalStep,realVec_sub,realVec_list_sum]
  simp only [List.map_map,Function.comp_def,projection_real]

private theorem sum_Iio_fin {count : ℕ} {Value : Type*} [AddCommMonoid Value]
    (index : Fin count) (function : Fin count → Value) :
    (∑ previous ∈ Finset.Iio index,function previous)=
      ∑ previous : Fin index.val,function ⟨previous.val,previous.isLt.trans index.isLt⟩ := by
  classical
  refine Finset.sum_bij (fun previous membership =>
    (⟨previous.val,show previous < index from Finset.mem_Iio.mp membership⟩ : Fin index.val)) ?_ ?_ ?_ ?_
  · intro previous membership
    exact Finset.mem_univ _
  · intro first hfirst second hsecond hequal
    exact Fin.ext (congrArg (fun value : Fin index.val => value.val) hequal)
  · intro previous membership
    refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,Finset.mem_Iio.mpr (show (⟨previous.val,previous.isLt.trans index.isLt⟩ : Fin count) < index from previous.isLt),?_⟩
    rfl
  · intro previous membership
    congr 1

/-- Every materialized rational cache prefix is exactly the ordinary real
Gram--Schmidt prefix after the actual rational-to-real embedding. -/
theorem cache_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (cache vectors steps).map realVec=List.ofFn (fun index : Fin steps =>
      gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hsteps index)) := by
  classical
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps<count := by omega
    let index : Fin count := ⟨steps,hstep⟩
    rw [cache,List.map_append,List.map_singleton,ih hprevious,List.ofFn_succ_last]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext previous
      congr 1
    · apply congrArg (fun value : Space dimension => [value])
      change realVec (orthogonalStep (cache vectors steps) (if h : steps<count then vectors ⟨steps,h⟩ else 0))=
        gramSchmidt ℝ (fun position => realVec (vectors position)) index
      rw [dif_pos hstep,orthogonalStep_real,ih hprevious]
      simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
      have h := gramSchmidt_def'' ℝ (fun position => realVec (vectors position)) index
      rw [sum_Iio_fin] at h
      have hequal : (∑ previous : Fin steps,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous)‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))=
          ∑ previous : Fin index.val,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩)
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩ := rfl
      rw [hequal]
      exact sub_eq_iff_eq_add.mpr h

theorem orthogonal_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    realVec (orthogonal vectors index)=gramSchmidt ℝ (fun position => realVec (vectors position)) index := by
  have h := congrArg (fun values : List (Space dimension) => values.getD index.val (realVec (0 : QVector dimension)))
    (cache_real vectors count (le_refl count))
  rw [List.getD_map] at h
  simpa [orthogonal,index.isLt] using h

theorem squaredNorm_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    (squaredNorm vectors index : ℝ)=‖gramSchmidt ℝ (fun position => realVec (vectors position)) index‖^2 := by
  rw [squaredNorm,innerQ_real,orthogonal_real,real_inner_self_eq_norm_sq]

end

noncomputable section

end

def entryMass {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : ℚ :=
  ∑ row,∑ column,|(basis row column : ℚ)|

def initialWidth {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (base : ℚ) : ℚ := base*(1+entryMass basis)

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeRationalGramSchmidtGeometry. -/
section P2MDyadicModule4

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

/-- Exact rational upper-triangular change from original input columns to
its materialized orthogonal cache. -/
def upper {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) : ℚ :=
  innerQ (orthogonal vectors row) (vectors column)/squaredNorm vectors row

noncomputable section

theorem inner_gramSchmidt_original {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    inner ℝ (gramSchmidt ℝ vectors index) (vectors index)=‖gramSchmidt ℝ vectors index‖^2 := by
  conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [inner_add_right]
  suffices inner ℝ (gramSchmidt ℝ vectors index)
      (∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ vectors previous) (vectors index)/‖gramSchmidt ℝ vectors previous‖^2) •
          gramSchmidt ℝ vectors previous)=0 by
    rw [this,add_zero,real_inner_self_eq_norm_sq]
  simp only [inner_sum,inner_smul_right]
  apply Finset.sum_eq_zero
  intro previous membership
  rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]

theorem upper_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) :
    (upper vectors row column : ℝ)=
      inner ℝ (gramSchmidt ℝ (fun index => realVec (vectors index)) row) (realVec (vectors column))/
        ‖gramSchmidt ℝ (fun index => realVec (vectors index)) row‖^2 := by
  rw [upper,Rat.cast_div,innerQ_real,orthogonal_real,squaredNorm_real]

theorem upper_diagonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index))) (index : Fin count) :
    upper vectors index index=1 := by
  have hreal : (upper vectors index index : ℝ)=1 := by
    rw [upper_real,inner_gramSchmidt_original]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero index independent)))
  exact_mod_cast hreal

theorem upper_triangular {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) (before : column < row) :
    upper vectors row column=0 := by
  have hreal : (upper vectors row column : ℝ)=0 := by
    rw [upper_real,gramSchmidt_inv_triangular ℝ (fun index => realVec (vectors index)) before,zero_div]
  exact_mod_cast hreal

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeNativeLLLOriginalBasis. -/
section P2MDyadicModule5

set_option autoImplicit true

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeLLL

open Hex.Internal

open scoped BigOperators

variable {n : Nat}

theorem basis_inputLattice_eq (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det ≠ 0) :
    IntegerBasis.inputLattice (basis B) (basis_det_ne_zero B hdet) = IntegerBasis.inputLattice B hdet := by
  apply SetLike.coe_injective
  rw [IntegerBasis.inputLattice_eq_target,IntegerBasis.inputLattice_eq_target,basis_lattice_eq]

end InfoLossLAR.WorstCase.NativeLLL

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeNativeLLLVendor.HexGramSchmidtTheory.Basic. -/
section P2MDyadicModule6

set_option autoImplicit true

public section

set_option maxHeartbeats 1600000

namespace Hex

namespace GramSchmidtTheory

/-- `rowToEuclidean` sends the zero row to the zero vector. -/
@[simp, grind =]
theorem rowToEuclidean_zero :
    rowToEuclidean (0 : Vector Rat m) = 0 := by
  ext j
  simp [rowToEuclidean]

/-- `rowToEuclidean` is additive: it sends a rowwise sum to the sum of converted
vectors. -/
@[simp, grind =]
theorem rowToEuclidean_add (a b : Vector Rat m) :
    rowToEuclidean (a + b) = rowToEuclidean a + rowToEuclidean b := by
  ext j
  simp [rowToEuclidean]

/-- `rowToEuclidean` is rational-linear: it sends a rational scalar multiple to the
corresponding real scalar multiple of the converted vector. -/
@[simp, grind =]
theorem rowToEuclidean_smul (c : Rat) (row : Vector Rat m) :
    rowToEuclidean (c • row) = (c : ℝ) • rowToEuclidean row := by
  ext j
  simp [rowToEuclidean]

private theorem cast_foldl_dotProduct_rat
    (xs : List (Fin m)) (a b : Vector Rat m) (acc : Rat) :
    ((xs.foldl (fun acc i => acc + a[i] * b[i]) acc : Rat) : ℝ) =
      (acc : ℝ) + (xs.map fun i => ((a[i] : Rat) : ℝ) * ((b[i] : Rat) : ℝ)).sum := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (acc := acc + a[i] * b[i])]
      simp only [Rat.cast_add, Rat.cast_mul]
      ring

/-- Mathlib's real inner product on converted rows agrees with the executable
rational dense dot product after casting to `ℝ`. -/
theorem rowToEuclidean_inner (a b : Vector Rat m) :
    inner ℝ (rowToEuclidean a) (rowToEuclidean b) =
      ((Vector.dotProduct (u := a) (v := b) : Rat) : ℝ) := by
  rw [PiLp.inner_apply]
  simp [rowToEuclidean, PiLp.toLp_apply,
    RCLike.inner_apply, mul_comm]
  rw [Vector.dotProduct, cast_foldl_dotProduct_rat]
  simp only [Rat.cast_zero, zero_add]
  rw [← List.sum_toFinset _ (List.nodup_finRange m)]
  simp [List.toFinset_finRange]

/-- A strictly lower executable coefficient agrees, after casting to `ℝ`, with
Mathlib's projection coefficient for the corresponding converted rows. -/
theorem rat_coeffs_lower_projection_real (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    ((Hex.GramSchmidt.entry (Hex.GramSchmidt.Rat.coeffs b) i j : Rat) : ℝ) =
      inner ℝ (rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j))
          (rowToEuclidean (b.row i)) /
        (‖rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j)‖ : ℝ) ^ 2 := by
  rw [Hex.GramSchmidt.Rat.coeffs_lower_projection_comm (b := b) hji]
  by_cases hnorm :
      ((Hex.GramSchmidt.Rat.basis b).row j).dotProduct
          ((Hex.GramSchmidt.Rat.basis b).row j) = 0
  · have hnorm_real :
        (‖rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j)‖ : ℝ) ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, rowToEuclidean_inner]
      exact_mod_cast hnorm
    simp [hnorm, hnorm_real]
  ·
    have hnorm_real :
        (‖rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j)‖ : ℝ) ^ 2 =
          ((((Hex.GramSchmidt.Rat.basis b).row j).dotProduct
            ((Hex.GramSchmidt.Rat.basis b).row j) : Rat) : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, rowToEuclidean_inner]
    simp [hnorm, rowToEuclidean_inner, hnorm_real]

private theorem rowToEuclidean_foldl_linear
    {α : Type*} (xs : List α) (c : α → Rat) (v : α → Vector Rat m)
    (acc : Vector Rat m) :
    rowToEuclidean (xs.foldl (fun acc x => acc + c x • v x) acc) =
      rowToEuclidean acc + (xs.map fun x => (c x : ℝ) • rowToEuclidean (v x)).sum := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (acc := acc + c x • v x)]
      simp [rowToEuclidean_add, rowToEuclidean_smul, add_assoc]

private theorem sum_fin_eq_sum_Iio {M : Type*} [AddCommMonoid M]
    (i : Fin n) (f : Fin n → M) :
    (∑ x : Fin i.val, f ⟨x.val, Nat.lt_trans x.isLt i.isLt⟩) =
      ∑ x ∈ Finset.Iio i, f x := by
  classical
  refine Finset.sum_bij
    (fun x _ => (⟨x.val, Nat.lt_trans x.isLt i.isLt⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro x _
    rw [Finset.mem_Iio]
    exact x.isLt
  · intro x _ y _ hxy
    apply Fin.ext
    exact congrArg (fun z : Fin n => z.val) hxy
  · intro y hy
    refine ⟨⟨y.val, ?_⟩, by simp, ?_⟩
    · simpa using hy
    · exact Fin.ext rfl
  · intro x _
    rfl

private theorem rowToEuclidean_prefixCombination_eq_Iio_sum
    (b : Matrix Rat n m) (i : Fin n)
    (hprev :
      ∀ j : Fin n, j.val < i.val →
        rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j) =
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j) :
    rowToEuclidean
        (Hex.GramSchmidt.prefixCombination
          (Hex.GramSchmidt.Rat.coeffs b) (Hex.GramSchmidt.Rat.basis b) i.val i.isLt) =
      ∑ j ∈ Finset.Iio i,
        (inner ℝ (InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j) (ratRowFamily b i) /
            (‖InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j‖ : ℝ) ^ 2) •
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j := by
  classical
  unfold Hex.GramSchmidt.prefixCombination
  rw [Fin.foldl_eq_finRange_foldl, rowToEuclidean_foldl_linear]
  simp only [rowToEuclidean_zero, zero_add]
  rw [← List.sum_toFinset _ (List.nodup_finRange i.val)]
  simpa [rat_coeffs_lower_projection_real, hprev, ratRowFamily] using
    sum_fin_eq_sum_Iio (i := i)
      (f := fun j =>
        (inner ℝ (InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j)
            (rowToEuclidean (b.row i)) /
          (‖InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j‖ : ℝ) ^ 2) •
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j)

/-- The rational Gram-Schmidt basis agrees rowwise with Mathlib's real-valued
`gramSchmidt` after coercing coefficients into `ℝ`. -/
theorem rat_basis_row_eq_gramSchmidt (b : Matrix Rat n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) i := by
  classical
  have hstrong :
      ∀ k : Nat, ∀ hk : k < n,
        rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row ⟨k, hk⟩) =
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let ik : Fin n := ⟨k, hk⟩
        have hprev :
            ∀ j : Fin n, j.val < ik.val →
              rowToEuclidean ((Hex.GramSchmidt.Rat.basis b).row j) =
                InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j := by
          intro j hj
          exact ih j.val hj j.isLt
        have hdecomp :=
          congrArg rowToEuclidean
            (Hex.GramSchmidt.Rat.basis_decomposition (b := b) k hk)
        rw [rowToEuclidean_add,
          rowToEuclidean_prefixCombination_eq_Iio_sum (b := b) (i := ik) hprev] at hdecomp
        have hmath := InnerProductSpace.gramSchmidt_def'' ℝ (ratRowFamily b) ik
        change rowToEuclidean (b.row ik) =
          InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) ik +
            ∑ j ∈ Finset.Iio ik,
              (inner ℝ (InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j)
                    (ratRowFamily b ik) /
                  (‖InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j‖ : ℝ) ^ 2) •
                InnerProductSpace.gramSchmidt ℝ (ratRowFamily b) j at hmath
        exact add_right_cancel (by rw [← hdecomp, hmath])
  exact hstrong i.val i.isLt

/-- The integer Gram-Schmidt basis agrees rowwise with Mathlib's real-valued
`gramSchmidt` after coercing coefficients into `ℝ`. -/
theorem int_basis_row_eq_gramSchmidt (b : Matrix Int n m) (i : Fin n) :
    rowToEuclidean ((Hex.GramSchmidt.Int.basis b).row i) =
      InnerProductSpace.gramSchmidt ℝ (intRowFamily b) i := by
  have key := rat_basis_row_eq_gramSchmidt (castIntMatrix b) i
  simp only [intRowFamily, castIntMatrix, Hex.GramSchmidt.Int.basis, Hex.GramSchmidt.Rat.basis] at key ⊢
  exact key

end GramSchmidtTheory

end Hex

end

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeNativeLLLQuality. -/
section P2MDyadicModule7

set_option autoImplicit true

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeLLL

open Hex.Internal

open scoped BigOperators

variable {n m : Nat}

theorem gsRow_norm_sq (b : Hex.Matrix Int n m) (i : Fin n) :
    ‖gsRow b i‖^2 = ((((Hex.GramSchmidt.Int.basis b).row i).normSq : ℚ) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [gsRow,PiLp.toLp_apply,Vector.normSq,Vector.dotProduct,
    HexMatrixTheory.foldl_finRange_eq_sum,Rat.cast_sum,Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem basis_column_eq (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det ≠ 0) (j : Fin n) :
    IntegerBasis.realBasis (basis B) (basis_det_ne_zero B hdet) j =
      HexLLLTheory.intRowToEuclidean ((current (input B)).row j) := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp only [basis,Matrix.transpose_apply,HexMatrixTheory.matrixEquiv_apply,
    HexLLLTheory.intRowToEuclidean,WithLp.ofLp_toLp,Hex.Matrix.getElem_row]

/-- A dimension-only ratio to the last GS vector, independent of input bitlength. -/
theorem basis_column_norm_sq_le_lastGS (B : Matrix (Fin n) (Fin n) ℤ)
    (hdet : B.det ≠ 0) (hn : 0 < n) (j : Fin n) :
    ‖IntegerBasis.realBasis (basis B) (basis_det_ne_zero B hdet) j‖^2 ≤
      (n : ℝ)*(2 : ℝ)^(n-1)*‖lastGS B hn‖^2 := by
  have hred := current_reduced (input B) hn (input_independent B hdet)
  have h := Hex.Internal.LLLCore.rowNormSq_le_basisNormSq (current (input B))
    hred (by norm_num) (by norm_num) (by norm_num) j (lastIndex hn)
    (by have := j.isLt; dsimp [lastIndex];omega)
  have hreal := (Rat.cast_le (K := ℝ)).mpr h
  norm_num at hreal
  rw [basis_column_eq B hdet j,HexLLLTheory.norm_sq_intRowToEuclidean,lastGS,gsRow_norm_sq]
  simpa only [Hex.Internal.LLLCore.basisNormSq,Rat.cast_intCast] using hreal

theorem basis_column_norm_le_lastGS (B : Matrix (Fin n) (Fin n) ℤ)
    (hdet : B.det ≠ 0) (hn : 0 < n) (j : Fin n) :
    ‖IntegerBasis.realBasis (basis B) (basis_det_ne_zero B hdet) j‖ ≤
      (n : ℝ)*(2 : ℝ)^n*‖lastGS B hn‖ := by
  have hs := basis_column_norm_sq_le_lastGS B hdet hn j
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hpow : (2 : ℝ)^(n-1) ≤ ((2 : ℝ)^n)^2 := by
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hcoeff : (n : ℝ)*(2 : ℝ)^(n-1) ≤ ((n : ℝ)*(2 : ℝ)^n)^2 := by
    calc
      _ ≤ (n : ℝ)^2*((2 : ℝ)^n)^2 := mul_le_mul hn2 hpow (by positivity) (by positivity)
      _ = _ := by ring
  have hsq : ‖IntegerBasis.realBasis (basis B) (basis_det_ne_zero B hdet) j‖^2 ≤
      ((n : ℝ)*(2 : ℝ)^n*‖lastGS B hn‖)^2 := by
    calc
      _ ≤ (n : ℝ)*(2 : ℝ)^(n-1)*‖lastGS B hn‖^2 := hs
      _ ≤ ((n : ℝ)*(2 : ℝ)^n)^2*‖lastGS B hn‖^2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

theorem gsRow_input_eq_orthogonal (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    gsRow (input B) i = RationalGramSchmidt.realVec
      (RationalGramSchmidt.orthogonal (RationalGramSchmidt.inputVectors B) i) := by
  rw [RationalGramSchmidt.orthogonal_real]
  have hfamily : Hex.GramSchmidtTheory.intRowFamily (input B) =
      fun j => RationalGramSchmidt.realVec (RationalGramSchmidt.inputVectors B j) := by
    funext j
    ext row
    simp only [Hex.GramSchmidtTheory.intRowFamily,Hex.GramSchmidtTheory.ratRowFamily,
      Hex.GramSchmidtTheory.rowToEuclidean,Hex.GramSchmidtTheory.castIntMatrix,
      Hex.Matrix.row,Hex.Matrix.getRow_ofRows,Hex.Matrix.getElem_row,Hex.Matrix.getElem_ofFn,input,Hex.Matrix.getElem_ofRows,
      Vector.getElem_map,Hex.Matrix.getElem_rows,Fin.getElem_fin,
      WithLp.ofLp_toLp,RationalGramSchmidt.realVec,RationalGramSchmidt.inputVectors,
      Rat.cast_intCast]
    change (((Hex.Matrix.ofFn (fun i j => B j i))[j][row] : ℤ) : ℝ) = (B row j : ℝ)
    rw [Hex.Matrix.getElem_ofFn]
  change Hex.GramSchmidtTheory.rowToEuclidean ((Hex.GramSchmidt.Int.basis (input B)).row i) = _
  rw [Hex.GramSchmidtTheory.int_basis_row_eq_gramSchmidt,hfamily]

/-- This is the last GS vector of the reduced basis, in the original project's
rational/real embedding; it is not the last GS vector of the unreduced input. -/
theorem lastGS_eq_orthogonal (B : Matrix (Fin n) (Fin n) ℤ) (hn : 0 < n) :
    lastGS B hn = RationalGramSchmidt.realVec
      (RationalGramSchmidt.orthogonal (RationalGramSchmidt.inputVectors (basis B)) (lastIndex hn)) := by
  rw [lastGS,←input_basis,gsRow_input_eq_orthogonal]

end InfoLossLAR.WorstCase.NativeLLL

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeIntegerDualCoordinates. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Each integral dual coordinate is exactly the pairing with the
corresponding original input column. -/
theorem dualCoordinates_inner (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) (index : Fin dimension) :
    inner ℝ (dualCoordinates basis hdet value) (integerBasis basis hdet index : Space (dimension:=dimension))=(value index : ℝ) := by
  have hreal : (integerBasis basis hdet index : Space (dimension:=dimension))=realBasis basis hdet index :=
    Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index
  have hdual (column row : Fin dimension) :
      inner ℝ (dualRealBasis basis hdet column) (realBasis basis hdet row)=if row=column then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left inner_nondegenerate (realBasis basis hdet) column row
  rw [dualCoordinates_apply,hreal,sum_inner]
  simp only [←Int.cast_smul_eq_zsmul ℝ,real_inner_smul_left]
  simp_rw [hdual]
  simp

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeRationalGramSchmidtHeight. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT.RationalNumerics

open scoped BigOperators

noncomputable section

theorem realVec_injective {dimension : ℕ} : Function.Injective (realVec (dimension:=dimension)) := by
  intro first second hequal
  funext index
  apply Rat.cast_injective (α:=ℝ)
  exact congrArg (fun vector : Space dimension => vector index) hequal

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeRationalInverseAlgebra. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

noncomputable section

/-- Analytical Cramer specification only. The native implementation below
will use the cached rational orthogonalization and reverse substitution. -/
def dualVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : QVector n :=
  fun row => (Matrix.cramer B.transpose (Pi.single i 1) row : ℚ)/(B.det : ℚ)

theorem dualVector_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (i k : Fin n) : innerQ (dualVector B i) (inputVectors B k)=if k=i then 1 else 0 := by
  have hD : (B.det : ℚ)≠0 := by exact_mod_cast hdet
  have hh:=congrFun (Matrix.mulVec_cramer B.transpose (Pi.single i 1)) k
  simp only [Matrix.mulVec,dotProduct,Matrix.det_transpose,Pi.smul_apply,smul_eq_mul,
    Matrix.transpose_apply,Pi.single_apply] at hh
  have hcast : (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))=
      (B.det : ℚ)*(if k=i then 1 else 0) := by exact_mod_cast hh
  calc
    _ = (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))/(B.det : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro row _
      simp only [innerQ,dualVector,inputVectors]
      ring
    _ = ((B.det : ℚ)*(if k=i then 1 else 0))/(B.det : ℚ) := by rw [hcast]
    _ = _ := by split_ifs <;> simp [hD]

/-- Pairings with the original input columns determine the entire real
vector, using the actual Euclidean dual basis. -/
theorem real_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : IntegerBasis.Space (dimension:=n))
    (h : ∀ k,inner ℝ x (IntegerBasis.realBasis B hdet k)=inner ℝ y (IntegerBasis.realBasis B hdet k)) : x=y := by
  apply (IntegerBasis.dualRealBasis B hdet).ext_elem
  intro k
  change ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet)).repr x) k=
    ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
      (IntegerBasis.realBasis B hdet)).repr y) k
  rw [LinearMap.BilinForm.dualBasis_repr_apply,LinearMap.BilinForm.dualBasis_repr_apply]
  exact h k

theorem dualVector_real {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (i : Fin n) :
    realVec (dualVector B i)=IntegerBasis.dualRealBasis B hdet i := by
  apply real_pairings_unique B hdet
  intro k
  have hx : inner ℝ (realVec (dualVector B i)) (IntegerBasis.realBasis B hdet k)=if k=i then 1 else 0 := by
    rw [←inputVectors_real B hdet k,←innerQ_real,dualVector_pairing B hdet]
    split_ifs <;> norm_num
  rw [hx]
  exact (LinearMap.BilinForm.apply_dualBasis_left IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet) i k).symm

theorem rational_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : QVector n) (h : ∀ k,innerQ x (inputVectors B k)=innerQ y (inputVectors B k)) : x=y := by
  apply realVec_injective
  apply real_pairings_unique B hdet
  intro k
  rw [←inputVectors_real B hdet k,←innerQ_real,←innerQ_real,h k]

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeRationalInverseRecurrence. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

@[simp] theorem innerQ_sub_left {n : ℕ} (x y z : QVector n) :
    innerQ (x-y) z=innerQ x z-innerQ y z := by simp [innerQ,sub_mul,Finset.sum_sub_distrib]

@[simp] theorem innerQ_smul_left {n : ℕ} (a : ℚ) (x y : QVector n) :
    innerQ (a • x) y=a*innerQ x y := by simp [innerQ,Finset.mul_sum,mul_assoc]

theorem innerQ_sum_left {n : ℕ} {J : Type*} (s : Finset J) (x : J → QVector n) (y : QVector n) :
    innerQ (∑ j∈s,x j) y=∑ j∈s,innerQ (x j) y := by
  simp only [innerQ,Finset.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- One reverse triangular substitution step. Its only arithmetic operands
are the cached original rational orthogonalization and future dual columns. -/
def dualStep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (cache : Fin n → QVector n) (i : Fin n) : QVector n :=
  (squaredNorm (inputVectors B) i)⁻¹ • orthogonal (inputVectors B) i-
    ∑ j∈Finset.Ioi i,upper (inputVectors B) i j • cache j

noncomputable section

theorem dualStep_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i k : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) :
    innerQ (dualStep B cache i) (inputVectors B k)=if k=i then 1 else 0 := by
  rw [dualStep,innerQ_sub_left,innerQ_smul_left,innerQ_sum_left]
  simp only [innerQ_smul_left]
  have hfirst : (squaredNorm (inputVectors B) i)⁻¹*innerQ (orthogonal (inputVectors B) i) (inputVectors B k)=
      upper (inputVectors B) i k := by unfold upper;ring
  rw [hfirst]
  have hsum : (∑ j∈Finset.Ioi i,upper (inputVectors B) i j*innerQ (cache j) (inputVectors B k))=
      if i< k then upper (inputVectors B) i k else 0 := by
    calc
      _ = ∑ j∈Finset.Ioi i,if k=j then upper (inputVectors B) i j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcache j (Finset.mem_Ioi.mp hj),dualVector_pairing B hdet]
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_Ioi]
  rw [hsum]
  by_cases he : k=i
  · subst k
    simp [upper_diagonal _ (inputVectors_independent B hdet)]
  · by_cases hi : i< k
    · simp [hi,he]
    · have hk : k< i := lt_of_le_of_ne (le_of_not_gt hi) he
      rw [upper_triangular _ i k hk]
      simp [hi,he]

theorem dualStep_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) : dualStep B cache i=dualVector B i := by
  apply rational_pairings_unique B hdet
  intro k
  rw [dualStep_pairing B hdet cache i k hcache,dualVector_pairing B hdet]

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeDualIntegerBasis. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Integral coordinates identify the genuine dual input lattice with the
free integer module, using exactly the original input-basis pairings. -/
def dualIntegerEquiv (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (Fin dimension → ℤ) ≃ₗ[ℤ] dual (inputLattice basis hdet) where
  toFun value := ⟨dualCoordinates basis hdet value,dualCoordinates_mem basis hdet value⟩
  invFun point := fun index => pairing (inputLattice basis hdet) point (integerBasis basis hdet index)
  left_inv value := by
    funext index
    apply Int.cast_injective (α:=ℝ)
    rw [pairing_spec]
    exact dualCoordinates_inner basis hdet value index
  right_inv point := by
    apply Subtype.ext
    exact dualCoordinates_pairing basis hdet point
  map_add' first second := Subtype.ext (map_add (dualCoordinates basis hdet) first second)
  map_smul' scalar value := Subtype.ext (map_smul (dualCoordinates basis hdet) scalar value)

/-- A genuine integral basis of the dual lattice. It is a mathematical
coordinate object; a separate native algorithm computes its rational entries. -/
def dualIntegerBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℤ (dual (inputLattice basis hdet)) :=
  (Pi.basisFun ℤ (Fin dimension)).map (dualIntegerEquiv basis hdet)

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgePrimalDualCoordinates. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection.CosetGeometry GaussianPoissonSeries

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem dualIntegerBasis_coe (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (index : Fin dimension) :
    (dualIntegerBasis basis hdet index : Space (dimension:=dimension))=dualRealBasis basis hdet index := by
  rw [dualIntegerBasis,Module.Basis.map_apply,Pi.basisFun_apply]
  change dualCoordinates basis hdet (Pi.single index 1)=_
  simp [dualCoordinates_apply,Pi.single_apply]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeLastGSSmoothingLower. -/
section P2MDyadicModule14

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RationalGramSchmidt RationalInverse IntegerBasis RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- In the actual original basis, the final dual column is its final
Gram--Schmidt vector divided by its squared norm. -/
theorem last_dual_gramSchmidt
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (last : Fin dimension) (hlast : ∀ index : Fin dimension,index ≤ last) :
    dualRealBasis basis hdet last=
      (‖realVec (orthogonal (inputVectors basis) last)‖^2)⁻¹ •
        realVec (orthogonal (inputVectors basis) last) := by
  have hformula := dualStep_correct basis hdet (fun _ => 0) last (by
    intro index hindex
    exact False.elim ((not_lt_of_ge (hlast index)) hindex))
  have hdual : dualVector basis last=(squaredNorm (inputVectors basis) last)⁻¹ •
      orthogonal (inputVectors basis) last := by
    rw [dualStep] at hformula
    simpa only [smul_zero,Finset.sum_const_zero,sub_zero] using hformula.symm
  rw [←dualVector_real basis hdet last,hdual,realVec_smul,Rat.cast_inv]
  have hnorm := squaredNorm_real (inputVectors basis) last
  rw [←orthogonal_real] at hnorm
  rw [hnorm]

/-- Exact reciprocal norm of the actual last dual column. -/
theorem last_dual_norm
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (last : Fin dimension) (hlast : ∀ index : Fin dimension,index ≤ last) :
    ‖dualRealBasis basis hdet last‖=1/‖realVec (orthogonal (inputVectors basis) last)‖ := by
  have hnorm : 0 < ‖realVec (orthogonal (inputVectors basis) last)‖ := by
    rw [orthogonal_real]
    exact norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero last (inputVectors_independent basis hdet))
  rw [last_dual_gramSchmidt basis hdet last hlast,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hnorm))]
  field_simp

/-- The actual smoothing parameter dominates the final Gram--Schmidt
length. Together with LLL's adjacent-norm bound, this limits DGS/BDD
stages by dimension rather than arbitrary basis input bit length. -/
theorem lastGS_le_smoothing
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (last : Fin dimension) (hlast : ∀ index : Fin dimension,index ≤ last)
    (error : ℝ) (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi)) :
    ‖realVec (orthogonal (inputVectors basis) last)‖ ≤ smoothingParam (inputLattice basis hdet) error := by
  have h := smoothing_reciprocal_dual_norm (inputLattice basis hdet) error
    (by have hi := last.isLt;omega) herror hsmall (dualIntegerBasis basis hdet last)
    ((dualIntegerBasis basis hdet).ne_zero last)
  change 1/‖(dualIntegerBasis basis hdet last : IntegerBasis.Space (dimension:=dimension))‖ ≤ _ at h
  rw [dualIntegerBasis_coe,last_dual_norm basis hdet last hlast,one_div_one_div] at h
  exact h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeNativeLLLSmoothingStopping. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv IntegerBasis RationalGramSchmidt

noncomputable section

variable {dimension : ℕ}

/-- The actual verified LLL output's final GS length is bounded by the
original input lattice's exact smoothing parameter. -/
theorem nativeLLL_lastGS_le_smoothing
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (hdimension : 0 < dimension) (error : ℝ) (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi)) :
    ‖NativeLLL.lastGS basis hdimension‖ ≤ smoothingParam (inputLattice basis hdet) error := by
  have h := lastGS_le_smoothing (NativeLLL.basis basis) (NativeLLL.basis_det_ne_zero basis hdet)
    (NativeLLL.lastIndex hdimension) (by
      intro index
      have hi := index.isLt
      change index.val ≤ dimension-1
      omega) error herror hsmall
  rw [←NativeLLL.lastGS_eq_orthogonal basis hdimension,NativeLLL.basis_inputLattice_eq basis hdet] at h
  exact h

/-- Every actual reduced column has a dimension-only ratio to the original
source smoothing threshold. No efficiently selected short basis is assumed. -/
theorem nativeLLL_column_norm_le_smoothing
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (hdimension : 0 < dimension) (error : ℝ) (herror : 0 < error) (hsmall : error ≤ Real.exp (-Real.pi))
    (index : Fin dimension) :
    ‖realBasis (NativeLLL.basis basis) (NativeLLL.basis_det_ne_zero basis hdet) index‖ ≤
      (dimension : ℝ)*(2 : ℝ)^dimension*smoothingParam (inputLattice basis hdet) error := by
  exact (NativeLLL.basis_column_norm_le_lastGS basis hdet hdimension index).trans
    (mul_le_mul_of_nonneg_left (nativeLLL_lastGS_le_smoothing basis hdet hdimension error herror hsmall) (by positivity))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule15


set_option autoImplicit false
set_option maxHeartbeats 750000
open scoped BigOperators
namespace SingleWidth
noncomputable section
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.GaussianPoissonSeries InfoLossLAR.WorstCase.IntegerBasis
open InfoLossLAR.WorstCase.RationalGramSchmidt
open RegevLWE.GaussConv

private theorem same_lattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) :
    inputModule B = inputLattice B hB := by
  unfold inputModule inputLattice
  congr 2
  funext i
  simp [realBasis_apply,latVec,Matrix.mulVec_single]

theorem small_error {n : ℕ} (hn : 2 ≤ n) : smoothingError n ≤ Real.exp (-Real.pi) := by
  have h3 : 3 ≤ Nat.size (n+2) := (Nat.lt_size).mpr (by norm_num; omega)
  have hexp : Real.exp Real.pi ≤ (2:ℝ)^9 := by
    calc
      _ ≤ Real.exp 4 := Real.exp_le_exp.mpr Real.pi_lt_four.le
      _ = (Real.exp 1)^4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3:ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
      _ ≤ _ := by norm_num
  unfold smoothingError
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (Real.exp_pos _)
  exact hexp.trans (pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.mul_self_le_mul_self h3]))

private theorem find_entry {n : ℕ} (hn : 0<n) (C : Matrix (Fin n) (Fin n) ℤ) (hdet : C.det ≠ 0) :
    ∃ i j, C i j ≠ 0 := by
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  by_contra! ha
  apply hdet
  have he : C=0 := Matrix.ext (fun _ _ => ha _ _)
  rw [he,Matrix.det_zero]

abbrev exponent (n b : ℕ) := 4*n+1+Nat.size b

theorem initial_width_cap {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (b : ℕ) :
    (initialWidth (NativeLLL.basis B) (b : ℚ) : ℝ) ≤
      (2:ℝ)^(exponent n b) * smoothingParam (inputModule B) (smoothingError n) := by
  let C := NativeLLL.basis B
  let η := smoothingParam (inputModule B) (smoothingError n)
  let A := (n:ℝ) * 2^n * η
  have hC := NativeLLL.basis_det_ne_zero B hB
  have hs : 0 < smoothingError n := by unfold smoothingError; positivity
  have hentry (i j : Fin n) : |(C i j : ℝ)| ≤ A := by
    have hb := nativeLLL_column_norm_le_smoothing B hB (by omega) (smoothingError n) hs (small_error hn) j
    rw [← same_lattice B hB] at hb
    apply le_trans _ hb
    have hc := PiLp.norm_apply_le (p := 2) (realBasis C hC j) i
    simpa only [realBasis_apply,PiLp.toLp_apply,Real.norm_eq_abs] using hc
  obtain ⟨i,j,hij⟩ := find_entry (by omega) C hC
  have hi : (1:ℝ) ≤ |(C i j : ℝ)| := by
    have hz : (1:ℤ) ≤ |C i j| := Int.add_one_le_iff.mpr (abs_pos.mpr hij)
    exact_mod_cast hz
  have hA := hi.trans (hentry i j)
  have hη : 0 ≤ η := by
    by_contra! h
    have hf : (n:ℝ)*2^n*η ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
    dsimp only [A] at hA; linarith
  have hmass : (entryMass C : ℝ) ≤ (n:ℝ)^2*A := by
    unfold entryMass
    push_cast
    calc
      _ ≤ ∑ i : Fin n, ∑ _ : Fin n, A := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hentry i j
      _ = _ := by simp [pow_two,mul_assoc]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hn1 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ hnR
  have hA' : (1:ℝ) ≤ (n:ℝ)^2*A := hA.trans (le_mul_of_one_le_left (by linarith) hn1)
  have hnp : (n:ℝ) ≤ 2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hbp : (b:ℝ) ≤ 2^(Nat.size b) := by exact_mod_cast (Nat.lt_size_self b).le
  have hcoeff : (b:ℝ)*2*(n:ℝ)^3*2^n ≤ 2^(exponent n b) := by
    calc
      _ ≤ (2:ℝ)^Nat.size b * 2 * ((2:ℝ)^n)^3 * 2^n := by gcongr
      _ = _ := by
        rw [show exponent n b = (Nat.size b + 1) + (n*3) + n by unfold exponent;omega]
        rw [pow_add, pow_add, pow_mul, pow_succ (2:ℝ) (Nat.size b)]
  change (initialWidth C (b:ℚ) : ℝ) ≤ _*η
  unfold initialWidth
  push_cast
  calc
    _ ≤ (b:ℝ) * (2*((n:ℝ)^2*A)) := mul_le_mul_of_nonneg_left (by linarith only [hmass,hA']) (by positivity)
    _ = ((b:ℝ)*2*(n:ℝ)^3*2^n)*η := by dsimp only [A]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hη

def startWidth {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (b : ℕ) : ℚ :=
  max (initialWidth (NativeLLL.basis B) b) (r * (famσ n : ℚ))

def terminal (n : ℕ) (r : ℚ) : ℝ :=
  (r:ℝ) * (famσ n : ℝ) / (Real.sqrt 2 * Real.sqrt n)

theorem pool_start_window {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r:ℝ)) (b : ℕ) :
    terminal n r ≤ (startWidth B r b : ℝ) ∧
      (startWidth B r b : ℝ) ≤ (2:ℝ)^exponent n b * terminal n r := by
  let η := smoothingParam (inputModule B) (smoothingError n)
  let d := Real.sqrt 2 * Real.sqrt n
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hs2 : 1 ≤ Real.sqrt 2 := (Real.one_le_sqrt).mpr (by norm_num)
  have hsn : 1 ≤ Real.sqrt n := (Real.one_le_sqrt).mpr hnR
  have hd : 1 ≤ d := one_le_mul_of_one_le_of_one_le hs2 hsn
  have hdpos : 0 < d := zero_lt_one.trans_le hd
  have hσ : (0:ℝ) < famσ n := by unfold famσ famL; positivity
  have hrR : 0 < (r:ℝ) := by exact_mod_cast hr
  have hw : 0 < terminal n r := div_pos (mul_pos hrR hσ) hdpos
  have hscale : terminal n r * d = (r:ℝ)*(famσ n : ℝ) := div_mul_cancel₀ _ hdpos.ne'
  have heta : η ≤ terminal n r := by
    by_cases he : η ≤ 0
    · exact he.trans hw.le
    have he' : 0 ≤ η := le_of_lt (lt_of_not_ge he)
    have hq : (1:ℝ) ≤ famq n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (famq n)))
    have hσcle : 16*(famq n : ℝ)*Real.sqrt n*η ≤ (r:ℝ)*(famσ n : ℝ) := by
      apply (div_le_iff₀ hσ).mp
      calc
        _ = dgsThreshold B := by unfold dgsThreshold;dsimp only [η];ring
        _ ≤ _ := hp
    have hs2_upper : Real.sqrt 2 ≤ 2 := Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    have hfactor : d ≤ 16*(famq n:ℝ)*Real.sqrt n := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith
    exact (le_div_iff₀ hdpos).mpr ((mul_comm η d).trans_le
      ((mul_le_mul_of_nonneg_right hfactor he').trans hσcle))
  have hnp : (n:ℝ) ≤ 2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hdle : d ≤ (2:ℝ)^exponent n b := by
    calc
      _ ≤ 2*(n:ℝ) := mul_le_mul (Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))) (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
        (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ (2:ℝ)^(n+1) := by rw [pow_succ,mul_comm];gcongr
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by unfold exponent; omega)
  have hstart : (startWidth B r b : ℝ) = max (initialWidth (NativeLLL.basis B) (b:ℚ) : ℝ)
      ((r:ℝ)*(famσ n : ℝ)) := by unfold startWidth; push_cast; rfl
  rw [hstart]
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    rw [← hscale]
    exact le_mul_of_one_le_right hw.le hd
  · refine max_le ((initial_width_cap hn B hB b).trans (mul_le_mul_of_nonneg_left heta (by positivity))) ?_
    rw [← hscale,mul_comm]
    exact mul_le_mul_of_nonneg_right hdle hw.le

private theorem first_halving_crossing (W w : ℝ) (K : ℕ)
    (hW : 0 < W) (_hw : 0 < w) (hstart : w ≤ W)
    (hcap : W ≤ (2 : ℝ)^K * w) :
    ∃ k : ℕ, k ≤ K ∧
      w / 2 ≤ W / (2 : ℝ)^k ∧ W / (2 : ℝ)^k ≤ w ∧
      ∀ j < k, w < W / (2 : ℝ)^j := by
  have hex : ∃ k : ℕ, W / (2 : ℝ)^k ≤ w := by
    refine ⟨K, (div_le_iff₀ (by positivity)).2 ?_⟩
    simpa [mul_comm] using hcap
  let k := Nat.find hex
  have hupper : W / (2 : ℝ)^k ≤ w := Nat.find_spec hex
  have hkle : k ≤ K := Nat.find_min' hex ((div_le_iff₀ (by positivity)).2 (by simpa [mul_comm] using hcap))
  have hbefore : ∀ j < k, w < W / (2 : ℝ)^j := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min hex hj)
  have hlower : w / 2 ≤ W / (2 : ℝ)^k := by
    by_cases hk : k = 0
    · rw [hk]
      norm_num
      linarith
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hprev := hbefore j (by omega)
      rw [hj, pow_succ]
      have hpos : (0 : ℝ) < (2 : ℝ)^j := by positivity
      have hsplit : W / ((2 : ℝ)^j * 2) = (W / (2 : ℝ)^j) / 2 := by ring
      rw [hsplit]
      linarith
  exact ⟨k, hkle, hlower, hupper, hbefore⟩


theorem dimension_halvings {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r:ℝ)) :
    let W : ℝ := startWidth B r (n+1)
    let w := terminal n r
    ∃ k : ℕ, k ≤ 5*n+2 ∧ w/2 ≤ W/2^k ∧ W/2^k ≤ w ∧ ∀ j < k, w < W/2^j := by
  dsimp only
  obtain ⟨hlo,hhi⟩ := pool_start_window hn B hB r hr hp (n+1)
  have hs : 0 < terminal n r := by
    dsimp only [terminal,famσ,famL]
    have hr' : (0:ℝ)<r := by exact_mod_cast hr
    have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    positivity
  have hsize : Nat.size (n+1) ≤ n+1 := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n+1))
  have hex : exponent n (n+1) ≤ 5*n+2 := by unfold exponent;omega
  exact first_halving_crossing _ _ _ (hs.trans_le hlo) hs hlo
    (hhi.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hex) hs.le))

/-- The terminal lower edge still lies strictly above the smoothing threshold
for a valid source, and the upper edge gives the required decoder radius. -/
theorem terminal_window_valid {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r:ℝ)) (v : ℝ)
    (hv : terminal n r / 2 ≤ v) (hv' : v ≤ terminal n r) :
    Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < v ∧
      Real.sqrt n / (Real.sqrt 2 * (r:ℝ)) ≤ (famσ n : ℝ)/(2*v) := by
  let η := smoothingParam (inputModule B) (smoothingError n)
  let d := Real.sqrt 2 * Real.sqrt n
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hs : 0 < (famσ n : ℝ) := by unfold famσ famL;positivity
  have hq : 0 < (famq n : ℝ) := by exact_mod_cast (NeZero.pos (famq n))
  have hd : 0 < d := mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr hn')
  have hw : 0 < terminal n r := div_pos (mul_pos hr' hs) hd
  have hσcle : 16*(famq n : ℝ)*Real.sqrt n*η ≤ (r:ℝ)*(famσ n : ℝ) := by
    apply (div_le_iff₀ hs).mp
    calc _ = dgsThreshold B := by unfold dgsThreshold;dsimp only [η];ring
         _ ≤ _ := hp
  have hroot : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · apply lt_of_lt_of_le _ hv
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    change (Real.sqrt 2 * (famq n:ℝ) * η) * 2 < (r:ℝ)*(famσ n:ℝ)/d
    apply (lt_div_iff₀ hd).mpr
    have heq : Real.sqrt 2 * (famq n:ℝ) * η * 2 * d = 4 * (famq n:ℝ)*Real.sqrt n*η := by
      dsimp only [d]; linear_combination 2 * (famq n:ℝ) * η * Real.sqrt n * hroot
    rw [heq]
    by_cases hz : η ≤ 0
    · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (by positivity) hz) (mul_pos hr' hs)
    have hh : 0 < (famq n:ℝ) * Real.sqrt n * η := by
      exact mul_pos (mul_pos hq (Real.sqrt_pos.mpr hn')) (lt_of_not_ge hz)
    linarith
  · have hvpos : 0<v := (half_pos hw).trans_le hv
    have hc := (le_div_iff₀ hd).mp hv'
    apply (div_le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hr') (by positivity)).mpr
    calc
      _ = Real.sqrt 2 * (v * d) := by
        dsimp only [d]
        linear_combination -(v * Real.sqrt n) * hroot
      _ ≤ Real.sqrt 2 * ((r:ℝ)*(famσ n:ℝ)) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring

/-- The selected sequence uses a dimension-only number of valid source widths.
Its last stage allows decoding at the radius needed for the requested Gaussian. -/
theorem schedule {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r:ℝ)) :
    let W : ℝ := startWidth B r (n+1)
    let w := terminal n r
    let η := smoothingParam (inputModule B) (smoothingError n)
    ∃ k : ℕ, k ≤ 5*n+2 ∧ w/2 ≤ W/2^k ∧ W/2^k ≤ w ∧
      (∀ j ≤ k, Real.sqrt 2 * (famq n : ℝ) * η < W/2^j) ∧
      Real.sqrt n / (Real.sqrt 2 * (r:ℝ)) ≤ (famσ n : ℝ)/(2*(W/2^k)) := by
  dsimp only
  obtain ⟨k, hk, hlo, hhi, hprev⟩ := dimension_halvings hn B hB r hr hp
  obtain ⟨hsource, hdecode⟩ := terminal_window_valid hn B r hr hp _ hlo hhi
  refine ⟨k, hk, hlo, hhi, ?_, hdecode⟩
  intro j hj
  rcases hj.lt_or_eq with hj | rfl
  · exact (hsource.trans_le hhi).trans (hprev j hj)
  · exact hsource

end
end SingleWidth

set_option autoImplicit false
open scoped BigOperators
open RegevLWE.GaussConv
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r : ℝ)) :
    ∃ D : Matrix (Fin n) (Fin n) ℤ, D.det ≠ 0 ∧ inputModule D = inputModule B ∧
    ∃ W : ℚ, W = max (((n+1 : ℕ) : ℚ) * (1 + ∑ i, ∑ j, |(D i j : ℚ)|)) (r * (famσ n : ℚ)) ∧
    ∃ h : ℕ, h ≤ 5*n+2 ∧
      (∀ j ≤ h, Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) <
        (W : ℝ) / 2^j) ∧
      Real.sqrt n / (Real.sqrt 2 * (r : ℝ)) ≤ (famσ n : ℝ)/(2*((W : ℝ)/2^h)) := by
  let D := InfoLossLAR.WorstCase.NativeLLL.basis B
  have hd : D.det ≠ 0 := InfoLossLAR.WorstCase.NativeLLL.basis_det_ne_zero B hB
  have hs (C : Matrix (Fin n) (Fin n) ℤ) (hC : C.det ≠ 0) :
      inputModule C = InfoLossLAR.WorstCase.IntegerBasis.inputLattice C hC := by
    unfold inputModule InfoLossLAR.WorstCase.IntegerBasis.inputLattice
    congr 2
    funext i
    simp [InfoLossLAR.WorstCase.IntegerBasis.realBasis_apply,latVec,Matrix.mulVec_single]
  have he : inputModule D = inputModule B := (hs D hd).trans
    ((InfoLossLAR.WorstCase.NativeLLL.basis_inputLattice_eq B hB).trans (hs B hB).symm)
  obtain ⟨h,hh,_,_,hsource,hdecode⟩ := SingleWidth.schedule hn B hB r hr hp
  exact ⟨D,hd,he,SingleWidth.startWidth B r (n+1),rfl,h,hh,hsource,hdecode⟩
