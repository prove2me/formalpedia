-- Prove2me | solution 1 for InfoLossLAR.WorstCase.NativeLLL.elementary_updates_preserve_validity
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T13:15:01.550101+00:00
-- url     : https://prove2.me/submissions/e770273c-b342-43e7-8d85-8d1896f07cb2

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
import Theorems.Thm_Hex_GramSchmidt_Int_getArrayEntry_scaledCoeffRowsSchur_eq
import Theorems.Thm_Hex_Matrix_bareissWith_eq_bareissDataWith_det
import Theorems.Thm_Hex_Matrix_det_gramMatrix_nonneg

set_option linter.all false
set_option Elab.async true
set_option cleanup.letToHave false
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
@[simp, grind =] theorem getRow_modifyRow_self (M : Matrix R n m) (i : Fin n)
    (f : Vector R m → Vector R m) : getRow (modifyRow M i.val f) i = f (getRow M i) := by
  rw [← getElem_rows (modifyRow M i.val f) i.val i.isLt, rows_modifyRow,
    Vector.getElem_modify_self i.isLt, getElem_rows]
@[simp, grind =] theorem getRow_modifyRow_ne (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) (j : Fin n) (h : i ≠ j.val) :
    getRow (modifyRow M i f) j = getRow M j := by
  rw [← getElem_rows (modifyRow M i f) j.val j.isLt, rows_modifyRow,
    Vector.getElem_modify_of_ne j.isLt h, getElem_rows]
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
@[simp, grind =] theorem row_rowSwap_left (M : Matrix R n m) (i j : Fin n) :
    row (rowSwap M i j) i = row M j := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) i)[kk] = (row M j)[kk]
  rw [getElem_row, getElem_row, getElem_rowSwap]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]
@[simp, grind =] theorem row_rowSwap_right (M : Matrix R n m) (i j : Fin n) :
    row (rowSwap M i j) j = row M i := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) j)[kk] = (row M i)[kk]
  rw [getElem_row, getElem_row, getElem_rowSwap]
  simp
theorem row_rowSwap_of_ne (M : Matrix R n m) {i j r : Fin n}
    (hri : r ≠ i) (hrj : r ≠ j) :
    row (rowSwap M i j) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowSwap M i j) r)[kk] = (row M r)[kk]
  rw [getElem_row, getElem_row, getElem_rowSwap]
  simp [hri, hrj]
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
theorem rowSwap_rowSwap (M : Matrix R n m) (i j : Fin n) :
    rowSwap (rowSwap M i j) i j = M := by
  apply ext_getElem
  intro rr kk
  rw [getElem_rowSwap]
  by_cases hrj : rr = j
  · rw [if_pos hrj]
    rw [getElem_rowSwap]
    by_cases hji : i = j
    · simp [hrj, hji]
    · simp [hrj, hji]
  · rw [if_neg hrj]
    by_cases hri : rr = i
    · rw [if_pos hri]
      rw [getElem_rowSwap]
      simp [hri]
    · rw [if_neg hri]
      rw [getElem_rowSwap, if_neg hrj, if_neg hri]
end Matrix
end Hex
end
end
section
section
namespace Hex
namespace GramSchmidt
private theorem gapH175
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (horth : ∀ otherBasisRow ∈ basisRev, otherBasisRow.dotProduct basisRow = 0) :
    projectionCoeff (reduceAgainstBasis basisRev row) basisRow =
      projectionCoeff row basisRow := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons otherBasisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      change
        projectionCoeff (reduceAgainstBasis rest (subtractProjection row otherBasisRow)) basisRow =
          projectionCoeff row basisRow
      rw [ih]
      · exact projectionCoeff_subtractProjection_eq
          (row := row) (otherBasisRow := otherBasisRow) (basisRow := basisRow)
          (horth otherBasisRow (by simp))
      · intro laterBasisRow hlater
        exact horth laterBasisRow (by simp [hlater])
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
private theorem gapH470
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) {u v : Vector Rat m}
    (hu : prefixSpan M i hi u) (hv : prefixSpan M i hi v) :
    prefixSpan M i hi (u - v) := by
  have hneg : prefixSpan M i hi ((-1 : Rat) • v) :=
    prefixSpan_smul M i hi (-1) hv
  have hadd := prefixSpan_add M i hi hu hneg
  have hsub : u + (-1 : Rat) • v = u - v := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_add, Vector.getElem_smul, Vector.getElem_sub]
    change u[idx] + (-1 : Rat) * v[idx] = u[idx] - v[idx]
    grind
  simpa [← hsub] using hadd
private theorem gapH341 (a b c : Vector Rat m) :
    a.dotProduct (b + c) = a.dotProduct b + a.dotProduct c := by
  rw [dot_comm_rat, gapH382, dot_comm_rat b a, dot_comm_rat c a]
private theorem gapH309 (s : Rat) (a b : Vector Rat m) :
    a.dotProduct (s • b) = s * a.dotProduct b := by
  rw [dot_comm_rat, gapH342, dot_comm_rat b a]
private theorem gapH479 (a b c : Vector Rat m) :
    a.dotProduct (b - c) = a.dotProduct b - a.dotProduct c := by
  have hsub : b - c = b + (-1 : Rat) • c := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    change b[idx] - (c)[idx] = b[idx] + (-1 : Rat) * (c)[idx]
    grind
  rw [hsub, gapH341, gapH309]
  grind
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
private theorem gapH202
    (M : Matrix Rat n m) (i : Nat) (hi : i < n)
    (u v : Vector Rat m)
    (hspan : prefixSpan M i hi v)
    (horth : ∀ j : Fin (i + 1), u.dotProduct ((prefixRows M i hi).row j) = 0) :
    u.dotProduct v = 0 := by
  rcases hspan with ⟨c, hc⟩
  rw [← hc, vecMul_eq_foldl_rows, Fin.foldl_eq_finRange_foldl]
  have hfold :
      ∀ xs : List (Fin (i + 1)), ∀ acc : Vector Rat m,
        u.dotProduct acc = 0 →
          u.dotProduct
            (xs.foldl
              (fun acc j => acc + (c)[j] • (prefixRows M i hi).row j) acc) = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        rw [gapH341, gapH309, hacc, horth j]
        grind
  exact hfold (List.finRange (i + 1)) 0 (gapH412 u)
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
private theorem gapH380
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (v : Vector Rat m)
    (hspan : prefixSpan M i hi v)
    (horth : ∀ j : Fin (i + 1), v.dotProduct ((prefixRows M i hi).row j) = 0) :
    v = 0 := by
  have hself : v.dotProduct v = 0 :=
    gapH202 M i hi v v hspan horth
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_zero]
  exact dot_self_eq_zero_get v hself ⟨idx, hidx⟩
private theorem gapH251
    (M : Matrix Rat n m) (i : Nat) (hi : i < n)
    (row r s : Vector Rat m)
    (hrspan : prefixSpan M i hi (row - r))
    (hsspan : prefixSpan M i hi (row - s))
    (hrorth : ∀ j : Fin (i + 1), r.dotProduct ((prefixRows M i hi).row j) = 0)
    (hsorth : ∀ j : Fin (i + 1), s.dotProduct ((prefixRows M i hi).row j) = 0) :
    r = s := by
  have hspanDiff :
      prefixSpan M i hi ((row - s) - (row - r)) :=
    gapH470 M i hi hsspan hrspan
  have hdiff_eq : (row - s) - (row - r) = r - s := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_sub, Vector.getElem_sub, Vector.getElem_sub]
    grind
  have hspan : prefixSpan M i hi (r - s) := by
    simpa [hdiff_eq] using hspanDiff
  have horth : ∀ j : Fin (i + 1),
      (r - s).dotProduct ((prefixRows M i hi).row j) = 0 := by
    intro j
    rw [dot_comm_rat (r - s) ((prefixRows M i hi).row j), gapH479]
    rw [dot_comm_rat ((prefixRows M i hi).row j) r,
      dot_comm_rat ((prefixRows M i hi).row j) s, hrorth j, hsorth j]
    grind
  have hzero := gapH380 M i hi (r - s) hspan horth
  apply Vector.ext
  intro idx hidx
  have hz := congrArg (fun v : Vector Rat m => v[(⟨idx, hidx⟩ : Fin m)]) hzero
  change (r - s)[idx] = (0 : Vector Rat m)[idx] at hz
  rw [Vector.getElem_sub, Vector.getElem_zero] at hz
  grind
private theorem gapH243
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n)
    (row r s : Vector Rat m)
    (hrspan : prefixSpan A i hi (row - r))
    (hsspan : prefixSpan B i hi (row - s))
    (hB_to_A : ∀ v : Vector Rat m, prefixSpan B i hi v → prefixSpan A i hi v)
    (hA_rows_to_B :
      ∀ j : Fin (i + 1), prefixSpan B i hi ((prefixRows A i hi).row j))
    (hrorth : ∀ j : Fin (i + 1), r.dotProduct ((prefixRows A i hi).row j) = 0)
    (hsorth : ∀ j : Fin (i + 1), s.dotProduct ((prefixRows B i hi).row j) = 0) :
    r = s := by
  apply gapH251 A i hi row r s hrspan (hB_to_A _ hsspan) hrorth
  intro j
  exact gapH202 B i hi s ((prefixRows A i hi).row j)
    (hA_rows_to_B j) hsorth
private theorem gapH72
    (b : Matrix Rat n m) (km1 k : Fin n) (i : Nat) (hi : i < n)
    (hkm1k : km1.val < k.val) (hki : k.val ≤ i) (j : Fin (i + 1)) :
    prefixSpan b i hi ((prefixRows (Matrix.rowSwap b km1 k) i hi).row j) := by
  let r : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩
  have hkm1_ne_k : km1 ≠ k := by
    intro h
    exact Nat.ne_of_lt hkm1k (congrArg Fin.val h)
  by_cases hjkm1 : r = km1
  · have hrow :
        (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row k := by
      apply Vector.ext
      intro col hcol
      let c : Fin m := ⟨col, hcol⟩
      simp [prefixRows, Matrix.row]
      change (Matrix.rowSwap b km1 k)[r][c] = b[k][c]
      rw [Matrix.getElem_rowSwap]
      simp [hjkm1, hkm1_ne_k]
    rw [hrow]
    exact prefixSpan_mono_le b k.isLt hi hki (prefixSpan_matrix_row b k)
  · by_cases hjk : r = k
    · have hkm1_le_i : km1.val ≤ i := by
        omega
      have hrow :
          (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row km1 := by
        apply Vector.ext
        intro col hcol
        let c : Fin m := ⟨col, hcol⟩
        simp [prefixRows, Matrix.row]
        change (Matrix.rowSwap b km1 k)[r][c] = b[km1][c]
        rw [Matrix.getElem_rowSwap]
        simp [hjk]
      rw [hrow]
      exact prefixSpan_mono_le b km1.isLt hi hkm1_le_i (prefixSpan_matrix_row b km1)
    · have hrle : r.val ≤ i := Nat.le_of_lt_succ j.isLt
      have hrow :
          (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row r := by
        apply Vector.ext
        intro col hcol
        let c : Fin m := ⟨col, hcol⟩
        simp [prefixRows, Matrix.row, r]
        change (Matrix.rowSwap b km1 k)[r][c] = b[r][c]
        rw [Matrix.getElem_rowSwap]
        simp [hjk, hjkm1]
      rw [hrow]
      exact prefixSpan_mono_le b r.isLt hi hrle (prefixSpan_matrix_row b r)
private theorem gapH66
    (b : Matrix Rat n m) (km1 k : Fin n) (i : Nat) (hi : i < n)
    (hkm1 : km1.val + 1 = k.val) (hki : k.val ≤ i) (v : Vector Rat m) :
    prefixSpan (Matrix.rowSwap b km1 k) i hi v ↔ prefixSpan b i hi v := by
  constructor
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      prefixSpan_vecMul
        (A := Matrix.rowSwap b km1 k) (B := b) (i := i) (hi := hi) c
        (by
          intro j
          exact gapH72
            (b := b) (km1 := km1) (k := k) (i := i) (hi := hi)
            (by omega) hki j)
    rwa [hc] at hspan
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      prefixSpan_vecMul
        (A := b) (B := Matrix.rowSwap b km1 k) (i := i) (hi := hi) c
        (by
          intro j
          have hrowspan :=
            gapH72
              (b := Matrix.rowSwap b km1 k) (km1 := km1) (k := k)
              (i := i) (hi := hi) (by omega) hki j
          have hswap_swap : Matrix.rowSwap (Matrix.rowSwap b km1 k) km1 k = b := by
            exact Matrix.rowSwap_rowSwap b km1 k
          simpa [hswap_swap] using hrowspan)
    rwa [hc] at hspan
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
private theorem gapH151
    (b : Matrix Rat n m) (src col : Fin n) (hsrccol : src.val < col.val) :
    GramSchmidt.projectionCoeff (b.row src) ((basis b).row col) = 0 := by
  have hsrc_toList : b.rows.toList[src.val]! = b.row src := by simp [Matrix.row, Hex.Matrix.getRow]
  have hbasis_col :
      (basis b).row col = (GramSchmidt.basisRows b.rows.toList)[col.val]! := by
    simpa [basis] using
      GramSchmidt.basisMatrix_row_eq_basisRows_get! (b := b) col.val col.isLt
  have hreduce :
      GramSchmidt.reduceAgainstBasis
          ((GramSchmidt.basisRows b.rows.toList).take col.val).reverse (b.row src) = 0 := by
    have key :=
      GramSchmidt.gapH32
        (rows := b.rows.toList) (j := src.val) (k := col.val) hsrccol
        (by simp [Vector.length_toList, Nat.le_of_lt col.isLt])
    rw [hsrc_toList] at key
    exact key
  have hproj :=
    GramSchmidt.gapH175
      (basisRev := ((GramSchmidt.basisRows b.rows.toList).take col.val).reverse)
      (row := b.row src) (basisRow := (basis b).row col)
      (by
        intro other hother
        rw [List.mem_reverse] at hother
        rw [List.mem_iff_getElem] at hother
        obtain ⟨idx, hidx, hget⟩ := hother
        have hh559 : ((GramSchmidt.basisRows b.rows.toList).take col.val).length = col.val := by
          rw [List.length_take]
          have hbasis_len : (GramSchmidt.basisRows b.rows.toList).length = n := by
            simp [GramSchmidt.basisRows_length]
          omega
        have hidx_col : idx < col.val := by
          rw [hh559] at hidx
          exact hidx
        have hbasis_len : (GramSchmidt.basisRows b.rows.toList).length = n := by
          simp [GramSchmidt.basisRows_length]
        have hh538 : idx < (GramSchmidt.basisRows b.rows.toList).length := by
          rw [hbasis_len]
          exact Nat.lt_trans hidx_col col.isLt
        have hother_get :
            other = (GramSchmidt.basisRows b.rows.toList)[idx]! := by
          rw [← hget, List.getElem_take]
          simp [hh538]
        rw [hother_get, hbasis_col]
        exact GramSchmidt.gapH190
          (b := b) idx col.val (Nat.lt_trans hidx_col col.isLt) col.isLt
          (Nat.ne_of_lt hidx_col))
  rw [hreduce] at hproj
  have hzero : GramSchmidt.projectionCoeff (0 : Vector Rat m) ((basis b).row col) = 0 := by
    by_cases hnorm : ((basis b).row col).dotProduct ((basis b).row col) = 0
    · simp [GramSchmidt.projectionCoeff, hnorm]
    · have hdot : (0 : Vector Rat m).dotProduct ((basis b).row col) = 0 := by
        unfold Vector.dotProduct
        induction List.finRange m with
        | nil => rfl
        | cons idx rest ih =>
            simp only [List.foldl_cons]
            have hentry : (0 : Vector Rat m)[idx] = 0 := by
              change (0 : Vector Rat m)[idx.val] = 0
              rw [Vector.getElem_zero]
            rw [hentry, show (0 : Rat) + 0 * ((basis b).row col)[idx] = 0 by grind]
            exact ih
      have hh561 : (0 : Rat) / ((basis b).row col).dotProduct ((basis b).row col) = 0 := by
        grind
      simp [GramSchmidt.projectionCoeff, hnorm, hdot, hh561]
  simpa [hzero] using hproj.symm
private theorem gapH451 (b : Matrix Rat n m) (i j : Fin n) :
    (Matrix.rowSwap b i j).row i = b.row j := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[i][c] = b[j][c]
  rw [Matrix.getElem_rowSwap (M := b) (i := i) (j := j) (r := i) (k := c)]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]
private theorem gapH438 (b : Matrix Rat n m) (i j : Fin n) :
    (Matrix.rowSwap b i j).row j = b.row i := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[j][c] = b[i][c]
  rw [Matrix.getElem_rowSwap (M := b) (i := i) (j := j) (r := j) (k := c)]
  simp
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
theorem coeffs_rowSwap_adjacent_lower_prev (b : Matrix Rat n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row km1 = b.row k :=
    gapH451 b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := km1) (j := j) hj,
    coeffs_lower_projection (b := b) (i := k) (j := j) (Nat.lt_trans hj hkm1k), hrow, hbasis]
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_curr (b : Matrix Rat n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row k = b.row km1 :=
    gapH438 b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := k) (j := j)
    (by omega)]
  rw [coeffs_lower_projection (b := b) (i := km1) (j := j) hj, hrow, hbasis]
@[grind =]
theorem coeffs_rowAdd_lower (b : Matrix Rat n m) (col src dst : Fin n)
    (hcolsrc : col.val < src.val) (hsrcdst : src.val < dst.val) (c : Rat) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col +
        c * GramSchmidt.entry (coeffs b) src col := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  have hcd := Nat.lt_trans hcolsrc hsrcdst
  rw [coeffs_lower (b.rowAdd src dst c) hcd, coeffs_lower b hcd, coeffs_lower b hcolsrc, hbasis]
  have hrow : (b.rowAdd src dst c).getRow dst = b.getRow dst + c • b.getRow src := by
    show Matrix.row (b.rowAdd src dst c) dst = _
    rw [Matrix.row_rowAdd_dst]
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul] <;> rfl
  have hrowRow : (b.rowAdd src dst c).row dst = b.row dst + c • b.row src := hrow
  rw [hrowRow, GramSchmidt.gapH124, GramSchmidt.gapH116]
@[grind =]
theorem coeffs_rowAdd_above_pivot (b : Matrix Rat n m) (src col dst : Fin n)
    (hsrccol : src.val < col.val) (hcoldst : col.val < dst.val) (c : Rat) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col := by
  have hsrcdst : src.val < dst.val := Nat.lt_trans hsrccol hcoldst
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  have hzero := gapH151 (b := b) (src := src) (col := col)
    hsrccol
  have hzero_get :
      GramSchmidt.projectionCoeff (b.getRow src) ((basis b).getRow col) = 0 := hzero
  rw [coeffs_lower (b.rowAdd src dst c) hcoldst, coeffs_lower b hcoldst, hbasis]
  have hrow : (b.rowAdd src dst c).getRow dst = b.getRow dst + c • b.getRow src := by
    show Matrix.row (b.rowAdd src dst c) dst = _
    rw [Matrix.row_rowAdd_dst]
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul] <;> rfl
  have hrowRow : (b.rowAdd src dst c).row dst = b.row dst + c • b.row src := hrow
  rw [hrowRow]
  rw [GramSchmidt.gapH124, GramSchmidt.gapH116,
    hzero]
  grind
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
private theorem gapH64
    (b : Matrix Rat n m) (i p : Nat) (hi : i < n) (hp : p < n)
    (hsucc : p + 1 = i) :
    GramSchmidt.prefixSpan (basis b) p hp
      (b.row ⟨i, hi⟩ - (basis b).row ⟨i, hi⟩) := by
  subst i
  refine ⟨GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
      (p + 1) (Nat.le_of_lt hi), ?_⟩
  change
    Matrix.vecMul (GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
          (p + 1) (Nat.le_of_lt hi)) (GramSchmidt.prefixRows (basis b) p hp) =
      b.row ⟨p + 1, hi⟩ - (basis b).row ⟨p + 1, hi⟩
  rw [← GramSchmidt.strictPrefixRows_succ_eq_prefixRows
    (M := basis b) (i := p) (hi := hi)]
  have hpc :
      GramSchmidt.prefixCombination (coeffs b) (basis b) (p + 1) hi =
        Matrix.vecMul (GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
            (p + 1) (Nat.le_of_lt hi)) (GramSchmidt.strictPrefixRows (basis b) (p + 1)
            (Nat.le_of_lt hi)) := by
    simpa [basis, coeffs] using
      GramSchmidt.prefixCombination_eq_strictPrefixRowCombination
        (b := b) (i := p + 1) (hi := hi)
  rw [← hpc]
  have hdec := basis_decomposition b (p + 1) hi
  apply Vector.ext
  intro col hcol
  have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
  rw [Vector.getElem_sub]
  simp only [Vector.getElem_add] at hdec_col
  grind
private theorem gapH110
    (b : Matrix Rat n m) (i p : Nat) (hi : i < n) (hp : p < n)
    (hsucc : p + 1 = i) :
    ∀ j : Fin (p + 1),
      ((basis b).row ⟨i, hi⟩).dotProduct
        ((GramSchmidt.prefixRows (basis b) p hp).row j) = 0 := by
  subst i
  intro j
  have hjn : j.val < n := Nat.lt_trans j.isLt hi
  have hrow :
      (GramSchmidt.prefixRows (basis b) p hp).row j =
        (basis b).row ⟨j.val, hjn⟩ := by
    apply Vector.ext
    intro col hcol
    simp [GramSchmidt.prefixRows, Matrix.row]
  rw [hrow]
  exact basis_orthogonal b (p + 1) j.val hi hjn (by omega)
private theorem gapH264 (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  let p := i.val - 1
  have hp : p < n := by
    dsimp [p]
    exact Nat.lt_of_le_of_lt (Nat.pred_le i.val) i.isLt
  have hsucc : p + 1 = i.val := by
    dsimp [p]
    omega
  have hkp : k.val ≤ p := by
    dsimp [p]
    omega
  have hsource :
      (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply Vector.ext
    intro col hcol
    let c : Fin m := ⟨col, hcol⟩
    change (Matrix.rowSwap b km1 k)[i][c] = b[i][c]
    rw [Matrix.getElem_rowSwap]
    have hik : i ≠ k := by
      intro h
      exact Nat.ne_of_gt hi (congrArg Fin.val h)
    have hikm1 : i ≠ km1 := by
      intro h
      have hval := congrArg Fin.val h
      omega
    simp [hik, hikm1]
  have horig_span :
      GramSchmidt.prefixSpan (basis b) p hp
        (b.row i - (basis b).row i) :=
    gapH64 (b := b) (i := i.val) (p := p)
      (hi := i.isLt) (hp := hp) hsucc
  have hswap_span :
      GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp
        (b.row i - (basis (Matrix.rowSwap b km1 k)).row i) := by
    have hraw :=
      gapH64 (b := Matrix.rowSwap b km1 k)
        (i := i.val) (p := p) (hi := i.isLt) (hp := hp) hsucc
    simpa [hsource] using hraw
  have hswap_to_orig :
      ∀ v : Vector Rat m,
        GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp v →
          GramSchmidt.prefixSpan (basis b) p hp v := by
    intro v hv
    have hswap_input := (basis_span (Matrix.rowSwap b km1 k) p hp v).1 hv
    have hinput :=
      (GramSchmidt.gapH66
        (b := b) (km1 := km1) (k := k) (i := p) (hi := hp)
        hkm1 hkp v).1 hswap_input
    exact (basis_span b p hp v).2 hinput
  have horig_rows_to_swap :
      ∀ j : Fin (p + 1),
        GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp
          ((GramSchmidt.prefixRows (basis b) p hp).row j) := by
    intro j
    have horig_basis :
        GramSchmidt.prefixSpan (basis b) p hp
          ((GramSchmidt.prefixRows (basis b) p hp).row j) :=
      GramSchmidt.prefixSpan_row (basis b) p hp j
    have horig_input :=
      (basis_span b p hp ((GramSchmidt.prefixRows (basis b) p hp).row j)).1 horig_basis
    have hswap_input :=
      (GramSchmidt.gapH66
        (b := b) (km1 := km1) (k := k) (i := p) (hi := hp)
        hkm1 hkp ((GramSchmidt.prefixRows (basis b) p hp).row j)).2 horig_input
    exact
      (basis_span (Matrix.rowSwap b km1 k) p hp
        ((GramSchmidt.prefixRows (basis b) p hp).row j)).2 hswap_input
  have horig_orth :=
    gapH110 (b := b) (i := i.val) (p := p)
      (hi := i.isLt) (hp := hp) hsucc
  have hswap_orth :=
    gapH110 (b := Matrix.rowSwap b km1 k)
      (i := i.val) (p := p) (hi := i.isLt) (hp := hp) hsucc
  have hres :=
    GramSchmidt.gapH243
      (A := basis b) (B := basis (Matrix.rowSwap b km1 k)) (i := p) (hi := hp)
      (row := b.row i) (r := (basis b).row i)
      (s := (basis (Matrix.rowSwap b km1 k)).row i)
      horig_span hswap_span hswap_to_orig horig_rows_to_swap horig_orth hswap_orth
  exact hres.symm
@[grind =]
theorem basis_rowSwap_of_after (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i :=
  gapH264 b km1 k i hkm1 hi
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
@[grind =]
theorem coeffs_rowSwap_adjacent_after_low (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hkm1k : km1.val < k.val := by omega
  have hji : j.val < i.val := by omega
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
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji,
    coeffs_lower_projection (b := b) (i := i) (j := j) hji, hrow, hbasis]
@[grind =]
theorem coeffs_rowSwap_adjacent_after_high (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : k.val < j.val)
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
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
    exact basis_rowSwap_of_after (b := b) (km1 := km1) (k := k) (i := j) hkm1 hj
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
theorem basis_rowSwap_of_after (b : Matrix Int n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis, GramSchmidt.Rat.basis, gapH24] using
    GramSchmidt.Rat.basis_rowSwap_of_after
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) hkm1 hi
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_prev (b : Matrix Int n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH24] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_lower_prev
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (j := j) hkm1 hj
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_curr (b : Matrix Int n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH24] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_lower_curr
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (j := j) hkm1 hj
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
theorem coeffs_rowSwap_adjacent_after_low (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH24] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_after_low
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hj
@[grind =]
theorem coeffs_rowSwap_adjacent_after_high (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : k.val < j.val)
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH24] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_after_high
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hj hji
@[grind =]
theorem coeffs_rowAdd_lower (b : Matrix Int n m) (col src dst : Fin n)
    (hcolsrc : col.val < src.val) (hsrcdst : src.val < dst.val) (c : Int) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col +
        (c : Rat) * GramSchmidt.entry (coeffs b) src col := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH137] using
    GramSchmidt.Rat.coeffs_rowAdd_lower
      (b := GramSchmidt.castIntMatrix b) (col := col) (src := src) (dst := dst)
      hcolsrc hsrcdst (c := (c : Rat))
@[grind =]
theorem coeffs_rowAdd_above_pivot (b : Matrix Int n m) (src col dst : Fin n)
    (hsrccol : src.val < col.val) (hcoldst : col.val < dst.val) (c : Int) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    gapH137] using
    GramSchmidt.Rat.coeffs_rowAdd_above_pivot
      (b := GramSchmidt.castIntMatrix b) (src := src) (col := col) (dst := dst)
      hsrccol hcoldst (c := (c : Rat))
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
private theorem gapH198
    (cols : List Nat) (rows gram : Array (Array Int)) (row i j : Nat)
    (hij : i < j) (hcols : ∀ c ∈ cols, c ≤ row) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        i j =
      getArrayEntry rows i j := by
  induction cols generalizing rows with
  | nil =>
      simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have hcols_tail : ∀ c ∈ cols, c ≤ row := by
        intro c hc
        exact hcols c (List.mem_cons_of_mem col hc)
      rw [ih _ hcols_tail]
      by_cases hrow : i = row
      · subst row
        have hcol_le : col ≤ i := hcols col (by simp)
        rw [gapH1]
        omega
      · rw [gapH4]
        exact hrow
private theorem gapH237
    (rowList : List Nat) (rows gram : Array (Array Int)) (i j : Nat)
    (hij : i < j) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i j =
      getArrayEntry rows i j := by
  induction rowList generalizing rows with
  | nil =>
      simp
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih _, gapH198]
      · exact hij
      · intro c hc
        rw [List.mem_range'] at hc
        omega
private theorem gapH148
    (b : Matrix Int n m) (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffRowsSchur b) i j = 0 := by
  simp [scaledCoeffRowsSchur]
  rw [gapH237]
  · exact gapH107 n i j
  · exact hij
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
private theorem gapH5
    {n : Nat} (a b : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none)
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = none) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have hh512 :=
      gapH222 a b state h_init h_sing
    rw [h_final] at hh512
    nomatch hh512
private theorem gapH96
    {n : Nat} (a b : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = some s)
    (hs_after : state.step + a ≤ s) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have hh512 :=
      gapH222 a b state h_init h_sing
    rw [h_final] at hh512
    injection hh512 with hks
    have hk_lt : k.val < state.step + a :=
      noPivotLoop_singularStep_lt a state h_init k.val h_sing
    omega
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
private theorem gapH46
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    getArrayEntry (scaledCoeffRows b) i i = 0 ∨
      getArrayEntry (scaledCoeffRows b) i i =
        Matrix.bareiss
          (Matrix.principalSubmatrix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi)) := by
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
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i = 0 ∨
    getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i =
        Matrix.bareiss
          (Matrix.principalSubmatrix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi))
  rcases hdiag with ⟨h_sing, h_eq⟩ | ⟨s, h_sing, h_cases⟩
  · right
    have h_final :
        (Matrix.noPivotLoop (i + (n - i))
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
      have h_split : i + (n - i) = n := by omega
      simpa [h_split] using h_sing
    have h_prefix :
        (Matrix.noPivotLoop i
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
      gapH5 i (n - i)
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_final
    have h_leading :=
      bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
        (b := b) i hi h_prefix
    have h_eq_noPivot :
        getArrayEntry
          (scaledCoeffArrayLoop n n
            { step := 0
              matrix := gramRows b
              coeffs := zeroRows n
              prevPivot := 1 }).coeffs i i =
          (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[iFin][iFin] := by
      simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq
    exact h_eq_noPivot.trans h_leading
  · rcases h_cases with ⟨_hsi, h_zero⟩ | ⟨his, h_eq⟩
    · left
      simpa [iFin] using h_zero
    · right
      have h_final :
          (Matrix.noPivotLoop (i + (n - i))
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s := by
        have h_split : i + (n - i) = n := by omega
        simpa [h_split] using h_sing
      have h_after : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + i ≤ s := by
        simp [Matrix.noPivotInitialState]
        have : i < s := by
          simpa [iFin] using his
        omega
      have h_prefix :
          (Matrix.noPivotLoop i
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
        gapH96 i (n - i)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_final h_after
      have h_leading :=
        bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
          (b := b) i hi h_prefix
      have h_eq_noPivot :
          getArrayEntry
            (scaledCoeffArrayLoop n n
              { step := 0
                matrix := gramRows b
                coeffs := zeroRows n
                prevPivot := 1 }).coeffs i i =
            (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[iFin][iFin] := by
        simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq
      exact h_eq_noPivot.trans h_leading
@[simp, grind =] theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := by
  rfl
@[grind =] theorem scaledCoeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  rw [scaledCoeffs_entry_eq_getArrayEntry]
  exact gapH148 b i j hij
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
theorem scaledCoeffs_diag_toNat (b : Matrix Int n m) (hquot : StepWitness b)
    (i : Nat) (hi : i < n) :
    (GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩).toNat =
      gramDet b (i + 1) (Nat.succ_le_of_lt hi) := by
  rw [scaledCoeffs_entry_eq_getArrayEntry]
  have hpack :
      (gramDetVec b).get ⟨i + 1, Nat.succ_lt_succ hi⟩ =
        (getArrayEntry (scaledCoeffRowsSchur b) i i).toNat := by
    unfold gramDetVec data
    dsimp only
    change (gramDetVecFromScaledCoeffRows (scaledCoeffRowsSchur b))[i + 1] = _
    unfold gramDetVecFromScaledCoeffRows
    rw [Vector.getElem_ofFn]
  rw [← hpack]
  exact gramDetVec_eq_gramDet (b := b) hquot (i + 1) (Nat.succ_le_of_lt hi)
theorem scaledCoeffs_diag_eq_zero_or_eq_principalSubmatrix_bareiss
    (b : Matrix Int n m) (hquot : StepWitness b)
    (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 0 ∨
      GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
        Matrix.bareiss
          (Matrix.principalSubmatrix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi)) := by
  rw [scaledCoeffs_entry_eq_getArrayEntry,
    getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
  exact gapH46 (b := b) i hi
theorem scaledCoeffs_diag_of_nonneg
    (b : Matrix Int n m) (hquot : StepWitness b)
    (i : Nat) (hi : i < n)
    (hnonneg : 0 ≤ GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  have hdiag := scaledCoeffs_diag_toNat (b := b) hquot i hi
  rw [← hdiag]
  exact (Int.toNat_of_nonneg hnonneg).symm
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
private theorem gapH33 {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') (r : Nat) (hr : r < n')
    (hri : r ≠ i.val) (hrj : r ≠ j.val) :
    (Matrix.rowSwap M i j).getRow ⟨r, hr⟩ = M.getRow ⟨r, hr⟩ :=
  Matrix.row_rowSwap_of_ne M (fun h => hri (congrArg Fin.val h)) (fun h => hrj (congrArg Fin.val h))
private theorem gapH172 {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j).getRow i = M.getRow j :=
  Matrix.row_rowSwap_left M i j
private theorem gapH156 {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j).getRow j = M.getRow i :=
  Matrix.row_rowSwap_right M i j
theorem scaledCoeffMatrix_rowSwap_adjacent_pivot_transpose
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val)
    (hkm1k : km1.val < k.val) :
    GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k =
      (GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose := by
  let t := km1.val + 1
  let ht : t ≤ n := Nat.succ_le_of_lt km1.isLt
  let last : Fin t := ⟨km1.val, Nat.lt_succ_self km1.val⟩
  apply Hex.Matrix.ext_getElem
  intro p q
  have hp_lt_k : p.val < k.val := by
    have := p.isLt
    omega
  have hq_lt_k : q.val < k.val := by
    have := q.isLt
    omega
  have hp_ne_k : (GramSchmidt.liftFinLE p ht).val ≠ k.val := by
    dsimp [GramSchmidt.liftFinLE]
    omega
  have hq_ne_k : (GramSchmidt.liftFinLE q ht).val ≠ k.val := by
    dsimp [GramSchmidt.liftFinLE]
    omega
  have hlast_val : last.val = km1.val := rfl
  by_cases hq_last : q = last
  · have hq_val : q.val = km1.val := by
      simpa [last] using congrArg Fin.val hq_last
    by_cases hp_last : p = last
    · have hp_lift : GramSchmidt.liftFinLE p ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hp_last
      have hq_lift : GramSchmidt.liftFinLE q ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hq_last
      rw [Matrix.getElem_transpose]
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn, Matrix.row]
      rw [if_pos hq_val, if_pos (by simpa [last] using congrArg Fin.val hp_last),
        gapH156]
      rw [hp_lift]
      rw [gapH172]
      rw [hq_lift]
      exact gapH324 _ _
    · have hp_ne_km1 : (GramSchmidt.liftFinLE p ht).val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last, GramSchmidt.liftFinLE] using h))
      have hq_lift : GramSchmidt.liftFinLE q ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hq_last
      have hp_val_ne : p.val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last] using h))
      rw [Matrix.getElem_transpose]
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn, Matrix.row]
      rw [if_pos hq_val, if_neg hp_val_ne, gapH156,
        gapH33]
      · rw [hq_lift]
        exact gapH324 _ _
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
  · have hh557 : q.val ≠ km1.val := by
      intro h
      exact hq_last (Fin.ext (by simpa [last] using h))
    by_cases hp_last : p = last
    · have hp_val : p.val = km1.val := by
        simpa [last] using congrArg Fin.val hp_last
      have hp_lift : GramSchmidt.liftFinLE p ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hp_last
      have hq_ne_km1 : (GramSchmidt.liftFinLE q ht).val ≠ km1.val := by
        intro h
        exact hh557 (by simpa [GramSchmidt.liftFinLE] using h)
      rw [Matrix.getElem_transpose]
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn, Matrix.row]
      rw [if_neg hh557, if_pos hp_val]
      rw [hp_lift]
      rw [gapH172, gapH33]
      · exact gapH324 _ _
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
    · have hp_ne_val : p.val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last] using h))
      have hp_ne_km1 : (GramSchmidt.liftFinLE p ht).val ≠ km1.val := by
        intro h
        exact hp_ne_val (by simpa [GramSchmidt.liftFinLE] using h)
      have hq_ne_km1 : (GramSchmidt.liftFinLE q ht).val ≠ km1.val := by
        intro h
        exact hh557 (by simpa [GramSchmidt.liftFinLE] using h)
      rw [Matrix.getElem_transpose]
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.getElem_ofFn, Matrix.row]
      rw [if_neg hh557, if_neg hp_ne_val, gapH33]
      · rw [gapH33]
        · exact gapH324 _ _
        · dsimp [GramSchmidt.liftFinLE]
          omega
        · dsimp [GramSchmidt.liftFinLE]
          omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
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
theorem coeffs_adjacentSwap_lower_prev (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.coeffs_rowSwap_adjacent_lower_prev
      (b := b) (km1 := km1) (k := k) (j := j) hkm1 hjkm1
theorem coeffs_adjacentSwap_lower_curr (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  simpa [adjacentSwap, km1] using
    GramSchmidt.Int.coeffs_rowSwap_adjacent_lower_curr
      (b := b) (km1 := km1) (k := k) (j := j) hkm1 hjkm1
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
theorem bareiss_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Hex.Matrix.det M :=
  (bareiss_eq_mathlib_det M).trans (det_eq M).symm
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
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  have h_det : GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
    exact_mod_cast scaledCoeffs_lower_eq_det_scaledCoeffMatrix b i j hji
  rw [h_det]
  exact ((HexMatrixTheory.bareiss_eq_mathlib_det
        (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
      (HexMatrixTheory.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm).symm
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
theorem dot_basis_castRow_eq_coeffs_mul_normSq
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((basis b).row ⟨j, Nat.lt_trans hj hi⟩).dotProduct
        (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩)) =
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ *
        ((basis b).row ⟨j, Nat.lt_trans hj hi⟩).normSq := by
  have hjlt : j < n := Nat.lt_trans hj hi
  have hrow := gapH20 b i hi
  show ((basis b).row ⟨j, hjlt⟩).dotProduct (castIntRow b ⟨i, hi⟩) = _
  rw [hrow, dot_add_right_rat]
  rw [basis_orthogonal b j i hjlt hi (Nat.ne_of_lt hj), Rat.zero_add]
  rw [gapH18 (coeffs := coeffs b) (basisM := basis b)
      (i := i) (hi := hi) (u := (basis b).row ⟨j, hjlt⟩)]
  have h_zero_term : ∀ q : Fin i, q.val ≠ j →
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩
            ⟨q.val, Nat.lt_trans q.isLt hi⟩ *
          ((basis b).row ⟨j, hjlt⟩).dotProduct
            ((basis b).row ⟨q.val, Nat.lt_trans q.isLt hi⟩) = 0 := by
    intro q hqj
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt hi
    rw [basis_orthogonal b j q.val hjlt hq_lt_n fun h => hqj h.symm]
    grind
  rw [foldl_finRange_isolate_rat i j hj _ h_zero_term]
  rfl
private theorem gapH126 :
    ∀ (i : Nat) (j₁ j₂ : Nat) (hj₁ : j₁ < i) (hj₂ : j₂ < i) (_hne : j₁ ≠ j₂)
      (f : Fin i → Rat),
      (∀ q : Fin i, q.val ≠ j₁ → q.val ≠ j₂ → f q = 0) →
      (List.finRange i).foldl (fun acc q => acc + f q) 0 =
        f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
  | 0, _, _, hj₁, _, _, _, _ => absurd hj₁ (Nat.not_lt_zero _)
  | i + 1, j₁, j₂, hj₁, hj₂, hne, f, h_zero => by
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h1 : j₁ = i
    ·
      subst h1
      have hj₂_lt : j₂ < j₁ := by
        have h_le : j₂ ≤ j₁ := Nat.lt_succ_iff.mp hj₂
        exact Nat.lt_of_le_of_ne h_le (fun h => hne h.symm)
      have hh562 : ∀ q : Fin j₁, q.val ≠ j₂ → f (Fin.castSucc q) = 0 := by
        intro q hqj₂
        apply h_zero
        · show q.val ≠ j₁
          exact Nat.ne_of_lt q.isLt
        · show q.val ≠ j₂
          exact hqj₂
      have hih := foldl_finRange_isolate_rat j₁ j₂ hj₂_lt
        (fun q => f (Fin.castSucc q)) hh562
      rw [hih]
      have h_cast_j₂ : (Fin.castSucc ⟨j₂, hj₂_lt⟩ : Fin (j₁ + 1)) = ⟨j₂, hj₂⟩ := by
        apply Fin.ext; rfl
      have h_last : (Fin.last j₁ : Fin (j₁ + 1)) = ⟨j₁, hj₁⟩ := by
        apply Fin.ext; rfl
      show f (Fin.castSucc ⟨j₂, hj₂_lt⟩) + f (Fin.last j₁) = f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
      rw [h_cast_j₂, h_last]
      ring
    · by_cases h2 : j₂ = i
      ·
        subst h2
        have hj₁_lt : j₁ < j₂ := by
          have h_le : j₁ ≤ j₂ := Nat.lt_succ_iff.mp hj₁
          exact Nat.lt_of_le_of_ne h_le h1
        have hh562 : ∀ q : Fin j₂, q.val ≠ j₁ → f (Fin.castSucc q) = 0 := by
          intro q hqj₁
          apply h_zero
          · show q.val ≠ j₁
            exact hqj₁
          · show q.val ≠ j₂
            exact Nat.ne_of_lt q.isLt
        have hih := foldl_finRange_isolate_rat j₂ j₁ hj₁_lt
          (fun q => f (Fin.castSucc q)) hh562
        rw [hih]
        have h_cast_j₁ : (Fin.castSucc ⟨j₁, hj₁_lt⟩ : Fin (j₂ + 1)) = ⟨j₁, hj₁⟩ := by
          apply Fin.ext; rfl
        have h_last : (Fin.last j₂ : Fin (j₂ + 1)) = ⟨j₂, hj₂⟩ := by
          apply Fin.ext; rfl
        show f (Fin.castSucc ⟨j₁, hj₁_lt⟩) + f (Fin.last j₂) = f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
        rw [h_cast_j₁, h_last]
      ·
        have hj₁_lt : j₁ < i := by
          have h_le : j₁ ≤ i := Nat.lt_succ_iff.mp hj₁
          exact Nat.lt_of_le_of_ne h_le h1
        have hj₂_lt : j₂ < i := by
          have h_le : j₂ ≤ i := Nat.lt_succ_iff.mp hj₂
          exact Nat.lt_of_le_of_ne h_le h2
        have hlast_zero : f (Fin.last i) = 0 := by
          apply h_zero
          · show (Fin.last i).val ≠ j₁
            show i ≠ j₁
            exact fun h => h1 h.symm
          · show (Fin.last i).val ≠ j₂
            show i ≠ j₂
            exact fun h => h2 h.symm
        rw [hlast_zero, Rat.add_zero]
        have hh562 : ∀ q : Fin i, q.val ≠ j₁ → q.val ≠ j₂ → f (Fin.castSucc q) = 0 := by
          intro q hqj₁ hqj₂
          apply h_zero
          · show q.val ≠ j₁
            exact hqj₁
          · show q.val ≠ j₂
            exact hqj₂
        have hih := gapH126 i j₁ j₂ hj₁_lt hj₂_lt hne
          (fun q => f (Fin.castSucc q)) hh562
        rw [hih]
        have h_cast_j₁ : (Fin.castSucc ⟨j₁, hj₁_lt⟩ : Fin (i + 1)) = ⟨j₁, hj₁⟩ := by
          apply Fin.ext; rfl
        have h_cast_j₂ : (Fin.castSucc ⟨j₂, hj₂_lt⟩ : Fin (i + 1)) = ⟨j₂, hj₂⟩ := by
          apply Fin.ext; rfl
        show f (Fin.castSucc ⟨j₁, hj₁_lt⟩) + f (Fin.castSucc ⟨j₂, hj₂_lt⟩) =
          f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
        rw [h_cast_j₁, h_cast_j₂]
theorem dot_basis_rowSwap_curr_prev_eq_normSq
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row km1) =
      ((basis (Matrix.rowSwap b km1 k)).row k).normSq := by
  have hkm1k : km1.val < k.val := by omega
  have hrow_eq : (Matrix.rowSwap b km1 k).row k = b.row km1 := by
    apply Vector.ext
    intro idx hidx
    let c : Fin m := ⟨idx, hidx⟩
    change (Matrix.rowSwap b km1 k)[k][c] = b[km1][c]
    rw [Matrix.getElem_rowSwap]
    simp
  have hpfx_b_zero :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          (GramSchmidt.prefixCombination (coeffs b) (basis b) km1.val km1.isLt) = 0 := by
    apply gapH9
    intro q
    have hq_lt_km1 : q.val < km1.val := q.isLt
    have hq_lt_k : q.val < k.val := by omega
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt km1.isLt
    have hbeq : (basis b).row ⟨q.val, hq_lt_n⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨q.val, hq_lt_n⟩ :=
      (basis_rowSwap_of_before b km1 k ⟨q.val, hq_lt_n⟩ hkm1k hq_lt_km1).symm
    rw [hbeq]
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (Nat.ne_of_gt hq_lt_k)
  have hpfx_b'_zero :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          (GramSchmidt.prefixCombination (coeffs (Matrix.rowSwap b km1 k))
            (basis (Matrix.rowSwap b km1 k)) k.val k.isLt) = 0 := by
    apply gapH9
    intro q
    have hq_lt_k : q.val < k.val := q.isLt
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt k.isLt
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (Nat.ne_of_gt hq_lt_k)
  have hdot_cast_b_km1 :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          (Vector.map (fun x : Int => (x : Rat)) (b.row km1)) =
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row km1) := by
    have hdec := basis_decomposition b km1.val km1.isLt
    show ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨km1.val, km1.isLt⟩)) = _
    rw [hdec, dot_add_right_rat, hpfx_b_zero, Rat.add_zero]
  have hdot_cast_b'_k :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row k)) =
      ((basis (Matrix.rowSwap b km1 k)).row k).normSq := by
    have hdec := basis_decomposition (Matrix.rowSwap b km1 k) k.val k.isLt
    show ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row ⟨k.val, k.isLt⟩)) = _
    rw [hdec, dot_add_right_rat, hpfx_b'_zero, Rat.add_zero]
    rfl
  have hcast_eq :
      Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row k) =
      Vector.map (fun x : Int => (x : Rat)) (b.row km1) := by
    rw [hrow_eq]
  rw [← hdot_cast_b_km1, ← hcast_eq, hdot_cast_b'_k]
theorem dot_basis_rowSwap_curr_castRow_eq
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val)
    (i : Fin n) (hki : k.val < i.val) :
    ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row km1) *
        (GramSchmidt.entry (coeffs b) i ⟨km1.val, Nat.lt_trans (Nat.lt_of_succ_le
          (le_of_eq hkm1)) k.isLt⟩ -
         GramSchmidt.entry (coeffs b) k ⟨km1.val, Nat.lt_trans (Nat.lt_of_succ_le
          (le_of_eq hkm1)) k.isLt⟩ *
         GramSchmidt.entry (coeffs b) i k) := by
  have hkm1k : km1.val < k.val := by omega
  have hh543 : km1.val < i.val := by omega
  have hh545 : km1.val < n := Nat.lt_trans hkm1k k.isLt
  set D : Rat := ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row km1) with hD_def
  have hdec_b_i := basis_decomposition b i.val i.isLt
  show ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
      (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i.val, i.isLt⟩)) = _
  rw [hdec_b_i, dot_add_right_rat]
  have hdot_basis_i :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row ⟨i.val, i.isLt⟩) = 0 := by
    have hh525 : (basis b).row ⟨i.val, i.isLt⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨i.val, i.isLt⟩ :=
      (basis_rowSwap_of_after b km1 k ⟨i.val, i.isLt⟩ hkm1 hki).symm
    rw [hh525]
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val i.val k.isLt i.isLt (Nat.ne_of_lt hki)
  rw [hdot_basis_i, Rat.zero_add]
  rw [gapH18 (coeffs := coeffs b) (basisM := basis b)
      (i := i.val) (hi := i.isLt) (u := (basis (Matrix.rowSwap b km1 k)).row k)]
  have hkm1_ne_k_val : km1.val ≠ k.val := by omega
  set f : Fin i.val → Rat := fun q =>
    GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
        ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩) with hf_def
  have h_zero : ∀ q : Fin i.val, q.val ≠ km1.val → q.val ≠ k.val → f q = 0 := by
    intro q hq_km1 hq_k
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt i.isLt
    have hbasis_eq_q : (basis b).row ⟨q.val, hq_lt_n⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨q.val, hq_lt_n⟩ := by
      by_cases hcase : q.val < km1.val
      · exact (basis_rowSwap_of_before b km1 k ⟨q.val, hq_lt_n⟩ hkm1k hcase).symm
      · have hge_km1 : km1.val ≤ q.val := Nat.le_of_not_lt hcase
        have h_gt_km1 : km1.val < q.val := Nat.lt_of_le_of_ne hge_km1 (fun h => hq_km1 h.symm)
        have h_gt_k : k.val < q.val := by omega
        exact (basis_rowSwap_of_after b km1 k ⟨q.val, hq_lt_n⟩ hkm1 h_gt_k).symm
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ _ *
        ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩) = 0
    rw [hbasis_eq_q]
    rw [basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (fun h => hq_k h.symm)]
    grind
  have hfoldl_eq :
      (List.finRange i.val).foldl (fun (acc : Rat) (q : Fin i.val) => acc + f q) 0 =
      f ⟨km1.val, hh543⟩ + f ⟨k.val, hki⟩ :=
    gapH126 i.val km1.val k.val hh543 hki hkm1_ne_k_val f h_zero
  show (List.finRange i.val).foldl
      (fun (acc : Rat) (q : Fin i.val) =>
        acc + GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
              ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
            ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
              ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩)) 0 = _
  rw [show (fun (acc : Rat) (q : Fin i.val) =>
        acc + GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
              ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
            ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
              ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩)) =
       (fun (acc : Rat) (q : Fin i.val) => acc + f q) from rfl]
  rw [hfoldl_eq]
  set μ : Rat := GramSchmidt.entry (coeffs b) k km1 with hμ_def
  have hh526 :
      (basis (Matrix.rowSwap b km1 k)).row km1 = (basis b).row k + μ • (basis b).row km1 :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  have hdot_swap_zero :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        ((basis (Matrix.rowSwap b km1 k)).row km1) = 0 :=
    basis_orthogonal (Matrix.rowSwap b km1 k) k.val km1.val k.isLt km1.isLt
      (fun h => Nat.lt_irrefl km1.val (h ▸ hkm1k))
  have hdot_curr :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row k) = -μ * D := by
    have h := hdot_swap_zero
    rw [hh526] at h
    rw [dot_add_right_rat, dot_smul_right_rat] at h
    have hD_eq : ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        ((basis b).row km1) = D := rfl
    rw [hD_eq] at h
    linarith
  show f ⟨km1.val, hh543⟩ + f ⟨k.val, hki⟩ = D * _
  have hf_km1 : f ⟨km1.val, hh543⟩ =
      GramSchmidt.entry (coeffs b) i ⟨km1.val, hh545⟩ * D := by
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨km1.val, _⟩ *
        ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          ((basis b).row ⟨km1.val, _⟩) = _
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨km1.val, hh545⟩ *
        ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          ((basis b).row ⟨km1.val, hh545⟩) =
        GramSchmidt.entry (coeffs b) i ⟨km1.val, hh545⟩ * D
    have hi_eq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    have hkm1_eq : (⟨km1.val, hh545⟩ : Fin n) = km1 := Fin.ext rfl
    rw [hi_eq, hkm1_eq]
  have hf_k : f ⟨k.val, hki⟩ =
      GramSchmidt.entry (coeffs b) i k * (-μ * D) := by
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨k.val, _⟩ *
        ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          ((basis b).row ⟨k.val, _⟩) = _
    have hi_eq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    have hk_eq : (⟨k.val, Nat.lt_trans hki i.isLt⟩ : Fin n) = k := Fin.ext rfl
    rw [hi_eq, hk_eq, hdot_curr]
  rw [hf_km1, hf_k]
  ring
theorem scaledCoeffs_eq_scaledCoeffMatrix_det
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  rw [scaledCoeffs_eq_scaledCoeffMatrix_bareiss]
  exact
    (HexMatrixTheory.bareiss_eq_mathlib_det
        (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
      (HexMatrixTheory.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm
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
theorem scaledCoeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  let hk : i + 1 ≤ n := Nat.succ_le_of_lt hi
  rcases scaledCoeffs_diag_eq_zero_or_eq_principalSubmatrix_bareiss b (StepWitness.ofGram b)
      i hi with hzero | hbareiss
  · have hnat := scaledCoeffs_diag_toNat (b := b) (StepWitness.ofGram b) i hi
    rw [hzero] at hnat
    simp at hnat
    rw [hzero, ← hnat]
    simp
  · apply scaledCoeffs_diag_of_nonneg b (StepWitness.ofGram b)
    rw [hbareiss]
    have hbareiss_eq :
        Matrix.bareiss
            (Matrix.principalSubmatrix (Matrix.gramMatrix b) (i + 1) hk) =
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (i + 1) hk) := by
      rw [← GramSchmidt.leadingGramMatrixInt_eq_principalSubmatrix_gram]
      exact HexMatrixTheory.bareiss_eq_det
        (GramSchmidt.leadingGramMatrixInt b (i + 1) hk)
    rw [hbareiss_eq]
    exact leadingGramMatrixInt_det_nonneg b (i + 1) hk
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
private theorem gapH273 {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (k : Fin m') :
    (Matrix.rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] :=
  Matrix.getElem_rowAdd M src dst r c k
private theorem gapH270 {n' : Nat} (xs : List (Fin n'))
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
private theorem gapH86 {n' : Nat} (u v : Vector Int n') :
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using
    gapH270 (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl
private theorem gapH55 {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (hr : r.val ≠ dst.val) :
    (Matrix.rowAdd M src dst c)[r] = M[r] := by
  rw [Matrix.rowAdd_eq_set]
  exact Hex.Matrix.setRow_row_ne M dst r _ (fun heq => hr (congrArg Fin.val heq))
private theorem gapH398 {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m')
    (xs : List (Fin m')) (acc accX accY : Int) (hacc : acc = accX + c * accY) :
    xs.foldl (fun a i => a + (Matrix.rowAdd M src dst c)[dst][i] * w[i]) acc =
      xs.foldl (fun a i => a + M[dst][i] * w[i]) accX +
        c * xs.foldl (fun a i => a + M[src][i] * w[i]) accY := by
  induction xs generalizing acc accX accY with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      have hentry : (Matrix.rowAdd M src dst c)[dst][i] = M[dst][i] + c * M[src][i] := by
        rw [gapH273]
        simp
      rw [hentry, hacc]
      grind
private theorem gapH161 {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    ((Matrix.rowAdd M src dst c)[dst]).dotProduct w =
      M[dst].dotProduct w + c * M[src].dotProduct w := by
  simp only [Vector.dotProduct]
  exact gapH398 M src dst c w (List.finRange m')
    0 0 0 (by show (0 : Int) = 0 + c * 0; grind)
private theorem gapH87 {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    w.dotProduct ((Matrix.rowAdd M src dst c)[dst]) =
      w.dotProduct M[dst] + c * w.dotProduct M[src] := by
  rw [gapH86 w, gapH161, gapH86 w M[dst], gapH86 w M[src]]
theorem scaledCoeffMatrix_rowAdd_pivot_det
    (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val) (c : Int) :
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
        c * Matrix.det
          (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  let t := j.val + 1
  let ht : t ≤ n := Nat.succ_le_of_lt j.isLt
  let last : Fin t := ⟨j.val, Nat.lt_succ_self j.val⟩
  let M := GramSchmidt.leadingGramMatrixInt b t ht
  let oldCol : Fin t → Int := fun p =>
    (b.row (GramSchmidt.liftFinLE p ht)).dotProduct (b.row k)
  let gramCol : Fin t → Int := fun p =>
    (b.row (GramSchmidt.liftFinLE p ht)).dotProduct (b.row j)
  have hnew :
      GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk =
        Matrix.setCol M last (fun p => oldCol p + c * gramCol p) := by
    apply Hex.Matrix.ext_getElem
    intro p qf
    have hp_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val := by
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_iff.mp hjk))
    have hp_row :
        (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
          b[GramSchmidt.liftFinLE p ht] :=
      gapH55 b j k (GramSchmidt.liftFinLE p ht) c hp_ne
    by_cases hqj : qf.val = j.val
    · have hqNat : qf.val = j.val := hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Hex.Matrix.getElem_setCol,
        Hex.Matrix.getElem_ofFn, hqNat, ite_true]
      rw [if_pos hq_last]
      simp only [Matrix.row]
      change ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht]).dotProduct
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      rw [hp_row]
      change (b.row (GramSchmidt.liftFinLE p ht)).dotProduct
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      exact gapH87 b j k c (b.row (GramSchmidt.liftFinLE p ht))
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : qf.val ≠ j.val := hqj
      have hq_ne_k : (GramSchmidt.liftFinLE qf ht).val ≠ k.val := by
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le qf.isLt (Nat.succ_le_iff.mp hjk))
      have hq_row :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE qf ht] =
            b[GramSchmidt.liftFinLE qf ht] :=
        gapH55 b j k (GramSchmidt.liftFinLE qf ht) c hq_ne_k
      simp only [GramSchmidt.scaledCoeffMatrix, Hex.Matrix.getElem_setCol,
        Hex.Matrix.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      simp only [Matrix.row, ← Hex.Matrix.getElem_eq_getRow]
      rw [hp_row, hq_row]
      show _ = (GramSchmidt.leadingGramMatrixInt b t ht)[p][qf]
      rw [gapH16]
  have hold :
      GramSchmidt.scaledCoeffMatrix b k j hjk =
        Matrix.setCol M last oldCol := by
    apply Hex.Matrix.ext_getElem
    intro p qf
    by_cases hqj : qf.val = j.val
    · have hqNat : qf.val = j.val := hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Hex.Matrix.getElem_setCol,
        Hex.Matrix.getElem_ofFn, hqNat, ite_true]
      rw [if_pos hq_last]
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : qf.val ≠ j.val := hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Hex.Matrix.getElem_setCol,
        Hex.Matrix.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      show _ = (GramSchmidt.leadingGramMatrixInt b t ht)[p][qf]
      rw [gapH16]
      rfl
  have hgram :
      Matrix.setCol M last gramCol = M := by
    apply Hex.Matrix.ext_getElem
    intro p qf
    by_cases hq_last : qf = last
    · have hq_lift : GramSchmidt.liftFinLE qf ht = j := by
        apply Fin.ext
        show (qf : Nat) = (j : Nat)
        have hval := congrArg Fin.val hq_last
        simpa [last] using hval
      simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Hex.Matrix.getElem_setCol,
        Hex.Matrix.getElem_ofFn]
      rw [if_pos hq_last, hq_lift]
    · simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Hex.Matrix.getElem_setCol,
        Hex.Matrix.getElem_ofFn]
      rw [if_neg hq_last]
  calc
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk)
        = Matrix.det (Matrix.setCol M last (fun p => oldCol p + c * gramCol p)) := by
          rw [hnew]
    _ = Matrix.det (Matrix.setCol M last oldCol) +
          Matrix.det (Matrix.setCol M last (fun p => c * gramCol p)) := by
          rw [Matrix.det_setCol_add]
    _ = Matrix.det (Matrix.setCol M last oldCol) +
          c * Matrix.det (Matrix.setCol M last gramCol) := by
          rw [Matrix.det_setCol_smul]
    _ = Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
          rw [← hold, hgram]
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
theorem scaledCoeffs_rowAdd_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j +
        c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  have hnew := scaledCoeffs_eq_scaledCoeffMatrix_det
    (b := Matrix.rowAdd b j k c) (i := k) (j := j) hjk
  have hold := scaledCoeffs_eq_scaledCoeffMatrix_det (b := b) (i := k) (j := j) hjk
  have hbridge := scaledCoeffMatrix_rowAdd_pivot_det (b := b) (j := j) (k := k) hjk c
  have hlead := leadingGramMatrixInt_det_eq_gramDet_int
    (b := b) (t := j.val + 1) (ht := Nat.succ_le_of_lt j.isLt)
  calc
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
        Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) := hnew
    _ =
        Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1)
              (Nat.succ_le_of_lt j.isLt)) := hbridge
    _ =
        GramSchmidt.entry (scaledCoeffs b) k j +
          c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
      rw [← hold, hlead]
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
private theorem gapH56 {a b : Int}
    (h : (a : Rat) = (b : Rat)) : a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega
private theorem gapH17 (b : Matrix Int n m) (i j : Fin n)
    (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
        GramSchmidt.entry (coeffs b) i j := by
  simpa using scaledCoeffs_eq (b := b) i.val j.val i.isLt hji
theorem scaledCoeffs_rowAdd_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l +
        c * GramSchmidt.entry (scaledCoeffs b) j l := by
  apply gapH56
  have hlk : l.val < k.val := Nat.lt_trans hlj hjk
  have hnew := gapH17 (b := Matrix.rowAdd b j k c) k l hlk
  have holdk := gapH17 (b := b) k l hlk
  have holdj := gapH17 (b := b) j l hlj
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_lower (b := b) l j k hlj hjk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            (GramSchmidt.entry (coeffs b) k l +
              (c : Rat) * GramSchmidt.entry (coeffs b) j l) := by
          rw [hdet, hcoeff]
    _ =
          ((GramSchmidt.entry (scaledCoeffs b) k l +
            c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
          calc
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                (GramSchmidt.entry (coeffs b) k l +
                  (c : Rat) * GramSchmidt.entry (coeffs b) j l)
                =
                  (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                    GramSchmidt.entry (coeffs b) k l +
                    (c : Rat) *
                      ((gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                        GramSchmidt.entry (coeffs b) j l) := by
                  grind
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) +
                    (c : Rat) *
                      ((GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  rw [← holdk, ← holdj]
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l +
                    c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  grind
theorem scaledCoeffs_rowAdd_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (i : Fin n) (hik : i ≠ k) :
    (scaledCoeffs (Matrix.rowAdd b j k c)).row i = (scaledCoeffs b).row i := by
  apply Vector.ext
  intro col hcol
  let l : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l =
    GramSchmidt.entry (scaledCoeffs b) i l
  by_cases hli : l.val < i.val
  · apply gapH56
    have hnew := gapH17 (b := Matrix.rowAdd b j k c) i l hli
    have hold := gapH17 (b := b) i l hli
    have hdet :
        gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
          gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
      gramDet_rowAdd_earlier b j k c (l.val + 1)
        (Nat.succ_le_of_lt l.isLt) hjk
    have hrow := coeffs_rowAdd_other_row (b := b) j k c hjk i hik
    have hcoeff :
        GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l =
          GramSchmidt.entry (coeffs b) i l := by
      have hget := congrArg (fun row => row[l]) hrow
      simpa [GramSchmidt.entry] using hget
    calc
      ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l : Int) : Rat)
          =
            (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
                (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l := hnew
      _ =
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs b) i l := by
            rw [hdet, hcoeff]
      _ = ((GramSchmidt.entry (scaledCoeffs b) i l : Int) : Rat) := hold.symm
  · by_cases hil : i = l
    · subst l
      rw [← hil, scaledCoeffs_diag, scaledCoeffs_diag]
      exact congrArg Int.ofNat
        (gramDet_rowAdd_earlier b j k c (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) hjk)
    · have hilv : i.val < l.val := by
        have hle : i.val ≤ l.val := Nat.le_of_not_lt hli
        exact Nat.lt_of_le_of_ne hle (fun h => hil (Fin.ext h))
      rw [scaledCoeffs_upper (Matrix.rowAdd b j k c) i.val l.val i.isLt l.isLt hilv,
        scaledCoeffs_upper b i.val l.val i.isLt l.isLt hilv]
theorem scaledCoeffs_rowAdd_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l := by
  apply gapH56
  have hnew := gapH17 (b := Matrix.rowAdd b j k c) k l hlk
  have hold := gapH17 (b := b) k l hlk
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_above_pivot (b := b) j l k hjl hlk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs b) k l := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) := hold.symm
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
end HexMatrixTheory
end
end
section
section
namespace HexLLLTheory
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
theorem scaledCoeffs_sizeReduce_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j -
        r * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  rw [sizeReduce, scaledCoeffs_rowAdd_pivot (b := b) (j := j) (k := k) hjk (-r),
    Int.neg_mul, Lean.Grind.Ring.sub_eq_add_neg]
theorem scaledCoeffs_sizeReduce_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (r : Int) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l -
        r * GramSchmidt.entry (scaledCoeffs b) j l := by
  rw [sizeReduce, scaledCoeffs_rowAdd_lower (b := b) (l := l) (j := j) (k := k) hlj hjk (-r),
    Int.neg_mul, Lean.Grind.Ring.sub_eq_add_neg]
theorem scaledCoeffs_sizeReduce_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (i : Fin n) (hik : i ≠ k) :
    (scaledCoeffs (sizeReduce b j k r)).row i = (scaledCoeffs b).row i := by
  rw [sizeReduce]
  exact scaledCoeffs_rowAdd_other_row (b := b) (j := j) (k := k) hjk (-r) i hik
theorem scaledCoeffs_sizeReduce_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (r : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (scaledCoeffs (sizeReduce b j k r)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l := by
  rw [sizeReduce]
  exact scaledCoeffs_rowAdd_above_pivot (b := b) (j := j) (k := k) hjk (-r) l hjl hlk
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
private theorem gapH13 {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by simp [h]
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega
theorem scaledCoeffs_adjacentSwap_lower_prev (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (scaledCoeffs b) k j := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by omega
  have hjk : j.val < k.val := by omega
  have hh541 : j.val + 1 ≠ k.val := by omega
  apply gapH13
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) km1.val j.val km1.isLt hjkm1
  have hRHS := scaledCoeffs_eq (b := b) k.val j.val k.isLt hjk
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) := by
    apply gramDet_adjacentSwap_of_ne
    exact hh541
  have hcoeff : GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j =
      GramSchmidt.entry (coeffs b) k j :=
    coeffs_adjacentSwap_lower_prev (b := b) k hk j hj
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) km1 j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) km1 j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs b) k j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k j : Int) : Rat) := hRHS.symm
theorem scaledCoeffs_adjacentSwap_lower_curr (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (j : Fin n) (hj : j.val + 1 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (scaledCoeffs b) km1 j := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by omega
  have hjk : j.val < k.val := by omega
  have hh541 : j.val + 1 ≠ k.val := by omega
  apply gapH13
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) k.val j.val k.isLt hjk
  have hRHS := scaledCoeffs_eq (b := b) km1.val j.val km1.isLt hjkm1
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) := by
    apply gramDet_adjacentSwap_of_ne
    exact hh541
  have hcoeff : GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j =
      GramSchmidt.entry (coeffs b) km1 j :=
    coeffs_adjacentSwap_lower_curr (b := b) k hk j hj
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) k j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjkm1 km1.isLt)) : Rat) *
          GramSchmidt.entry (coeffs b) km1 j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) km1 j : Int) : Rat) := hRHS.symm
theorem scaledCoeffs_adjacentSwap_pivot (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) :
    let km1 := GramSchmidt.prevRow k hk
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k km1 =
      GramSchmidt.entry (scaledCoeffs b) k km1 := by
  intro km1
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hkm1k : km1.val < k.val := by omega
  calc
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) k km1
        = Matrix.det
            (GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k) := by
          rw [scaledCoeffs_eq_scaledCoeffMatrix_det]
          rfl
    _ = Matrix.det ((GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose) := by
          rw [GramSchmidt.Int.scaledCoeffMatrix_rowSwap_adjacent_pivot_transpose
            (b := b) (km1 := km1) (k := k) hkm1 hkm1k]
    _ = Matrix.det (GramSchmidt.scaledCoeffMatrix b k km1 hkm1k) := by
          rw [Matrix.det_transpose]
    _ = GramSchmidt.entry (scaledCoeffs b) k km1 := by
          rw [← scaledCoeffs_eq_scaledCoeffMatrix_det]
theorem scaledCoeffs_adjacentSwap_before (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i j : Fin n)
    (hi : i.val + 1 < k.val) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i j =
      GramSchmidt.entry (scaledCoeffs b) i j := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hikm1 : i.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hh541 : j.val + 1 ≠ k.val := by omega
  apply gapH13
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) i.val j.val i.isLt hji
  have hRHS := scaledCoeffs_eq (b := b) i.val j.val i.isLt hji
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1) (Nat.succ_le_of_lt j.isLt) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) := by
    apply gramDet_adjacentSwap_of_ne
    exact hh541
  have hcoeff :
      GramSchmidt.entry (coeffs (adjacentSwap b k hk)) i j =
        GramSchmidt.entry (coeffs b) i j := by
    simpa [adjacentSwap, km1] using
      coeffs_rowSwap_adjacent_before (b := b) (km1 := km1) (k := k) (i := i) (j := j)
        hkm1 hikm1 hji
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) i j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
          GramSchmidt.entry (coeffs b) i j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) := hRHS.symm
theorem scaledCoeffs_adjacentSwap_above_low (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i j : Fin n)
    (hki : k.val < i.val) (hj : j.val + 1 < k.val) :
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i j =
      GramSchmidt.entry (scaledCoeffs b) i j := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hjkm1 : j.val < km1.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hji : j.val < i.val := by omega
  have hh541 : j.val + 1 ≠ k.val := by omega
  apply gapH13
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) i.val j.val i.isLt hji
  have hRHS := scaledCoeffs_eq (b := b) i.val j.val i.isLt hji
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1) (Nat.succ_le_of_lt j.isLt) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) := by
    apply gramDet_adjacentSwap_of_ne
    exact hh541
  have hcoeff :
      GramSchmidt.entry (coeffs (adjacentSwap b k hk)) i j =
        GramSchmidt.entry (coeffs b) i j := by
    simpa [adjacentSwap, km1] using
      coeffs_rowSwap_adjacent_after_low (b := b) (km1 := km1) (k := k) (i := i)
        (j := j) hkm1 hki hjkm1
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) i j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
          GramSchmidt.entry (coeffs b) i j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) := hRHS.symm
theorem scaledCoeffs_adjacentSwap_above_high (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i j : Fin n)
    (hki : k.val < i.val) (hkj : k.val < j.val) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i j =
      GramSchmidt.entry (scaledCoeffs b) i j := by
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]
    omega
  have hh541 : j.val + 1 ≠ k.val := by omega
  apply gapH13
  have hLHS := scaledCoeffs_eq (b := adjacentSwap b k hk) i.val j.val i.isLt hji
  have hRHS := scaledCoeffs_eq (b := b) i.val j.val i.isLt hji
  have hdet :
      gramDet (adjacentSwap b k hk) (j.val + 1) (Nat.succ_le_of_lt j.isLt) =
        gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) := by
    apply gramDet_adjacentSwap_of_ne
    exact hh541
  have hcoeff :
      GramSchmidt.entry (coeffs (adjacentSwap b k hk)) i j =
        GramSchmidt.entry (coeffs b) i j := by
    simpa [adjacentSwap, km1] using
      coeffs_rowSwap_adjacent_after_high (b := b) (km1 := km1) (k := k) (i := i)
        (j := j) hkm1 hki hkj hji
  calc ((GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i j : Int) : Rat)
      = (gramDet (adjacentSwap b k hk) (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
          GramSchmidt.entry (coeffs (adjacentSwap b k hk)) i j := hLHS
    _ = (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
          GramSchmidt.entry (coeffs b) i j := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) := hRHS.symm
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
theorem bareiss_scaledCoeffMatrix_rowSwap_above_prev
    (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hki : k.val < i.val)
    (_hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    let km1 := GramSchmidt.prevRow k hk
    let hkm1i : km1.val < i.val := by
      dsimp [km1, GramSchmidt.prevRow]; omega
    Hex.Matrix.bareiss (GramSchmidt.scaledCoeffMatrix
        (Matrix.rowSwap b km1 k) i km1 hkm1i) *
      ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      adjacentSwapScaledCoeffAbovePrevNumerator b k hk i := by
  intro km1 hkm1i
  rw [← scaledCoeffs_eq_scaledCoeffMatrix_bareiss
      (Matrix.rowSwap b km1 k) i km1 hkm1i]
  apply gapH13
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hkm1k : km1.val < k.val := by omega
  have hh543 : km1.val < i.val := hkm1i
  have hk_le_n : k.val ≤ n := Nat.le_of_lt k.isLt
  have hh542 : km1.val ≤ n := Nat.le_of_lt km1.isLt
  have hk1_le_n : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hh546 : km1.val + 1 ≤ n := Nat.succ_le_of_lt km1.isLt
  set μ : Rat := GramSchmidt.entry (coeffs b) k km1 with hμ_def
  set prev : Vector Rat m := (basis b).row km1 with hprev_def
  set curr : Vector Rat m := (basis b).row k with hcurr_def
  set G : Rat := gramSchmidtNormProduct b km1.val hh542 with hG_def
  set Nkm1 : Rat := prev.normSq with hNkm1_def
  set Nk : Rat := curr.normSq with hNk_def
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
  have hN'_eq : ((basis (Matrix.rowSwap b km1 k)).row km1).normSq =
      Nk + μ ^ 2 * Nkm1 := by
    rw [hh526]
    exact normSq_add_smul_orthogonal_rat curr prev μ horth
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
    rw [hN'_eq]
  have hB_rat :
      ((GramSchmidt.entry (scaledCoeffs b) k km1 : Int) : Rat) = G * Nkm1 * μ := by
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
  have hnuik_rat :
      ((GramSchmidt.entry (scaledCoeffs b) i k : Int) : Rat) =
        G * Nkm1 * Nk * GramSchmidt.entry (coeffs b) i k := by
    have heq := scaledCoeffs_eq b i.val k.val i.isLt hki
    show ((GramSchmidt.entry (scaledCoeffs b) ⟨i.val, i.isLt⟩
        ⟨k.val, Nat.lt_trans hki i.isLt⟩ : Int) : Rat) = _
    rw [heq, hh533]
  have hnuikm1_rat :
      ((GramSchmidt.entry (scaledCoeffs b) i km1 : Int) : Rat) =
        G * Nkm1 * GramSchmidt.entry (coeffs b) i km1 := by
    have heq := scaledCoeffs_eq b i.val km1.val i.isLt hh543
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hh543 i.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show ((GramSchmidt.entry (scaledCoeffs b) ⟨i.val, i.isLt⟩
        ⟨km1.val, Nat.lt_trans hh543 i.isLt⟩ : Int) : Rat) = _
    rw [heq, hgd_eq, hdk_rat]
  have hrow_b'_i : (Matrix.rowSwap b km1 k)[i] = b[i] := by
    have hh537 : (i : Fin n) ≠ km1 := fun h => by
      have : i.val = km1.val := congrArg Fin.val h
      omega
    have hi_ne_k : (i : Fin n) ≠ k := fun h => by
      have : i.val = k.val := congrArg Fin.val h
      omega
    exact gapH14 b km1 k i hh537 hi_ne_k
  have hcastRow_b'i :
      Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row i) =
        Vector.map (fun x : Int => (x : Rat)) (b.row i) := by
    show Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k)[i]) = _
    rw [hrow_b'_i]
    rfl
  have hdotk : curr.dotProduct
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      GramSchmidt.entry (coeffs b) i k * Nk := by
    have h := dot_basis_castRow_eq_coeffs_mul_normSq b i.val k.val i.isLt hki
    show ((basis b).row ⟨k.val, k.isLt⟩).dotProduct _ = _
    rw [h]
  have hdotkm1 : prev.dotProduct
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      GramSchmidt.entry (coeffs b) i km1 * Nkm1 := by
    have h := dot_basis_castRow_eq_coeffs_mul_normSq b i.val km1.val i.isLt hh543
    show ((basis b).row ⟨km1.val, km1.isLt⟩).dotProduct _ = _
    rw [h]
  have hdot_b'_km1 :
      ((basis (Matrix.rowSwap b km1 k)).row km1).dotProduct
          (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row i)) =
        GramSchmidt.entry (coeffs b) i k * Nk +
          μ * (GramSchmidt.entry (coeffs b) i km1 * Nkm1) := by
    rw [hcastRow_b'i, hh526]
    rw [dot_add_left_rat, dot_smul_left_rat, hdotk, hdotkm1]
  have hnu'_rat :
      ((GramSchmidt.entry (scaledCoeffs (Matrix.rowSwap b km1 k)) i km1 : Int) : Rat) =
        G * (GramSchmidt.entry (coeffs b) i k * Nk +
            μ * (GramSchmidt.entry (coeffs b) i km1 * Nkm1)) := by
    have hcoeff_normSq :
        GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i km1 *
          ((basis (Matrix.rowSwap b km1 k)).row km1).normSq =
        ((basis (Matrix.rowSwap b km1 k)).row km1).dotProduct
          (Vector.map (fun x : Int => (x : Rat))
            ((Matrix.rowSwap b km1 k).row i)) := by
      have h := dot_basis_castRow_eq_coeffs_mul_normSq
        (Matrix.rowSwap b km1 k) i.val km1.val i.isLt hh543
      show GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) ⟨i.val, i.isLt⟩
            ⟨km1.val, Nat.lt_trans hh543 i.isLt⟩ *
          ((basis (Matrix.rowSwap b km1 k)).row
            ⟨km1.val, km1.isLt⟩).normSq = _
      exact h.symm
    have heq := scaledCoeffs_eq (Matrix.rowSwap b km1 k) i.val km1.val i.isLt hh543
    show ((GramSchmidt.entry (scaledCoeffs (Matrix.rowSwap b km1 k)) ⟨i.val, i.isLt⟩
            ⟨km1.val, Nat.lt_trans hh543 i.isLt⟩ : Int) : Rat) = _
    rw [heq]
    have hgd_eq :
        gramDet (Matrix.rowSwap b km1 k) (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hh543 i.isLt)) =
          gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n :=
      gramDet_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1
    rw [hgd_eq, hdprime_rat]
    have hcoeff_inner :
        GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k))
            ⟨i.val, i.isLt⟩
            ⟨km1.val, Nat.lt_trans hh543 i.isLt⟩ *
          (Nk + μ ^ 2 * Nkm1) =
        GramSchmidt.entry (coeffs b) i k * Nk +
          μ * (GramSchmidt.entry (coeffs b) i km1 * Nkm1) := by
      rw [← hN'_eq, hcoeff_normSq]
      exact hdot_b'_km1
    linear_combination G * hcoeff_inner
  unfold adjacentSwapScaledCoeffAbovePrevNumerator adjacentSwapPivotCoeff
  push_cast
  rw [hnu'_rat, hdk_rat, hh532, hnuik_rat, hnuikm1_rat, hB_rat]
  ring
theorem bareiss_scaledCoeffMatrix_rowSwap_above_curr
    (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val)
    (i : Fin n) (hki : k.val < i.val)
    (_hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    Hex.Matrix.bareiss (GramSchmidt.scaledCoeffMatrix
        (Matrix.rowSwap b (GramSchmidt.prevRow k hk) k) i k hki) *
      ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      adjacentSwapScaledCoeffAboveCurrNumerator b k hk i := by
  rw [← scaledCoeffs_eq_scaledCoeffMatrix_bareiss
      (Matrix.rowSwap b (GramSchmidt.prevRow k hk) k) i k hki]
  apply gapH13
  let km1 := GramSchmidt.prevRow k hk
  have hkm1 : km1.val + 1 = k.val := by
    dsimp [km1, GramSchmidt.prevRow]; omega
  have hkm1k : km1.val < k.val := by omega
  have hh543 : km1.val < i.val := by omega
  have hk_le_n : k.val ≤ n := Nat.le_of_lt k.isLt
  have hh542 : km1.val ≤ n := Nat.le_of_lt km1.isLt
  have hk1_le_n : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hh546 : km1.val + 1 ≤ n := Nat.succ_le_of_lt km1.isLt
  set μ : Rat := GramSchmidt.entry (coeffs b) k km1 with hμ_def
  set prev : Vector Rat m := (basis b).row km1 with hprev_def
  set curr : Vector Rat m := (basis b).row k with hcurr_def
  set G : Rat := gramSchmidtNormProduct b km1.val hh542 with hG_def
  set Nkm1 : Rat := prev.normSq with hNkm1_def
  set Nk : Rat := curr.normSq with hNk_def
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
  have hk1_ne_k : k.val + 1 ≠ k.val := by omega
  have hdkp1_swap_nat :
      gramDet (Matrix.rowSwap b km1 k) (k.val + 1) hk1_le_n =
        gramDet b (k.val + 1) hk1_le_n := by
    show gramDet (adjacentSwap b k hk) (k.val + 1) hk1_le_n = _
    exact gramDet_adjacentSwap_of_ne b k hk (k.val + 1) hk1_le_n hk1_ne_k
  have hdkp1_swap_rat :
      (gramDet (Matrix.rowSwap b km1 k) (k.val + 1) hk1_le_n : Rat) =
        G * Nkm1 * Nk := by
    rw [hdkp1_swap_nat]; exact hh533
  have hB_rat :
      ((GramSchmidt.entry (scaledCoeffs b) k km1 : Int) : Rat) = G * Nkm1 * μ := by
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
  have hnuik_rat :
      ((GramSchmidt.entry (scaledCoeffs b) i k : Int) : Rat) =
        G * Nkm1 * Nk * GramSchmidt.entry (coeffs b) i k := by
    have heq := scaledCoeffs_eq b i.val k.val i.isLt hki
    show ((GramSchmidt.entry (scaledCoeffs b) ⟨i.val, i.isLt⟩
        ⟨k.val, Nat.lt_trans hki i.isLt⟩ : Int) : Rat) = _
    rw [heq, hh533]
  have hnuikm1_rat :
      ((GramSchmidt.entry (scaledCoeffs b) i km1 : Int) : Rat) =
        G * Nkm1 * GramSchmidt.entry (coeffs b) i km1 := by
    have heq := scaledCoeffs_eq b i.val km1.val i.isLt hh543
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hh543 i.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show ((GramSchmidt.entry (scaledCoeffs b) ⟨i.val, i.isLt⟩
        ⟨km1.val, Nat.lt_trans hh543 i.isLt⟩ : Int) : Rat) = _
    rw [heq, hgd_eq, hdk_rat]
  set Nk' : Rat := ((basis (Matrix.rowSwap b km1 k)).row k).normSq with hNk'_def
  set Nkm1' : Rat := ((basis (Matrix.rowSwap b km1 k)).row km1).normSq with hNkm1'_def
  have hdkp1_swap_rat_factored :
      (gramDet (Matrix.rowSwap b km1 k) (k.val + 1) hk1_le_n : Rat) =
        G * Nkm1' * Nk' := by
    have h_succ := gramDet_succ_rat (Matrix.rowSwap b km1 k) k.val hk1_le_n
    have h_gnp_eq :
        gramSchmidtNormProduct (Matrix.rowSwap b km1 k) k.val hk_le_n =
          gramSchmidtNormProduct (Matrix.rowSwap b km1 k) (km1.val + 1) hh546 :=
      gramSchmidtNormProduct_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1.symm
    rw [h_succ, h_gnp_eq,
        gramSchmidtNormProduct_succ (Matrix.rowSwap b km1 k) km1.val hh546,
        gramSchmidtNormProduct_rowSwap_below b km1 k hkm1k]
  have hprod_eq : G * Nkm1' * Nk' = G * Nkm1 * Nk :=
    hdkp1_swap_rat_factored.symm.trans hdkp1_swap_rat
  have hcoeff_normSq :
      GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i k * Nk' =
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        (Vector.map (fun x : Int => (x : Rat))
          ((Matrix.rowSwap b km1 k).row i)) := by
    have h := dot_basis_castRow_eq_coeffs_mul_normSq
      (Matrix.rowSwap b km1 k) i.val k.val i.isLt hki
    show GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) ⟨i.val, i.isLt⟩
          ⟨k.val, Nat.lt_trans hki i.isLt⟩ *
        ((basis (Matrix.rowSwap b km1 k)).row
          ⟨k.val, k.isLt⟩).normSq = _
    exact h.symm
  have hrow_b'_i : (Matrix.rowSwap b km1 k)[i] = b[i] := by
    have hh537 : (i : Fin n) ≠ km1 := fun h => by
      have : i.val = km1.val := congrArg Fin.val h
      omega
    have hi_ne_k : (i : Fin n) ≠ k := fun h => by
      have : i.val = k.val := congrArg Fin.val h
      omega
    exact gapH14 b km1 k i hh537 hi_ne_k
  have hcastRow_b'i :
      Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row i) =
        Vector.map (fun x : Int => (x : Rat)) (b.row i) := by
    show Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k)[i]) = _
    rw [hrow_b'_i]
    rfl
  set D : Rat := ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row km1)
    with hD_def
  have hdot_castb_i :
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
          (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
        D * (GramSchmidt.entry (coeffs b) i km1 -
          μ * GramSchmidt.entry (coeffs b) i k) := by
    have h := dot_basis_rowSwap_curr_castRow_eq b km1 k hkm1 i hki
    show ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row km1) *
        (GramSchmidt.entry (coeffs b) i km1 -
         μ * GramSchmidt.entry (coeffs b) i k)
    convert h using 2
  have hD_eq_normSq : D = Nk' := by
    show ((basis (Matrix.rowSwap b km1 k)).row k).dotProduct ((basis b).row km1) =
      ((basis (Matrix.rowSwap b km1 k)).row k).normSq
    exact dot_basis_rowSwap_curr_prev_eq_normSq b km1 k hkm1
  have hcoeff_eq_Nk' :
      GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i k * Nk' =
      Nk' * (GramSchmidt.entry (coeffs b) i km1 -
          μ * GramSchmidt.entry (coeffs b) i k) := by
    rw [hcoeff_normSq, hcastRow_b'i, hdot_castb_i, hD_eq_normSq]
  have hkey :
      (G * Nkm1 * Nk) * GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i k =
        (G * Nkm1 * Nk) * (GramSchmidt.entry (coeffs b) i km1 -
             μ * GramSchmidt.entry (coeffs b) i k) := by
    have hScale :
        G * Nkm1' * (GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i k * Nk') =
        G * Nkm1' * (Nk' * (GramSchmidt.entry (coeffs b) i km1 -
            μ * GramSchmidt.entry (coeffs b) i k)) := by
      rw [hcoeff_eq_Nk']
    linear_combination hScale + hprod_eq *
      ((GramSchmidt.entry (coeffs b) i km1 -
        μ * GramSchmidt.entry (coeffs b) i k) -
       GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i k)
  have hnu'_rat :
      ((GramSchmidt.entry (scaledCoeffs (Matrix.rowSwap b km1 k)) i k : Int) : Rat) =
        G * Nkm1 * Nk *
          GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i k := by
    have heq := scaledCoeffs_eq (Matrix.rowSwap b km1 k) i.val k.val i.isLt hki
    show ((GramSchmidt.entry (scaledCoeffs (Matrix.rowSwap b km1 k)) ⟨i.val, i.isLt⟩
        ⟨k.val, Nat.lt_trans hki i.isLt⟩ : Int) : Rat) = _
    rw [heq, hdkp1_swap_rat]
  unfold adjacentSwapScaledCoeffAboveCurrNumerator adjacentSwapPivotCoeff
  push_cast
  rw [hnu'_rat, hdk_rat, hh533, hB_rat, hnuik_rat, hnuikm1_rat]
  linear_combination (G * Nkm1) * hkey
theorem scaledCoeffs_adjacentSwap_above_prev (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) (hki : k.val < i.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i
        (GramSchmidt.prevRow k hk) =
      adjacentSwapScaledCoeffAbovePrevNumerator b k hk i / adjacentSwapDenom b k := by
  have hkm1i : (GramSchmidt.prevRow k hk).val < i.val := by
    dsimp [GramSchmidt.prevRow]; omega
  have hdk_pos : ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ≠ 0 := by
    intro hzero; exact hdet (Int.ofNat.inj hzero)
  have h := bareiss_scaledCoeffMatrix_rowSwap_above_prev b k hk i hki hdet
  have hbridge := scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (Matrix.rowSwap b (GramSchmidt.prevRow k hk) k) i (GramSchmidt.prevRow k hk) hkm1i
  show GramSchmidt.entry
        (scaledCoeffs (Matrix.rowSwap b (GramSchmidt.prevRow k hk) k))
        i (GramSchmidt.prevRow k hk) =
      adjacentSwapScaledCoeffAbovePrevNumerator b k hk i /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)
  rw [hbridge, ← h]
  exact (Int.mul_ediv_cancel _ hdk_pos).symm
theorem scaledCoeffs_adjacentSwap_above_curr (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) (hki : k.val < i.val)
    (hdet : gramDet b k.val (Nat.le_of_lt k.isLt) ≠ 0) :
    GramSchmidt.entry (scaledCoeffs (adjacentSwap b k hk)) i k =
      adjacentSwapScaledCoeffAboveCurrNumerator b k hk i / adjacentSwapDenom b k := by
  have hdk_pos : ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) ≠ 0 := by
    intro hzero; exact hdet (Int.ofNat.inj hzero)
  have h := bareiss_scaledCoeffMatrix_rowSwap_above_curr b k hk i hki hdet
  have hbridge := scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (Matrix.rowSwap b (GramSchmidt.prevRow k hk) k) i k hki
  show GramSchmidt.entry
        (scaledCoeffs (Matrix.rowSwap b (GramSchmidt.prevRow k hk) k)) i k =
      adjacentSwapScaledCoeffAboveCurrNumerator b k hk i /
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)
  rw [hbridge, ← h]
  exact (Int.mul_ediv_cancel _ hdk_pos).symm
end GramSchmidt.Int
end Hex
end
end
section
section
private theorem gapH10 {α : Type*} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.get i = v[i.1] := rfl
namespace Hex
open Hex.Internal
namespace Matrix
end Matrix
namespace Internal.LLLState
private theorem gapH359 {α : Type*} {n : Nat}
    (v : Vector α n) (i : Fin n) (f : α → α) :
    (v.modify i.val f).get i = f (v.get i) := by
  unfold Vector.modify
  simp [Vector.get, Array.getElem_modify]
private theorem gapH391 {α : Type*} {n : Nat}
    (v : Vector α n) (i : Nat) (f : α → α) (j : Fin n) (h : i ≠ j.val) :
    (v.modify i f).get j = v.get j := by
  unfold Vector.modify
  simp [Vector.get, Array.getElem_modify, h]
private theorem gapH346
    (xs : List (Fin n)) (base source : Vector Int n) (l : Fin n) :
    (xs.foldl (fun row i => row.set i (source.get i)) base).get l =
      if (∃ i ∈ xs, i.val = l.val) then source.get l else base.get l := by
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
        change (base.set x.val (source.get x) x.isLt)[x.val] = _
        exact Vector.getElem_set_self x.isLt
      · have h_cons : ¬ ∃ i ∈ x :: xs, i.val = l.val := by
          rintro ⟨i, hi, hi_l⟩
          rcases List.mem_cons.mp hi with rfl | hxs
          · exact h_xl hi_l
          · exact h_xs ⟨i, hxs, hi_l⟩
        simp only [h_xs, ↓reduceIte, h_cons]
        change (base.set x.val (source.get x) x.isLt)[l.val] = base[l.val]
        exact Vector.getElem_set_ne x.isLt l.isLt h_xl
private theorem gapH369
    {kmVal : Nat} (hkm : kmVal ≤ n)
    (source base : Vector Int n) (l : Fin n) :
    ((List.finRange kmVal).foldl
        (fun (row : Vector Int n) (j : Fin kmVal) =>
          let jFin : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hkm⟩
          row.set jFin (source.get jFin))
        base).get l =
      if l.val < kmVal then source.get l else base.get l := by
  let cast : Fin kmVal → Fin n :=
    fun j => ⟨j.val, Nat.lt_of_lt_of_le j.isLt hkm⟩
  show ((List.finRange kmVal).foldl
        (fun (row : Vector Int n) (j : Fin kmVal) =>
          row.set (cast j) (source.get (cast j)))
        base).get l = _
  rw [show ((List.finRange kmVal).foldl
        (fun (row : Vector Int n) (j : Fin kmVal) =>
          row.set (cast j) (source.get (cast j)))
        base) =
      ((List.finRange kmVal).map cast).foldl
        (fun (row : Vector Int n) (i : Fin n) =>
          row.set i (source.get i))
        base from
      (@List.foldl_map (Fin kmVal) (Fin n) (Vector Int n) cast
        (fun row i => row.set i (source.get i))
        (List.finRange kmVal) base).symm]
  rw [gapH346]
  by_cases hlj : l.val < kmVal
  · have hex : ∃ i ∈ (List.finRange kmVal).map cast, i.val = l.val := by
      refine ⟨⟨l.val, Nat.lt_of_lt_of_le hlj hkm⟩, ?_, rfl⟩
      rw [List.mem_map]
      exact ⟨⟨l.val, hlj⟩, List.mem_finRange _, rfl⟩
    rw [if_pos hex, if_pos hlj]
  · have hno : ¬ ∃ i ∈ (List.finRange kmVal).map cast, i.val = l.val := by
      rintro ⟨i, hi_mem, hi_eq⟩
      rw [List.mem_map] at hi_mem
      obtain ⟨l', _, hl'⟩ := hi_mem
      have hcast : (cast l').val = l'.val := rfl
      have : l.val < kmVal := by
        rw [← hi_eq, ← hl', hcast]
        exact l'.isLt
      exact hlj this
    rw [if_neg hno, if_neg hlj]
private theorem gapH377 {source row : Vector Int n} {km1 : Fin n}
    (l : Fin n) (hl : l.val < km1.val) :
    (setPrefix source row km1).get l = source.get l := by
  unfold setPrefix
  rw [Fin.foldl_eq_finRange_foldl,
    gapH369 (Nat.le_of_lt km1.isLt) source row l]
  simp [hl]
private theorem gapH383
    {α : Type*} (k : Nat) (xs : List (Fin n)) (hnd : xs.Nodup)
    (base : Vector α n) (upd : Fin n → α → α) (l : Fin n) :
    (xs.foldl
        (fun (acc : Vector α n) (i : Fin n) =>
          if k < i.val then acc.modify i.val (upd i) else acc) base).get l =
      if (l ∈ xs ∧ k < l.val) then upd l (base.get l) else base.get l := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hxnd : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hxs_nd : xs.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hkx : k < x.val
    · rw [if_pos hkx]
      rw [ih hxs_nd (base.modify x.val (upd x))]
      by_cases hlx : x.val = l.val
      · have hxeq : x = l := Fin.eq_of_val_eq hlx
        subst hxeq
        have h1 : (x ∈ x :: xs) := List.mem_cons_self
        have h2 : ¬(x ∈ xs) := hxnd
        simp [h1, h2, hkx, gapH359]
      · have hl_ne : l ≠ x := fun h => hlx (h ▸ rfl)
        have hxv_ne : x.val ≠ l.val := hlx
        rw [gapH391 base x.val (upd x) l hxv_ne]
        have hl_cons_iff : (l ∈ x :: xs) ↔ (l ∈ xs) := by
          constructor
          · intro h
            rcases List.mem_cons.mp h with rfl | h'
            · exact (hl_ne rfl).elim
            · exact h'
          · exact fun h => List.mem_cons.mpr (Or.inr h)
        simp only [hl_cons_iff]
    · rw [if_neg hkx]
      rw [ih hxs_nd base]
      by_cases hxl : x = l
      · subst hxl
        simp [hkx]
      · have hl_cons_iff : (l ∈ x :: xs) ↔ (l ∈ xs) := by
          constructor
          · intro h
            rcases List.mem_cons.mp h with rfl | h'
            · exact (hxl rfl).elim
            · exact h'
          · exact fun h => List.mem_cons.mpr (Or.inr h)
        simp only [hl_cons_iff]
private theorem gapH305
    (k : Nat) (xs : List (Fin n)) (hnd : xs.Nodup)
    (base : Hex.Matrix Int n n) (upd : Fin n → Vector Int n → Vector Int n) (l : Fin n) :
    (xs.foldl
        (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
          if k < i.val then ν.modifyRow i.val (upd i) else ν) base).getRow l =
      if (l ∈ xs ∧ k < l.val) then upd l (base.getRow l) else base.getRow l := by
  have key : ∀ (acc : Hex.Matrix Int n n),
      (xs.foldl
          (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
            if k < i.val then ν.modifyRow i.val (upd i) else ν) acc).rows =
        xs.foldl
          (fun (a : Vector (Vector Int n) n) (i : Fin n) =>
            if k < i.val then a.modify i.val (upd i) else a) acc.rows := by
    intro acc
    clear hnd
    induction xs generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hkx : k < x.val
      · rw [if_pos hkx, if_pos hkx,
          ih (acc.modifyRow x.val (upd x)), Hex.Matrix.rows_modifyRow]
      · rw [if_neg hkx, if_neg hkx, ih acc]
  have h := gapH383 k xs hnd base.rows upd l
  rw [← key base] at h
  simpa [gapH10, Hex.Matrix.getElem_rows] using h
theorem swapStep_valid (s : LLLState n m) (k : Nat)
    (hind : s.b.independent) (hvalid : s.Valid) :
    (s.swapStep k).Valid := by
  unfold swapStep
  by_cases hk : k < n
  · rw [dif_pos hk]
    by_cases hk0 : 0 < k
    · rw [dif_pos hk0]
      set kFin : Fin n := ⟨k, hk⟩ with hkFin_def
      set km1 : Fin n := GramSchmidt.prevRow kFin hk0 with hkm1_def
      have hkFinVal : kFin.val = k := rfl
      have hkm1Val : km1.val = k - 1 := by
        simp [hkm1_def, GramSchmidt.prevRow, hkFinVal]
      have hkm1 : km1.val + 1 = k := by omega
      have hh544 : km1.val < k := by omega
      have hdk_pos : 0 < GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
        have := hind ⟨km1.val, Nat.lt_trans hh544 hk⟩
        simpa [hkm1] using this
      have hh531 :
          GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) ≠ 0 := Nat.pos_iff_ne_zero.mp hdk_pos
      set B : Int := (s.ν.getRow kFin).get km1 with hB_def
      set dkPrev : Nat := s.d.get ⟨km1.val, Nat.lt_succ_of_lt km1.isLt⟩ with hdkPrev_def
      set dk : Nat := s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩ with hdk_def
      set dkNext : Nat := s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩ with hdkNext_def
      have hh530 :
          dkPrev = GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) := by
        simpa using hvalid.d_eq km1.val (Nat.lt_succ_of_lt km1.isLt)
      have hdk_eq :
          dk = GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) := by
        simpa using hvalid.d_eq k (Nat.lt_succ_of_lt hk)
      have hh529 :
          dkNext = GramSchmidt.Int.gramDet s.b (k + 1) (Nat.succ_le_of_lt hk) := by
        simpa using hvalid.d_eq (k + 1) (Nat.succ_lt_succ hk)
      have hB_eq :
          B = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := by
        rw [hB_def]
        simpa [GramSchmidt.entry, Matrix.row, gapH10] using
          hvalid.ν_eq kFin.val km1.val kFin.isLt km1.isLt (by omega)
      have hdk_kFin_ne_zero :
          GramSchmidt.Int.gramDet s.b kFin.val (Nat.le_of_lt kFin.isLt) ≠ 0 := by
        change GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt hk) ≠ 0
        exact hh531
      have hgramPivot :=
        GramSchmidt.Int.gramDet_adjacentSwap_pivot s.b kFin hk0 hdk_kFin_ne_zero
      have hh545 : km1.val < n := km1.isLt
      have hh542 : km1.val ≤ n := Nat.le_of_lt km1.isLt
      let pairs : Vector (Int × Int) n :=
        Vector.ofFn fun i =>
          if _ : k < i.val then ((s.ν.getRow i).get kFin, (s.ν.getRow i).get km1)
          else (0, 0)
      let upd : Fin n → Vector Int n → Vector Int n :=
        fun i row =>
          let prev :=
            (Int.ofNat dkPrev * (pairs.get i).1 + B * (pairs.get i).2) / Int.ofNat dk
          let curr :=
            (Int.ofNat dkNext * (pairs.get i).2 - B * (pairs.get i).1) / Int.ofNat dk
          (row.set km1 prev).set kFin curr
      have hpairs_at : ∀ (i : Fin n), k < i.val →
          pairs.get i = ((s.ν.getRow i).get kFin, (s.ν.getRow i).get km1) := by
        intro i hi
        show (Vector.ofFn _)[i.1] = _
        rw [Vector.getElem_ofFn]
        exact dif_pos hi
      have hkm1_ne_kFin : km1 ≠ kFin := by
        intro h; rw [h] at hh544; omega
      have hkm1_val_ne_kFin : km1.val ≠ kFin.val := fun h =>
        hkm1_ne_kFin (Fin.eq_of_val_eq h)
      refine ⟨?_, ?_⟩
      ·
        intro i j hi hj hji
        set b' : Hex.Matrix Int n m := GramSchmidt.Int.adjacentSwap s.b kFin hk0 with hb'_def
        set iFin : Fin n := ⟨i, hi⟩ with hiFin_def
        set jFin : Fin n := ⟨j, hj⟩ with hjFin_def
        have hjiFin : jFin.val < iFin.val := hji
        set νRowsSwapped : Hex.Matrix Int n n :=
          (s.ν.modifyRow km1.val (setPrefix (s.ν.getRow kFin) · km1)).modifyRow kFin.val
            (setPrefix (s.ν.getRow km1) · km1) with hνRows_def
        set νPivot : Hex.Matrix Int n n := νRowsSwapped.modifyRow kFin.val (·.set km1 B)
          with hνPivot_def
        show
          ((Fin.foldl n
              (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if _ : k < i.val then
                  ν.modifyRow i.val (upd i)
                else ν)
              νPivot).getRow iFin).get jFin =
            ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
        rw [Fin.foldl_eq_finRange_foldl]
        have hν'_get :
            ((List.finRange n).foldl
                (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                  if k < i.val then ν.modifyRow i.val (upd i) else ν)
                νPivot).getRow iFin =
              if k < iFin.val then upd iFin (νPivot.getRow iFin) else νPivot.getRow iFin := by
          have := gapH305 (n := n) k
            (List.finRange n) (List.nodup_finRange n) νPivot upd iFin
          simp [List.mem_finRange] at this
          exact this
        have hbody_eq :
            (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if _ : k < i.val then ν.modifyRow i.val (upd i) else ν) =
              (fun (ν : Hex.Matrix Int n n) (i : Fin n) =>
                if k < i.val then ν.modifyRow i.val (upd i) else ν) := by
          funext ν i
          split <;> rfl
        rw [hbody_eq, hν'_get]
        have hνRows_get_ne :
            ∀ (l : Fin n), l.val ≠ km1.val → l.val ≠ kFin.val →
              νRowsSwapped.getRow l = s.ν.getRow l := by
          intro l hl_km1 hl_kFin
          rw [hνRows_def, Hex.Matrix.getRow_modifyRow_ne _ kFin.val _ l (fun h => hl_kFin h.symm),
            Hex.Matrix.getRow_modifyRow_ne _ km1.val _ l (fun h => hl_km1 h.symm)]
        have hνRows_get_km1 : νRowsSwapped.getRow km1 = setPrefix (s.ν.getRow kFin) (s.ν.getRow km1) km1 := by
          rw [hνRows_def, Hex.Matrix.getRow_modifyRow_ne _ kFin.val _ km1 (fun h => hkm1_val_ne_kFin h.symm)]
          exact Hex.Matrix.getRow_modifyRow_self _ km1 _
        have hνRows_get_kFin :
            νRowsSwapped.getRow kFin = setPrefix (s.ν.getRow km1) (s.ν.getRow kFin) km1 := by
          rw [hνRows_def, Hex.Matrix.getRow_modifyRow_self _ kFin _,
            Hex.Matrix.getRow_modifyRow_ne _ km1.val _ kFin hkm1_val_ne_kFin]
        have hνPivot_get_ne :
            ∀ (l : Fin n), l.val ≠ kFin.val → νPivot.getRow l = νRowsSwapped.getRow l := by
          intro l hl_kFin
          rw [hνPivot_def]
          exact Hex.Matrix.getRow_modifyRow_ne _ kFin.val _ l (fun h => hl_kFin h.symm)
        have hνPivot_get_kFin :
            νPivot.getRow kFin = (νRowsSwapped.getRow kFin).set km1.val B hh545 := by
          rw [hνPivot_def]
          exact Hex.Matrix.getRow_modifyRow_self _ kFin _
        have hν_eq := hvalid.ν_eq
        by_cases hki : k < iFin.val
        ·
          rw [if_pos hki]
          have hh537 : iFin.val ≠ km1.val := by
            have : iFin.val > km1.val := by omega
            omega
          have hh536 : iFin.val ≠ kFin.val := by
            have : iFin.val > kFin.val := hki
            omega
          rw [hνPivot_get_ne iFin hh536, hνRows_get_ne iFin hh537 hh536]
          show ((let prev := (Int.ofNat dkPrev * (pairs.get iFin).1 +
                              B * (pairs.get iFin).2) / Int.ofNat dk
                 let curr := (Int.ofNat dkNext * (pairs.get iFin).2 -
                              B * (pairs.get iFin).1) / Int.ofNat dk
                 ((s.ν.getRow iFin).set km1 prev).set kFin curr).get jFin) =
            ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
          rw [show pairs.get iFin = ((s.ν.getRow iFin).get kFin, (s.ν.getRow iFin).get km1)
              from hpairs_at iFin hki]
          show ((((s.ν.getRow iFin).set km1.val
                ((Int.ofNat dkPrev * (s.ν.getRow iFin).get kFin +
                    B * (s.ν.getRow iFin).get km1) /
                  Int.ofNat dk) hh545).set kFin.val
              ((Int.ofNat dkNext * (s.ν.getRow iFin).get km1 -
                  B * (s.ν.getRow iFin).get kFin) /
                Int.ofNat dk) hk).get jFin) =
            ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
          have hν_at_kFin :
              (s.ν.getRow iFin).get kFin =
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) iFin kFin := by
            have := hν_eq iFin.val kFin.val iFin.isLt kFin.isLt
              (by rw [hkFinVal]; exact hki)
            simpa [GramSchmidt.entry, Matrix.row, gapH10] using this
          have hν_at_km1 :
              (s.ν.getRow iFin).get km1 =
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) iFin km1 := by
            have hh543 : km1.val < iFin.val := by omega
            have := hν_eq iFin.val km1.val iFin.isLt km1.isLt hh543
            simpa [GramSchmidt.entry, Matrix.row, gapH10] using this
          by_cases hjk : jFin.val = kFin.val
          ·
            rw [show jFin = kFin from Fin.eq_of_val_eq hjk]
            show ((((s.ν.getRow iFin).set km1.val _ hh545).set kFin.val _ hk).get kFin) = _
            rw [show ∀ (xs : Vector Int n) (x : Int),
                      (xs.set kFin.val x hk).get kFin = x from
                  fun xs x => Vector.getElem_set_self hk]
            rw [hh529, hdk_eq, hB_eq, hν_at_kFin, hν_at_km1]
            have hsc := GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_curr s.b kFin hk0
              iFin hki hdk_kFin_ne_zero
            change _ = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs b') iFin kFin
            rw [hsc]
            unfold GramSchmidt.Int.adjacentSwapScaledCoeffAboveCurrNumerator
                  GramSchmidt.Int.adjacentSwapDenom
                  GramSchmidt.Int.adjacentSwapPivotCoeff
            rfl
          · by_cases hjkm1 : jFin.val = km1.val
            ·
              rw [show jFin = km1 from Fin.eq_of_val_eq hjkm1]
              have hkFin_ne_km1 : kFin.val ≠ km1.val := fun h => hkm1_val_ne_kFin h.symm
              show ((((s.ν.getRow iFin).set km1.val _ hh545).set kFin.val _ hk).get km1) = _
              rw [show ((((s.ν.getRow iFin).set km1.val _ hh545).set kFin.val _ hk).get km1) =
                    (((s.ν.getRow iFin).set km1.val _ hh545).get km1) from
                  Vector.getElem_set_ne (h := hkFin_ne_km1) _ km1.isLt]
              rw [show (((s.ν.getRow iFin).set km1.val _ hh545).get km1) = _ from
                  Vector.getElem_set_self hh545]
              rw [hh530, hdk_eq, hB_eq, hν_at_kFin, hν_at_km1]
              have hsc := GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_prev s.b kFin hk0
                iFin hki hdk_kFin_ne_zero
              change _ = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs b') iFin
                (GramSchmidt.prevRow kFin hk0)
              rw [hsc]
              unfold GramSchmidt.Int.adjacentSwapScaledCoeffAbovePrevNumerator
                    GramSchmidt.Int.adjacentSwapDenom
                    GramSchmidt.Int.adjacentSwapPivotCoeff
              rfl
            ·
              have hkFin_ne_jFin : kFin.val ≠ jFin.val := fun h => hjk h.symm
              have hkm1_ne_jFin : km1.val ≠ jFin.val := fun h => hjkm1 h.symm
              show ((((s.ν.getRow iFin).set km1.val _ hh545).set kFin.val _ hk).get jFin) = _
              rw [show ((((s.ν.getRow iFin).set km1.val _ hh545).set kFin.val _ hk).get jFin) =
                    (((s.ν.getRow iFin).set km1.val _ hh545).get jFin) from
                  Vector.getElem_set_ne (h := hkFin_ne_jFin) _ jFin.isLt]
              rw [show (((s.ν.getRow iFin).set km1.val _ hh545).get jFin) = _ from
                  Vector.getElem_set_ne (h := hkm1_ne_jFin) _ jFin.isLt]
              have hν := hν_eq iFin.val jFin.val iFin.isLt jFin.isLt hjiFin
              by_cases hh540 : jFin.val < km1.val
              ·
                have hsc :=
                  GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_low s.b kFin hk0 iFin jFin
                    hki (by rw [hkFinVal]; omega)
                show (s.ν.getRow iFin)[jFin.val] = _
                calc (s.ν.getRow iFin)[jFin.val]
                    = ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := hν
                  _ = ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin := by
                        simpa [GramSchmidt.entry, Matrix.row, gapH10] using hsc.symm
              ·
                have hj_gt_k : kFin.val < jFin.val := by
                  rw [hkFinVal]; rw [hkm1Val] at hh540; omega
                have hsc :=
                  GramSchmidt.Int.scaledCoeffs_adjacentSwap_above_high s.b kFin hk0 iFin jFin
                    hki hj_gt_k hjiFin
                show (s.ν.getRow iFin)[jFin.val] = _
                calc (s.ν.getRow iFin)[jFin.val]
                    = ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := hν
                  _ = ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin := by
                        simpa [GramSchmidt.entry, Matrix.row, gapH10] using hsc.symm
        ·
          rw [if_neg hki]
          have hki : iFin.val ≤ k := Nat.le_of_not_lt hki
          by_cases hi_eq_k : iFin.val = kFin.val
          ·
            have hi_eq : iFin = kFin := Fin.eq_of_val_eq hi_eq_k
            rw [hi_eq, hνPivot_get_kFin]
            by_cases hj_eq_km1 : jFin.val = km1.val
            ·
              have hj_eq : jFin = km1 := Fin.eq_of_val_eq hj_eq_km1
              rw [hj_eq,
                show ((νRowsSwapped.getRow kFin).set km1.val B hh545).get km1 = B from
                    Vector.getElem_set_self km1.isLt]
              have hsc := GramSchmidt.Int.scaledCoeffs_adjacentSwap_pivot s.b kFin hk0
              show B = ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get km1
              calc B = GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 := hB_eq
                _ = ((GramSchmidt.Int.scaledCoeffs s.b).getRow kFin).get km1 := rfl
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get km1 := by
                      have := hsc
                      simp [GramSchmidt.entry, Matrix.row] at this
                      exact this.symm
            ·
              have hh539 : jFin.val < kFin.val := by
                rw [← hi_eq_k]; exact hjiFin
              have hh540 : jFin.val < km1.val := by
                have : jFin.val < k := by rw [hkFinVal] at hh539; exact hh539
                omega
              have hj_succ_lt_k : jFin.val + 1 < k := by omega
              have hj_ne_km1 : km1.val ≠ jFin.val := fun h => hj_eq_km1 h.symm
              rw [show ((νRowsSwapped.getRow kFin).set km1.val B hh545).get jFin = _ from
                    Vector.getElem_set_ne (h := hj_ne_km1) _ jFin.isLt]
              rw [hνRows_get_kFin]
              change (setPrefix (s.ν.getRow km1) (s.ν.getRow kFin) km1).get jFin = _
              rw [gapH377 jFin hh540]
              have hν := hν_eq km1.val jFin.val km1.isLt jFin.isLt hh540
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_lower_curr s.b kFin hk0 jFin
                  (by rw [hkFinVal]; exact hj_succ_lt_k)
              show (s.ν.getRow km1).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get jFin
              calc (s.ν.getRow km1).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).getRow km1).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow kFin).get jFin := by
                      simpa [GramSchmidt.entry, Matrix.row, gapH10] using hsc.symm
          ·
            have hi_lt_k : iFin.val < kFin.val := lt_of_le_of_ne hki hi_eq_k
            by_cases hi_eq_km1 : iFin.val = km1.val
            ·
              have hi_eq : iFin = km1 := Fin.eq_of_val_eq hi_eq_km1
              have hh536 : iFin.val ≠ kFin.val := by
                rw [hi_eq_km1, hkFinVal]; omega
              have hh540 : jFin.val < km1.val := by
                have : jFin.val < iFin.val := hjiFin
                omega
              have hj_succ_lt_k : jFin.val + 1 < k := by omega
              have hh539 : jFin.val < kFin.val := by rw [hkFinVal]; omega
              rw [hνPivot_get_ne iFin hh536, hi_eq, hνRows_get_km1,
                  gapH377 (km1 := km1) jFin hh540]
              have hν := hν_eq kFin.val jFin.val kFin.isLt jFin.isLt hh539
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_lower_prev s.b kFin hk0 jFin
                  (by rw [hkFinVal]; exact hj_succ_lt_k)
              show (s.ν.getRow kFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').getRow km1).get jFin
              calc (s.ν.getRow kFin).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).getRow kFin).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow km1).get jFin := by
                      simpa [GramSchmidt.entry, Matrix.row, gapH10] using hsc.symm
            ·
              have hi_lt_km1 : iFin.val < km1.val := by omega
              have hh537 : iFin.val ≠ km1.val := Nat.ne_of_lt hi_lt_km1
              have hh536 : iFin.val ≠ kFin.val := by
                rw [hkFinVal]; omega
              rw [hνPivot_get_ne iFin hh536, hνRows_get_ne iFin hh537 hh536]
              have hν := hν_eq iFin.val jFin.val iFin.isLt jFin.isLt hjiFin
              have hsc :=
                GramSchmidt.Int.scaledCoeffs_adjacentSwap_before s.b kFin hk0 iFin jFin
                  (by rw [hkFinVal]; omega) hjiFin
              show (s.ν.getRow iFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin
              calc (s.ν.getRow iFin).get jFin
                  = ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := hν
                _ = ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin := hsc.symm
      ·
        intro i hi
        change
          (s.d.set k (Int.toNat
              ((Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2) / Int.ofNat dk))
            (Nat.lt_succ_of_lt hk)).get ⟨i, hi⟩ =
            GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) i
              (Nat.le_of_lt_succ hi)
        by_cases hik : i = k
        · subst hik
          rw [show (s.d.set i _ (Nat.lt_succ_of_lt hk)).get ⟨i, hi⟩ = _ from
                Vector.getElem_set_self (xs := s.d) hi]
          rw [hh529, hh530, hdk_eq, hB_eq]
          have hgramPivot' := hgramPivot
          dsimp only at hgramPivot'
          show
            ((((GramSchmidt.Int.gramDet s.b (i + 1) (Nat.succ_le_of_lt hk) : Nat) : Int) *
                  ((GramSchmidt.Int.gramDet s.b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
                GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) kFin km1 ^ 2) /
                ((GramSchmidt.Int.gramDet s.b i (Nat.le_of_lt hk) : Nat) : Int)).toNat =
              GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) i
                (Nat.le_of_lt_succ hi)
          rw [← hgramPivot']
          exact Int.toNat_natCast _
        · rw [show (s.d.set k _ (Nat.lt_succ_of_lt hk)).get ⟨i, hi⟩ = _ from
                Vector.getElem_set_ne (h := fun h => hik h.symm) (xs := s.d) _ hi]
          have hvalid_d := hvalid.d_eq i hi
          change s.d.get ⟨i, hi⟩ =
            GramSchmidt.Int.gramDet (GramSchmidt.Int.adjacentSwap s.b kFin hk0) i
              (Nat.le_of_lt_succ hi)
          rw [hvalid_d]
          exact (GramSchmidt.Int.gramDet_adjacentSwap_of_ne s.b kFin hk0 i
                  (Nat.le_of_lt_succ hi) hik).symm
    · rw [dif_neg hk0]
      exact hvalid
  · rw [dif_neg hk]
    exact hvalid
end Internal.LLLState
namespace Internal.LLLState
private theorem gapH322 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) :
    (s.sizeReduceColumn j k hjk).b =
      GramSchmidt.Int.sizeReduce s.b j k
        (nearestQuotient ((s.ν.getRow k).get j)
          (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) := by
  unfold sizeReduceColumn; rw [dif_pos hreduce]
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
private theorem gapH320 (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val)
    (hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    (i : Fin n) (hi : i ≠ k) :
    (s.sizeReduceColumn j k hjk).ν.getRow i = s.ν.getRow i := by
  unfold sizeReduceColumn; rw [dif_pos hreduce]
  exact Hex.Matrix.setRow_row_ne s.ν k i _ hi
theorem sizeReduceColumn_valid (s : LLLState n m) (j k : Fin n)
    (hjk : j.val < k.val) (hvalid : s.Valid) :
    (s.sizeReduceColumn j k hjk).Valid := by
  by_cases hreduce :
      2 * Int.natAbs ((s.ν.getRow k).get j) >
        s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  ·
    have hν_at : ∀ (i : Fin n) (j' : Fin n), j'.val < i.val →
        (s.ν.getRow i).get j' =
          GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs s.b) i j' := by
      intro i j' hj'i
      have := hvalid.ν_eq i.val j'.val i.isLt j'.isLt hj'i
      simpa [GramSchmidt.entry, Matrix.row, gapH10] using this
    have hd_at : ∀ (i : Nat) (hi : i < n + 1),
        s.d.get ⟨i, hi⟩ =
          GramSchmidt.Int.gramDet s.b i (Nat.le_of_lt_succ hi) :=
      hvalid.d_eq
    set r : Int := nearestQuotient ((s.ν.getRow k).get j)
      (s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with hr_def
    set b' : Matrix Int n m := GramSchmidt.Int.sizeReduce s.b j k r with hb'_def
    have hb_eq : (s.sizeReduceColumn j k hjk).b = b' :=
      gapH322 s j k hjk hreduce
    have hd_state_eq : (s.sizeReduceColumn j k hjk).d = s.d :=
      gapH275 s j k hjk
    refine ⟨?_, ?_⟩
    ·
      intro iVal jVal hi hj' hji
      set iFin : Fin n := ⟨iVal, hi⟩
      set jFin : Fin n := ⟨jVal, hj'⟩
      have hji' : jFin.val < iFin.val := hji
      show ((s.sizeReduceColumn j k hjk).ν.getRow iFin).get jFin =
        ((GramSchmidt.Int.scaledCoeffs (s.sizeReduceColumn j k hjk).b).getRow iFin).get jFin
      rw [hb_eq]
      by_cases hi_k : iFin = k
      ·
        subst hi_k
        rw [gapH136 s j iFin hjk hreduce r hr_def]
        by_cases hj_eq : jFin = j
        ·
          subst hj_eq
          rw [show ∀ (xs : Vector Int n) (x : Int),
              (xs.set jFin.val x jFin.isLt).get jFin = x from
                fun xs x => Vector.getElem_set_self jFin.isLt]
          rw [hν_at iFin jFin hji']
          have hd : s.d.get ⟨jFin.val + 1, Nat.succ_lt_succ jFin.isLt⟩ =
              GramSchmidt.Int.gramDet s.b (jFin.val + 1)
                (Nat.succ_le_of_lt jFin.isLt) :=
            hd_at (jFin.val + 1) (Nat.succ_lt_succ jFin.isLt)
          rw [hd]
          have hsc := GramSchmidt.Int.scaledCoeffs_sizeReduce_pivot s.b jFin iFin hjk r
          have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
              ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin -
                r * Int.ofNat (GramSchmidt.Int.gramDet s.b (jFin.val + 1)
                  (Nat.succ_le_of_lt jFin.isLt)) := by
            simpa [GramSchmidt.entry, Matrix.row, gapH10] using hsc
          rw [hsc']
          rfl
        ·
          rw [show ∀ (xs : Vector Int n) (x : Int),
              (xs.set j.val x j.isLt).get jFin = xs.get jFin from
                fun xs x => Vector.getElem_set_ne j.isLt jFin.isLt
                  (fun h => hj_eq (Fin.eq_of_val_eq h).symm)]
          rw [LLLState.foldl_finRange_set_outerSubMul_get_eq j.val
              (Nat.le_of_lt j.isLt) (s.ν.getRow iFin) (s.ν.getRow iFin) (s.ν.getRow j) r jFin]
          by_cases hjlt : jFin.val < j.val
          ·
            rw [if_pos hjlt, hν_at iFin jFin hji', hν_at j jFin hjlt]
            have hsc :=
              GramSchmidt.Int.scaledCoeffs_sizeReduce_lower s.b jFin j iFin hjlt hjk r
            have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin -
                  r * ((GramSchmidt.Int.scaledCoeffs s.b).getRow j).get jFin := by
              simpa [GramSchmidt.entry, Matrix.row, gapH10] using hsc
            rw [hsc']
            rfl
          ·
            rw [if_neg hjlt]
            have hjge : j.val ≤ jFin.val := Nat.le_of_not_lt hjlt
            have hjlt' : j.val < jFin.val := lt_of_le_of_ne hjge
              (fun h => hj_eq (Fin.eq_of_val_eq h.symm))
            rw [hν_at iFin jFin hji']
            have hjlt_k : jFin.val < iFin.val := hji'
            have hsc :=
              GramSchmidt.Int.scaledCoeffs_sizeReduce_above_pivot s.b j iFin hjk r jFin
                hjlt' hjlt_k
            have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
                ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := by
              simpa [GramSchmidt.entry, Matrix.row, gapH10] using hsc
            rw [hsc']
            rfl
      ·
        rw [gapH320 s j k hjk hreduce iFin hi_k, hν_at iFin jFin hji']
        have hsc :=
          GramSchmidt.Int.scaledCoeffs_sizeReduce_other_row s.b j k hjk r iFin hi_k
        have hsc' : ((GramSchmidt.Int.scaledCoeffs b').getRow iFin).get jFin =
            ((GramSchmidt.Int.scaledCoeffs s.b).getRow iFin).get jFin := by
          have hrow := hsc
          rw [Matrix.row, Matrix.row] at hrow
          exact congrArg (fun v : Vector Int n => v.get jFin) hrow
        rw [hsc']
        rfl
    ·
      intro i hi
      rw [hd_state_eq, hd_at i hi, hb_eq]
      exact (GramSchmidt.Int.gramDet_sizeReduce s.b j k hjk r i (Nat.le_of_lt_succ hi)).symm
  ·
    have h_eq : s.sizeReduceColumn j k hjk = s := by
      unfold sizeReduceColumn; rw [dif_neg hreduce]
    rw [h_eq]; exact hvalid
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
end Internal.LLLState
end Hex
end
section
namespace Hex
open Hex.Internal
namespace Internal.LLLState
end Internal.LLLState
end Hex
end
section
section
namespace HexLLLTheory
end HexLLLTheory
end
end
section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeFiniteDraw
open AFT AFT.RationalNumerics AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2NativeFiniteSeries TM2NativeRootGroupProfiles
open scoped BigOperators
end Integration9_9.TM2NativeFiniteDraw
end
section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineApply
open AFT AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase
open scoped BigOperators
end Integration9_9.TM2NativeAffineApply
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2PlatformSerialization
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open QAlgorithms.Complexity
open Polynomial
section RepeatedParser
variable {α : Type} [Coding α] [Inhabited α]
variable (read : Str → Str × α)
end RepeatedParser
end Integration9_9.TM2PlatformSerialization
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARPlatformEncoding
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open TM2PlatformSerialization
section BinaryList
variable {α : Type} [Coding α] [Inhabited α]
variable (read : Str → Str × α)
end BinaryList
end Integration9_9.LARPlatformEncoding
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinMachine
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open LARPlatformEncoding Polynomial
open scoped BigOperators
end Integration9_9.LARCoinMachine
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide
open AFT GaussianSource RationalNumerics BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9 TM2NativeFiniteDraw
open scoped BigOperators
end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide
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
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n : Nat}
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
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option autoImplicit false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.RegevSketch
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
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.NativeLLL
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineEncoding
open AFT AFT.BinaryArithmetic QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase LARPlatformEncoding
end Integration9_9.TM2NativeAffineEncoding
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase QAlgorithms.Complexity Function Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime LARPlatformEncoding LARRankOneMachine TM2PlatformSerialization
end Integration9_9.LARCoinLayout
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open QAlgorithms.Complexity
open Integration9_9
open Integration9_9.LARPlatformEncoding
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase.RegevSketch
open NativeLLL
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option autoImplicit false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open AFT.RationalNumerics
open scoped BigOperators
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open AFT.RationalNumerics
open scoped BigOperators
noncomputable section
end
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.RationalInverse.Native
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open AFT.RationalNumerics
open RationalGramSchmidt
open RationalGramSchmidt.Native
open scoped BigOperators
noncomputable section
end
end InfoLossLAR.WorstCase.RationalInverse.Native
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
open scoped BigOperators
namespace InfoLossLAR.WorstCase.NativeLLL
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.RegevSketch
open NativeLLL
open RationalGramSchmidt.Native
open OAI.MetricKMedian.Binary.Automatic
open QAlgorithms.Complexity
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option autoImplicit false
open scoped BigOperators
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open scoped Polynomial
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase.RegevSketch
open NativeLLL
open Hex.Internal
open OAI.MetricKMedian.Binary.Automatic
open QAlgorithms.Complexity
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n m : ℕ}
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
variable {n m : ℕ}
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2NativeSliceProbability
open Hex.Internal
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Hex.Internal
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
variable {n m : ℕ}
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Hex.Internal
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
namespace InfoLossLAR.WorstCase.NativeLLL
end InfoLossLAR.WorstCase.NativeLLL
end
section
set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.RegevSketch InfoLossLAR.WorstCase.NativeLLL
end

set_option autoImplicit false

theorem solution {n m : ℕ} (s : Hex.Internal.LLLState n m) (hvalid : s.Valid) :
    (∀ (j k : Fin n) (hjk : j.val < k.val), (s.sizeReduceColumn j k hjk).Valid) ∧
      (s.b.independent → ∀ k : ℕ, (s.swapStep k).Valid) := by
  exact ⟨fun j k hjk => Hex.Internal.LLLState.sizeReduceColumn_valid s j k hjk hvalid,
    fun hind k => Hex.Internal.LLLState.swapStep_valid s k hind hvalid⟩
