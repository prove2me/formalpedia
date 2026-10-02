-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_3_split_torus_reflection_data
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T11:51:13.120158+00:00
-- url     : https://prove2.me/submissions/a8e69340-0654-4861-8141-5bcde69c4a79

/-
Original formalization: Qiuzhen-CFSG/CFSG and original source authors.
Commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; Apache-2.0.
arexychen: declaration extraction, exact-environment replay, packaging and validation.
Retained mathematical proof bodies are unchanged. Source scopes/visibility and
upload entry names are adapted; accepted cut theorems are imported.

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
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

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
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

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
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

set_option autoImplicit false
namespace CFSGPackSplit

section Source1
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/BenderSuzuki/MatrixGroups/PSL2.lean
/-!
# Projective special linear matrix groups

This file contains the concrete `PSL(2,F)` matrix-group models used by the
Peterfalvi Part II formalization.  The declarations live in the `BenderSuzuki.MatrixGroups` namespace so matrix-group models are not hidden under a Peterfalvi chapter namespace.
-/

namespace BenderSuzuki
namespace MatrixGroups

open scoped MatrixGroups
universe w

/-- The actual projective special linear matrix group `PSL(2,F)`. -/
abbrev PSL2MatrixGroup (F : Type w) [Field F] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) F


-- Omitted: outside declaration proof/source closure.

end MatrixGroups
end BenderSuzuki


end Source1

section Source4
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonSylow.lean
/-!
# Sylow subgroups of PSL(2,q)

This module isolates the cardinality and upper-unitriangular calculation used
to identify Sylow subgroups in Dickson's classification.
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups

universe u

/-- The field exponent in Huppert II.8.27 is nonzero. -/
theorem huppert_II_8_27_field_exponent_ne_zero
    {F : Type u} [Field F] [Finite F] {p f : ℕ}
    (hFcard : Nat.card F = p ^ f) :
    f ≠ 0 := by
  intro hf
  subst f
  have hcard : Nat.card F = 1 := by
    simpa using hFcard
  exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard

-- Omitted: outside declaration proof/source closure.

end Dickson
end Glauberman


end Source4

section Source8
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonSplitTorusMatrices.lean
/-!
# Concrete split-torus matrices in SL(2,F)

Finite `2 × 2` case splits live here, outside the large group-theoretic proof
of the split-torus normalizer theorem.
-/

namespace Glauberman
namespace Dickson

universe u

/-- The standard diagonal copy of `Fˣ` in `SL(2,F)`. -/
@[expose] public def splitTorusSLHom (F : Type u) [Field F] :
    Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
  { toFun := fun a => ⟨!![(a : F), 0; 0, (a⁻¹ : F)], by
      simp [Matrix.det_fin_two]⟩
    map_one' := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      ext i j
      change (!![(↑(a * b) : F), 0; 0, (↑(a * b) : F)⁻¹] :
          Matrix (Fin 2) (Fin 2) F) i j =
        ((!![(a : F), 0; 0, (a⁻¹ : F)] : Matrix (Fin 2) (Fin 2) F) *
          (!![(b : F), 0; 0, (b⁻¹ : F)] : Matrix (Fin 2) (Fin 2) F)) i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm] }

@[simp] public theorem splitTorusSLHom_coe
    {F : Type u} [Field F] (a : Fˣ) :
    (splitTorusSLHom F a : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, (a⁻¹ : F)] := rfl

/-- A split-torus matrix whose two diagonal entries agree is scalar. -/
theorem splitTorusSLHom_eq_scalar_of_val_eq_inv
    {F : Type u} [Field F] (a : Fˣ)
    (ha : (a : F) = (a⁻¹ : F)) :
    Matrix.scalar (Fin 2) (a : F) =
      (splitTorusSLHom F a : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · exact ha

/-- The standard Weyl reflection in `SL(2,F)`. -/
@[expose] public def standardSplitWeylSL (F : Type u) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

@[simp] public theorem standardSplitWeylSL_coe
    (F : Type u) [Field F] :
    (standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F) =
      !![0, -1; 1, 0] := rfl

/-- The inverse of the standard Weyl reflection. -/
theorem standardSplitWeylSL_inv
    (F : Type u) [Field F] :
    (standardSplitWeylSL F)⁻¹ =
      (⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [standardSplitWeylSL, Matrix.adjugate_fin_two]

/-- The standard Weyl reflection inverts the standard split torus. -/
theorem standardSplitWeylSL_conj
    {F : Type u} [Field F] (a : Fˣ) :
    standardSplitWeylSL F * splitTorusSLHom F a *
        (standardSplitWeylSL F)⁻¹ =
      splitTorusSLHom F a⁻¹ := by
  rw [standardSplitWeylSL_inv]
  apply Subtype.ext
  change ((standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F) *
      (splitTorusSLHom F a : Matrix (Fin 2) (Fin 2) F) *
        ((⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ :
          Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
    (splitTorusSLHom F a⁻¹ : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardSplitWeylSL_coe, splitTorusSLHom_coe,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The square of the standard Weyl reflection is central. -/
theorem standardSplitWeylSL_sq_mem_center
    (F : Type u) [Field F] :
    standardSplitWeylSL F * standardSplitWeylSL F ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  change Matrix.scalar (Fin 2) (-1 : F) =
    ((standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F) *
      (standardSplitWeylSL F : Matrix (Fin 2) (Fin 2) F))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardSplitWeylSL, Matrix.mul_apply, Fin.sum_univ_two]

/-- A diagonal element of `SL(2,F)` belongs to the standard split torus. -/
theorem eq_splitTorusSLHom_of_offDiagonal_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    ∃ u : Fˣ, A = splitTorusSLHom F u := by
  have hdet := A.property
  rw [Matrix.det_fin_two, h01, h10, zero_mul, sub_zero] at hdet
  have hA00 : A 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  let u : Fˣ := Units.mk0 (A 0 0) hA00
  have hA11 : A 1 1 = (A 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  refine ⟨u, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusSLHom_coe, u, h01, h10, hA11]

/-- An antidiagonal element of `SL(2,F)` is a Weyl reflection times a
standard split-torus element. -/
theorem eq_standardSplitWeylSL_mul_splitTorusSLHom_of_diagonal_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h00 : A 0 0 = 0) (h11 : A 1 1 = 0) :
    ∃ u : Fˣ, A = standardSplitWeylSL F * splitTorusSLHom F u := by
  have hdet := A.property
  rw [Matrix.det_fin_two, h00, h11, zero_mul, zero_sub] at hdet
  have hA10 : A 1 0 ≠ 0 := by
    intro h
    rw [h, mul_zero, neg_zero] at hdet
    exact zero_ne_one hdet
  let u : Fˣ := Units.mk0 (A 1 0) hA10
  have hnegprod : (-A 0 1) * A 1 0 = 1 := by
    simpa using hdet
  have hneg : -A 0 1 = (A 1 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left hnegprod
  have hA01 : A 0 1 = -(A 1 0)⁻¹ := by
    calc
      A 0 1 = -(-A 0 1) := by simp
      _ = -(A 1 0)⁻¹ := congrArg Neg.neg hneg
  refine ⟨u, ?_⟩
  apply Subtype.ext
  ext i j
  change (A : Matrix (Fin 2) (Fin 2) F) i j =
    ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) *
      !![(u : F), 0; 0, (u⁻¹ : F)]) i j
  fin_cases i <;> fin_cases j <;>
    simp [u, Matrix.mul_apply, Fin.sum_univ_two, h00, h11, hA01]

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

/-- A matrix intertwining a noncentral split-torus element with another
split-torus element is diagonal or antidiagonal. -/
theorem split_matrix_diag_or_antidiag
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (a b : Fˣ) (r : F)
    (ha_ne_inv : (a : F) ≠ (a⁻¹ : F))
    (heq :
      !![(b : F), 0; 0, (b⁻¹ : F)] * Matrix.scalar (Fin 2) r *
          (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          !![(a : F), 0; 0, (a⁻¹ : F)]) :
    (A 0 1 = 0 ∧ A 1 0 = 0) ∨
      (A 0 0 = 0 ∧ A 1 1 = 0) := by
  have h00 := congrFun (congrFun heq (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun heq (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun heq (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun heq (1 : Fin 2)) (1 : Fin 2)
  simp [Matrix.mul_apply] at h00 h01 h10 h11
  by_cases hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  · right
    refine ⟨hA00, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA00, zero_mul, zero_sub] at hdet
    have hA01 : A 0 1 ≠ 0 := by
      intro h
      rw [h, zero_mul, neg_zero] at hdet
      exact zero_ne_one hdet
    have hA10 : A 1 0 ≠ 0 := by
      intro h
      rw [h, mul_zero, neg_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    by_contra hA11
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)
  · left
    have hbr_a : (b : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA00
      simpa [mul_assoc, mul_comm] using h00
    have hA01 : A 0 1 = 0 := by
      by_contra hA01
      have hbr_ainv : (b : F) * r = (a⁻¹ : F) := by
        apply mul_right_cancel₀ hA01
        simpa [mul_assoc, mul_comm] using h01
      exact False.elim (ha_ne_inv (hbr_a.symm.trans hbr_ainv))
    refine ⟨hA01, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA01, zero_mul, sub_zero] at hdet
    have hA11 : A 1 1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    by_contra hA10
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)

end Dickson
end Glauberman


end Source8

section Source9
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonSplitTorus.lean
/-!
# Split tori in PSL(2,q)

This module isolates Huppert II.8.3 and its concrete diagonal/antidiagonal
matrix calculations from the rest of Dickson's classification.
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise
universe u v


/-- Huppert II.8.3(a,c), retaining the Weyl reflection and its inversion
action on the standard split torus. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U : Subgroup (PSL2MatrixGroup F),
      ∃ w : PSL2MatrixGroup F,
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      w ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      w ∉ U ∧
      w * w = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (U ⊔ Subgroup.zpowers w :
        Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card U ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          U ⊔ Subgroup.zpowers w := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
        Nat.card (rootsOfUnity 2 F) =
          Nat.gcd (Nat.card F - 1) 2 := by
      let e :=
        Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
          Units.val_injective
      have he :
          Nat.card (rootsOfUnity 2 F) =
            Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
        Nat.card_congr e
      rw [Units.val_set_image_rootsOfUnity_two] at he
      by_cases hp_two : p = 2
      · have htwo : (2 : F) = 0 := by
          subst p
          exact CharP.cast_eq_zero F 2
        have hneg_one : (-1 : F) = 1 := by
          apply (neg_eq_iff_add_eq_zero).2
          have hone_add_one : (1 : F) + 1 = 0 := by
            rw [show (1 : F) + 1 = 2 by norm_num, htwo]
          exact hone_add_one
        have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
          simpa [hneg_one] using he
        have hq_even : Even (Nat.card F) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
          rw [hFcard, hp_two, hk, pow_succ]
          use 2 ^ k
          ring
        have hq_sub_one_odd : Odd (Nat.card F - 1) := by
          rw [← Nat.not_even_iff_odd]
          intro heven
          have hparity :=
            (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
              heven
          exact Nat.not_even_one (hparity.mp hq_even)
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
          Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
        rw [hleft, hgcd]
      · have hring_char_ne_two : ringChar F ≠ 2 := by
          rw [ringChar.eq F p]
          exact hp_two
        have hneg_one : (-1 : F) ≠ 1 :=
          Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
        have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
          simpa [hneg_one, Ne.symm hneg_one] using he
        have hq_odd : Odd (Nat.card F) := by
          rw [hFcard]
          exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
        have htwo_dvd : 2 ∣ Nat.card F - 1 := by
          rcases hq_odd with ⟨k, hk⟩
          use k
          omega
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
          Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
            (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
        rw [hleft, hgcd]
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    splitTorusSLHom F
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp splitTorusSL
  have hsplit_mem_ker_iff (a : Fˣ) :
      a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
    rw [MonoidHom.mem_ker, mem_rootsOfUnity]
    constructor
    · intro ha
      have hcenter :
          splitTorusSL a ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
      have hscalar :=
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
      have ha_inv_val := congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
      have ha_inv : a = a⁻¹ := by
        apply Units.ext
        simpa [splitTorusSL] using ha_inv_val
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
    · intro ha
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨(a : F), ?_, ?_⟩
      · simpa using congrArg Units.val ha
      · have ha_inv : a = a⁻¹ :=
          eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
        have ha_inv_val : (a : F) = (a⁻¹ : F) := by
          simpa using congrArg Units.val ha_inv
        simpa [splitTorusSL] using
          splitTorusSLHom_eq_scalar_of_val_eq_inv a ha_inv_val
  have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
    ext a
    exact hsplit_mem_ker_iff a
  have hsplit_ker_card :
      Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
    rw [hsplit_ker_eq, hcard_roots]
  have hsplit_range_mul :
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F - 1 := by
    calc
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          splitTorus.ker.index * Nat.card splitTorus.ker := by
        rw [Subgroup.index_ker, hsplit_ker_card]
      _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
  have hsplit_range_card :
      Nat.card splitTorus.range =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hsplit_range_mul
  have hsplit_range_cyclic : IsCyclic splitTorus.range := by
    have hUnitsCyclic : IsCyclic Fˣ := by
      let : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
      exact isCyclic_of_surjective
        ((⊤ : Subgroup Fˣ).subtype) (by
          intro a
          exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
    let : IsCyclic Fˣ := hUnitsCyclic
    exact isCyclic_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F))
  let splitWeylSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    standardSplitWeylSL F
  let splitWeyl : PSL2MatrixGroup F := qSL splitWeylSL
  have hsplitWeylSL_conj (a : Fˣ) :
      splitWeylSL * splitTorusSL a * splitWeylSL⁻¹ =
        splitTorusSL a⁻¹ := by
    simpa [splitWeylSL, splitTorusSL] using standardSplitWeylSL_conj a
  have hsplitWeylSL_sq_center :
      splitWeylSL * splitWeylSL ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    simpa [splitWeylSL] using standardSplitWeylSL_sq_mem_center F
  have hsplitWeyl_sq : splitWeyl * splitWeyl = 1 := by
    change qSL splitWeylSL * qSL splitWeylSL = 1
    rw [← map_mul]
    change QuotientGroup.mk (splitWeylSL * splitWeylSL) =
      QuotientGroup.mk 1
    apply Quotient.sound
    change QuotientGroup.leftRel
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
        (splitWeylSL * splitWeylSL) 1
    rw [QuotientGroup.leftRel_eq]
    simpa using
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).inv_mem
        hsplitWeylSL_sq_center
  have hsplitWeyl_inv : splitWeyl⁻¹ = splitWeyl := by
    calc
      splitWeyl⁻¹ = splitWeyl⁻¹ * 1 := (mul_one _).symm
      _ = splitWeyl⁻¹ * (splitWeyl * splitWeyl) := by
        rw [hsplitWeyl_sq]
      _ = splitWeyl := by
        rw [← mul_assoc]
        simp
  have hsplitWeyl_conj (a : Fˣ) :
      splitWeyl * splitTorus a * splitWeyl⁻¹ =
        splitTorus a⁻¹ := by
    have hqWsq : qSL (splitWeylSL * splitWeylSL) = 1 := by
      change QuotientGroup.mk (splitWeylSL * splitWeylSL) =
        QuotientGroup.mk 1
      apply Quotient.sound
      change QuotientGroup.leftRel
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
          (splitWeylSL * splitWeylSL) 1
      rw [QuotientGroup.leftRel_eq]
      simpa using
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).inv_mem
          hsplitWeylSL_sq_center
    have hsource :
        splitWeylSL * splitTorusSL a * splitWeylSL =
          (splitWeylSL * splitTorusSL a * splitWeylSL⁻¹) *
            (splitWeylSL * splitWeylSL) := by
      group
    rw [hsplitWeyl_inv]
    change qSL splitWeylSL * qSL (splitTorusSL a) *
        qSL splitWeylSL = qSL (splitTorusSL a⁻¹)
    calc
      qSL splitWeylSL * qSL (splitTorusSL a) *
          qSL splitWeylSL =
          qSL (splitWeylSL * splitTorusSL a * splitWeylSL) := by
            rw [map_mul, map_mul]
      _ = qSL ((splitWeylSL * splitTorusSL a * splitWeylSL⁻¹) *
            (splitWeylSL * splitWeylSL)) :=
        congrArg qSL hsource
      _ = qSL (splitTorusSL a⁻¹ *
            (splitWeylSL * splitWeylSL)) := by
        rw [hsplitWeylSL_conj]
      _ = qSL (splitTorusSL a⁻¹) *
            qSL (splitWeylSL * splitWeylSL) := by rw [map_mul]
      _ = qSL (splitTorusSL a⁻¹) := by rw [hqWsq, mul_one]
  have hsplitWeyl_not_mem : splitWeyl ∉ splitTorus.range := by
    rintro ⟨a, ha⟩
    change qSL (splitTorusSL a) = qSL splitWeylSL at ha
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp ha with
      ⟨z, hz, hzeq⟩
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeq
    change (splitTorusSL a : Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) =
      (splitWeylSL : Matrix (Fin 2) (Fin 2) F) at hmat
    rw [← hscalar] at hmat
    have h01 := congrFun (congrFun hmat (0 : Fin 2)) (1 : Fin 2)
    have hneg_one_zero : (-1 : F) = 0 := by
      simpa [splitTorusSL, splitWeylSL, Matrix.mul_apply] using h01.symm
    exact one_ne_zero (neg_eq_zero.mp hneg_one_zero)
  have hsplitWeyl_mem_normalizer :
      splitWeyl ∈
        Subgroup.normalizer (splitTorus.range : Set (PSL2MatrixGroup F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a⁻¹, (hsplitWeyl_conj a).symm⟩
    · rintro ⟨a, ha⟩
      refine ⟨a⁻¹, ?_⟩
      calc
        splitTorus a⁻¹ =
            splitWeyl⁻¹ *
              (splitWeyl * splitTorus a⁻¹ * splitWeyl⁻¹) *
                splitWeyl := by group
        _ = splitWeyl⁻¹ * splitTorus a * splitWeyl := by
          rw [hsplitWeyl_conj]
          group
        _ = y := by rw [ha]; group
  have hreflection_candidate_data
      (T : Subgroup (PSL2MatrixGroup F)) (w : PSL2MatrixGroup F)
      (hw_normalizer : w ∈ Subgroup.normalizer (T : Set _))
      (hw_sq : w * w = 1) (hw_not_mem : w ∉ T) :
      Nat.card (Subgroup.zpowers w) = 2 ∧
        Disjoint T (Subgroup.zpowers w) ∧
        Nat.card (T ⊔ (Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) : Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card T := by
    let Z : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers w
    have hw_ne_one : w ≠ 1 := by
      intro hw_one
      apply hw_not_mem
      rw [hw_one]
      exact Subgroup.one_mem T
    have hw_zpowers_card : Nat.card Z = 2 := by
      change Nat.card (Subgroup.zpowers w) = 2
      rw [Nat.card_zpowers]
      have hw_pow : w ^ 2 = 1 := by
        simpa [pow_two] using hw_sq
      have hord_dvd : orderOf w ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hw_pow
      rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
      · exact False.elim (hw_ne_one (orderOf_eq_one_iff.mp hord))
      · exact hord
    have hdisjoint : Disjoint T Z := by
      let R : Subgroup Z := T.comap Z.subtype
      let : Fact (Nat.card Z).Prime := ⟨by
        rw [show Nat.card Z = 2 by exact hw_zpowers_card]
        exact Nat.prime_two⟩
      rcases R.eq_bot_or_eq_top_of_prime_card with hR | hR
      · rw [disjoint_iff, eq_bot_iff]
        intro x hx
        have hxR : (⟨x, hx.2⟩ : Z) ∈ R := hx.1
        rw [hR] at hxR
        have hxone : (⟨x, hx.2⟩ : Z) = 1 := by simpa using hxR
        exact congrArg Subtype.val hxone
      · exfalso
        apply hw_not_mem
        have hwR : (⟨w, Subgroup.mem_zpowers w⟩ : Z) ∈ R := by
          rw [hR]
          simp
        exact hwR
    let D : Subgroup (PSL2MatrixGroup F) := T ⊔ Z
    have hD_le_normalizer : D ≤ Subgroup.normalizer (T : Set _) := by
      apply sup_le Subgroup.le_normalizer
      exact Subgroup.zpowers_le.2 hw_normalizer
    let TD : Subgroup D := T.subgroupOf D
    let ZD : Subgroup D := Z.subgroupOf D
    let : TD.Normal := by
      change (T.subgroupOf D).Normal
      exact Subgroup.normal_subgroupOf_of_le_normalizer hD_le_normalizer
    have hTDZD : Disjoint TD ZD := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxAmbient : (x : PSL2MatrixGroup F) ∈ T ⊓ Z := by
        change (x : PSL2MatrixGroup F) ∈ T ∧ (x : PSL2MatrixGroup F) ∈ Z
        exact ⟨hx.1, hx.2⟩
      have hxone : (x : PSL2MatrixGroup F) = 1 := by
        rw [hdisjoint.eq_bot] at hxAmbient
        simpa using hxAmbient
      apply Subtype.ext
      exact hxone
    have hsup : TD ⊔ ZD = ⊤ := by
      change T.subgroupOf D ⊔ Z.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup (show T ≤ D from le_sup_left)
        (show Z ≤ D from le_sup_right)]
      exact Subgroup.subgroupOf_self D
    have hZD_le_normalizer : ZD ≤ Subgroup.normalizer (TD : Set D) := by
      rw [Subgroup.normalizer_eq_top TD]
      exact le_top
    have hmul : (ZD : Set D) * (TD : Set D) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right ZD TD
        hZD_le_normalizer, sup_comm, hsup]
      rfl
    have hcomp : ZD.IsComplement' TD :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hTDZD.symm hmul
    have hZDcard : Nat.card ZD = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ D from le_sup_right)).toEquiv
    have hTDcard : Nat.card TD = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show T ≤ D from le_sup_left)).toEquiv
    refine ⟨hw_zpowers_card, hdisjoint, ?_⟩
    calc
      Nat.card (T ⊔ Z : Subgroup (PSL2MatrixGroup F)) = Nat.card D := rfl
      _ = Nat.card ZD * Nat.card TD := hcomp.card_mul_card.symm
      _ = 2 * Nat.card T := by
        rw [hZDcard, hTDcard, hw_zpowers_card]
  let splitWeylZ : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers splitWeyl
  rcases hreflection_candidate_data splitTorus.range splitWeyl
      hsplitWeyl_mem_normalizer hsplitWeyl_sq hsplitWeyl_not_mem with
    ⟨hsplitWeyl_zpowers_card, hsplit_torus_zpowers_disjoint,
      hsplitCandidate_card_raw⟩
  have hsplitCandidate_card :
      Nat.card (splitTorus.range ⊔ splitWeylZ : Subgroup (PSL2MatrixGroup F)) =
        2 * ((Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) := by
    have hraw :
        Nat.card (splitTorus.range ⊔ splitWeylZ : Subgroup (PSL2MatrixGroup F)) =
          2 * Nat.card splitTorus.range := by
      simpa [splitWeylZ] using hsplitCandidate_card_raw
    rw [hsplit_range_card] at hraw
    exact hraw
  have hsplit_normalizer_sub_candidate
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ splitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) ≤
        splitTorus.range ⊔ splitWeylZ := by
    obtain ⟨r, hr_ne_one⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
    rcases hR_le r.property with ⟨a, ha⟩
    have ha_not_ker : a ∉ splitTorus.ker := by
      intro hak
      apply hr_ne_one
      apply Subtype.ext
      change (r : PSL2MatrixGroup F) = 1
      rw [← ha]
      exact hak
    have ha_ne_inv : (a : F) ≠ (a⁻¹ : F) := by
      intro hai
      apply ha_not_ker
      apply (hsplit_mem_ker_iff a).2
      rw [mem_rootsOfUnity]
      have haiU : a = a⁻¹ := by
        apply Units.ext
        simpa using hai
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp haiU)
    intro g
    refine QuotientGroup.induction_on g ?_
    intro A hA_normalizes
    have hr_conj_R :
        qSL A * (r : PSL2MatrixGroup F) * (qSL A)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hA_normalizes
        (r : PSL2MatrixGroup F)).mp r.property
    rcases hR_le hr_conj_R with ⟨b, hb⟩
    have hq :
        qSL (splitTorusSL b) = qSL (A * splitTorusSL a * A⁻¹) := by
      simpa [splitTorus, qSL, ← ha] using hb
    rcases (QuotientGroup.mk'_eq_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        splitTorusSL b * z * A = A * splitTorusSL a := by
      calc
        splitTorusSL b * z * A =
            (A * splitTorusSL a * A⁻¹) * A := by rw [hzeq]
        _ = A * splitTorusSL a := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (!![(b : F), 0; 0, (b⁻¹ : F)] :
          Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        !![(a : F), 0; 0, (a⁻¹ : F)] at hmat
    rw [← hscalar] at hmat
    rcases split_matrix_diag_or_antidiag A a b
        ((z : Matrix (Fin 2) (Fin 2) F) 0 0)
        ha_ne_inv hmat with hdiag | hanti
    · rcases hdiag with ⟨h01, h10⟩
      obtain ⟨u, hAeq⟩ :=
        eq_splitTorusSLHom_of_offDiagonal_eq_zero A h01 h10
      have hAeq : A = splitTorusSL u := by
        simpa [splitTorusSL] using hAeq
      rw [hAeq]
      exact (show splitTorus.range ≤
        splitTorus.range ⊔ splitWeylZ from le_sup_left)
          ⟨u, rfl⟩
    · rcases hanti with ⟨h00, h11⟩
      obtain ⟨u, hAeq⟩ :=
        eq_standardSplitWeylSL_mul_splitTorusSLHom_of_diagonal_eq_zero
          A h00 h11
      have hAeq : A = splitWeylSL * splitTorusSL u := by
        simpa [splitWeylSL, splitTorusSL] using hAeq
      have hw :
          splitWeyl ∈
            splitTorus.range ⊔ splitWeylZ :=
        (show splitWeylZ ≤
          splitTorus.range ⊔ splitWeylZ from le_sup_right)
            (Subgroup.mem_zpowers splitWeyl)
      have hu :
          splitTorus u ∈
            splitTorus.range ⊔ splitWeylZ :=
        (show splitTorus.range ≤
          splitTorus.range ⊔ splitWeylZ from le_sup_left)
            ⟨u, rfl⟩
      change qSL A ∈ splitTorus.range ⊔ splitWeylZ
      rw [hAeq, map_mul]
      exact (splitTorus.range ⊔ splitWeylZ).mul_mem hw hu
  have hsplit_normalizer_eq_candidate
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ splitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) =
        splitTorus.range ⊔ splitWeylZ := by
    apply le_antisymm
    · exact hsplit_normalizer_sub_candidate R hR_le hR_ne
    · apply sup_le
      · intro t ht
        have hsplit_comm {x y : PSL2MatrixGroup F}
            (hx : x ∈ splitTorus.range)
            (hy : y ∈ splitTorus.range) : Commute x y := by
          rcases hx with ⟨a, rfl⟩
          rcases hy with ⟨b, rfl⟩
          change splitTorus a * splitTorus b =
            splitTorus b * splitTorus a
          simp only [← map_mul]
          rw [mul_comm]
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hsplit_comm ht (hR_le hy)
          simpa [hcomm.eq, mul_assoc] using hy
        · intro hy
          have hy' : y = t⁻¹ * (t * y * t⁻¹) * t := by
            simp [mul_assoc]
          have hconjR : t * y * t⁻¹ ∈ R := hy
          have hcomm := hsplit_comm
            (splitTorus.range.inv_mem ht) (hR_le hconjR)
          have hfixed :
              t⁻¹ * (t * y * t⁻¹) * t = t * y * t⁻¹ := by
            calc
              t⁻¹ * (t * y * t⁻¹) * t =
                  (t * y * t⁻¹) * t⁻¹ * t := by rw [hcomm.eq]
              _ = t * y * t⁻¹ := by group
          rw [hy', hfixed]
          exact hconjR
      · apply Subgroup.zpowers_le.2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rcases hR_le hy with ⟨a, ha⟩
          have hy_inv : y⁻¹ ∈ R := R.inv_mem hy
          have hconj :
              splitWeyl * y * splitWeyl⁻¹ = y⁻¹ := by
            rw [← ha]
            simpa using hsplitWeyl_conj a
          rw [hconj]
          exact hy_inv
        · intro hy
          have hyT :
              splitWeyl * y * splitWeyl⁻¹ ∈ splitTorus.range :=
            hR_le hy
          rcases hyT with ⟨a, ha⟩
          have hrecover : y = splitTorus a⁻¹ := by
            calc
              y = splitWeyl⁻¹ *
                  (splitWeyl * y * splitWeyl⁻¹) * splitWeyl := by
                    simp [mul_assoc]
              _ = splitWeyl⁻¹ * splitTorus a * splitWeyl := by
                    rw [← ha]
              _ = splitTorus a⁻¹ := by
                calc
                  splitWeyl⁻¹ * splitTorus a * splitWeyl =
                      splitWeyl⁻¹ *
                        (splitWeyl * splitTorus a⁻¹ * splitWeyl⁻¹) *
                          splitWeyl := by rw [hsplitWeyl_conj]; simp
                  _ = splitTorus a⁻¹ := by simp [mul_assoc]
          have hy_inv :
              (splitWeyl * y * splitWeyl⁻¹)⁻¹ ∈ R := R.inv_mem hy
          rw [hrecover]
          rw [← ha] at hy_inv
          simpa using hy_inv
  refine ⟨splitTorus.range, splitWeyl, hsplit_range_cyclic,
    hsplit_range_card, hsplitWeyl_mem_normalizer, hsplitWeyl_not_mem,
    hsplitWeyl_sq, ?_, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨a, rfl⟩
    simpa using hsplitWeyl_conj a
  · simpa [splitWeylZ] using hsplitCandidate_card_raw
  · intro R hR hRne
    simpa [splitWeylZ] using
      hsplit_normalizer_eq_candidate R hR hRne

-- Omitted: outside declaration proof/source closure.


end Dickson
end Glauberman


end Source9

end CFSGPackSplit
