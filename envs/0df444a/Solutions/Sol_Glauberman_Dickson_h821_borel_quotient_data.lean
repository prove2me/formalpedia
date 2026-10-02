-- Prove2me | solution 1 for Glauberman.Dickson.h821_borel_quotient_data
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:38:27.496262+00:00
-- url     : https://prove2.me/submissions/2adc8f2f-2c81-412c-9f46-e085ad161760

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
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_2_a_sylow_equiv_additive

set_option autoImplicit false
namespace Glauberman.Dickson
end Glauberman.Dickson
namespace CFSGPackBorel
open _root_.Glauberman.Dickson

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

section Source3
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonUnipotent.lean
/-!
# Unipotent characters for Dickson's classification

The concrete `2 × 2` matrix calculations are kept in this small module so
callers can reuse the resulting character and injectivity theorem without
elaborating finite index case splits in a large local context.
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups

universe u

/-- The upper-unitriangular additive character in `SL(2,F)`. -/
@[expose] public def unipotentSLAddChar
    (F : Type u) [Field F] :
    AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
  { toFun := fun a => ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
    map_zero_eq_one' := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    map_add_eq_mul' := by
      intro a b
      apply Subtype.ext
      ext i j
      change (!![1, a + b; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j =
        ((!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) *
          (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F)) i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm] }

@[simp] public theorem unipotentSLAddChar_coe
    {F : Type u} [Field F] (a : F) :
    (unipotentSLAddChar F a : Matrix (Fin 2) (Fin 2) F) =
      !![1, a; 0, 1] := rfl

-- Omitted: outside declaration proof/source closure.

/-- The upper-unitriangular additive character in `PSL(2,F)`. -/
@[expose] public def projectiveUnipotentAddChar
    (F : Type u) [Field F] :
    AddChar F (PSL2MatrixGroup F) :=
  (QuotientGroup.mk'
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).compAddChar
      (unipotentSLAddChar F)

/-- Distinct upper-unitriangular matrices remain distinct in `PSL(2,F)`. -/
theorem projectiveUnipotentAddChar_injective
    (F : Type u) [Field F] :
    Function.Injective (projectiveUnipotentAddChar F) := by
  intro a b hab
  have hdiff : projectiveUnipotentAddChar F (a - b) = 1 := by
    rw [sub_eq_add_neg, (projectiveUnipotentAddChar F).map_add_eq_mul,
      (projectiveUnipotentAddChar F).map_neg_eq_inv, hab, mul_inv_cancel]
  have hcenter :
      unipotentSLAddChar F (a - b) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    exact (QuotientGroup.eq_one_iff (unipotentSLAddChar F (a - b))).mp hdiff
  have hscalar :=
    Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have hab0 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply sub_eq_zero.mp
  change (0 : F) = a - b at hab0
  exact hab0.symm

end Dickson
end Glauberman


end Source3

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

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

end Dickson
end Glauberman


end Source8

section Source14
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonBorelMatrices.lean
/-!
# Concrete Borel matrix identities for Dickson's classification
-/

namespace Glauberman
namespace Dickson

universe u

/-- A split-torus matrix moves past an upper unipotent by scaling its
parameter by the square of the diagonal entry. -/
theorem splitTorusSLHom_mul_unipotentSLAddChar
    {F : Type u} [Field F] (a : Fˣ) (x : F) :
    splitTorusSLHom F a * unipotentSLAddChar F x =
      unipotentSLAddChar F ((a : F) ^ 2 * x) * splitTorusSLHom F a := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusSLHom_coe, unipotentSLAddChar_coe,
      Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc, mul_comm]

/-- An upper-triangular determinant-one matrix factors as unipotent times
split torus. -/
theorem eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h10 : A 1 0 = 0) :
    ∃ a : Fˣ,
      A = unipotentSLAddChar F (A 0 1 * A 0 0) * splitTorusSLHom F a := by
  have hdet := A.property
  rw [Matrix.det_fin_two] at hdet
  have had : A 0 0 * A 1 1 = 1 := by
    simpa [h10] using hdet
  have ha_zero : A 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one had
  let a : Fˣ := Units.mk0 (A 0 0) ha_zero
  have hd_inv : A 1 1 = (a⁻¹ : F) := by
    simpa [a] using eq_inv_of_mul_eq_one_right had
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a]
  · simp [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a, ha_zero]
  · simpa [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a] using h10
  · simpa [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a] using hd_inv

end Dickson
end Glauberman


end Source14

section Source15
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonSylowNormalizer.lean
/-!
# Sylow normalizers in Dickson's classification

This module isolates Huppert II.8.21 and the Sylow-normalizer shape used by
the II.8.22 counting argument.
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise
universe u v

-- Omitted: outside declaration proof/source closure.

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The standard upper-triangular Borel data used in Huppert II.8.21. -/
private theorem h821_standard_borel_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U T : Subgroup (PSL2MatrixGroup F),
      Nat.card U = Nat.card F ∧
      IsPGroup p U ∧
      IsMulCommutative U ∧
      IsCyclic T ∧
      Nat.card T =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card T ∣ Nat.card F - 1 ∧
      T ≤ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      (∀ t : PSL2MatrixGroup F, t ∈ T →
        ∀ x : PSL2MatrixGroup F, x ∈ U →
          t * x * t⁻¹ = x → t = 1 ∨ x = 1) ∧
      (∀ x : PSL2MatrixGroup F, x ∈ U ⊔ T → x ∉ U →
        ∃ u : PSL2MatrixGroup F, u ∈ U ∧
          x ∈ T.map (MulAut.conj u).toMonoidHom) ∧
      (∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) ≤ U ⊔ T) ∧
      ∃ unipotent : AddChar F (PSL2MatrixGroup F),
        ∃ splitTorus : Fˣ →* PSL2MatrixGroup F,
          Function.Injective unipotent ∧
          U = unipotent.toMonoidHom.range ∧
          T = splitTorus.range ∧
          (∀ a : Fˣ, ∀ x : F,
            splitTorus a * unipotent x * (splitTorus a)⁻¹ =
              unipotent ((a : F) ^ 2 * x)) ∧
          (∀ x : F, unipotent x =
            QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) ∧
          ∀ a : Fˣ, splitTorus a =
            QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    unipotentSLAddChar F
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    qSL.compAddChar unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    simpa [unipotent, qSL, unipotentSL, projectiveUnipotentAddChar] using
      projectiveUnipotentAddChar_injective F
  let U : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hUcard : Nat.card U = Nat.card F := by
    let e : Multiplicative F ≃ U :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU_isPGroup : IsPGroup p U := by
    apply IsPGroup.of_card
    rw [hUcard, hFcard]
  have hU_commutative : IsMulCommutative U := by
    constructor
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    apply Subtype.ext
    change unipotent a.toAdd * unipotent b.toAdd =
      unipotent b.toAdd * unipotent a.toAdd
    rw [← unipotent.map_add_eq_mul, add_comm,
      unipotent.map_add_eq_mul]
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    splitTorusSLHom F
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    qSL.comp splitTorusSL
  let T : Subgroup (PSL2MatrixGroup F) := splitTorus.range
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
          (Nat.even_sub
            (show 1 ≤ Nat.card F from
              (Finite.one_lt_card (α := F)).le)).mp heven
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
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
          hcenter (0 : Fin 2)
      have ha_inv_val :=
        congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
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
        simpa [Nat.card_eq_fintype_card] using
          (Fintype.card_units (α := F))
  have hTcard :
      Nat.card T =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hsplit_range_mul
  have hT_cyclic : IsCyclic T := by
    have hUnitsCyclic : IsCyclic Fˣ := by
      let : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
      exact isCyclic_of_surjective
        ((⊤ : Subgroup Fˣ).subtype) (by
          intro a
          exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
    let : IsCyclic Fˣ := hUnitsCyclic
    exact isCyclic_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
  have hTcard_dvd : Nat.card T ∣ Nat.card F - 1 := by
    have hdvd := Subgroup.card_dvd_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
    have hUnitsCard : Nat.card Fˣ = Nat.card F - 1 := by
      simpa [Nat.card_eq_fintype_card] using
        (Fintype.card_units (α := F))
    rw [← hUnitsCard]
    simpa [T] using hdvd
  have hsplitSL_mul (a : Fˣ) (x : F) :
      splitTorusSL a * unipotentSL x =
        unipotentSL ((a : F) ^ 2 * x) * splitTorusSL a := by
    simpa [splitTorusSL, unipotentSL] using
      splitTorusSLHom_mul_unipotentSLAddChar a x
  have hsplitSL_conj (a : Fˣ) (x : F) :
      splitTorusSL a * unipotentSL x * (splitTorusSL a)⁻¹ =
        unipotentSL ((a : F) ^ 2 * x) := by
    rw [hsplitSL_mul]
    simp
  have hsplit_conj (a : Fˣ) (x : F) :
      splitTorus a * unipotent x * (splitTorus a)⁻¹ =
        unipotent ((a : F) ^ 2 * x) := by
    simpa [splitTorus, unipotent] using congrArg qSL
      (hsplitSL_conj a x)
  have hT_le_normalizer :
      T ≤ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) := by
    intro t ht
    rcases ht with ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rcases hh with ⟨x, hx⟩
      refine ⟨Multiplicative.ofAdd ((a : F) ^ 2 * x.toAdd), ?_⟩
      change unipotent ((a : F) ^ 2 * x.toAdd) =
        splitTorus a * h * (splitTorus a)⁻¹
      rw [← hx]
      exact (hsplit_conj a x.toAdd).symm
    · intro hh
      rcases hh with ⟨y, hy⟩
      refine ⟨Multiplicative.ofAdd (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd), ?_⟩
      change unipotent (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd) = h
      calc
        unipotent (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd) =
            splitTorus a⁻¹ * unipotent y.toAdd * (splitTorus a⁻¹)⁻¹ :=
          (hsplit_conj a⁻¹ y.toAdd).symm
        _ = h := by
          change unipotent y.toAdd = splitTorus a * h * (splitTorus a)⁻¹ at hy
          have hTa_inv : splitTorus a⁻¹ = (splitTorus a)⁻¹ :=
            map_inv splitTorus a
          rw [hy, hTa_inv]
          group
  have hT_fixedPointFree
      (t : PSL2MatrixGroup F) (ht : t ∈ T)
      (x : PSL2MatrixGroup F) (hx : x ∈ U)
      (hfix : t * x * t⁻¹ = x) : t = 1 ∨ x = 1 := by
    rcases ht with ⟨a, ha⟩
    rcases hx with ⟨b, hb⟩
    change unipotent b.toAdd = x at hb
    have hcoord : (a : F) ^ 2 * b.toAdd = b.toAdd := by
      apply h_unipotent_injective
      calc
        unipotent ((a : F) ^ 2 * b.toAdd) =
            splitTorus a * unipotent b.toAdd * (splitTorus a)⁻¹ :=
          (hsplit_conj a b.toAdd).symm
        _ = splitTorus a * x * (splitTorus a)⁻¹ := by rw [hb]
        _ = t * x * t⁻¹ := by rw [ha]
        _ = x := hfix
        _ = unipotent b.toAdd := hb.symm
    by_cases hbzero : b.toAdd = 0
    · right
      rw [← hb, hbzero]
      simp
    · left
      rw [← ha]
      apply MonoidHom.mem_ker.mp
      apply (hsplit_mem_ker_iff a).2
      rw [mem_rootsOfUnity]
      apply Units.ext
      apply mul_right_cancel₀ hbzero
      simpa using hcoord
  have hB_conjugate_torus
      (x : PSL2MatrixGroup F) (hxB : x ∈ U ⊔ T) (hxU : x ∉ U) :
      ∃ u : PSL2MatrixGroup F, u ∈ U ∧
        x ∈ T.map (MulAut.conj u).toMonoidHom := by
    have hB_product :
        (U : Set (PSL2MatrixGroup F)) * (T : Set (PSL2MatrixGroup F)) =
          (U ⊔ T : Subgroup (PSL2MatrixGroup F)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left
        U T hT_le_normalizer]
    change x ∈ ((U ⊔ T : Subgroup (PSL2MatrixGroup F)) :
      Set (PSL2MatrixGroup F)) at hxB
    rw [← hB_product] at hxB
    rcases hxB with ⟨y, hyU, z, hzT, hyz⟩
    rcases hyU with ⟨b, hb⟩
    rcases hzT with ⟨a, ha⟩
    have hfactor : unipotent b.toAdd * splitTorus a = x := by
      rw [← hb, ← ha] at hyz
      exact hyz
    have hsplit_ne_one : splitTorus a ≠ 1 := by
      intro ha_one
      apply hxU
      rw [← hfactor, ha_one, mul_one]
      exact ⟨b, rfl⟩
    have ha_sq_ne : (a : F) ^ 2 ≠ 1 := by
      intro ha_sq
      apply hsplit_ne_one
      have ha_sq_units : a ^ 2 = 1 := by
        apply Units.ext
        simpa using ha_sq
      exact MonoidHom.mem_ker.mp
        ((hsplit_mem_ker_iff a).2
          (by simpa [mem_rootsOfUnity] using ha_sq_units))
    have hden : 1 - (a : F) ^ 2 ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm ha_sq_ne)
    let s : F := b.toAdd / (1 - (a : F) ^ 2)
    let u : PSL2MatrixGroup F := unipotent s
    have hs : s + (a : F) ^ 2 * (-s) = b.toAdd := by
      dsimp [s]
      field_simp [hden]
      ring
    have hx_conj :
        u * splitTorus a * u⁻¹ = x := by
      rw [← hfactor]
      change unipotent s * splitTorus a * (unipotent s)⁻¹ =
        unipotent b.toAdd * splitTorus a
      calc
        unipotent s * splitTorus a * (unipotent s)⁻¹ =
            unipotent s *
              (splitTorus a * unipotent (-s) * (splitTorus a)⁻¹) *
                splitTorus a := by
          rw [unipotent.map_neg_eq_inv]
          group
        _ = unipotent s * unipotent ((a : F) ^ 2 * (-s)) *
              splitTorus a := by
          rw [hsplit_conj]
        _ = unipotent (s + (a : F) ^ 2 * (-s)) * splitTorus a := by
          rw [unipotent.map_add_eq_mul]
        _ = unipotent b.toAdd * splitTorus a := by rw [hs]
    refine ⟨u, ⟨Multiplicative.ofAdd s, rfl⟩, ?_⟩
    rw [← hx_conj]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom
      (⟨a, rfl⟩ : splitTorus a ∈ T)
  have hnormalizer_le
      (R : Subgroup (PSL2MatrixGroup F)) (hR_le_U : R ≤ U)
      (hR_ne_bot : R ≠ ⊥) :
      Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) ≤ U ⊔ T := by
    obtain ⟨r, hr_ne_one⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne_bot
    have hrU : (r : PSL2MatrixGroup F) ∈ U := hR_le_U r.property
    rcases hrU with ⟨t, ht⟩
    have ht_ne_zero : t.toAdd ≠ 0 := by
      intro ht_zero
      apply hr_ne_one
      apply Subtype.ext
      change (r : PSL2MatrixGroup F) = 1
      rw [← ht]
      change unipotent t.toAdd = 1
      rw [ht_zero]
      simp
    have hr_eq : (r : PSL2MatrixGroup F) = unipotent t.toAdd := by
      simpa using ht.symm
    intro g
    refine QuotientGroup.induction_on g ?_
    intro A hA_normalizes
    have hr_conj_R :
        qSL A * (r : PSL2MatrixGroup F) * (qSL A)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hA_normalizes
        (r : PSL2MatrixGroup F)).mp r.property
    have hconj_mem :
        qSL A * unipotent t.toAdd * (qSL A)⁻¹ ∈ U := by
      rw [← hr_eq]
      exact hR_le_U hr_conj_R
    rcases hconj_mem with ⟨x, hx⟩
    have hxq :
        qSL (unipotentSL x.toAdd) =
          qSL (A * unipotentSL t.toAdd * A⁻¹) := by
      simpa [unipotent] using hx
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hxq with
      ⟨z, hz_center, hz_eq⟩
    have hz_eq_mul_A :
        unipotentSL x.toAdd * z * A = A * unipotentSL t.toAdd := by
      calc
        unipotentSL x.toAdd * z * A =
            (A * unipotentSL t.toAdd * A⁻¹) * A := by rw [hz_eq]
        _ = A * unipotentSL t.toAdd := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz_center (0 : Fin 2)
    have hz_eq_matrix := congrArg Subtype.val hz_eq_mul_A
    change
      (unipotentSL x.toAdd : Matrix (Fin 2) (Fin 2) F) *
          (z : Matrix (Fin 2) (Fin 2) F) *
            (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          (unipotentSL t.toAdd : Matrix (Fin 2) (Fin 2) F) at hz_eq_matrix
    rw [← hscalar] at hz_eq_matrix
    have h10 := congrFun (congrFun hz_eq_matrix (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hz_eq_matrix (1 : Fin 2)) (1 : Fin 2)
    simp [unipotentSL, Matrix.mul_apply] at h10 h11
    have hc_zero : A (1 : Fin 2) (0 : Fin 2) = 0 := by
      by_cases hr_one : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      · rw [hr_one, one_mul] at h11
        have hcancel := congrArg (fun y : F => y - A 1 1) h11
        have hct : A 1 0 * t.toAdd = 0 := by
          simpa using hcancel.symm
        exact (mul_eq_zero.mp hct).resolve_right ht_ne_zero
      · have hprod :
            (((z : Matrix (Fin 2) (Fin 2) F) 0 0) - 1) *
                A (1 : Fin 2) (0 : Fin 2) = 0 := by
          calc
            (((z : Matrix (Fin 2) (Fin 2) F) 0 0) - 1) * A 1 0 =
                ((z : Matrix (Fin 2) (Fin 2) F) 0 0) * A 1 0 - A 1 0 := by ring
            _ = 0 := by rw [h10]; ring
        exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hr_one)
    obtain ⟨aU, hfactor0⟩ :=
      eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero
        A hc_zero
    have hfactor :
        A = unipotentSL (A 0 1 * A 0 0) * splitTorusSL aU := by
      simpa [unipotentSL, splitTorusSL] using hfactor0
    have hfactor_q := congrArg qSL hfactor
    change qSL A ∈ U ⊔ T
    have hfactor_q' :
        qSL A = unipotent (A 0 1 * A 0 0) * splitTorus aU := by
      simpa [unipotent, splitTorus] using hfactor_q
    rw [hfactor_q']
    exact (U ⊔ T).mul_mem
      ((show U ≤ U ⊔ T from le_sup_left)
        ⟨Multiplicative.ofAdd (A 0 1 * A 0 0), rfl⟩)
      ((show T ≤ U ⊔ T from le_sup_right) ⟨aU, rfl⟩)
  exact ⟨U, T, hUcard, hU_isPGroup, hU_commutative, hT_cyclic,
    hTcard, hTcard_dvd, hT_le_normalizer, hT_fixedPointFree,
    hB_conjugate_torus, hnormalizer_le, unipotent, splitTorus,
    h_unipotent_injective, rfl, rfl, hsplit_conj,
    fun _ => rfl, fun _ => rfl⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The normalizer quotient in Huppert II.8.21 embeds in the cyclic
split-torus quotient of a standard Borel subgroup. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hP_ne_bot : (P : Subgroup H) ≠ ⊥)
    (N : Subgroup H) (hN : N = Subgroup.normalizer (P : Set H))
    (PN : Subgroup N) [PN.Normal]
    (hPN : PN = (P : Subgroup H).subgroupOf N) :
    IsCyclic (N ⧸ PN) ∧
      Nat.card (N ⧸ PN) ∣
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      (∀ n : N, n ∉ PN → ∀ x : (P : Subgroup H), x ≠ 1 →
        (n : H) * (x : H) * (n : H)⁻¹ ≠ (x : H)) ∧
      ∃ U T : Subgroup (PSL2MatrixGroup F),
        ∃ conjH : H →* PSL2MatrixGroup F,
          Function.Injective conjH ∧
          (∃ g : PSL2MatrixGroup F, ∀ h : H,
            conjH h = g * (h : PSL2MatrixGroup F) * g⁻¹) ∧
          IsMulCommutative U ∧
          IsCyclic T ∧
          Nat.card T =
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
          (∀ t : PSL2MatrixGroup F, t ∈ T →
            ∀ x : PSL2MatrixGroup F, x ∈ U →
              t * x * t⁻¹ = x → t = 1 ∨ x = 1) ∧
          (P : Subgroup H).map conjH ≤ U ∧
          U ⊔ T ≤ Subgroup.normalizer
            (U : Set (PSL2MatrixGroup F)) ∧
          (∀ x : PSL2MatrixGroup F, x ∈ U ⊔ T → x ∉ U →
            ∃ u : PSL2MatrixGroup F, u ∈ U ∧
              x ∈ T.map (MulAut.conj u).toMonoidHom) ∧
          (∀ n : N, conjH (n : H) ∈ U ⊔ T) ∧
          (∀ n : N, conjH (n : H) ∈ U ↔ n ∈ PN) ∧
          ∃ unipotent : AddChar F (PSL2MatrixGroup F),
            ∃ splitTorus : Fˣ →* PSL2MatrixGroup F,
              Function.Injective unipotent ∧
              U = unipotent.toMonoidHom.range ∧
              T = splitTorus.range ∧
              (∀ a : Fˣ, ∀ x : F,
                splitTorus a * unipotent x * (splitTorus a)⁻¹ =
                  unipotent ((a : F) ^ 2 * x)) ∧
              (∀ x : F, unipotent x =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F)) ∧
              ∀ a : Fˣ, splitTorus a =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                      by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  obtain ⟨U, T, hUcard, hU_isPGroup, hU_commutative,
      hT_cyclic, hTcard, hTcard_dvd, hT_le_normalizer,
      hT_fixedPointFree, hB_conjugate_torus, hnormalizer_le,
      unipotent, splitTorus, h_unipotent_injective,
      hU_range, hT_range, hsplit_conj, hunipotent_matrix,
      hsplitTorus_matrix⟩ :=
    h821_standard_borel_data hFcard
  obtain ⟨Q0, hU_le_Q0⟩ := hU_isPGroup.exists_le_sylow
  have hQ0card : Nat.card (Q0 : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    rcases huppert_II_8_2_a_sylow_equiv_additive hFcard Q0 with ⟨eQ⟩
    exact (Nat.card_congr eQ.toEquiv).symm
  have hU_eq_Q0 : U = (Q0 : Subgroup (PSL2MatrixGroup F)) :=
    Subgroup.eq_of_le_of_card_ge hU_le_Q0 (by rw [hQ0card, hUcard])
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  have hPmap_le_Q : (P : Subgroup H).map H.subtype ≤
      (Q : Subgroup (PSL2MatrixGroup F)) := by
    rw [Subgroup.map_le_iff_le_comap, hQcomap]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (PSL2MatrixGroup F) Q Q0
  let Pambient : Subgroup (PSL2MatrixGroup F) :=
    (P : Subgroup H).map H.subtype
  let Pconj : Subgroup (PSL2MatrixGroup F) :=
    Pambient.map (MulAut.conj g).toMonoidHom
  have hQconj_eq :
      (Q : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom = U := by
    have hg' := congrArg
      (fun S : Sylow p (PSL2MatrixGroup F) =>
        (S : Subgroup (PSL2MatrixGroup F))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      ← hU_eq_Q0] at hg'
    exact hg'
  have hPconj_le_U : Pconj ≤ U := by
    rw [← hQconj_eq]
    exact Subgroup.map_mono hPmap_le_Q
  have hPambient_ne_bot : Pambient ≠ ⊥ := by
    intro hbot
    apply hP_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective
      (P : Subgroup H) H.subtype_injective).mp hbot
  have hPconj_ne_bot : Pconj ≠ ⊥ := by
    intro hbot
    apply hPambient_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective Pambient
      (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp hbot
  let B : Subgroup (PSL2MatrixGroup F) := U ⊔ T
  have hPconj_normalizer_le_B :
      Subgroup.normalizer (Pconj : Set (PSL2MatrixGroup F)) ≤ B := by
    simpa [B] using hnormalizer_le Pconj hPconj_le_U hPconj_ne_bot
  have h_normalizer_conj_to_B (n : N) :
      (MulAut.conj g) (H.subtype n) ∈ B := by
    have hn_normalizer : (n : H) ∈
        Subgroup.normalizer (P : Set H) := by
      rw [← hN]
      exact n.property
    have hn_ambient :
        H.subtype n ∈ Subgroup.normalizer
          (Pambient : Set (PSL2MatrixGroup F)) := by
      apply Subgroup.le_normalizer_map H.subtype
      exact ⟨n, hn_normalizer, rfl⟩
    have hn_conj :
        (MulAut.conj g) (H.subtype n) ∈
          Subgroup.normalizer (Pconj : Set (PSL2MatrixGroup F)) := by
      change (MulAut.conj g) (H.subtype n) ∈
        Subgroup.normalizer
          ((Pambient.map (MulAut.conj g).toMonoidHom :
            Subgroup (PSL2MatrixGroup F)) : Set (PSL2MatrixGroup F))
      apply Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom
      exact ⟨H.subtype n, hn_ambient, rfl⟩
    exact hPconj_normalizer_le_B hn_conj
  let conjH : H →* PSL2MatrixGroup F :=
    (MulAut.conj g).toMonoidHom.comp H.subtype
  have hconjH_injective : Function.Injective conjH :=
    (MulAut.conj g).injective.comp H.subtype_injective
  let KH : Subgroup H := U.comap conjH
  have hP_le_KH : (P : Subgroup H) ≤ KH := by
    intro x hx
    change conjH x ∈ U
    apply hPconj_le_U
    change conjH x ∈
      Pambient.map (MulAut.conj g).toMonoidHom
    refine ⟨H.subtype x, ?_, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hKH_isPGroup : IsPGroup p KH :=
    hU_isPGroup.comap_of_injective conjH hconjH_injective
  have hKH_eq_P : KH = (P : Subgroup H) :=
    P.is_maximal' hKH_isPGroup hP_le_KH
  have hU_le_B : U ≤ B := by
    exact le_sup_left
  have hT_le_B : T ≤ B := by
    exact le_sup_right
  let UB : Subgroup B := U.subgroupOf B
  let TB : Subgroup B := T.subgroupOf B
  let hUB_normal : UB.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer hT_le_normalizer)
  have hUB_sup_TB : UB ⊔ TB = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup hU_le_B hT_le_B
    simpa [B, UB, TB] using hsup.symm
  have hTB_cyclic : IsCyclic TB := by
    let eTB : TB ≃* T := Subgroup.subgroupOfEquivOfLe hT_le_B
    let : IsCyclic T := hT_cyclic
    exact isCyclic_of_surjective eTB.symm eTB.symm.surjective
  let borelQuotient : B →* B ⧸ UB := QuotientGroup.mk' UB
  have hmap_UB_bot : Subgroup.map borelQuotient UB = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' UB).symm
  have hmap_TB_top : Subgroup.map borelQuotient TB = ⊤ := by
    calc
      Subgroup.map borelQuotient TB =
          ⊥ ⊔ Subgroup.map borelQuotient TB := by simp
      _ = Subgroup.map borelQuotient (UB ⊔ TB) := by
        rw [Subgroup.map_sup, hmap_UB_bot]
      _ = Subgroup.map borelQuotient ⊤ := by rw [hUB_sup_TB]
      _ = ⊤ := Subgroup.map_top_of_surjective borelQuotient
        (QuotientGroup.mk'_surjective UB)
  let torusToBorelQuotient : TB →* B ⧸ UB :=
    borelQuotient.comp TB.subtype
  have htorusToBorelQuotient_surjective :
      Function.Surjective torusToBorelQuotient := by
    intro y
    have hy : y ∈ Subgroup.map borelQuotient TB := by
      rw [hmap_TB_top]
      trivial
    rcases hy with ⟨b, hb, hby⟩
    exact ⟨⟨b, hb⟩, hby⟩
  have hB_quotient_cyclic : IsCyclic (B ⧸ UB) := by
    let : IsCyclic TB := hTB_cyclic
    exact isCyclic_of_surjective torusToBorelQuotient
      htorusToBorelQuotient_surjective
  have hB_quotient_card_dvd : Nat.card (B ⧸ UB) ∣ Nat.card T := by
    have hdvd := Subgroup.card_dvd_of_surjective
      torusToBorelQuotient htorusToBorelQuotient_surjective
    have hTBcard : Nat.card TB = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_B).toEquiv
    rwa [hTBcard] at hdvd
  let normToB : N →* B :=
    (conjH.comp N.subtype).codRestrict B h_normalizer_conj_to_B
  have hnormToB_injective : Function.Injective normToB := by
    intro x y hxy
    apply Subtype.ext
    apply hconjH_injective
    exact congrArg Subtype.val hxy
  let normToBQuotient : N →* B ⧸ UB :=
    borelQuotient.comp normToB
  have hborelQuotient_ker : borelQuotient.ker = UB :=
    QuotientGroup.ker_mk' UB
  have hnormToBQuotient_ker : normToBQuotient.ker = PN := by
    ext n
    constructor
    · intro hn
      have hn' : normToB n ∈ borelQuotient.ker := hn
      rw [hborelQuotient_ker] at hn'
      have hnU : conjH (n : H) ∈ U := hn'
      have hnKH : (n : H) ∈ KH := hnU
      rw [hKH_eq_P] at hnKH
      rw [hPN]
      exact hnKH
    · intro hn
      have hnP : (n : H) ∈ (P : Subgroup H) := by
        rw [hPN] at hn
        exact hn
      have hnU : conjH (n : H) ∈ U := by
        change (n : H) ∈ KH
        rw [hKH_eq_P]
        exact hnP
      have hn' : normToB n ∈ borelQuotient.ker := by
        rw [hborelQuotient_ker]
        exact hnU
      exact hn'
  let eNormalizerQuotient : N ⧸ PN ≃* normToBQuotient.range :=
    (QuotientGroup.quotientMulEquivOfEq hnormToBQuotient_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange normToBQuotient)
  have hNormalizer_quotient_cyclic : IsCyclic (N ⧸ PN) := by
    have hRangeCyclic : IsCyclic normToBQuotient.range := by
      let : IsCyclic (B ⧸ UB) := hB_quotient_cyclic
      exact Subgroup.isCyclic normToBQuotient.range
    let : IsCyclic normToBQuotient.range := hRangeCyclic
    exact isCyclic_of_surjective eNormalizerQuotient.symm
      eNormalizerQuotient.symm.surjective
  have hNormalizer_quotient_card_dvd :
      Nat.card (N ⧸ PN) ∣
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    have hRange_dvd :
        Nat.card normToBQuotient.range ∣ Nat.card (B ⧸ UB) :=
      normToBQuotient.range.card_subgroup_dvd_card
    have hdvd := dvd_trans hRange_dvd hB_quotient_card_dvd
    have hquotient_eq_range :
        Nat.card (N ⧸ PN) = Nat.card normToBQuotient.range :=
      Nat.card_congr eNormalizerQuotient.toEquiv
    rw [hquotient_eq_range]
    rw [← hTcard]
    exact hdvd
  have hP_map_conjH_le_U : (P : Subgroup H).map conjH ≤ U := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hP_le_KH
  have hB_le_normalizer :
      U ⊔ T ≤ Subgroup.normalizer
        (U : Set (PSL2MatrixGroup F)) :=
    sup_le Subgroup.le_normalizer hT_le_normalizer
  have hconjH_mem_U_iff (n : N) :
      conjH (n : H) ∈ U ↔ n ∈ PN := by
    constructor
    · intro hnU
      have hnKH : (n : H) ∈ KH := hnU
      rw [hKH_eq_P] at hnKH
      rw [hPN]
      exact hnKH
    · intro hn
      have hnP : (n : H) ∈ (P : Subgroup H) := by
        rw [hPN] at hn
        exact hn
      change (n : H) ∈ KH
      rw [hKH_eq_P]
      exact hnP
  have hNormalizer_fixedPointFree :
      ∀ n : N, n ∉ PN → ∀ x : (P : Subgroup H), x ≠ 1 →
        (n : H) * (x : H) * (n : H)⁻¹ ≠ (x : H) := by
    intro n hnPN x hx hfix
    have hn_not_U : conjH (n : H) ∉ U := by
      intro hnU
      exact hnPN ((hconjH_mem_U_iff n).mp hnU)
    obtain ⟨u, huU, hntorus⟩ :=
      hB_conjugate_torus (conjH (n : H))
        (h_normalizer_conj_to_B n) hn_not_U
    rcases hntorus with ⟨t, htT, ht⟩
    change u * t * u⁻¹ = conjH (n : H) at ht
    have hxU : conjH (x : H) ∈ U :=
      hP_map_conjH_le_U (Subgroup.mem_map_of_mem conjH x.property)
    let x' : PSL2MatrixGroup F := u⁻¹ * conjH (x : H) * u
    have hx'U : x' ∈ U := by
      exact U.mul_mem (U.mul_mem (U.inv_mem huU) hxU) huU
    have hx'ne : x' ≠ 1 := by
      intro hx'one
      apply hx
      apply Subtype.ext
      apply hconjH_injective
      have hconjx : conjH (x : H) = 1 := by
        calc
          conjH (x : H) = u * x' * u⁻¹ := by
            dsimp [x']
            group
          _ = 1 := by rw [hx'one]; simp
      simpa using hconjx
    have hfixMap :
        conjH (n : H) * conjH (x : H) * (conjH (n : H))⁻¹ =
          conjH (x : H) := by
      simpa using congrArg conjH hfix
    have hfix' : t * x' * t⁻¹ = x' := by
      dsimp [x']
      calc
        t * (u⁻¹ * conjH (x : H) * u) * t⁻¹ =
            u⁻¹ * ((u * t * u⁻¹) * conjH (x : H) *
              (u * t * u⁻¹)⁻¹) * u := by group
        _ = u⁻¹ * (conjH (n : H) * conjH (x : H) *
              (conjH (n : H))⁻¹) * u := by rw [ht]
        _ = u⁻¹ * conjH (x : H) * u := by rw [hfixMap]
    have htne : t ≠ 1 := by
      intro htone
      apply hn_not_U
      rw [← ht, htone]
      simp
    rcases hT_fixedPointFree t htT x' hx'U hfix' with htone | hx'one
    · exact htne htone
    · exact hx'ne hx'one
  exact ⟨hNormalizer_quotient_cyclic, hNormalizer_quotient_card_dvd,
    hNormalizer_fixedPointFree, U, T, conjH, hconjH_injective,
    ⟨g, fun _ => rfl⟩,
    hU_commutative, hT_cyclic,
    hTcard, hT_fixedPointFree, hP_map_conjH_le_U, hB_le_normalizer,
    hB_conjugate_torus, h_normalizer_conj_to_B,
    hconjH_mem_U_iff, unipotent, splitTorus,
    h_unipotent_injective, hU_range, hT_range, hsplit_conj,
    hunipotent_matrix, hsplitTorus_matrix⟩


-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.


-- Omitted: outside declaration proof/source closure.


-- Omitted: outside declaration proof/source closure.


-- Omitted: outside declaration proof/source closure.


end Dickson
end Glauberman


end Source15

end CFSGPackBorel
