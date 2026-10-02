-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_2_a_sylow_equiv_additive
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T11:35:43.808982+00:00
-- url     : https://prove2.me/submissions/e1e3b8f9-15c0-493e-87f3-40801aff6926

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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

set_option autoImplicit false
namespace CFSGPackSylow

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

-- Omitted: outside declaration proof/source closure.

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

/-- Huppert II.8.2(a): every Sylow `p`-subgroup of `PSL(2,p^f)` is
isomorphic to the additive group of the defining field. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (Q : Sylow p (PSL2MatrixGroup F)) :
    Nonempty (Multiplicative F ≃* Q) := by
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
  have hcard_psl :
      Nat.card (PSL2MatrixGroup F) * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F * (Nat.card F ^ 2 - 1) := by
    have hcard_sl :
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
          Nat.card F * (Nat.card F ^ 2 - 1) := by
      have hdet_range_top :
          (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).range = ⊤ := by
        ext u
        constructor
        · intro _
          simp
        · intro _
          let diagonalGL : GL (Fin 2) F :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              (Matrix.diagonal ![(u : F), 1]) (by
                simp [Matrix.det_diagonal, Fin.prod_univ_two])
          refine ⟨diagonalGL, ?_⟩
          ext
          simp [diagonalGL, Matrix.det_diagonal, Fin.prod_univ_two]
      have hGL :
          Nat.card (GL (Fin 2) F) =
            (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F) := by
        simpa [Fin.prod_univ_two] using
          (Matrix.card_GL_field (𝔽 := F) 2)
      let detHom :=
        Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
      have hRange :
          Nat.card detHom.range = Nat.card F - 1 := by
        rw [hdet_range_top]
        simpa using (Fintype.card_units (α := F))
      have hmul :
          Nat.card detHom.range * Nat.card detHom.ker =
            Nat.card (GL (Fin 2) F) := by
        rw [← Subgroup.index_ker detHom]
        exact detHom.ker.index_mul_card
      have hker :
          Nat.card detHom.ker =
            Nat.card F * (Nat.card F ^ 2 - 1) := by
        have hq : 1 < Nat.card F := Finite.one_lt_card
        have hdiff :
            Nat.card F ^ 2 - Nat.card F =
              Nat.card F * (Nat.card F - 1) := by
          rw [pow_two]
          calc
            Nat.card F * Nat.card F - Nat.card F =
                Nat.card F * Nat.card F - Nat.card F * 1 := by simp
            _ = Nat.card F * (Nat.card F - 1) :=
              (Nat.mul_sub_left_distrib _ _ _).symm
        have hcancel :
            (Nat.card F - 1) * Nat.card detHom.ker =
              (Nat.card F - 1) *
                (Nat.card F * (Nat.card F ^ 2 - 1)) := by
          calc
            (Nat.card F - 1) * Nat.card detHom.ker =
                Nat.card (GL (Fin 2) F) := by
              rw [hRange] at hmul
              exact hmul
            _ = (Nat.card F ^ 2 - 1) *
                (Nat.card F ^ 2 - Nat.card F) := hGL
            _ = (Nat.card F - 1) *
                (Nat.card F * (Nat.card F ^ 2 - 1)) := by
              rw [hdiff]
              ring
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F))) hcancel
      calc
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
            Nat.card detHom.ker := by
          let slEquivDetKer :
              Matrix.SpecialLinearGroup (Fin 2) F ≃ detHom.ker := by
            refine Equiv.ofBijective
              (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
                exact Matrix.SpecialLinearGroup.coeToGL_det A⟩) ?_
            constructor
            · intro A B h
              apply Matrix.SpecialLinearGroup.toGL_injective
              exact congrArg Subtype.val h
            · intro A
              refine ⟨⟨(A : GL (Fin 2) F), ?_⟩, ?_⟩
              · have hmem := A.property
                change
                  Matrix.GeneralLinearGroup.det
                    (A : GL (Fin 2) F) = 1 at hmem
                exact Units.ext_iff.mp hmem
              · apply Subtype.ext
                apply Matrix.GeneralLinearGroup.ext
                intro i j
                rfl
          exact Nat.card_congr slEquivDetKer
        _ = Nat.card F * (Nat.card F ^ 2 - 1) := hker

    have hcard_center :
        Nat.card
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F)) =
          Nat.gcd (Nat.card F - 1) 2 := by
      rw [Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
          (R := F) (n := Fin 2) 0).toEquiv]
      simpa using hcard_roots
    calc
      Nat.card (PSL2MatrixGroup F) *
          Nat.gcd (Nat.card F - 1) 2 =
          Nat.card (PSL2MatrixGroup F) *
            Nat.card
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F)) := by
            rw [hcard_center]
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))).symm
      _ = Nat.card F * (Nat.card F ^ 2 - 1) := hcard_sl
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    projectiveUnipotentAddChar F
  have h_unipotent_injective : Function.Injective unipotent :=
    projectiveUnipotentAddChar_injective F
  let U : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hUcard : Nat.card U = Nat.card F := by
    let e : Multiplicative F ≃ U :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU_isPGroup : IsPGroup p U := by
    apply IsPGroup.of_card
    rw [hUcard, hFcard]
  have hU_index_not_dvd : ¬ p ∣ U.index := by
    have hindex_card : U.index * Nat.card U = Nat.card (PSL2MatrixGroup F) :=
      U.index_mul_card
    have hindex_gcd :
        U.index * Nat.gcd (Nat.card F - 1) 2 = Nat.card F ^ 2 - 1 := by
      have hmul :
          Nat.card F * (U.index * Nat.gcd (Nat.card F - 1) 2) =
            Nat.card F * (Nat.card F ^ 2 - 1) := by
        calc
          Nat.card F * (U.index * Nat.gcd (Nat.card F - 1) 2) =
              (U.index * Nat.card U) * Nat.gcd (Nat.card F - 1) 2 := by
                rw [hUcard]
                ring
          _ = Nat.card (PSL2MatrixGroup F) *
                Nat.gcd (Nat.card F - 1) 2 := by rw [hindex_card]
          _ = Nat.card F * (Nat.card F ^ 2 - 1) := hcard_psl
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    intro hp_index
    have hp_bad : p ∣ Nat.card F ^ 2 - 1 := by
      rw [← hindex_gcd]
      exact dvd_mul_of_dvd_left hp_index _
    have hf_ne_zero : f ≠ 0 :=
      huppert_II_8_27_field_exponent_ne_zero hFcard
    have hp_card : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p hf_ne_zero
    have hp_sq : p ∣ Nat.card F ^ 2 := dvd_pow hp_card (by norm_num)
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_sq hp_bad
      have hpos : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
      have hsub : Nat.card F ^ 2 - (Nat.card F ^ 2 - 1) = 1 := by omega
      rw [hsub] at h
      exact h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  let ambientSylow : Sylow p (PSL2MatrixGroup F) :=
    hU_isPGroup.toSylow hU_index_not_dvd
  let eU : Multiplicative F ≃* U :=
    MulEquiv.ofBijective unipotent.toMonoidHom.rangeRestrict
      ⟨by
        intro a b hab
        exact h_unipotent_injective (congrArg Subtype.val hab),
        MonoidHom.rangeRestrict_surjective _⟩
  have hAmbient : (ambientSylow : Subgroup (PSL2MatrixGroup F)) = U := rfl
  let eAmbient : Multiplicative F ≃* ambientSylow :=
    eU.trans (MulEquiv.subgroupCongr hAmbient.symm)
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq
      (α := Sylow p (PSL2MatrixGroup F))
      (PSL2MatrixGroup F) ambientSylow Q
  let eConj : ambientSylow ≃*
      (g • ambientSylow : Sylow p (PSL2MatrixGroup F)) :=
    (MulAut.conj g).subgroupMap ambientSylow
  rw [hg] at eConj
  exact ⟨eAmbient.trans eConj⟩

end Dickson
end Glauberman


end Source4

end CFSGPackSylow
