-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_26_dickson_case_p_part_normalizer_large
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:50:36.875229+00:00
-- url     : https://prove2.me/submissions/90b8ab9f-aff6-419c-818c-bd76ac759d2d

/-
Original formalization: Qiuzhen-CFSG/CFSG and original source authors.
Commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; Apache-2.0.
arexychen: declaration extraction, exact-environment replay, packaging and validation.
Adaptation: unused subfield-conjugacy witness fields are removed from
the proof of the plain endpoint. A finite arithmetic case check clears
irrelevant context; one sum equality uses transitivity instead of simp.
All mathematical premises and the public conclusion are unchanged. Source scopes/visibility and
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
import Definitions.Def_cfsg_elementary_abelian
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Independence
import Theorems.Thm_Glauberman_Dickson_h821_borel_quotient_data
import Theorems.Thm_Glauberman_Dickson_h826_group_order_cases
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_dickson_counting
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_partition_count_of_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_25_transitive_degree_six_order_sixty
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_2_a_sylow_equiv_additive

import Theorems.Thm_Glauberman_Dickson_h826_cyclic_family_shape
import Theorems.Thm_BenderSuzuki_External_huppert_II_6_11_projective_action
import Theorems.Thm_Glauberman_Dickson_h826_subfield_embedding_of_borel_and_swap
set_option autoImplicit false
namespace Glauberman.Dickson
end Glauberman.Dickson
namespace BenderSuzuki.External
end BenderSuzuki.External
namespace CFSGPackCase826
open _root_.BenderSuzuki.External
open _root_.Glauberman.Dickson

section Source0
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/BenderSuzuki/PFAppendixIII/Basic.lean
/-!
# Appendix III Suzuki two-group interfaces
-/

namespace BenderSuzuki
namespace PFAppendixIII

section BasicGroup

/-- Local instance for the prime `2`, shared by Suzuki two-group coordinates and matrix models. -/
instance instFactNatPrimeTwo : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

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

-- Omitted: outside declaration proof/source closure.

end BasicGroup

-- Omitted: outside declaration proof/source closure.

universe u v

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
/-!
# Appendix III Suzuki two-group coordinate interfaces
-/
-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

end PFAppendixIII
end BenderSuzuki


end Source0

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
open PFAppendixIII

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


section Source7
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/BenderSuzuki/External/Huppert/II/theorem_6_14.lean
/-!
# Huppert II.6.14

This file records the two small-field identifications used in
Huppert--Blackburn XI.1.3.
-/

namespace BenderSuzuki
namespace External

universe u

theorem huppert614_card_specialLinearGroup
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hdet_range_top :
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K)).range = ⊤ := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      let diagonalGL : GL (Fin 2) K :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero
          (Matrix.diagonal ![(u : K), 1]) (by
            simp [Matrix.det_diagonal, Fin.prod_univ_two])
      refine ⟨diagonalGL, ?_⟩
      ext
      simp [diagonalGL, Matrix.det_diagonal, Fin.prod_univ_two]
  have hGL :
      Nat.card (GL (Fin 2) K) =
        (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
    simpa [Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let detHom := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K)
  have hRange : Nat.card detHom.range = Nat.card K - 1 := by
    rw [hdet_range_top]
    simpa using (Fintype.card_units (α := K))
  have hmul :
      Nat.card detHom.range * Nat.card detHom.ker =
        Nat.card (GL (Fin 2) K) := by
    rw [← Subgroup.index_ker detHom]
    exact detHom.ker.index_mul_card
  have hker :
      Nat.card detHom.ker = Nat.card K * (Nat.card K ^ 2 - 1) := by
    have hdiff :
        Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
      rw [pow_two]
      calc
        Nat.card K * Nat.card K - Nat.card K =
            Nat.card K * Nat.card K - Nat.card K * 1 := by simp
        _ = Nat.card K * (Nat.card K - 1) :=
          (Nat.mul_sub_left_distrib _ _ _).symm
    have hcancel :
        (Nat.card K - 1) * Nat.card detHom.ker =
          (Nat.card K - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) := by
      calc
        (Nat.card K - 1) * Nat.card detHom.ker =
            Nat.card (GL (Fin 2) K) := by
          rw [hRange] at hmul
          exact hmul
        _ = (Nat.card K ^ 2 - 1) *
            (Nat.card K ^ 2 - Nat.card K) := hGL
        _ = (Nat.card K - 1) *
            (Nat.card K * (Nat.card K ^ 2 - 1)) := by
          rw [hdiff]
          ring
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K))) hcancel
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
        Nat.card detHom.ker := by
      let slEquivDetKer :
          Matrix.SpecialLinearGroup (Fin 2) K ≃ detHom.ker := by
        refine Equiv.ofBijective
          (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
            exact Matrix.SpecialLinearGroup.coeToGL_det A⟩) ?_
        constructor
        · intro A B h
          apply Matrix.SpecialLinearGroup.toGL_injective
          exact congrArg Subtype.val h
        · intro A
          refine ⟨⟨(A : GL (Fin 2) K), ?_⟩, ?_⟩
          · have hmem := A.property
            change Matrix.GeneralLinearGroup.det (A : GL (Fin 2) K) = 1 at hmem
            exact Units.ext_iff.mp hmem
          · apply Subtype.ext
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            rfl
      exact Nat.card_congr slEquivDetKer
    _ = Nat.card K * (Nat.card K ^ 2 - 1) := hker

theorem huppert614_card_center_of_neg_one_eq_one
    {K : Type u} [Field K] [Finite K] (hneg : (-1 : K) = 1) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let e :=
    Equiv.Set.image ((↑) : Kˣ → K) (rootsOfUnity 2 K : Set Kˣ)
      Units.val_injective
  have he :
      Nat.card (rootsOfUnity 2 K) =
        Nat.card (((↑) : Kˣ → K) '' (rootsOfUnity 2 K : Set Kˣ)) :=
    Nat.card_congr e
  rw [Units.val_set_image_rootsOfUnity_two] at he
  have hroots : Nat.card (rootsOfUnity 2 K) = 1 := by
    simpa [hneg] using he
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (R := K) (n := Fin 2) 0).toEquiv]
  exact hroots

theorem huppert614_card_center_of_neg_one_ne_one
    {K : Type u} [Field K] [Finite K] (hneg : (-1 : K) ≠ 1) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let e :=
    Equiv.Set.image ((↑) : Kˣ → K) (rootsOfUnity 2 K : Set Kˣ)
      Units.val_injective
  have he :
      Nat.card (rootsOfUnity 2 K) =
        Nat.card (((↑) : Kˣ → K) '' (rootsOfUnity 2 K : Set Kˣ)) :=
    Nat.card_congr e
  rw [Units.val_set_image_rootsOfUnity_two] at he
  have hroots : Nat.card (rootsOfUnity 2 K) = 2 := by
    simpa [hneg, Ne.symm hneg] using he
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (R := K) (n := Fin 2) 0).toEquiv]
  exact hroots

theorem huppert614_card_psl_mul_center
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  calc
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).symm
    _ = Nat.card K * (Nat.card K ^ 2 - 1) :=
      huppert614_card_specialLinearGroup

-- Omitted: outside declaration proof/source closure.


end External
end BenderSuzuki


end Source7

section Source13
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonTorusNormalizer.lean
/-!
# Cyclic torus normalizers for Dickson's classification

This module isolates the maximal cyclic representatives and reflection/dihedral
normalizer package used in Huppert II.8.22.
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise

universe u v

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

theorem relIndex_le_two_of_inter_eq
    {G : Type u} [Group G] [Finite G]
    (T B N A : Subgroup G)
    (hB_le : B ≤ N) (hinter : T ⊓ B = A)
    (hindex : T.relIndex N = 2) :
    A.relIndex B ≤ 2 := by
  rw [← hinter, Subgroup.inf_relIndex_right]
  rw [← hindex]
  exact Subgroup.relIndex_le_of_le_right hB_le (by
    rw [Subgroup.relIndex]
    exact Nat.card_pos.ne')

theorem relIndex_eq_two_of_card_eq_two_mul
    {G : Type u} [Group G] [Finite G]
    (T N : Subgroup G) (hT_le : T ≤ N)
    (hcard : Nat.card N = 2 * Nat.card T) :
    T.relIndex N = 2 := by
  rw [Subgroup.relIndex]
  have hsubcard : Nat.card (T.subgroupOf N) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le).toEquiv
  have hmul := (T.subgroupOf N).index_mul_card
  rw [hsubcard, hcard] at hmul
  exact Nat.mul_right_cancel Nat.card_pos hmul

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

end Dickson
end Glauberman


end Source13

section Source18
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean
/-!
# Huppert II.8.27

Dickson's subgroup classification for subgroups of PSL(2,p^f).
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open scoped Pointwise
open scoped LinearAlgebra.Projectivization

universe u v

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

/-- The II.8.2(a) consequence used in II.8.26: a Sylow subgroup of a
subgroup of `PSL(2,p^f)` is elementary abelian. -/
private theorem h826_sylow_elementary
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) :
    IsElementaryAbelian p P := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  have hPmemQ (x : P) :
      (((x : P) : H) : PSL2MatrixGroup F) ∈ (Q : Subgroup _) := by
    have hx :
        (x : H) ∈ (Q : Subgroup (PSL2MatrixGroup F)).comap H.subtype := by
      rw [hQcomap]
      exact x.property
    exact hx
  have hFieldElementary : IsElementaryAbelian p (Multiplicative F) := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => mul_comm x y⟩ }
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    change Multiplicative.ofAdd x.toAdd ^ p = 1
    rw [← ofAdd_nsmul]
    simp
  obtain ⟨eQ⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard Q
  have hQElementary : IsElementaryAbelian p Q := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => ?_⟩ }
        exponent_dvd_p := ?_ }
    · apply eQ.symm.injective
      simpa using
        hFieldElementary.toIsMulCommutative.is_comm.comm
          (eQ.symm x) (eQ.symm y)
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply eQ.symm.injective
      have hx : (eQ.symm x) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          hFieldElementary.exponent_dvd_p (eQ.symm x)
      simpa using hx
  refine
    { toIsMulCommutative :=
        { is_comm := ⟨fun x y => ?_⟩ }
      exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    let yQ : Q := ⟨((y : H) : PSL2MatrixGroup F), hPmemQ y⟩
    have hxy := congrArg Subtype.val
      (hQElementary.toIsMulCommutative.is_comm.comm xQ yQ)
    simpa [xQ, yQ] using hxy
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    have hxpow : xQ ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        hQElementary.exponent_dvd_p xQ
    simpa [xQ] using congrArg Subtype.val hxpow

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

private theorem h826_card_actor_dvd_group_card_sub_one
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E]
    (hfree : ∀ a : A, a ≠ 1 → ∀ e : E, a • e = e → e = 1) :
    Nat.card A ∣ Nat.card E - 1 := by
  classical
  let X := {e : E // e ≠ 1}
  let : MulAction A X :=
    { smul := fun a e => ⟨a • (e : E), by
        intro h
        apply e.2
        have h' := congrArg (fun x : E => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro e
        apply Subtype.ext
        change (1 : A) • (e : E) = (e : E)
        exact one_smul A (e : E)
      mul_smul := by
        intro a b e
        apply Subtype.ext
        change (a * b) • (e : E) = a • (b • (e : E))
        exact mul_smul a b (e : E) }
  have hstab : ∀ e : X, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_ne_one
    have hfix : a • (e : E) = (e : E) := congrArg Subtype.val hae
    exact e.2 (hfree a ha_ne_one (e : E) hfix)
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hXcard : Nat.card X = Nat.card E - 1 := by
    let : Fintype E := Fintype.ofFinite E
    let : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {e : E // e ≠ 1} = Fintype.card E - 1
    simp
  rw [hXcard, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A X)), by
    rw [mul_comm]
    exact hcard⟩

private theorem h826_card_actor_dvd_two_mul_card
    {A X : Type*} [Group A] [Finite A] [Finite X] [MulAction A X]
    (hstab : ∀ x : X, Nat.card (MulAction.stabilizer A x) ≤ 2) :
    Nat.card A ∣ 2 * Nat.card X := by
  classical
  let Ω := Quotient (MulAction.orbitRel A X)
  let : Fintype Ω := Fintype.ofFinite Ω
  have horbit (ω : Ω) :
      Nat.card A ∣ 2 * Nat.card (MulAction.orbit A ω.out) := by
    let : Fintype A := Fintype.ofFinite A
    let : Fintype (MulAction.orbit A ω.out) := Fintype.ofFinite _
    let : Fintype (MulAction.stabilizer A ω.out) := Fintype.ofFinite _
    have hmul :
        Nat.card (MulAction.orbit A ω.out) *
            Nat.card (MulAction.stabilizer A ω.out) = Nat.card A := by
      simpa [Nat.card_eq_fintype_card] using
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group A ω.out
    have hstab_cases :
        Nat.card (MulAction.stabilizer A ω.out) = 1 ∨
          Nat.card (MulAction.stabilizer A ω.out) = 2 := by
      have hpos : 0 < Nat.card (MulAction.stabilizer A ω.out) := Nat.card_pos
      have hle := hstab ω.out
      omega
    rcases hstab_cases with hs | hs
    · rw [hs, mul_one] at hmul
      rw [← hmul]
      exact ⟨2, by ring⟩
    · rw [hs] at hmul
      rw [← hmul]
      exact ⟨1, by ring⟩
  have hcardX :
      Nat.card X = ∑ ω : Ω, Nat.card (MulAction.orbit A ω.out) := by
    calc
      Nat.card X =
          Nat.card (Σ ω : Ω, MulAction.orbit A ω.out) :=
        Nat.card_congr (MulAction.selfEquivSigmaOrbits A X)
      _ = ∑ ω : Ω, Nat.card (MulAction.orbit A ω.out) := Nat.card_sigma
  have hsum :
      Nat.card A ∣
        ∑ ω : Ω, 2 * Nat.card (MulAction.orbit A ω.out) := by
    exact Finset.dvd_sum fun ω _hω => horbit ω
  simpa only [hcardX, Finset.mul_sum] using hsum

private theorem h826_card_pgl2
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
          Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalar_inj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) *
        (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) *
        (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

@[expose] public def h826_pglMap
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) :
    Matrix.ProjGenLinGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F := by
  let f : GL (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjGenLinGroup.mk.comp
      (Matrix.GeneralLinearGroup.map e)
  apply Matrix.ProjGenLinGroup.lift f
  ext a
  change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map e
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.map e a, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.scalar]

set_option backward.isDefEq.respectTransparency false in
theorem h826_pglMap_mk
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (A : GL (Fin 2) K) :
    h826_pglMap e (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map e A) := by
  unfold h826_pglMap
  exact Matrix.ProjGenLinGroup.lift_mk _ A

theorem h826_pglMap_injective
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (he : Function.Injective e) :
    Function.Injective (h826_pglMap e) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pglMap_mk] at hx
    have hcenterF :
        Matrix.GeneralLinearGroup.map e A ∈
          Subgroup.center (GL (Fin 2) F) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterF with ⟨c, hc⟩
    have hc00 :
        c = e ((A : Matrix (Fin 2) (Fin 2) K) 0 0) := by
      have h := congrFun (congrFun hc (0 : Fin 2)) (0 : Fin 2)
      simpa [Matrix.GeneralLinearGroup.map_apply] using h
    have hcenterK : A ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
      ext i j
      apply he
      have h := congrFun (congrFun hc i) j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map_apply, hc00] at h ⊢ <;>
        exact h
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker,
      Matrix.ProjGenLinGroup.ker_mk]
    exact hcenterK
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

@[expose] public def h826_pslToPGL
    {K : Type u} [Field K] :
    PSL2MatrixGroup K →*
      Matrix.ProjGenLinGroup (Fin 2) K := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) K :=
    Matrix.ProjGenLinGroup.mk.comp
      Matrix.SpecialLinearGroup.toGL
  apply QuotientGroup.lift
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) f
  intro A hA
  rw [MonoidHom.mem_ker]
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL A) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
  rcases Matrix.SpecialLinearGroup.mem_center_iff.mp hA with
    ⟨c, _, hc⟩
  exact ⟨c, by simpa using hc⟩

theorem h826_pslToPGL_mk
    {K : Type u} [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    h826_pslToPGL
        (QuotientGroup.mk'
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.SpecialLinearGroup.toGL A) := by
  rfl

theorem h826_pslToPGL_injective
    {K : Type u} [Field K] :
    Function.Injective (h826_pslToPGL (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases QuotientGroup.mk'_surjective
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K)) x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pslToPGL_mk] at hx
    have hcenterGL :
        Matrix.SpecialLinearGroup.toGL A ∈
          Subgroup.center (GL (Fin 2) K) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterGL with ⟨c, hc⟩
    have hc_sq : c ^ 2 = 1 := by
      have hc' :
          Matrix.scalar (Fin 2) c =
            (A : Matrix (Fin 2) (Fin 2) K) := by
        simpa using hc
      have hdet := A.property
      rw [← hc'] at hdet
      simpa [Matrix.det_diagonal, Fin.prod_univ_two, pow_two] using hdet
    have hcenterSL :
        A ∈ Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      exact ⟨c, by simpa using hc_sq, by simpa using hc⟩
    exact (QuotientGroup.eq_one_iff A).mpr hcenterSL
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

/-- The concrete subfield retained by the large-normalizer branch of
Dickson's classification.  After one projective conjugation, the ambient
inclusion of `H` is the scalar-extension of a faithful projective
representation over `K`. -/
private def h826_slEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) L := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.SpecialLinearGroup (Fin 2) L :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let g : Matrix.SpecialLinearGroup (Fin 2) L →*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]

private def h826_pslEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) :
    PSL2MatrixGroup K ≃* PSL2MatrixGroup L := by
  let eSL := h826_slEquiv e
  apply QuotientGroup.congr
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) L)) eSL
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (MulEquivClass.apply_mem_center_iff eSL).2 hB
  · intro hA
    refine ⟨eSL.symm A, ?_, eSL.apply_symm_apply A⟩
    exact (MulEquivClass.apply_mem_center_iff eSL.symm).2 hA

set_option backward.isDefEq.respectTransparency false in
private theorem h826_pslToPGL_range_le_of_index_two
    {K : Type u} [Field K] [Finite K]
    (htwo : (2 : K) ≠ 0)
    (M : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K))
    (hMindex : M.index = 2) :
    (h826_pslToPGL (K := K)).range ≤ M := by
  classical
  intro x hx
  rcases hx with ⟨y, rfl⟩
  induction y using QuotientGroup.induction_on with
  | _ A =>
      change h826_pslToPGL
          (QuotientGroup.mk'
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) K)) A) ∈ M
      rw [h826_pslToPGL_mk]
      let PMatrix : Matrix (Fin 2) (Fin 2) K → Prop := fun B =>
        ∃ hB : Matrix.det B = 1,
          Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL
              (⟨B, hB⟩ : Matrix.SpecialLinearGroup (Fin 2) K)) ∈ M
      have hP : PMatrix (A : Matrix (Fin 2) (Fin 2) K) := by
        apply Matrix.diagonal_transvection_induction PMatrix
        · intro D hdet
          have hDdet : Matrix.det (Matrix.diagonal D) = 1 :=
            hdet.trans A.property
          let AD : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨Matrix.diagonal D, hDdet⟩
          have hDprod : D 0 * D 1 = 1 := by
            simpa [Matrix.det_diagonal, Fin.prod_univ_two] using hDdet
          have hD0ne : D 0 ≠ 0 := by
            intro hzero
            rw [hzero, zero_mul] at hDprod
            exact zero_ne_one hDprod
          let B : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![D 0, 0; 0, 1]
              (by simp [Matrix.det_fin_two, hD0ne])
          let d0 : Kˣ := Units.mk0 (D 0) hD0ne
          have hmat :
              B * B =
                Matrix.GeneralLinearGroup.scalar (Fin 2) d0 *
                  Matrix.SpecialLinearGroup.toGL AD := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [B, d0, AD, Matrix.GeneralLinearGroup.scalar,
                Matrix.mul_apply, hDprod]
          refine ⟨hDdet, ?_⟩
          have hsquare :=
            Subgroup.sq_mem_of_index_two hMindex
              (Matrix.ProjGenLinGroup.mk B)
          rw [pow_two, ← map_mul, hmat, map_mul,
            Matrix.ProjGenLinGroup.mk_scalar, one_mul] at hsquare
          exact hsquare
        · intro t
          let thalf : Matrix.TransvectionStruct (Fin 2) K :=
            ⟨t.i, t.j, t.hij, t.c / 2⟩
          let B : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨thalf.toMatrix, thalf.det⟩
          let C : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨t.toMatrix, t.det⟩
          have hc : t.c / 2 + t.c / 2 = t.c := by
            field_simp
            ring
          have hBC : B * B = C := by
            apply Subtype.ext
            change Matrix.transvection t.i t.j (t.c / 2) *
                Matrix.transvection t.i t.j (t.c / 2) =
              Matrix.transvection t.i t.j t.c
            rw [Matrix.transvection_mul_transvection_same
              t.i t.j t.hij, hc]
          refine ⟨t.det, ?_⟩
          have hsquare :=
            Subgroup.sq_mem_of_index_two hMindex
              (Matrix.ProjGenLinGroup.mk
                (Matrix.SpecialLinearGroup.toGL B))
          rw [pow_two, ← map_mul, ← map_mul, hBC] at hsquare
          exact hsquare
        · rintro B C ⟨hBdet, hB⟩ ⟨hCdet, hC⟩
          have hBCdet : Matrix.det (B * C) = 1 := by
            simp [hBdet, hCdet]
          let Bs : Matrix.SpecialLinearGroup (Fin 2) K := ⟨B, hBdet⟩
          let Cs : Matrix.SpecialLinearGroup (Fin 2) K := ⟨C, hCdet⟩
          let BCs : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨B * C, hBCdet⟩
          have hmul : Bs * Cs = BCs := by rfl
          refine ⟨hBCdet, ?_⟩
          change Matrix.ProjGenLinGroup.mk
              (Matrix.SpecialLinearGroup.toGL BCs) ∈ M
          rw [← hmul, map_mul, map_mul]
          exact M.mul_mem hB hC
      rcases hP with ⟨hdet, hmem⟩
      have hAeq :
          (⟨(A : Matrix (Fin 2) (Fin 2) K), hdet⟩ :
            Matrix.SpecialLinearGroup (Fin 2) K) = A :=
        Subtype.ext rfl
      rw [hAeq] at hmem
      exact hmem

private theorem h826_pslToPGL_range_index_eq_two
    {K : Type u} [Field K] [Finite K]
    (hneg : (-1 : K) ≠ 1) :
    (h826_pslToPGL (K := K)).range.index = 2 := by
  let iota := h826_pslToPGL (K := K)
  have hcenter :
      Nat.card
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 :=
    huppert614_card_center_of_neg_one_ne_one hneg
  have hPSLmul := huppert614_card_psl_mul_center (K := K)
  rw [hcenter] at hPSLmul
  have hPGLcard := h826_card_pgl2 (K := K)
  have hrangeCard :
      Nat.card (PSL2MatrixGroup K) = Nat.card iota.range :=
    Nat.card_congr (MonoidHom.ofInjective h826_pslToPGL_injective).toEquiv
  have hindex := iota.range.index_mul_card
  rw [← hrangeCard, hPGLcard, ← hPSLmul] at hindex
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := PSL2MatrixGroup K))
  calc
    iota.range.index * Nat.card (PSL2MatrixGroup K) =
        Nat.card (PSL2MatrixGroup K) * 2 := hindex
    _ = 2 * Nat.card (PSL2MatrixGroup K) := by ring

private theorem h826_index_two_subgroup_eq_pslRange
    {K : Type u} [Field K] [Finite K]
    (htwo : (2 : K) ≠ 0)
    (M : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K))
    (hMindex : M.index = 2)
    (hPSLindex : (h826_pslToPGL (K := K)).range.index = 2) :
    M = (h826_pslToPGL (K := K)).range := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let R := (h826_pslToPGL (K := K)).range
  let : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite M := Finite.of_injective M.subtype M.subtype_injective
  let : Finite R := Finite.of_injective R.subtype R.subtype_injective
  have hRleM : R ≤ M :=
    h826_pslToPGL_range_le_of_index_two htwo M hMindex
  have hMcard := M.card_mul_index
  have hRcard := R.card_mul_index
  rw [hMindex] at hMcard
  rw [hPSLindex] at hRcard
  have hcardEq : Nat.card M = Nat.card R := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    exact hMcard.trans hRcard.symm
  exact (Subgroup.eq_of_le_of_card_ge hRleM (by rw [hcardEq])).symm

private def h826_scalarStabilizer
    {F : Type*} [Field F] [Finite F] (W : AddSubgroup F) :
    Subfield F where
  carrier := {a | ∀ x : F, x ∈ W → a * x ∈ W}
  zero_mem' := by
    intro x hx
    simp
  one_mem' := by
    intro x hx
    simpa using hx
  add_mem' := by
    intro a b ha hb x hx
    rw [add_mul]
    exact W.add_mem (ha x hx) (hb x hx)
  neg_mem' := by
    intro a ha x hx
    rw [neg_mul]
    exact W.neg_mem (ha x hx)
  mul_mem' := by
    intro a b ha hb x hx
    rw [mul_assoc]
    exact ha (b * x) (hb x hx)
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      intro x hx
      simp
    · let φ : W → W := fun x => ⟨a * (x : F), ha x x.property⟩
      have hφinj : Function.Injective φ := by
        intro x y hxy
        apply Subtype.ext
        have hval := congrArg Subtype.val hxy
        exact mul_left_cancel₀ ha0 hval
      have hφsurj : Function.Surjective φ :=
        Finite.injective_iff_surjective.mp hφinj
      intro x hx
      obtain ⟨y, hy⟩ := hφsurj ⟨x, hx⟩
      have hyval : a * (y : F) = x := congrArg Subtype.val hy
      have heq : a⁻¹ * x = (y : F) := by
        rw [← hyval]
        field_simp
      rw [heq]
      exact y.property

private theorem h826_exponent_dvd_of_pow_sub_one_dvd
    {p m f : ℕ} (hp : 2 ≤ p)
    (h : p ^ m - 1 ∣ p ^ f - 1) :
    m ∣ f := by
  have hgcd :
      Nat.gcd (p ^ m - 1) (p ^ f - 1) = p ^ m - 1 :=
    Nat.gcd_eq_left_iff_dvd.mpr h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hgcd
  have hleft : 1 ≤ p ^ Nat.gcd m f := one_le_pow₀ (by omega)
  have hright : 1 ≤ p ^ m := one_le_pow₀ (by omega)
  have hpow : p ^ Nat.gcd m f = p ^ m := by omega
  have heq : Nat.gcd m f = m := Nat.pow_right_injective hp hpow
  rw [← heq]
  exact Nat.gcd_dvd_right m f

-- Omitted: outside declaration proof/source closure.

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- Huppert II.8.26: the Dickson case with a larger Sylow p-normalizer. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hP_nontrivial : Nat.card P ≠ 1)
    (hnormalizer : Subgroup.normalizer (P : Set H) ≠ (P : Subgroup H)) :
    (∃ m t : ℕ,
      t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
      ∃ N C : Subgroup H,
        N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
        IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
    (∃ m : ℕ, p ^ m = 3 ∧
      (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
      Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) := by
  obtain ⟨m, hPm⟩ := P.isPGroup'.exists_card_eq
  have hm_ne_zero : m ≠ 0 := by
    intro hm
    subst m
    apply hP_nontrivial
    simpa using hPm
  have h826_counting_shapes :
      Nat.card H = Nat.card (Subgroup.normalizer (P : Set H)) ∨
      (p ^ m = 3 ∧ Nat.card H = 60 ∧
        (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nat.card (Sylow 5 H) = 6 ∧
        Function.Injective (MulAction.toPermHom H (Sylow 5 H))) ∨
      (2 * m ∣ f ∧ Nonempty
        (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
      (m ∣ f ∧ Nonempty
        (H ≃* PSL2MatrixGroup (GaloisField p m))) := by
    classical
    let : Fintype F := Fintype.ofFinite F
    let : CharP F p :=
      charP_of_card_eq_prime_pow (by simpa using hFcard)
    rcases huppert_II_8_22_dickson_counting hFcard H P hPm with
      ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
        hrepresentative, hdistinct, hs, hnormalizerZ, _hdihedral,
        hnormalizerP, hdivides, _hcounting⟩
    let NP : Subgroup H := Subgroup.normalizer (P : Set H)
    let NZ : Fin r → Subgroup H := fun i =>
      Subgroup.normalizer (Z i : Set H)
    let term : Fin r → ℕ := fun i =>
      (Nat.card (Z i) - 1) * (NZ i).index
    have hpartition_count :
        Nat.card H =
          1 + (p ^ m - 1) * NP.index + ∑ i, term i := by
      dsimp only [NP, NZ, term]
      apply huppert_II_8_22_partition_count_of_unique_family P hPm Z
      intro x hx
      convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
        hcoprime hmaximal hrepresentative hdistinct x hx using 1
      funext A
      rcases A with Q | z <;> rfl
    have hz_index_factor :
        ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
      intro i
      have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
        dsimp only [NZ]
        exact hnormalizerZ i
      calc
        (Nat.card (Z i) * s i) * (NZ i).index =
            Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
        _ = Nat.card H := (NZ i).card_mul_index
    have hterm_factor (i : Fin r) :
        term i + (NZ i).index =
          Nat.card (Z i) * (NZ i).index := by
      dsimp only [term]
      calc
        (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
            (Nat.card (Z i) - 1 + 1) * (NZ i).index := by ring
        _ = Nat.card (Z i) * (NZ i).index := by
          rw [Nat.sub_add_cancel (hnontrivial i).le]
    have hterm_bound (i : Fin r) :
        Nat.card H ≤ 4 * term i := by
      have hzbound :
          Nat.card (Z i) * s i ≤ 4 * (Nat.card (Z i) - 1) := by
        calc
          Nat.card (Z i) * s i ≤ Nat.card (Z i) * 2 :=
            Nat.mul_le_mul_left (Nat.card (Z i)) (hs i).2
          _ ≤ (2 * (Nat.card (Z i) - 1)) * 2 :=
            Nat.mul_le_mul_right 2 (by
              have hzi := hnontrivial i
              omega)
          _ = 4 * (Nat.card (Z i) - 1) := by ring
      calc
        Nat.card H = (Nat.card (Z i) * s i) * (NZ i).index :=
          (hz_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * term i := by simp only [term]; ring
    have hfamily_bound : r ≤ 3 := by
      let T := ∑ i, term i
      have hrs : r * Nat.card H ≤ 4 * T := by
        calc
          r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
          _ ≤ Finset.univ.sum fun i : Fin r => 4 * term i :=
            Finset.sum_le_sum fun i _hi => hterm_bound i
          _ = 4 * T := by simp [T, Finset.mul_sum]
      have hTlt : T < Nat.card H := by
        have hcount : Nat.card H =
            1 + (p ^ m - 1) * NP.index + T := by
          simpa only [T] using hpartition_count
        omega
      have hcancel : r * Nat.card H < 4 * Nat.card H :=
        hrs.trans_lt ((Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hTlt)
      have hrlt : r < 4 :=
        (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
      omega
    have hpm_gt : 1 < p ^ m := by
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero,
          fun h => hP_nontrivial (hPm.trans h)⟩
    obtain ⟨i0, hNPcard⟩ :
        ∃ i, Nat.card NP = p ^ m * Nat.card (Z i) := by
      rcases hnormalizerP hpm_gt with hsmall | hlarge
      · exfalso
        have hPN : (P : Subgroup H) = NP := by
          apply Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer
          have hsmall' : Nat.card NP = p ^ m := by
            simpa only [NP] using hsmall
          have hcard_ge : Nat.card NP ≤ Nat.card (P : Subgroup H) := by
            rw [hsmall', hPm]
          exact hcard_ge
        exact hnormalizer (by simpa [NP] using hPN.symm)
      · exact hlarge
    have hNP_index_factor :
        (p ^ m * Nat.card (Z i0)) * NP.index = Nat.card H := by
      calc
        (p ^ m * Nat.card (Z i0)) * NP.index =
            Nat.card NP * NP.index := by rw [hNPcard]
        _ = Nat.card H := NP.card_mul_index
    have hpre_shape :
        Nat.card H = Nat.card NP ∨ (r = 2 ∧ ∀ i, s i = 2) :=
      _root_.Glauberman.Dickson.h826_cyclic_family_shape
      (p ^ m) r NP Z NZ s term i0 hpm_gt hfamily_bound hnontrivial hs
      hpartition_count hz_index_factor hterm_factor hterm_bound hNP_index_factor
    rcases hpre_shape with hnormal | ⟨hr, hs_two⟩
    · exact Or.inl (by simpa [NP] using hnormal)
    · subst r
      have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hPm]
        exact hpm_gt
      let PN : Subgroup NP := (P : Subgroup H).subgroupOf NP
      let : PN.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (by
          simp [NP])
      obtain ⟨hquotient_cyclic, hquotient_card_dvd,
          hNormalizer_fixedPointFree, U, T, conjH, hconjH_injective,
          hconjH_conj,
          hU_commutative, hT_cyclic, hTcard, hT_fixedPointFree,
          hP_map_conjH_le_U, hB_le_normalizer, hB_conjugate_torus,
          hNP_maps_B, hU_preimage, unipotent, splitTorus,
          h_unipotent_injective, hU_range, hT_range, hsplit_conj,
          hunipotent_matrix, hsplitTorus_matrix⟩ :=
        h821_borel_quotient_data hFcard H P hP_ne_bot NP rfl PN rfl
      have hi0_divisors :
          Nat.card (Z i0) ∣ p ^ m - 1 ∧
          Nat.card (Z i0) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
        have hquotient_card_dvd_sub_one :
            Nat.card (NP ⧸ PN) ∣ Nat.card F - 1 :=
          dvd_trans hquotient_card_dvd
            (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
        have hf_ne_zero : f ≠ 0 :=
          huppert_II_8_27_field_exponent_ne_zero hFcard
        have hp_dvd_cardF : p ∣ Nat.card F := by
          rw [hFcard]
          exact dvd_pow_self p hf_ne_zero
        have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
          intro hp_sub
          have hp_one : p ∣ 1 := by
            have hd := Nat.dvd_sub hp_dvd_cardF hp_sub
            have hsub : Nat.card F - (Nat.card F - 1) = 1 := by
              have hcard_pos : 0 < Nat.card F := Nat.card_pos
              omega
            rwa [hsub] at hd
          exact (Fact.out : p.Prime).not_dvd_one hp_one
        have hcop_p_quotient : Nat.Coprime p (Nat.card (NP ⧸ PN)) :=
          Nat.Coprime.of_dvd_right hquotient_card_dvd_sub_one
            ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
              hp_not_dvd_cardF_sub_one)
        have hPNcard : Nat.card PN = p ^ m := by
          calc
            Nat.card PN = Nat.card P :=
              Nat.card_congr
                (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
            _ = p ^ m := hPm
        have hPNindex : PN.index = Nat.card (NP ⧸ PN) := rfl
        have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
          rw [hPNcard, hPNindex]
          exact hcop_p_quotient.pow_left m
        obtain ⟨C, hcomp⟩ :=
          Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
        have hCcard : Nat.card C = Nat.card (Z i0) := by
          have hmul := hcomp.card_mul_card
          rw [hPNcard, hNPcard] at hmul
          exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hpm_gt) hmul
        let : MulDistribMulAction C PN :=
          MulDistribMulAction.compHom PN
            ((MulAut.conjNormal (H := PN)).comp C.subtype)
        have hfree :
            ∀ c : C, c ≠ 1 → ∀ x : PN, c • x = x → x = 1 := by
          intro c hc x hfix
          by_contra hx
          have hc_not_PN : (c : NP) ∉ PN := by
            intro hcPN
            have hc_one : (c : NP) = 1 :=
              Subgroup.disjoint_def.mp hcomp.disjoint hcPN c.property
            apply hc
            apply Subtype.ext
            exact hc_one
          have hx_mem_P : ((x : NP) : H) ∈ (P : Subgroup H) := by
            have hx_mem := x.property
            change ((x : NP) : H) ∈ (P : Subgroup H) at hx_mem
            exact hx_mem
          let xP : P := ⟨((x : NP) : H), hx_mem_P⟩
          have hxP_ne : xP ≠ 1 := by
            intro hxP
            apply hx
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun y : P => (y : H)) hxP
          have hfixNP := congrArg Subtype.val hfix
          change (c : NP) * (x : NP) * (c : NP)⁻¹ = (x : NP) at hfixNP
          have hfixH := congrArg Subtype.val hfixNP
          exact (hNormalizer_fixedPointFree (c : NP) hc_not_PN xP hxP_ne hfixH).elim
        have hCdiv : Nat.card C ∣ p ^ m - 1 := by
          have hdiv := h826_card_actor_dvd_group_card_sub_one hfree
          rwa [hPNcard] at hdiv
        have hCquotient : Nat.card C = Nat.card (NP ⧸ PN) := by
          calc
            Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
            _ = Nat.card (NP ⧸ PN) := rfl
        constructor
        · rwa [← hCcard]
        · rw [← hCcard, hCquotient]
          exact hquotient_card_dvd
      have hi0_dvd_sub_one := hi0_divisors.1
      have hi0_dvd_ambient := hi0_divisors.2
      let i1 : Fin 2 := if i0 = 0 then 1 else 0
      have hi1_ne_i0 : i1 ≠ i0 := by
        fin_cases i0 <;> simp [i1]
      have hi0_ne_i1 : i0 ≠ i1 := Ne.symm hi1_ne_i0
      have huniv_pair : ({i0, i1} : Finset (Fin 2)) = Finset.univ := by
        ext j
        fin_cases i0 <;> fin_cases j <;> simp [i1]
      have htorus_inf_eq_bot (i j : Fin 2) (g : H)
          (hne : Z i ≠ (Z j).map (MulAut.conj g).toMonoidHom) :
          Z i ⊓ (Z j).map (MulAut.conj g).toMonoidHom = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        by_cases hx_one : x = 1
        · simp [hx_one]
        · exfalso
          obtain ⟨A, hxA, hAunique⟩ :=
            huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
              hcoprime hmaximal hrepresentative hdistinct x hx_one
          let Ai : (Sylow p H) ⊕
              (Σ k : Fin 2, {W : Subgroup H // ∃ a : H,
                W = (Z k).map (MulAut.conj a).toMonoidHom}) :=
            Sum.inr ⟨i, ⟨Z i, ⟨1, by ext y; simp⟩⟩⟩
          let Aj : (Sylow p H) ⊕
              (Σ k : Fin 2, {W : Subgroup H // ∃ a : H,
                W = (Z k).map (MulAut.conj a).toMonoidHom}) :=
            Sum.inr ⟨j, ⟨(Z j).map (MulAut.conj g).toMonoidHom, ⟨g, rfl⟩⟩⟩
          have hxAi : x ∈ match Ai with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H) := by
            simpa [Ai] using hx.1
          have hxAj : x ∈ match Aj with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H) := by
            simpa [Aj] using hx.2
          have hAiAj : Ai = Aj :=
            (hAunique Ai hxAi).trans (hAunique Aj hxAj).symm
          have hcarrier := congrArg
            (fun B => match B with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H)) hAiAj
          exact hne (by simpa [Ai, Aj] using hcarrier)
      let : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
      let X := MulAction.orbit H (Z i0)
      let base : X := ⟨Z i0, MulAction.mem_orbit_self (Z i0)⟩
      let : Nonempty X := ⟨base⟩
      have hbase_fixed (a : Z i0) : a • base = base := by
        apply Subtype.ext
        change MulAut.conj (a : H) • Z i0 = Z i0
        exact Subgroup.conj_smul_eq_self_of_mem a.property
      let X0 : SubMulAction (Z i0) X :=
        { carrier := {W | W ≠ base}
          smul_mem' := by
            intro a W hW haW
            apply hW
            calc
              W = a⁻¹ • (a • W) := (inv_smul_smul a W).symm
              _ = a⁻¹ • base := congrArg (fun Y : X => a⁻¹ • Y) haW
              _ = base := hbase_fixed a⁻¹ }
      have hstab_normalizer (W : Subgroup H) :
          MulAction.stabilizer H W =
            Subgroup.normalizer (W : Set H) := by
        ext g
        change g • W = W ↔ g ∈ Subgroup.normalizer (W : Set H)
        rw [eq_comm, SetLike.ext_iff,
          ← inv_mem_iff (G := H) (H := Subgroup.normalizer W),
          Subgroup.mem_normalizer_iff, inv_inv]
        exact
          forall_congr' fun h =>
            iff_congr Iff.rfl
              ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
                fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
                  MulAut.apply_inv_self H (MulAut.conj g) h⟩⟩
      have horbit_normalizer_card (W : X) :
          Nat.card (Subgroup.normalizer ((W : Subgroup H) : Set H)) =
            2 * Nat.card (W : Subgroup H) := by
        rcases W.property with ⟨g, hg⟩
        have hgmap :
            (W : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change (W : Subgroup H) = g • Z i0
          exact hg.symm
        calc
          Nat.card (Subgroup.normalizer ((W : Subgroup H) : Set H)) =
              Nat.card (Subgroup.normalizer (Z i0 : Set H)) := by
            rw [hgmap, ← Subgroup.map_equiv_normalizer_eq,
              Subgroup.card_map_of_injective (MulAut.conj g).injective]
          _ = Nat.card (Z i0) * 2 := by rw [hnormalizerZ i0, hs_two i0]
          _ = 2 * Nat.card (W : Subgroup H) := by
            rw [hgmap,
              Subgroup.card_map_of_injective (MulAut.conj g).injective]
            ring
      have hrestricted_stabilizer_card_le_two
          (A : Subgroup H) (W : X)
          (hAW : A ⊓ (W : Subgroup H) = ⊥) :
          Nat.card (MulAction.stabilizer A W) ≤ 2 := by
        let B : Subgroup H :=
          A ⊓ Subgroup.normalizer (((W : Subgroup H)) : Set H)
        have hWB :
            (W : Subgroup H) ⊓ B = ⊥ := by
          calc
            (W : Subgroup H) ⊓ B =
                (A ⊓ (W : Subgroup H)) ⊓
                  Subgroup.normalizer (((W : Subgroup H)) : Set H) := by
              dsimp only [B]
              ac_rfl
            _ = ⊥ := by simp [hAW]
        have hWindex :
            (W : Subgroup H).relIndex
                (Subgroup.normalizer (((W : Subgroup H)) : Set H)) = 2 :=
          relIndex_eq_two_of_card_eq_two_mul
            (W : Subgroup H)
            (Subgroup.normalizer (((W : Subgroup H)) : Set H))
            Subgroup.le_normalizer (horbit_normalizer_card W)
        have hBrel : (⊥ : Subgroup H).relIndex B ≤ 2 :=
          relIndex_le_two_of_inter_eq
            (W : Subgroup H) B
            (Subgroup.normalizer (((W : Subgroup H)) : Set H)) ⊥
            inf_le_right hWB hWindex
        have hBcard : Nat.card B ≤ 2 := by
          simpa only [Subgroup.relIndex_bot_left] using hBrel
        have hstab_eq :
            MulAction.stabilizer A W =
              (Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A := by
          ext a
          rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
          constructor
          · intro ha
            have haval := congrArg Subtype.val ha
            change (a : H) • (W : Subgroup H) = (W : Subgroup H) at haval
            have hamem :
                (a : H) ∈ MulAction.stabilizer H (W : Subgroup H) := by
              simpa [MulAction.mem_stabilizer_iff] using haval
            rwa [hstab_normalizer] at hamem
          · intro ha
            apply Subtype.ext
            change (a : H) • (W : Subgroup H) = (W : Subgroup H)
            have hamem :
                (a : H) ∈ MulAction.stabilizer H (W : Subgroup H) := by
              rwa [hstab_normalizer]
            simpa [MulAction.mem_stabilizer_iff] using hamem
        rw [hstab_eq]
        calc
          Nat.card
                ((Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A) =
              Nat.card
                (((Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A).map
                  A.subtype) :=
            (Subgroup.card_map_of_injective A.subtype_injective).symm
          _ = Nat.card
                ↥((Subgroup.normalizer (((W : Subgroup H)) : Set H) : Subgroup H) ⊓ A) := by
            rw [Subgroup.subgroupOf_map_subtype]
          _ = Nat.card B := by
            apply congrArg (fun K : Subgroup H => Nat.card K)
            dsimp only [B]
            exact inf_comm _ _
          _ ≤ 2 := hBcard
      have hstab_X0 (W : X0) :
          Nat.card (MulAction.stabilizer (Z i0) W) ≤ 2 := by
        have hW_ne : (W : X) ≠ base := W.property
        rcases (W : X).property with ⟨g, hg⟩
        have hgmap :
            ((W : X) : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change ((W : X) : Subgroup H) = g • Z i0
          exact hg.symm
        have hinter :
            Z i0 ⊓ ((W : X) : Subgroup H) = ⊥ := by
          rw [hgmap]
          apply htorus_inf_eq_bot
          intro heq
          apply hW_ne
          apply Subtype.ext
          exact (heq.trans hgmap.symm).symm
        have hle :=
          hrestricted_stabilizer_card_le_two (Z i0) (W : X) hinter
        have hstab_eq :
            MulAction.stabilizer (Z i0) W =
              MulAction.stabilizer (Z i0) (W : X) := by
          ext a
          simp only [MulAction.mem_stabilizer_iff]
          constructor
          · exact fun h => congrArg Subtype.val h
          · exact fun h => Subtype.ext h
        rwa [hstab_eq]
      have hi0_dvd_orbit_punctured :
          Nat.card (Z i0) ∣ 2 * Nat.card X0 :=
        h826_card_actor_dvd_two_mul_card hstab_X0
      have hX0card : Nat.card X0 = Nat.card X - 1 := by
        change Nat.card {W : X // W ≠ base} = Nat.card X - 1
        let : Fintype X := Fintype.ofFinite X
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp
      have hi0_dvd_orbit :
          Nat.card (Z i0) ∣ 2 * (Nat.card X - 1) := by
        rwa [hX0card] at hi0_dvd_orbit_punctured
      have hstab_i1 (W : X) :
          Nat.card (MulAction.stabilizer (Z i1) W) ≤ 2 := by
        rcases W.property with ⟨g, hg⟩
        have hgmap :
            (W : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change (W : Subgroup H) = g • Z i0
          exact hg.symm
        have hne : Z i1 ≠
            (Z i0).map (MulAut.conj g).toMonoidHom := by
          intro heq
          apply hi0_ne_i1
          exact hdistinct i0 i1 g heq.symm
        have hinter : Z i1 ⊓ (W : Subgroup H) = ⊥ := by
          rw [hgmap]
          exact htorus_inf_eq_bot i1 i0 g hne
        exact hrestricted_stabilizer_card_le_two (Z i1) W hinter
      have hi1_dvd_orbit :
          Nat.card (Z i1) ∣ 2 * Nat.card X :=
        h826_card_actor_dvd_two_mul_card hstab_i1
      have htorus_gcd :
          Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣ 2 := by
        have hleft :
            Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣
              2 * (Nat.card X - 1) :=
          dvd_trans (Nat.gcd_dvd_left _ _) hi0_dvd_orbit
        have hright :
            Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣
              2 * Nat.card X :=
          dvd_trans (Nat.gcd_dvd_right _ _) hi1_dvd_orbit
        have hsub := Nat.dvd_sub hright hleft
        have hXpos : 0 < Nat.card X := Nat.card_pos
        have hdiff : 2 * Nat.card X - 2 * (Nat.card X - 1) = 2 := by
          omega
        rwa [hdiff] at hsub
      let c := Nat.lcm (p ^ m * Nat.card (Z i0))
        (Nat.lcm (2 * Nat.card (Z i0)) (2 * Nat.card (Z i1)))
      have hi0_factor :
          (2 * Nat.card (Z i0)) * (NZ i0).index = Nat.card H := by
        calc
          (2 * Nat.card (Z i0)) * (NZ i0).index =
              (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
          _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by
            rw [hs_two i0]
          _ = Nat.card H := hz_index_factor i0
      have hi1_factor :
          (2 * Nat.card (Z i1)) * (NZ i1).index = Nat.card H := by
        calc
          (2 * Nat.card (Z i1)) * (NZ i1).index =
              (Nat.card (Z i1) * 2) * (NZ i1).index := by ring
          _ = (Nat.card (Z i1) * s i1) * (NZ i1).index := by
            rw [hs_two i1]
          _ = Nat.card H := hz_index_factor i1
      have hqa_dvd_c : p ^ m * Nat.card (Z i0) ∣ c := by
        exact Nat.dvd_lcm_left _ _
      have h2a_dvd_c : 2 * Nat.card (Z i0) ∣ c := by
        exact dvd_trans (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_right _ _)
      have h2b_dvd_c : 2 * Nat.card (Z i1) ∣ c := by
        exact dvd_trans (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _)
      have hc_dvd_H : c ∣ Nat.card H := by
        apply Nat.lcm_dvd
        · exact ⟨NP.index, hNP_index_factor.symm⟩
        · apply Nat.lcm_dvd
          · exact ⟨(NZ i0).index, hi0_factor.symm⟩
          · exact ⟨(NZ i1).index, hi1_factor.symm⟩
      have hquotient_dvd_NP : Nat.card H / c ∣ NP.index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H hqa_dvd_c
        have hindex : NP.index =
            Nat.card H / (p ^ m * Nat.card (Z i0)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
              (Nat.card_pos (α := Z i0)))) hNP_index_factor
        rwa [← hindex] at hdiv
      have hquotient_dvd_NZi0 : Nat.card H / c ∣ (NZ i0).index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H h2a_dvd_c
        have hindex : (NZ i0).index =
            Nat.card H / (2 * Nat.card (Z i0)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (by norm_num)
              (Nat.card_pos (α := Z i0)))) hi0_factor
        rwa [← hindex] at hdiv
      have hquotient_dvd_NZi1 : Nat.card H / c ∣ (NZ i1).index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H h2b_dvd_c
        have hindex : (NZ i1).index =
            Nat.card H / (2 * Nat.card (Z i1)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (by norm_num)
              (Nat.card_pos (α := Z i1)))) hi1_factor
        rwa [← hindex] at hdiv
      have hsum_pair :
          (∑ i, term i) = term i0 + term i1 := by
        rw [← huniv_pair]
        simp [hi0_ne_i1]
      have hcount_pair : Nat.card H =
          1 + (p ^ m - 1) * NP.index +
            (Nat.card (Z i0) - 1) * (NZ i0).index +
            (Nat.card (Z i1) - 1) * (NZ i1).index := by
        rw [hpartition_count, hsum_pair]
        simp only [term]
        ring
      have hquotient_dvd_tail : Nat.card H / c ∣
          (p ^ m - 1) * NP.index +
            (Nat.card (Z i0) - 1) * (NZ i0).index +
            (Nat.card (Z i1) - 1) * (NZ i1).index := by
        exact Nat.dvd_add
          (Nat.dvd_add
            (dvd_mul_of_dvd_right hquotient_dvd_NP _)
            (dvd_mul_of_dvd_right hquotient_dvd_NZi0 _))
          (dvd_mul_of_dvd_right hquotient_dvd_NZi1 _)
      have hquotient_dvd_H : Nat.card H / c ∣ Nat.card H :=
        Nat.div_dvd_of_dvd hc_dvd_H
      have hquotient_dvd_one : Nat.card H / c ∣ 1 := by
        have hsub := Nat.dvd_sub hquotient_dvd_H hquotient_dvd_tail
        have htail_eq : Nat.card H -
            ((p ^ m - 1) * NP.index +
              (Nat.card (Z i0) - 1) * (NZ i0).index +
              (Nat.card (Z i1) - 1) * (NZ i1).index) = 1 := by
          omega
        rwa [htail_eq] at hsub
      have hquotient_one : Nat.card H / c = 1 :=
        Nat.eq_one_of_dvd_one hquotient_dvd_one
      have hH_eq_c : Nat.card H = c := by
        have hmul := Nat.div_mul_cancel hc_dvd_H
        rw [hquotient_one, one_mul] at hmul
        exact hmul.symm
      have hPNcard : Nat.card PN = p ^ m := by
        calc
          Nat.card PN = Nat.card P :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
          _ = p ^ m := hPm
      have hPNindex : PN.index = Nat.card (Z i0) := by
        have hmul := PN.card_mul_index
        rw [hPNcard, hNPcard] at hmul
        exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hpm_gt) hmul
      have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
        rw [hPNcard, hPNindex]
        exact (hcoprime i0).pow_left m
      obtain ⟨C, hcomp⟩ :=
        Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
      have hCcyclic : IsCyclic C := by
        let eC : NP ⧸ PN ≃* C := hcomp.symm.QuotientMulEquiv
        let : IsCyclic (NP ⧸ PN) := hquotient_cyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      have hCcard : Nat.card C = Nat.card (Z i0) := by
        calc
          Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
          _ = Nat.card (Z i0) := hPNindex
      let : IsCyclic C := hCcyclic
      obtain ⟨cgen, hcgen⟩ := IsCyclic.exists_generator (α := C)
      have hcgen_ne_one : cgen ≠ 1 := by
        intro hc
        have hsub : Subsingleton C := by
          constructor
          intro x y
          rcases hcgen x with ⟨i, hi⟩
          rcases hcgen y with ⟨j, hj⟩
          rw [hc] at hi hj
          simp only [one_zpow] at hi hj
          exact hi.symm.trans hj
        have hcard_one : Nat.card C = 1 := Nat.card_eq_one_iff_unique.mpr
          ⟨hsub, ⟨1⟩⟩
        rw [hCcard] at hcard_one
        exact (hnontrivial i0).ne hcard_one.symm
      let cN : NP := (cgen : C)
      have hcN_not_PN : cN ∉ PN := by
        intro hcPN
        have hcC : cN ∈ C := cgen.property
        have hc_one : cN = 1 :=
          Subgroup.disjoint_def.mp hcomp.disjoint hcPN hcC
        exact hcgen_ne_one (Subtype.ext hc_one)
      have hcN_not_U : conjH (cN : H) ∉ U := by
        intro hcU
        exact hcN_not_PN ((hU_preimage cN).mp hcU)
      obtain ⟨u, huU, hc_torus⟩ :=
        hB_conjugate_torus (conjH (cN : H))
          (hNP_maps_B cN) hcN_not_U
      rcases hc_torus with ⟨t, htT, ht⟩
      change u * t * u⁻¹ = conjH (cN : H) at ht
      let conjH' : H →* PSL2MatrixGroup F :=
        (MulAut.conj u⁻¹).toMonoidHom.comp conjH
      have hconjH'_injective : Function.Injective conjH' :=
        (MulAut.conj u⁻¹).injective.comp hconjH_injective
      have hP_map_conjH'_le_U : (P : Subgroup H).map conjH' ≤ U := by
        rintro y ⟨x, hxP, rfl⟩
        change u⁻¹ * conjH x * (u⁻¹)⁻¹ ∈ U
        exact U.mul_mem
          (U.mul_mem (U.inv_mem huU)
            (hP_map_conjH_le_U (Subgroup.mem_map_of_mem conjH hxP)))
          (by simpa using huU)
      have hcgen_image : conjH' (cN : H) = t := by
        dsimp only [conjH']
        change u⁻¹ * conjH (cN : H) * (u⁻¹)⁻¹ = t
        rw [← ht]
        group
      rw [hT_range] at htT
      rcases htT with ⟨r, hr⟩
      have hcgen_split : conjH' (cN : H) = splitTorus r := by
        rw [hcgen_image, hr]
      let P0 : Subgroup (PSL2MatrixGroup F) :=
        (P : Subgroup H).map conjH'
      let W : AddSubgroup F :=
        { carrier := {x | unipotent x ∈ P0}
          zero_mem' := by
            change unipotent 0 ∈ P0
            simp
          add_mem' := by
            intro x y hx hy
            change unipotent (x + y) ∈ P0
            rw [unipotent.map_add_eq_mul]
            exact P0.mul_mem hx hy
          neg_mem' := by
            intro x hx
            change unipotent (-x) ∈ P0
            rw [unipotent.map_neg_eq_inv]
            exact P0.inv_mem hx }
      have hWcard : Nat.card W = p ^ m := by
        let eW : W ≃ P0 := Equiv.ofBijective
          (fun x : W => (⟨unipotent (x : F), x.property⟩ : P0)) (by
            constructor
            · intro x y hxy
              apply Subtype.ext
              apply h_unipotent_injective
              exact congrArg Subtype.val hxy
            · intro y
              have hyU : (y : PSL2MatrixGroup F) ∈ U := by
                apply hP_map_conjH'_le_U
                exact y.property
              rw [hU_range] at hyU
              rcases hyU with ⟨x, hx⟩
              refine ⟨⟨x, ?_⟩, ?_⟩
              · change unipotent.toMonoidHom x ∈ P0
                rw [hx]
                exact y.property
              · apply Subtype.ext
                exact hx)
        calc
          Nat.card W = Nat.card P0 := Nat.card_congr eW
          _ = Nat.card P :=
            Subgroup.card_map_of_injective hconjH'_injective
          _ = p ^ m := hPm
      have hW_ne_bot : W ≠ ⊥ := by
        rw [← AddSubgroup.one_lt_card_iff_ne_bot, hWcard]
        exact hpm_gt
      obtain ⟨x0, hx0_ne_zero⟩ :=
        AddSubgroup.ne_bot_iff_exists_ne_zero.mp hW_ne_bot
      have hx0_val_ne_zero : (x0 : F) ≠ 0 := by
        intro hx
        exact hx0_ne_zero (Subtype.ext hx)
      have hx0_unipotent_ne_one : unipotent (x0 : F) ≠ 1 := by
        intro hx
        have hxzero := h_unipotent_injective
          (hx.trans unipotent.map_zero_eq_one.symm)
        exact hx0_ne_zero (Subtype.ext hxzero)
      have hlambda_mem_W :
          ∀ x : F, x ∈ W → (r : F) ^ 2 * x ∈ W := by
        intro x hxW
        change unipotent ((r : F) ^ 2 * x) ∈ P0
        rw [← hsplit_conj]
        rcases hxW with ⟨y, hyP, hy⟩
        have hc_normalizes :
            (cN : H) ∈ Subgroup.normalizer (P : Set H) := cN.property
        have hcyP :
            (cN : H) * y * (cN : H)⁻¹ ∈ (P : Subgroup H) :=
          (Subgroup.mem_normalizer_iff.mp hc_normalizes y).mp hyP
        refine ⟨(cN : H) * y * (cN : H)⁻¹, hcyP, ?_⟩
        rw [map_mul, map_mul, map_inv, hcgen_split, hy]
      let K : Subfield F := h826_scalarStabilizer W
      have hlambda_mem_K : (r : F) ^ 2 ∈ K := hlambda_mem_W
      have hK_le_W_card : Nat.card K ≤ Nat.card W := by
        let φ : K → W := fun a =>
          ⟨(a : F) * (x0 : F), a.property (x0 : F) x0.property⟩
        have hφinj : Function.Injective φ := by
          intro a b hab
          apply Subtype.ext
          have hval := congrArg Subtype.val hab
          exact mul_right_cancel₀ hx0_val_ne_zero hval
        exact Nat.card_le_card_of_injective φ hφinj
      have hK_le_q : Nat.card K ≤ p ^ m := by
        rw [← hWcard]
        exact hK_le_W_card
      have hcgen_order : orderOf cgen = Nat.card C :=
        orderOf_eq_card_of_forall_mem_zpowers hcgen
      have hsplit_order :
          orderOf (splitTorus r) = Nat.card (Z i0) := by
        calc
          orderOf (splitTorus r) = orderOf (conjH' (cN : H)) := by
            rw [hcgen_split]
          _ = orderOf (cN : H) :=
            orderOf_injective conjH' hconjH'_injective (cN : H)
          _ = orderOf cN := Subgroup.orderOf_coe cN
          _ = orderOf cgen := Subgroup.orderOf_coe cgen
          _ = Nat.card C := hcgen_order
          _ = Nat.card (Z i0) := hCcard
      let lambdaU : Fˣ := r ^ 2
      have hsplit_pow_fixed (j : ℕ) :
          (splitTorus r) ^ j * unipotent (x0 : F) *
              ((splitTorus r) ^ j)⁻¹ =
            unipotent ((lambdaU ^ j : Fˣ) * (x0 : F)) := by
        calc
          (splitTorus r) ^ j * unipotent (x0 : F) *
                ((splitTorus r) ^ j)⁻¹ =
              splitTorus (r ^ j) * unipotent (x0 : F) *
                (splitTorus (r ^ j))⁻¹ := by rw [map_pow]
          _ = unipotent (((r ^ j : Fˣ) : F) ^ 2 * (x0 : F)) :=
            hsplit_conj (r ^ j) (x0 : F)
          _ = unipotent ((lambdaU ^ j : Fˣ) * (x0 : F)) := by
            congr 2
            simp only [lambdaU, Units.val_pow_eq_pow_val]
            ring
      have hlambda_pow_of_split_pow {j : ℕ}
          (hj : (splitTorus r) ^ j = 1) :
          lambdaU ^ j = 1 := by
        have hfix := hsplit_pow_fixed j
        rw [hj] at hfix
        simp only [one_mul, mul_one, inv_one] at hfix
        have hcoord :
            (x0 : F) = (lambdaU ^ j : Fˣ) * (x0 : F) :=
          h_unipotent_injective hfix
        apply Units.ext
        apply mul_right_cancel₀ hx0_val_ne_zero
        simpa using hcoord.symm
      have hsplit_pow_of_lambda_pow {j : ℕ}
          (hj : lambdaU ^ j = 1) :
          (splitTorus r) ^ j = 1 := by
        have hfix := hsplit_pow_fixed j
        rw [hj] at hfix
        simp only [Units.val_one, one_mul] at hfix
        have hsplit_mem : splitTorus r ∈ T := by
          rw [hT_range]
          exact ⟨r, rfl⟩
        rcases hT_fixedPointFree
            ((splitTorus r) ^ j) (T.pow_mem hsplit_mem j)
            (unipotent (x0 : F))
            (hP_map_conjH'_le_U x0.property) hfix with ht | hx
        · exact ht
        · exact (hx0_unipotent_ne_one hx).elim
      have hlambda_order :
          orderOf lambdaU = Nat.card (Z i0) := by
        apply Nat.dvd_antisymm
        · apply orderOf_dvd_of_pow_eq_one
          apply hlambda_pow_of_split_pow
          rw [← hsplit_order]
          exact pow_orderOf_eq_one (splitTorus r)
        · rw [← hsplit_order]
          apply orderOf_dvd_of_pow_eq_one
          apply hsplit_pow_of_lambda_pow
          exact pow_orderOf_eq_one lambdaU
      let lambdaK0 : K := ⟨(lambdaU : F), hlambda_mem_K⟩
      have hlambdaK0_ne_zero : lambdaK0 ≠ 0 := by
        intro hzero
        have hval := congrArg Subtype.val hzero
        exact Units.ne_zero lambdaU hval
      let lambdaK : Kˣ := Units.mk0 lambdaK0 hlambdaK0_ne_zero
      let inclUnits : Kˣ →* Fˣ :=
        Units.map (K.subtype : K →+* F)
      have hinclUnits_injective : Function.Injective inclUnits :=
        Units.map_injective K.subtype_injective
      have hlambda_map :
          inclUnits lambdaK = lambdaU := by
        apply Units.ext
        rfl
      have hlambdaK_order :
          orderOf lambdaK = Nat.card (Z i0) := by
        calc
          orderOf lambdaK = orderOf (inclUnits lambdaK) :=
            (orderOf_injective inclUnits hinclUnits_injective lambdaK).symm
          _ = orderOf lambdaU := congrArg orderOf hlambda_map
          _ = Nat.card (Z i0) := hlambda_order
      have hKunits_card : Nat.card Kˣ = Nat.card K - 1 := by
        let : Fintype K := Fintype.ofFinite K
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
      have hCcard_dvd_K_sub_one : Nat.card (Z i0) ∣ Nat.card K - 1 := by
        rw [← hKunits_card, ← hlambdaK_order]
        exact orderOf_dvd_natCard lambdaK
      have hK_lower : Nat.card (Z i0) + 1 ≤ Nat.card K := by
        have hKcard_gt : 1 < Nat.card K := Finite.one_lt_card
        have hle := Nat.le_of_dvd (by omega) hCcard_dvd_K_sub_one
        calc
          Nat.card (Z i0) + 1 ≤ (Nat.card K - 1) + 1 :=
            Nat.add_le_add_right hle 1
          _ = Nat.card K := Nat.sub_add_cancel hKcard_gt.le
      let Point := ℙ F (Fin 2 → F)
      let inf : Point :=
        Projectivization.mk F ![(1 : F), 0] (by simp)
      let zero : Point :=
        Projectivization.mk F ![(0 : F), 1] (by simp)
      let affine (x : F) : Point :=
        Projectivization.mk F ![x, 1] (by simp)
      obtain ⟨rho, hrho, hrho_apply, _hrho_two_transitive⟩ :=
        huppert_II_6_11_projective_action (K := F) 2 (by omega)
      let : MulAction (PSL2MatrixGroup F) Point :=
        MulAction.compHom Point rho
      have hunipotent_fixes_inf (x : F) :
          unipotent x • inf = inf := by
        rw [hunipotent_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) inf = inf
        rw [hrho_apply]
        dsimp only [inf]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨1, ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct]
      have hsplit_fixes_inf (a : Fˣ) :
          splitTorus a • inf = inf := by
        rw [hsplitTorus_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) inf = inf
        rw [hrho_apply]
        dsimp only [inf]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨(a : F), ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct]
      have hsplit_fixes_zero (a : Fˣ) :
          splitTorus a • zero = zero := by
        rw [hsplitTorus_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) zero = zero
        rw [hrho_apply]
        dsimp only [zero]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨(a⁻¹ : F), ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct]
      have hunipotent_affine (w x : F) :
          unipotent w • affine x = affine (x + w) := by
        rw [hunipotent_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) (affine x) =
          affine (x + w)
        rw [hrho_apply]
        dsimp only [affine]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨1, ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, add_comm]
      have hunipotent_fixed_eq_inf
          (w : F) (hw : w ≠ 0) (z : Point)
          (hfix : unipotent w • z = z) :
          z = inf := by
        rw [← Projectivization.mk_rep z] at hfix
        rw [hunipotent_matrix] at hfix
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F))
              (Projectivization.mk F z.rep z.rep_nonzero) =
            Projectivization.mk F z.rep z.rep_nonzero at hfix
        rw [hrho_apply, Projectivization.smul_mk] at hfix
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
          ⟨a, ha⟩
        have h0 := congrFun ha (0 : Fin 2)
        have h1 := congrFun ha (1 : Fin 2)
        simp [Matrix.mulVec, dotProduct] at h0 h1
        by_cases hz1 : z.rep 1 = 0
        · rw [← Projectivization.mk_rep z]
          dsimp only [inf]
          apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
          refine ⟨z.rep 0, ?_⟩
          ext i
          fin_cases i
          · simp
          · simp [hz1]
        · have ha_one : a = 1 := by
            apply mul_right_cancel₀ hz1
            simpa using h1
          rw [ha_one, one_mul] at h0
          have hprod : w * z.rep 1 = 0 := by
            linear_combination -h0
          exact (mul_ne_zero hw hz1 hprod).elim
      have hB_fixes_inf :
          U ⊔ T ≤ MulAction.stabilizer (PSL2MatrixGroup F) inf := by
        apply sup_le
        · intro g hg
          rw [MulAction.mem_stabilizer_iff]
          rw [hU_range] at hg
          rcases hg with ⟨x, rfl⟩
          exact hunipotent_fixes_inf x
        · intro g hg
          rw [MulAction.mem_stabilizer_iff]
          rw [hT_range] at hg
          rcases hg with ⟨a, rfl⟩
          exact hsplit_fixes_inf a
      have hfix_inf_mem_B
          (g : PSL2MatrixGroup F) (hfix : g • inf = inf) :
          g ∈ U ⊔ T := by
        refine QuotientGroup.induction_on g ?_ hfix
        intro A hAfix
        have hA10 :
            (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          change rho
              (QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) A) inf = inf at hAfix
          rw [hrho_apply] at hAfix
          dsimp only [inf] at hAfix
          rw [Projectivization.smul_mk] at hAfix
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hAfix with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simpa [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct] using h1.symm
        have hdet :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
          have h := A.property
          rw [Matrix.det_fin_two, hA10, mul_zero, sub_zero] at h
          exact h
        have ha_zero :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
          left_ne_zero_of_mul_eq_one hdet
        let aU : Fˣ :=
          Units.mk0 ((A : Matrix (Fin 2) (Fin 2) F) 0 0) ha_zero
        have hd_inv :
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (aU⁻¹ : F) := by
          simpa [aU] using eq_inv_of_mul_eq_one_right hdet
        let Bsl : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![1,
              (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                (A : Matrix (Fin 2) (Fin 2) F) 0 0;
              0, 1], by simp [Matrix.det_fin_two]⟩
        let Dsl : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![(aU : F), 0; 0, (aU⁻¹ : F)],
            by simp [Matrix.det_fin_two]⟩
        have hfactor : A = Bsl * Dsl := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j
          · simp [Bsl, Dsl, Matrix.mul_apply, aU]
          · simp [Bsl, Dsl, Matrix.mul_apply, aU, ha_zero]
          · simpa [Bsl, Dsl, Matrix.mul_apply, aU] using hA10
          · simpa [Bsl, Dsl, Matrix.mul_apply, aU] using hd_inv
        have hBsl :
            QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) Bsl =
              unipotent
                ((A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                  (A : Matrix (Fin 2) (Fin 2) F) 0 0) := by
          rw [hunipotent_matrix]
        have hDsl :
            QuotientGroup.mk'
                (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F)) Dsl =
              splitTorus aU := by
          rw [hsplitTorus_matrix]
        change QuotientGroup.mk'
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F)) A ∈ U ⊔ T
        rw [hfactor, map_mul, hBsl, hDsl]
        exact (U ⊔ T).mul_mem
          ((show U ≤ U ⊔ T from le_sup_left)
            (by rw [hU_range]; exact ⟨_, rfl⟩))
          ((show T ≤ U ⊔ T from le_sup_right)
            (by rw [hT_range]; exact ⟨_, rfl⟩))
      have hmem_NP_of_image_mem_B
          (g : H) (hgB : conjH' g ∈ U ⊔ T) :
          g ∈ NP := by
        let Qg : Subgroup H :=
          (P : Subgroup H).map (MulAut.conj g).toMonoidHom
        have hg_normalizes_U :
            conjH' g ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) :=
          hB_le_normalizer hgB
        have hQg_map_le_U : Qg.map conjH' ≤ U := by
          rintro y ⟨z, ⟨x, hxP, rfl⟩, rfl⟩
          change conjH' (g * x * g⁻¹) ∈ U
          rw [map_mul, map_mul, map_inv]
          exact
            (Subgroup.mem_normalizer_iff.mp hg_normalizes_U
              (conjH' x)).mp
              (hP_map_conjH'_le_U
                (Subgroup.mem_map_of_mem conjH' hxP))
        have hP_normalizes_Qg :
            (P : Subgroup H) ≤ Subgroup.normalizer (Qg : Set H) := by
          intro x hxP
          rw [Subgroup.mem_normalizer_iff]
          intro y
          have hxU : conjH' x ∈ U :=
            hP_map_conjH'_le_U (Subgroup.mem_map_of_mem conjH' hxP)
          have hzU (z : H) (hz : z ∈ Qg) : conjH' z ∈ U :=
            hQg_map_le_U (Subgroup.mem_map_of_mem conjH' hz)
          have hcomm (z : H) (hz : z ∈ Qg) : Commute x z := by
            let : IsMulCommutative U := hU_commutative
            apply hconjH'_injective
            simpa only [map_mul] using setLike_mul_comm hxU (hzU z hz)
          constructor
          · intro hy
            have hxy : x * y * x⁻¹ = y := by
              calc
                x * y * x⁻¹ = y * x * x⁻¹ := by
                  rw [(hcomm y hy).eq]
                _ = y := by simp
            rwa [hxy]
          · intro hy
            have hzcomm : Commute x (x * y * x⁻¹) :=
              hcomm (x * y * x⁻¹) hy
            have hy_eq : y = x * y * x⁻¹ := by
              calc
                y = x⁻¹ * (x * y * x⁻¹) * x := by group
                _ = x⁻¹ * (x * (x * y * x⁻¹)) := by
                  rw [mul_assoc, hzcomm.eq.symm]
                _ = x * y * x⁻¹ := by simp
            rw [hy_eq]
            exact hy
        have hQg_isPGroup : IsPGroup p Qg :=
          P.isPGroup'.map (MulAut.conj g).toMonoidHom
        have hsup_isPGroup :
            IsPGroup p ((P : Subgroup H) ⊔ Qg : Subgroup H) :=
          P.isPGroup'.to_sup_of_normal_right' hQg_isPGroup hP_normalizes_Qg
        have hsup_eq_P :
            (P : Subgroup H) ⊔ Qg = (P : Subgroup H) :=
          P.is_maximal' hsup_isPGroup le_sup_left
        have hQg_le_P : Qg ≤ (P : Subgroup H) := by
          calc
            Qg ≤ (P : Subgroup H) ⊔ Qg := le_sup_right
            _ = (P : Subgroup H) := hsup_eq_P
        have hQg_card : Nat.card Qg = Nat.card P :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
        have hQg_eq_P : Qg = (P : Subgroup H) :=
          Subgroup.eq_of_le_of_card_ge hQg_le_P (by rw [hQg_card])
        apply (Subgroup.conjAct_pointwise_smul_iff
          (H := (P : Subgroup H)) (g := g)).mp
        change Qg = (P : Subgroup H)
        exact hQg_eq_P
      let rhoH : H →* Equiv.Perm Point := rho.comp conjH'
      let : MulAction H Point := MulAction.compHom Point rhoH
      have hstabilizer_inf :
          MulAction.stabilizer H inf = NP := by
        ext g
        rw [MulAction.mem_stabilizer_iff]
        constructor
        · intro hfix
          apply hmem_NP_of_image_mem_B g
          apply hfix_inf_mem_B (conjH' g)
          exact hfix
        · intro hgNP
          have hgB0 : conjH (g : H) ∈ U ⊔ T :=
            hNP_maps_B ⟨g, hgNP⟩
          have hgB : conjH' g ∈ U ⊔ T := by
            change u⁻¹ * conjH g * (u⁻¹)⁻¹ ∈ U ⊔ T
            exact (U ⊔ T).mul_mem
              ((U ⊔ T).mul_mem
                ((show U ≤ U ⊔ T from le_sup_left) (U.inv_mem huU)) hgB0)
              ((show U ≤ U ⊔ T from le_sup_left) (by simpa using huU))
          apply hB_fixes_inf
          exact hgB
      let S := MulAction.orbit H inf
      let baseS : S := ⟨inf, MulAction.mem_orbit_self inf⟩
      have hstabilizer_base :
          MulAction.stabilizer H baseS = NP := by
        ext g
        rw [MulAction.mem_stabilizer_iff]
        constructor
        · intro hfix
          have hfix_val := congrArg Subtype.val hfix
          have : g • inf = inf := by
            rw [MulAction.orbit.coe_smul] at hfix_val
            exact hfix_val
          rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf] at this
          exact this
        · intro hg
          apply Subtype.ext
          change g • inf = inf
          rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
          exact hg
      have hsplit_fixed_eq_inf_or_zero
          (a : Fˣ) (ha : splitTorus a ≠ 1) (z : Point)
          (hfix : splitTorus a • z = z) :
          z = inf ∨ z = zero := by
        rw [← Projectivization.mk_rep z] at hfix
        rw [hsplitTorus_matrix] at hfix
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F))
              (Projectivization.mk F z.rep z.rep_nonzero) =
            Projectivization.mk F z.rep z.rep_nonzero at hfix
        rw [hrho_apply, Projectivization.smul_mk] at hfix
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
          ⟨c0, hc0⟩
        have h0 := congrFun hc0 (0 : Fin 2)
        have h1 := congrFun hc0 (1 : Fin 2)
        simp [Matrix.mulVec, dotProduct] at h0 h1
        by_cases hz0 : z.rep 0 = 0
        · right
          rw [← Projectivization.mk_rep z]
          dsimp only [zero]
          apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
          refine ⟨z.rep 1, ?_⟩
          ext i
          fin_cases i
          · simp [hz0]
          · simp
        · by_cases hz1 : z.rep 1 = 0
          · left
            rw [← Projectivization.mk_rep z]
            dsimp only [inf]
            apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
            refine ⟨z.rep 0, ?_⟩
            ext i
            fin_cases i
            · simp
            · simp [hz1]
          · exfalso
            have hc_eq_a : c0 = (a : F) := by
              apply mul_right_cancel₀ hz0
              simpa using h0
            have hc_eq_ainv : c0 = (a⁻¹ : F) := by
              apply mul_right_cancel₀ hz1
              simpa using h1
            have ha_sq : (a : F) ^ 2 = 1 := by
              have hai : (a : F) = (a⁻¹ : F) :=
                hc_eq_a.symm.trans hc_eq_ainv
              calc
                (a : F) ^ 2 = (a : F) * (a : F) := pow_two _
                _ = (a : F) * (a⁻¹ : F) :=
                  congrArg (fun z : F => (a : F) * z) hai
                _ = 1 := mul_inv_cancel₀ (Units.ne_zero a)
            have hfix_x0 :
                splitTorus a * unipotent (x0 : F) *
                    (splitTorus a)⁻¹ =
                  unipotent (x0 : F) := by
              rw [hsplit_conj, ha_sq, one_mul]
            have haT : splitTorus a ∈ T := by
              rw [hT_range]
              exact ⟨a, rfl⟩
            rcases hT_fixedPointFree
                (splitTorus a) haT (unipotent (x0 : F))
                (hP_map_conjH'_le_U x0.property) hfix_x0 with ha1 | hx1
            · exact ha ha1
            · exact hx0_unipotent_ne_one hx1
      have hzero_mem_S
          (hS_card : Nat.card S = p ^ m + 1) :
          zero ∈ S := by
        by_contra hzero_not
        let cToH : C →* H := NP.subtype.comp C.subtype
        let : MulAction C S := MulAction.compHom S cToH
        have hbase_fixed (d : C) : d • baseS = baseS := by
          apply Subtype.ext
          change (cToH d) • inf = inf
          apply MulAction.mem_stabilizer_iff.mp
          rw [hstabilizer_inf]
          exact (d : NP).property
        let S0 : SubMulAction C S :=
          { carrier := {y | y ≠ baseS}
            smul_mem' := by
              intro d y hy hdy
              apply hy
              calc
                y = d⁻¹ • (d • y) := (inv_smul_smul d y).symm
                _ = d⁻¹ • baseS := congrArg (fun z : S => d⁻¹ • z) hdy
                _ = baseS := hbase_fixed d⁻¹ }
        have hstab (y : S0) :
            MulAction.stabilizer C y = ⊥ := by
          rw [eq_bot_iff]
          intro d hd
          by_contra hd_ne_one
          have hdy : d • (y : S) = (y : S) := by
            have hdy0 : d • y = y :=
              MulAction.mem_stabilizer_iff.mp hd
            simpa only [SubMulAction.val_smul] using
              congrArg Subtype.val hdy0
          have hpoint_fixed :
              conjH' (cToH d) • ((y : S) : Point) = ((y : S) : Point) := by
            have hval := congrArg Subtype.val hdy
            exact hval
          rcases hcgen d with ⟨j, hj⟩
          have himage :
              conjH' (cToH d) = splitTorus (r ^ j) := by
            calc
              conjH' (cToH d) = conjH' (cToH (cgen ^ j)) := by rw [← hj]
              _ = (conjH' (cToH cgen)) ^ j := map_zpow conjH' _ _
              _ = (splitTorus r) ^ j := by
                have hcToH : cToH cgen = (cN : H) := rfl
                rw [hcToH, hcgen_split]
              _ = splitTorus (r ^ j) := (map_zpow splitTorus r j).symm
          have himage_ne : splitTorus (r ^ j) ≠ 1 := by
            intro himage_one
            apply hd_ne_one
            apply Subtype.ext
            apply Subtype.ext
            apply hconjH'_injective
            change conjH' (cToH d) = conjH' (cToH 1)
            rw [himage, himage_one]
            exact (map_one conjH').symm
          have hfixed_cases :=
            hsplit_fixed_eq_inf_or_zero (r ^ j) himage_ne
              ((y : S) : Point) (by rwa [← himage])
          rcases hfixed_cases with hyinf | hyzero
          · apply y.property
            apply Subtype.ext
            exact hyinf
          · apply hzero_not
            rw [← hyzero]
            exact (y : S).property
        have hC_dvd_S0 : Nat.card C ∣ Nat.card S0 := by
          have hcard :=
            Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
          rw [Nat.card_prod] at hcard
          exact ⟨Nat.card (Quotient (MulAction.orbitRel C S0)), by
            rw [mul_comm]
            exact hcard⟩
        have hS0card : Nat.card S0 = p ^ m := by
          have hsub : Nat.card S0 = Nat.card S - 1 := by
            change Nat.card {y : S // y ≠ baseS} = Nat.card S - 1
            let : Fintype S := Fintype.ofFinite S
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            simp
          rw [hsub, hS_card]
          omega
        have hzi0_dvd_q : Nat.card (Z i0) ∣ p ^ m := by
          rw [← hCcard, ← hS0card]
          exact hC_dvd_S0
        have hzi0_dvd_one : Nat.card (Z i0) ∣ 1 := by
          have hsub := Nat.dvd_sub hzi0_dvd_q hi0_dvd_sub_one
          have hdiff : p ^ m - (p ^ m - 1) = 1 := by omega
          rwa [hdiff] at hsub
        have hzi0_one := Nat.eq_one_of_dvd_one hzi0_dvd_one
        exact (hnontrivial i0).ne hzi0_one.symm
      have haffine_injective : Function.Injective affine := by
        intro x y hxy
        dsimp only [affine] at hxy
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hxy with
          ⟨a, ha⟩
        have h0 := congrFun ha (0 : Fin 2)
        have h1 := congrFun ha (1 : Fin 2)
        simp at h1
        simpa [h1] using h0.symm
      have hsubline_swap
          (hS_card : Nat.card S = p ^ m + 1) :
          ∃ h : H,
            h • inf = zero ∧ h • zero = inf ∧
            (∀ z : S, (z : Point) ≠ inf →
              ∃ w : W, (z : Point) = affine (w : F)) ∧
            NP ⊔ Subgroup.zpowers h = ⊤ := by
        have hzeroS : zero ∈ S := hzero_mem_S hS_card
        have hzero_ne_inf : zero ≠ inf := by
          intro hzero_inf
          dsimp only [zero, inf] at hzero_inf
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp
              hzero_inf with ⟨a, ha⟩
          have h0 := congrFun ha (0 : Fin 2)
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let zeroS : S := ⟨zero, hzeroS⟩
        let S0 := {z : S // z ≠ baseS}
        have hS0card : Nat.card S0 = p ^ m := by
          have hsub : Nat.card S0 = Nat.card S - 1 := by
            change Nat.card {z : S // z ≠ baseS} = Nat.card S - 1
            let : Fintype S := Fintype.ofFinite S
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            simp
          rw [hsub, hS_card]
          omega
        have haffine_mem_S (w : W) : affine (w : F) ∈ S := by
          rcases w.property with ⟨g, hgP, hg⟩
          rcases hzeroS with ⟨h0, hh0⟩
          change h0 • inf = zero at hh0
          refine ⟨g * h0, ?_⟩
          change (g * h0) • inf = affine (w : F)
          rw [mul_smul, hh0]
          change rho (conjH' g) zero = affine (w : F)
          rw [hg]
          change unipotent (w : F) • affine 0 = affine (w : F)
          simpa using hunipotent_affine (w : F) 0
        have haffine_ne_inf (w : W) : affine (w : F) ≠ inf := by
          intro hwi
          dsimp only [affine, inf] at hwi
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hwi with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let affineW : W → S0 := fun w =>
          ⟨⟨affine (w : F), haffine_mem_S w⟩, by
            intro heq
            apply haffine_ne_inf w
            exact congrArg Subtype.val heq⟩
        have haffineW_inj : Function.Injective affineW := by
          intro x y hxy
          apply Subtype.ext
          apply haffine_injective
          exact congrArg (fun z : S0 => ((z : S) : Point)) hxy
        have haffineW_card : Nat.card W = Nat.card S0 := by
          rw [hWcard, hS0card]
        have haffineW_surj : Function.Surjective affineW :=
          (Nat.bijective_iff_injective_and_card affineW).mpr
            ⟨haffineW_inj, haffineW_card⟩ |>.2
        have hcover :
            ∀ z : S, (z : Point) ≠ inf →
              ∃ w : W, (z : Point) = affine (w : F) := by
          intro z hz
          have hzbase : z ≠ baseS := by
            intro heq
            exact hz (congrArg Subtype.val heq)
          obtain ⟨w, hw⟩ := haffineW_surj ⟨z, hzbase⟩
          refine ⟨w, ?_⟩
          exact congrArg (fun y : S0 => ((y : S) : Point)) hw.symm
        have hP_trans :
            ∀ y z : S0, ∃ g : P, (g : H) • (y : S) = (z : S) := by
          intro y z
          obtain ⟨wy, hwy⟩ := hcover (y : S) (by
            intro hy
            exact y.property (Subtype.ext hy))
          obtain ⟨wz, hwz⟩ := hcover (z : S) (by
            intro hz
            exact z.property (Subtype.ext hz))
          have hdiff_mem : unipotent ((wz : F) - (wy : F)) ∈ P0 := by
            change (wz : F) - (wy : F) ∈ W
            exact W.sub_mem wz.property wy.property
          rcases hdiff_mem with ⟨g, hgP, hg⟩
          refine ⟨⟨g, hgP⟩, ?_⟩
          apply Subtype.ext
          change rho (conjH' g) ((y : S) : Point) = ((z : S) : Point)
          rw [hwy, hwz, hg]
          change unipotent ((wz : F) - (wy : F)) • affine (wy : F) =
            affine (wz : F)
          rw [hunipotent_affine]
          congr 2
          ring
        have htwo :
            MulAction.IsMultiplyPretransitive H S 2 := by
          rw [MulAction.is_two_pretransitive_iff]
          intro a b c d hab hcd
          let : MulAction.IsPretransitive H S := inferInstance
          obtain ⟨g, hg⟩ :=
            (inferInstance : MulAction.IsPretransitive H S).exists_smul_eq
              a baseS
          obtain ⟨k, hk⟩ :=
            (inferInstance : MulAction.IsPretransitive H S).exists_smul_eq
              baseS c
          have hgb : g • b ≠ baseS := by
            intro hgb
            exact hab (smul_left_cancel g (hg.trans hgb.symm))
          have hkd : k⁻¹ • d ≠ baseS := by
            intro hkd
            apply hcd
            calc
              c = k • baseS := hk.symm
              _ = k • (k⁻¹ • d) := by rw [hkd]
              _ = d := smul_inv_smul k d
          obtain ⟨p0, hp0⟩ :=
            hP_trans ⟨g • b, hgb⟩ ⟨k⁻¹ • d, hkd⟩
          refine ⟨k * (p0 : H) * g, ?_, ?_⟩
          · simp only [mul_smul]
            have hpbase : (p0 : H) • baseS = baseS := by
              apply Subtype.ext
              change (p0 : H) • inf = inf
              rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
              exact Subgroup.le_normalizer p0.property
            rw [hg, hpbase, hk]
          · simp only [mul_smul]
            rw [hp0, smul_inv_smul]
        have hzeroS_ne_base : zeroS ≠ baseS := by
          intro heq
          exact hzero_ne_inf (congrArg Subtype.val heq)
        let : Nontrivial S :=
          ⟨⟨zeroS, baseS, hzeroS_ne_base⟩⟩
        have htwo' := (MulAction.is_two_pretransitive_iff.mp htwo)
          hzeroS_ne_base.symm hzeroS_ne_base
        rcases htwo' with ⟨h, hinf, hzero⟩
        have : MulAction.IsPreprimitive H S :=
          MulAction.isPreprimitive_of_is_two_pretransitive htwo
        have hcoatom :
            IsCoatom (MulAction.stabilizer H baseS) :=
          MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive H baseS
        rw [hstabilizer_base] at hcoatom
        have hgen : NP ⊔ Subgroup.zpowers h = ⊤ := by
          rcases hcoatom.le_iff.mp le_sup_left with htop | heq
          · exact htop
          · exfalso
            have hhNP : h ∈ NP := by
              rw [← heq]
              exact (show Subgroup.zpowers h ≤ NP ⊔ Subgroup.zpowers h from
                le_sup_right) (Subgroup.mem_zpowers h)
            have hhfix : h • inf = inf := by
              rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
              exact hhNP
            exact hzero_ne_inf ((congrArg Subtype.val hinf).symm.trans hhfix)
        refine ⟨h, congrArg Subtype.val hinf,
          congrArg Subtype.val hzero, hcover, hgen⟩
      have hPGL_embedding
          (hKcard : Nat.card K = p ^ m)
          (hswap : H) (hswap_inf : hswap • inf = zero)
          (hswap_zero : hswap • zero = inf)
          (hcover : ∀ z : S, (z : Point) ≠ inf →
            ∃ w : W, (z : Point) = affine (w : F))
          (hgen : NP ⊔ Subgroup.zpowers hswap = ⊤) :
          ∃ phi : H →* Matrix.ProjGenLinGroup (Fin 2) K,
            Function.Injective phi := by
        exact _root_.Glauberman.Dickson.h826_subfield_embedding_of_borel_and_swap
          H P U conjH' hconjH'_injective unipotent splitTorus
          hP_map_conjH'_le_U hU_range hunipotent_matrix hsplitTorus_matrix
          C hcomp cgen hcgen r hcgen_split x0 hx0_ne_zero hx0_val_ne_zero
          K (fun a x hx => a.property x hx) (hKcard.trans hWcard.symm)
          (by simpa only [pow_two] using hlambda_mem_K)
          (by intro h; exact Units.ne_zero (r*r) (congrArg Subtype.val h))
          rho hrho_apply hunipotent_affine haffine_injective hswap
          hswap_inf hswap_zero hcover hgen
      have htwo_torus_core :
          (p ^ m = 3 ∧ Nat.card H = 60 ∧
            (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
            Nat.card (Sylow 5 H) = 6 ∧
            Function.Injective (MulAction.toPermHom H (Sylow 5 H))) ∨
          (2 * m ∣ f ∧ Nonempty
            (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
          (m ∣ f ∧ Nonempty
            (H ≃* PSL2MatrixGroup (GaloisField p m))) := by
        have horder_cases :=
          h826_group_order_cases
            (p ^ m) (Nat.card (Z i0)) (Nat.card (Z i1))
            (Nat.card H) NP.index (NZ i0).index (NZ i1).index
            hpm_gt (hnontrivial i0) (hnontrivial i1)
            ((hcoprime i0).pow_left m) ((hcoprime i1).pow_left m)
            hi0_dvd_sub_one htorus_gcd
            (by simpa only [c] using hH_eq_c)
            hNP_index_factor hi0_factor hi1_factor hcount_pair
        rcases horder_cases with hsmall | hfull | hhalf
        · left
          rcases hsmall with ⟨hpm3, hi0card, hi1card, hcard60⟩
          have hrestriction : p = 5 ∨ 5 ∣ p ^ (2 * f) - 1 := by
            by_cases hp5 : p = 5
            · exact Or.inl hp5
            · right
              have hfive_torus :
                  5 ∣ (Nat.card F - 1) /
                      Nat.gcd (Nat.card F - 1) 2 ∨
                    5 ∣ (Nat.card F + 1) /
                      Nat.gcd (Nat.card F - 1) 2 := by
                have h := hdivides i1
                rw [hi1card] at h
                exact h
              have hgcd_dvd_add :
                  Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
                have hadd := Nat.dvd_add
                  (Nat.gcd_dvd_left (Nat.card F - 1) 2)
                  (Nat.gcd_dvd_right (Nat.card F - 1) 2)
                have hFpos : 0 < Nat.card F := Nat.card_pos
                convert hadd using 1
                all_goals omega
              have hfive_factor :
                  5 ∣ Nat.card F - 1 ∨ 5 ∣ Nat.card F + 1 := by
                rcases hfive_torus with hminus | hplus
                · exact Or.inl (dvd_trans hminus
                    (Nat.div_dvd_of_dvd
                      (Nat.gcd_dvd_left (Nat.card F - 1) 2)))
                · exact Or.inr (dvd_trans hplus
                    (Nat.div_dvd_of_dvd hgcd_dvd_add))
              have hfive_sq : 5 ∣ Nat.card F ^ 2 - 1 := by
                have hfactor :
                    Nat.card F ^ 2 - 1 =
                      (Nat.card F - 1) * (Nat.card F + 1) := by
                  simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
                rw [hfactor]
                rcases hfive_factor with hminus | hplus
                · exact dvd_mul_of_dvd_left hminus _
                · exact dvd_mul_of_dvd_right hplus _
              rw [hFcard, ← pow_mul] at hfive_sq
              simpa [mul_comm] using hfive_sq
          have hi1index : (Z i1).index = 12 := by
            have hmul := (Z i1).card_mul_index
            rw [hi1card, hcard60] at hmul
            apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5)
            simpa using hmul
          have hNZi1index : (NZ i1).index = 6 := by
            have hfactor := hi1_factor
            rw [hi1card, hcard60] at hfactor
            apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 10)
            norm_num at hfactor ⊢
            exact hfactor
          let : Fact (Nat.Prime 5) := ⟨by decide⟩
          let hZi1P : IsPGroup 5 (Z i1) :=
            IsPGroup.of_card (n := 1) (by simpa using hi1card)
          let Q : Sylow 5 H := hZi1P.toSylow (by
            rw [hi1index]
            norm_num)
          have hSylow5 : Nat.card (Sylow 5 H) = 6 := by
            calc
              Nat.card (Sylow 5 H) =
                  (Subgroup.normalizer (Q : Set H)).index :=
                Q.card_eq_index_normalizer
              _ = (NZ i1).index := by rfl
              _ = 6 := hNZi1index
          let act := MulAction.toPermHom H (Sylow 5 H)
          have hker_le_normalizer (R : Sylow 5 H) :
              act.ker ≤ Subgroup.normalizer (R : Set H) := by
            intro x hx
            have hxperm : act x = 1 := hx
            have hxfix : x • R = R := by
              have h := DFunLike.congr_fun hxperm R
              simpa [act] using h
            exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
          have hnormalizer_card_ten :
              Nat.card (Subgroup.normalizer (Q : Set H)) = 10 := by
            have hQindex :
                (Subgroup.normalizer (Q : Set H)).index = 6 := by
              calc
                (Subgroup.normalizer (Q : Set H)).index =
                    Nat.card (Sylow 5 H) :=
                  Q.card_eq_index_normalizer.symm
                _ = 6 := hSylow5
            have hmul :=
              (Subgroup.normalizer (Q : Set H)).card_mul_index
            rw [hQindex, hcard60] at hmul
            apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
            simpa using hmul
          have hker_card_dvd_ten : Nat.card act.ker ∣ 10 := by
            have hdvd : Nat.card act.ker ∣
                Nat.card (Subgroup.normalizer (Q : Set H)) :=
              Subgroup.card_dvd_of_le (hker_le_normalizer Q)
            rw [hnormalizer_card_ten] at hdvd
            exact hdvd
          have hno_sylow_le_ker (R : Sylow 5 H) :
              ¬ (R : Subgroup H) ≤ act.ker := by
            intro hRker
            let : Fintype (Sylow 5 H) := Fintype.ofFinite _
            obtain ⟨S, hSR⟩ :=
              Fintype.exists_ne_of_one_lt_card
                (by simpa [Nat.card_eq_fintype_card] using
                  (show 1 < Nat.card (Sylow 5 H) by
                    rw [hSylow5]
                    norm_num)) R
            have hRnormalizesS :
                (R : Subgroup H) ≤ Subgroup.normalizer (S : Set H) := by
              intro x hx
              exact hker_le_normalizer S (hRker hx)
            have hsupP :
                IsPGroup 5
                  ((R : Subgroup H) ⊔ (S : Subgroup H) : Subgroup H) :=
              R.isPGroup'.to_sup_of_normal_right' S.isPGroup' hRnormalizesS
            have hsup_eq :
                (R : Subgroup H) ⊔ (S : Subgroup H) = S :=
              S.is_maximal' hsupP le_sup_right
            have hRleS : (R : Subgroup H) ≤ S := by
              calc
                (R : Subgroup H) ≤ (R : Subgroup H) ⊔ (S : Subgroup H) :=
                  le_sup_left
                _ = S := hsup_eq
            exact hSR (Sylow.ext (R.is_maximal' S.isPGroup' hRleS))
          have hfive_not_dvd_ker : ¬ 5 ∣ Nat.card act.ker := by
            intro hfive
            obtain ⟨x, hxorder⟩ :=
              exists_prime_orderOf_dvd_card' 5 hfive
            have hxHorder : orderOf (x : H) = 5 :=
              (Subgroup.orderOf_coe x).trans hxorder
            have hXisP : IsPGroup 5 (Subgroup.zpowers (x : H)) :=
              IsPGroup.of_card
                (((Nat.card_zpowers (x : H)).trans hxHorder).trans
                  (pow_one 5).symm)
            obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
            have hXcard : Nat.card (Subgroup.zpowers (x : H)) = 5 :=
              (Nat.card_zpowers (x : H)).trans hxHorder
            have hRcard : Nat.card R = 5 := by
              calc
                Nat.card R = Nat.card Q :=
                  Nat.card_congr (Sylow.equiv R Q).toEquiv
                _ = 5 := by
                  change Nat.card (Z i1) = 5
                  exact hi1card
            have hXR_eq :
                Subgroup.zpowers (x : H) = (R : Subgroup H) :=
              Subgroup.eq_of_le_of_card_ge hXR (by rw [hXcard, hRcard])
            apply hno_sylow_le_ker R
            rw [← hXR_eq]
            intro y hy
            rcases hy with ⟨j, rfl⟩
            exact act.ker.zpow_mem x.2 j
          have hker_card_cases :
              Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
            have hpos : 0 < Nat.card act.ker := Nat.card_pos
            have hle : Nat.card act.ker ≤ 10 :=
              Nat.le_of_dvd (by norm_num) hker_card_dvd_ten
            generalize Nat.card act.ker = n at hpos hle hker_card_dvd_ten hfive_not_dvd_ker ⊢
            clear * - n hpos hle hker_card_dvd_ten hfive_not_dvd_ker
            interval_cases n <;> norm_num at *
          have hker_bot : act.ker = ⊥ := by
            rcases hker_card_cases with hker_one | hker_two
            · exact Subgroup.card_eq_one.mp hker_one
            · exfalso
              obtain ⟨y, hyorder⟩ :=
                exists_prime_orderOf_dvd_card' 5 (by
                  rw [hcard60]
                  norm_num)
              obtain ⟨c0, hc0order⟩ :=
                exists_prime_orderOf_dvd_card' 2 (by rw [hker_two])
              have hc0ne : c0 ≠ 1 := by
                intro hc
                rw [hc, orderOf_one] at hc0order
                norm_num at hc0order
              obtain ⟨c1, hc1ne, hc1unique⟩ :=
                (Nat.card_eq_two_iff' (1 : act.ker)).mp hker_two
              have hc0eq : c0 = c1 := hc1unique c0 hc0ne
              have hc0central : (c0 : H) ∈ Subgroup.center H := by
                rw [Subgroup.mem_center_iff]
                intro g
                let d : act.ker :=
                  ⟨g * (c0 : H) * g⁻¹,
                    (inferInstance : act.ker.Normal).conj_mem
                      (c0 : H) c0.2 g⟩
                have hdne : d ≠ 1 := by
                  intro hd
                  have hdval := congrArg Subtype.val hd
                  change g * (c0 : H) * g⁻¹ = 1 at hdval
                  apply hc0ne
                  apply Subtype.ext
                  calc
                    (c0 : H) = g⁻¹ * (g * (c0 : H) * g⁻¹) * g := by group
                    _ = 1 := by rw [hdval]; simp
                have hdeq : d = c0 := by
                  rw [hc0eq]
                  exact hc1unique d hdne
                have hdval := congrArg Subtype.val hdeq
                change g * (c0 : H) * g⁻¹ = (c0 : H) at hdval
                calc
                  g * (c0 : H) = (g * (c0 : H) * g⁻¹) * g := by group
                  _ = (c0 : H) * g := by rw [hdval]
              have hc0Horder : orderOf (c0 : H) = 2 :=
                (Subgroup.orderOf_coe c0).trans hc0order
              have hyHorder : orderOf (y : H) = 5 :=
                hyorder
              have hcomm : Commute (c0 : H) (y : H) :=
                (Subgroup.mem_center_iff.mp hc0central (y : H)).symm
              have hcop :
                  Nat.Coprime (orderOf (c0 : H)) (orderOf (y : H)) := by
                rw [hc0Horder, hyHorder]
                norm_num
              let x : H := (c0 : H) * (y : H)
              have hxorder : orderOf x = 10 := by
                dsimp only [x]
                rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
                  hc0Horder, hyHorder]
              have hxne : x ≠ 1 := by
                intro hx
                rw [hx, orderOf_one] at hxorder
                norm_num at hxorder
              obtain ⟨A, hxA, _⟩ :=
                huppert_II_8_22_unique_family hFcard H Z
                  hcyclic hnontrivial hcoprime hmaximal
                  hrepresentative hdistinct x hxne
              rcases A with Qp | z
              · have hxdvd : orderOf x ∣ Nat.card Qp :=
                  (Qp : Subgroup H).orderOf_dvd_natCard hxA
                have hQpcard : Nat.card Qp = 3 := by
                  calc
                    Nat.card Qp = Nat.card P :=
                      Nat.card_congr (Sylow.equiv Qp P).toEquiv
                    _ = 3 := hPm.trans hpm3
                rw [hxorder, hQpcard] at hxdvd
                norm_num at hxdvd
              · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                  z.2.1.orderOf_dvd_natCard hxA
                obtain ⟨g, hg⟩ := z.2.2
                have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
                  rw [hg, Subgroup.card_map_of_injective
                    (MulAut.conj g).injective]
                have hz_cases : z.1 = i0 ∨ z.1 = i1 := by
                  have hzmem : z.1 ∈ ({i0, i1} : Finset (Fin 2)) := by
                    rw [huniv_pair]
                    simp
                  simpa using hzmem
                rw [hxorder, hzcard] at hxdvd
                rcases hz_cases with hzi0 | hzi1
                · rw [hzi0, hi0card] at hxdvd
                  norm_num at hxdvd
                · rw [hzi1, hi1card] at hxdvd
                  norm_num at hxdvd
          have hfaithful : Function.Injective act := by
            rw [← MonoidHom.ker_eq_bot_iff]
            exact hker_bot
          exact ⟨hpm3, hcard60, hrestriction, hSylow5, hfaithful⟩
        · have hKcard : Nat.card K = p ^ m := by
            apply Nat.le_antisymm hK_le_q
            calc
              p ^ m = (p ^ m - 1) + 1 :=
                (Nat.sub_add_cancel (Nat.zero_lt_of_lt hpm_gt)).symm
              _ = Nat.card (Z i0) + 1 := by rw [hfull.1]
              _ ≤ Nat.card K := hK_lower
          have hS_card : Nat.card S = p ^ m + 1 := by
            have hNPindex : NP.index = p ^ m + 1 := by
              have hqsubpos : 0 < p ^ m - 1 := by omega
              apply Nat.eq_of_mul_eq_mul_left
                (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
                  hqsubpos)
              calc
                (p ^ m * (p ^ m - 1)) * NP.index =
                    Nat.card NP * NP.index := by rw [hNPcard, hfull.1]
                _ = Nat.card H := NP.card_mul_index
                _ = (p ^ m + 1) * p ^ m * (p ^ m - 1) := hfull.2.2
                _ = (p ^ m * (p ^ m - 1)) * (p ^ m + 1) := by ring
            have hindex_card :=
              MulAction.index_stabilizer_of_transitive H baseS
            rw [hstabilizer_base, hNPindex] at hindex_card
            exact hindex_card.symm
          obtain ⟨hswap, hswap_inf, hswap_zero, hcover, hgen⟩ :=
            hsubline_swap hS_card
          have hmdiv : m ∣ f := by
            have hsplit_dvd :
                p ^ m - 1 ∣
                  (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
              rw [← hfull.1]
              exact hi0_dvd_ambient
            have hpowdiv : p ^ m - 1 ∣ p ^ f - 1 := by
              rw [← hFcard]
              exact dvd_trans hsplit_dvd
                (Nat.div_dvd_of_dvd
                  (Nat.gcd_dvd_left (Nat.card F - 1) 2))
            exact h826_exponent_dvd_of_pow_sub_one_dvd
              (Fact.out : p.Prime).two_le hpowdiv
          obtain ⟨phi, hphi⟩ :=
            hPGL_embedding hKcard hswap hswap_inf hswap_zero hcover hgen
          have hPGLcard :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                p ^ m * ((p ^ m) ^ 2 - 1) := by
            rw [h826_card_pgl2, hKcard]
          have hfactor :
              (p ^ m) ^ 2 - 1 =
                (p ^ m - 1) * (p ^ m + 1) := by
            simpa [mul_comm] using Nat.sq_sub_sq (p ^ m) 1
          have hFullCardEq :
              Nat.card H =
                Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) := by
            rw [hfull.2.2, hPGLcard, hfactor]
            ring
          let : Fintype K := Fintype.ofFinite K
          let : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
            Finite.of_surjective Matrix.ProjGenLinGroup.mk
              Matrix.ProjGenLinGroup.mk_surjective
          let eHPGL :
              H ≃* Matrix.ProjGenLinGroup (Fin 2) K :=
            MulEquiv.ofBijective phi
              ((Nat.bijective_iff_injective_and_card phi).2
                ⟨hphi, hFullCardEq⟩)
          by_cases hp_two : p = 2
          · subst p
            let : CharP K 2 :=
              charP_of_card_eq_prime_pow (by simpa using hKcard)
            let : Algebra (ZMod 2) K := ZMod.algebra K 2
            have htwozero : (2 : K) = 0 :=
              CharP.cast_eq_zero K 2
            have hneg_one : (-1 : K) = 1 := by
              apply (neg_eq_iff_add_eq_zero).2
              rw [show (1 : K) + 1 = 2 by norm_num, htwozero]
            have hcenter :
                Nat.card
                    (Subgroup.center
                      (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 :=
              huppert614_card_center_of_neg_one_eq_one hneg_one
            have hPSLcard := huppert614_card_psl_mul_center (K := K)
            rw [hcenter, mul_one] at hPSLcard
            have hPSLPGLcard :
                Nat.card (PSL2MatrixGroup K) =
                  Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) :=
              hPSLcard.trans (h826_card_pgl2 (K := K)).symm
            let ePSLPGL :
                PSL2MatrixGroup K ≃*
                  Matrix.ProjGenLinGroup (Fin 2) K :=
              MulEquiv.ofBijective h826_pslToPGL
                ((Nat.bijective_iff_injective_and_card
                    (h826_pslToPGL (K := K))).2
                  ⟨h826_pslToPGL_injective, hPSLPGLcard⟩)
            let eK :=
              GaloisField.algEquivGaloisField 2 m hKcard
            let eHPSL : H ≃* PSL2MatrixGroup K :=
              eHPGL.trans ePSLPGL.symm
            exact Or.inr (Or.inr
              ⟨hmdiv, ⟨eHPSL.trans (h826_pslEquiv eK.toRingEquiv)⟩⟩)
          · have hp_odd : Odd p :=
              (Fact.out : p.Prime).odd_of_ne_two hp_two
            have hFodd : Odd (Nat.card F) := by
              rw [hFcard]
              exact hp_odd.pow
            have hF_two_dvd : 2 ∣ Nat.card F - 1 :=
              even_iff_two_dvd.mp (Nat.Odd.sub_odd hFodd odd_one)
            have hFgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hF_two_dvd (dvd_refl 2))
            have hsplit_dvd :
                p ^ m - 1 ∣ (p ^ f - 1) / 2 := by
              rw [← hFcard, ← hFgcd, ← hfull.1]
              exact hi0_dvd_ambient
            have hpow_two_dvd : 2 ∣ p ^ f - 1 := by
              rwa [← hFcard]
            have htwo_split_dvd :
                2 * (p ^ m - 1) ∣ p ^ f - 1 :=
              Nat.mul_dvd_of_dvd_div hpow_two_dvd hsplit_dvd
            have hqminus_dvd : p ^ m - 1 ∣ p ^ f - 1 :=
              dvd_trans hsplit_dvd
                (Nat.div_dvd_of_dvd hpow_two_dvd)
            have htwo_dvd_quot :
                2 ∣ (p ^ f - 1) / (p ^ m - 1) :=
              (Nat.dvd_div_iff_mul_dvd hqminus_dvd).2
                (by simpa [mul_comm] using htwo_split_dvd)
            obtain ⟨k, hfk⟩ := hmdiv
            have hquotEven :
                Even (((p ^ m) ^ k - 1) / (p ^ m - 1)) := by
              rw [hfk, pow_mul] at htwo_dvd_quot
              exact even_iff_two_dvd.mpr htwo_dvd_quot
            have hsumEven :
                Even (∑ i ∈ Finset.range k, (p ^ m) ^ i) := by
              rw [Nat.geomSum_eq (by omega)]
              exact hquotEven
            have hkEven : Even k := by
              rw [Finset.even_sum_iff_even_card_odd] at hsumEven
              simpa [(hp_odd.pow : Odd (p ^ m)).pow] using hsumEven
            have htwo_m_div : 2 * m ∣ f := by
              rcases hkEven with ⟨r0, hr0⟩
              refine ⟨r0, ?_⟩
              rw [hfk, hr0]
              ring
            let : Algebra (ZMod p) K := ZMod.algebra K p
            let eK :=
              GaloisField.algEquivGaloisField p m hKcard
            let pglHom :
                Matrix.ProjGenLinGroup (Fin 2) K →*
                  Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m) :=
              h826_pglMap eK.toRingEquiv.toRingHom
            let : Finite
                (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
              Finite.of_surjective Matrix.ProjGenLinGroup.mk
                Matrix.ProjGenLinGroup.mk_surjective
            have hPGLFieldCard :
                Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                  Nat.card
                    (Matrix.ProjGenLinGroup (Fin 2)
                      (GaloisField p m)) := by
              rw [h826_card_pgl2, h826_card_pgl2,
                Nat.card_congr eK.toEquiv]
            let ePGL :
                Matrix.ProjGenLinGroup (Fin 2) K ≃*
                  Matrix.ProjGenLinGroup (Fin 2)
                    (GaloisField p m) :=
              MulEquiv.ofBijective pglHom
                ((Nat.bijective_iff_injective_and_card pglHom).2
                  ⟨h826_pglMap_injective _
                    eK.injective, hPGLFieldCard⟩)
            exact Or.inr (Or.inl
              ⟨htwo_m_div, ⟨eHPGL.trans ePGL⟩⟩)
        · have hqodd : Odd (p ^ m) := hhalf.1.odd_of_right
          have hp_ne_two : p ≠ 2 := by
            intro hp
            subst p
            have hnot : ¬ 2 ∣ 2 ^ m :=
              Nat.prime_two.coprime_iff_not_dvd.mp hhalf.1.symm
            exact hnot (dvd_pow_self 2 hm_ne_zero)
          have hp_three : 3 ≤ p := by
            have hpgt := (Fact.out : p.Prime).one_lt
            omega
          have hq_two_dvd : 2 ∣ p ^ m - 1 :=
            even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one)
          have hzi0_twice :
              2 * Nat.card (Z i0) = p ^ m - 1 := by
              rw [hhalf.2.1, mul_comm]
              exact Nat.div_mul_cancel hq_two_dvd
          let : Algebra (ZMod p) K := ZMod.algebra K p
          have hKcard : Nat.card K = p ^ m := by
            let e := Module.finrank (ZMod p) K
            have hKpow : p ^ e = Nat.card K :=
              FiniteField.pow_finrank_eq_natCard p K
            have he_le_m : e ≤ m := by
              rw [← Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt,
                hKpow]
              exact hK_le_q
            obtain ⟨m0, hm0⟩ :=
              Nat.exists_eq_succ_of_ne_zero hm_ne_zero
            have hqeq : p ^ m = p ^ m0 * p := by
              rw [hm0, pow_succ]
            have hprev_lt_K : p ^ m0 < Nat.card K := by
              have hp_bound :
                  3 * p ^ m0 ≤ p ^ m := by
                rw [hqeq]
                simpa [mul_comm] using
                  Nat.mul_le_mul_left (p ^ m0) hp_three
              omega
            have heq : e = m := by
              by_contra hne
              have he_lt : e < m := lt_of_le_of_ne he_le_m hne
              have he_le_m0 : e ≤ m0 := by omega
              have hpow_le : p ^ e ≤ p ^ m0 :=
                Nat.pow_le_pow_right (Fact.out : p.Prime).pos he_le_m0
              rw [hKpow] at hpow_le
              omega
            rw [← hKpow, heq]
          have hS_card : Nat.card S = p ^ m + 1 := by
            have hcard_rewrite :
                Nat.card H =
                  (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) := by
              rw [hhalf.2.2.2, show Nat.gcd (p ^ m - 1) 2 = 2 from
                Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                  (Nat.dvd_gcd hq_two_dvd (dvd_refl 2))]
              exact Nat.mul_div_assoc ((p ^ m + 1) * p ^ m)
                hq_two_dvd
            have hNPindex : NP.index = p ^ m + 1 := by
              have hhalfpos : 0 < (p ^ m - 1) / 2 :=
                Nat.div_pos (by omega) (by norm_num)
              apply Nat.eq_of_mul_eq_mul_left
                (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
                  hhalfpos)
              calc
                (p ^ m * ((p ^ m - 1) / 2)) * NP.index =
                    Nat.card NP * NP.index := by
                      rw [hNPcard, hhalf.2.1]
                _ = Nat.card H := NP.card_mul_index
                _ = (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) :=
                  hcard_rewrite
                _ = (p ^ m * ((p ^ m - 1) / 2)) * (p ^ m + 1) := by ring
            have hindex_card :=
              MulAction.index_stabilizer_of_transitive H baseS
            rw [hstabilizer_base, hNPindex] at hindex_card
            exact hindex_card.symm
          obtain ⟨hswap, hswap_inf, hswap_zero, hcover, hgen⟩ :=
            hsubline_swap hS_card
          have hmdiv : m ∣ f := by
            have hf_ne_zero :=
              huppert_II_8_27_field_exponent_ne_zero hFcard
            have hFodd : Odd (Nat.card F) := by
              rw [hFcard]
              exact ((Fact.out : p.Prime).odd_of_ne_two hp_ne_two).pow
            have hF_two_dvd : 2 ∣ Nat.card F - 1 :=
              even_iff_two_dvd.mp (Nat.Odd.sub_odd hFodd odd_one)
            have hFgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hF_two_dvd (dvd_refl 2))
            have hhalf_dvd :
                (p ^ m - 1) / 2 ∣ (Nat.card F - 1) / 2 := by
              calc
                (p ^ m - 1) / 2 = Nat.card (Z i0) := hhalf.2.1.symm
                _ ∣ (Nat.card F - 1) /
                    Nat.gcd (Nat.card F - 1) 2 := hi0_dvd_ambient
                _ = (Nat.card F - 1) / 2 := by rw [hFgcd]
            obtain ⟨k, hk⟩ := hhalf_dvd
            have hpowdiv_card : p ^ m - 1 ∣ Nat.card F - 1 := by
              refine ⟨k, ?_⟩
              calc
                Nat.card F - 1 =
                    ((Nat.card F - 1) / 2) * 2 :=
                  (Nat.div_mul_cancel hF_two_dvd).symm
                _ = (((p ^ m - 1) / 2) * k) * 2 := by rw [hk]
                _ = (p ^ m - 1) * k := by
                  rw [mul_assoc, mul_comm k 2, ← mul_assoc,
                    Nat.div_mul_cancel hq_two_dvd]
            have hpowdiv : p ^ m - 1 ∣ p ^ f - 1 := by
              rwa [hFcard] at hpowdiv_card
            exact h826_exponent_dvd_of_pow_sub_one_dvd
              (Fact.out : p.Prime).two_le hpowdiv
          obtain ⟨phi, hphi⟩ :=
            hPGL_embedding hKcard hswap hswap_inf hswap_zero hcover hgen
          have hcharF_ne_two : ringChar F ≠ 2 := by
            rw [ringChar.eq F p]
            exact hp_ne_two
          have hnegF : (-1 : F) ≠ 1 :=
            Ring.neg_one_ne_one_of_char_ne_two hcharF_ne_two
          have hnegK : (-1 : K) ≠ 1 := by
            intro hneg
            apply hnegF
            simpa using congrArg Subtype.val hneg
          have htwoK : (2 : K) ≠ 0 := by
            intro htwo
            apply hnegK
            apply (neg_eq_iff_add_eq_zero).2
            simpa [show (1 : K) + 1 = 2 by norm_num] using htwo
          have hcardH :
              Nat.card H =
                (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) := by
            rw [hhalf.2.2.2, show Nat.gcd (p ^ m - 1) 2 = 2 from
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hq_two_dvd (dvd_refl 2))]
            exact Nat.mul_div_assoc ((p ^ m + 1) * p ^ m)
              hq_two_dvd
          have hPGLcard :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                p ^ m * ((p ^ m) ^ 2 - 1) := by
            rw [h826_card_pgl2, hKcard]
          have hfactor :
              (p ^ m) ^ 2 - 1 = (p ^ m - 1) * (p ^ m + 1) := by
            simpa [mul_comm] using Nat.sq_sub_sq (p ^ m) 1
          have hPGLtwice :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                Nat.card H * 2 := by
            rw [hPGLcard, hfactor, hcardH]
            obtain ⟨r0, hr0⟩ := hq_two_dvd
            rw [hr0]
            simp
            ring
          have hRangeCard :
              Nat.card H = Nat.card phi.range :=
            Nat.card_congr (MonoidHom.ofInjective hphi).toEquiv
          let : Fintype K := Fintype.ofFinite K
          let : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
            Finite.of_surjective Matrix.ProjGenLinGroup.mk
              Matrix.ProjGenLinGroup.mk_surjective
          let : Finite phi.range :=
            Finite.of_injective phi.range.subtype
              phi.range.subtype_injective
          have hphiIndex : phi.range.index = 2 := by
            have hindex := phi.range.index_mul_card
            rw [← hRangeCard, hPGLtwice] at hindex
            apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
            calc
              phi.range.index * Nat.card H = Nat.card H * 2 := hindex
              _ = 2 * Nat.card H := by ring
          have hPSLindex :=
            h826_pslToPGL_range_index_eq_two hnegK
          have hRangeEq :=
            h826_index_two_subgroup_eq_pslRange
              htwoK phi.range hphiIndex hPSLindex
          let eHRange : H ≃* phi.range :=
            MonoidHom.ofInjective hphi
          let ePSLRange :
              PSL2MatrixGroup K ≃*
                (h826_pslToPGL (K := K)).range :=
            MonoidHom.ofInjective h826_pslToPGL_injective
          let eHK : H ≃* PSL2MatrixGroup K :=
            eHRange.trans
              ((MulEquiv.subgroupCongr hRangeEq).trans ePSLRange.symm)
          let eK :=
            GaloisField.algEquivGaloisField p m hKcard
          exact Or.inr (Or.inr
            ⟨hmdiv, ⟨eHK.trans (h826_pslEquiv eK.toRingEquiv)⟩⟩)
      exact Or.inr htwo_torus_core
  have h826_semidirect_structure
      (hcard : Nat.card H =
        Nat.card (Subgroup.normalizer (P : Set H))) :
      ∃ t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤ := by
    have hPnormal : (P : Subgroup H).Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      exact Subgroup.eq_top_of_card_eq
        (H := Subgroup.normalizer (P : Set H)) hcard.symm
    have hPelementary : IsElementaryAbelian p P :=
      h826_sylow_elementary hFcard H P
    have h826_cyclic_complement :
        ∃ C : Subgroup H,
          IsCyclic C ∧ Disjoint (P : Subgroup H) C ∧
            (P : Subgroup H) ⊔ C = ⊤ ∧
            Nat.card C ∣
              (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
            (∀ c : C, c ≠ 1 →
              ∀ x : (P : Subgroup H), x ≠ 1 →
              (c : H) * (x : H) * (c : H)⁻¹ ≠ (x : H)) := by
      classical
      let N : Subgroup H := Subgroup.normalizer (P : Set H)
      have hN : N = Subgroup.normalizer (P : Set H) := rfl
      have hNtop : N = ⊤ := by
        exact Subgroup.eq_top_of_card_eq (H := N) hcard.symm
      have hP_le_N : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
      let PN : Subgroup N := (P : Subgroup H).subgroupOf N
      let : PN.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (by
          simp [N])
      obtain ⟨hquotient_cyclic, hquotient_card_dvd,
          hNormalizer_fixedPointFree, _⟩ :=
        h821_borel_quotient_data hFcard H P
          (by rw [← Subgroup.one_lt_card_iff_ne_bot, hPm]
              exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
                ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero,
                  fun h => hP_nontrivial (hPm.trans h)⟩)
          N hN PN rfl
      have hquotient_card_dvd_sub_one :
          Nat.card (N ⧸ PN) ∣ Nat.card F - 1 :=
        dvd_trans hquotient_card_dvd
          (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
      have hf_ne_zero : f ≠ 0 :=
        huppert_II_8_27_field_exponent_ne_zero hFcard
      have hp_dvd_cardF : p ∣ Nat.card F := by
        rw [hFcard]
        exact dvd_pow_self p hf_ne_zero
      have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
        intro hp_sub
        have hp_one : p ∣ 1 := by
          have hd := Nat.dvd_sub hp_dvd_cardF hp_sub
          have hcard_pos : 0 < Nat.card F := Nat.card_pos
          have hsub : Nat.card F - (Nat.card F - 1) = 1 := by
            omega
          rwa [hsub] at hd
        exact (Fact.out : p.Prime).not_dvd_one hp_one
      have hcop_p_quotient :
          Nat.Coprime p (Nat.card (N ⧸ PN)) :=
        Nat.Coprime.of_dvd_right hquotient_card_dvd_sub_one
          ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
            hp_not_dvd_cardF_sub_one)
      have hPNcard : Nat.card PN = p ^ m := by
        calc
          Nat.card PN = Nat.card P :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
          _ = p ^ m := hPm
      have hPNindex : PN.index = Nat.card (N ⧸ PN) := rfl
      have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
        rw [hPNcard, hPNindex]
        exact hcop_p_quotient.pow_left m
      obtain ⟨CN, hcomp⟩ :=
        Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
      have hCNcyclic : IsCyclic CN := by
        let eC : N ⧸ PN ≃* CN := hcomp.symm.QuotientMulEquiv
        let : IsCyclic (N ⧸ PN) := hquotient_cyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      let C : Subgroup H := CN.map N.subtype
      have hCcyclic : IsCyclic C := by
        let eC : CN ≃* C :=
          Subgroup.equivMapOfInjective CN N.subtype N.subtype_injective
        let : IsCyclic CN := hCNcyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      have hPNmap : PN.map N.subtype = (P : Subgroup H) := by
        exact Subgroup.map_subgroupOf_eq_of_le hP_le_N
      have hdisjoint : Disjoint (P : Subgroup H) C := by
        rw [← hPNmap]
        exact Subgroup.disjoint_map N.subtype_injective hcomp.disjoint
      have hsup : (P : Subgroup H) ⊔ C = ⊤ := by
        rw [← hPNmap, ← Subgroup.map_sup, hcomp.sup_eq_top]
        rw [← MonoidHom.range_eq_map, N.range_subtype, hNtop]
      have hCNcard : Nat.card CN = Nat.card (N ⧸ PN) := by
        calc
          Nat.card CN = PN.index := hcomp.symm.index_eq_card.symm
          _ = Nat.card (N ⧸ PN) := hPNindex
      have hCcard : Nat.card C = Nat.card (N ⧸ PN) := by
        calc
          Nat.card C = Nat.card CN :=
            Subgroup.card_map_of_injective N.subtype_injective
          _ = Nat.card (N ⧸ PN) := hCNcard
      have hCdiv : Nat.card C ∣
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
        rw [hCcard]
        exact hquotient_card_dvd
      have hCfixedPointFree :
          ∀ c : C, c ≠ 1 →
            ∀ x : (P : Subgroup H), x ≠ 1 →
            (c : H) * (x : H) * (c : H)⁻¹ ≠ (x : H) := by
        intro c hc x hx
        rcases c.property with ⟨n, hnCN, hn⟩
        have hnPN : n ∉ PN := by
          intro hnmem
          have hn_one : n = 1 :=
            Subgroup.disjoint_def.mp hcomp.disjoint hnmem hnCN
          apply hc
          apply Subtype.ext
          change (c : H) = 1
          rw [← hn, hn_one]
          rfl
        have hnfree := hNormalizer_fixedPointFree n hnPN x hx
        intro hfix
        apply hnfree
        have hn' : (n : H) = (c : H) := hn
        rw [hn']
        exact hfix
      exact ⟨C, hCcyclic, hdisjoint, hsup, hCdiv,
        hCfixedPointFree⟩
    obtain ⟨C, hCcyclic, hPCdisjoint, hPCsup, hCdiv,
        hCfixedPointFree⟩ :=
      h826_cyclic_complement
    have h826_complement_order_divides_sylow :
        Nat.card C ∣ p ^ m - 1 := by
      let : (P : Subgroup H).Normal := hPnormal
      let : MulDistribMulAction C P :=
        MulDistribMulAction.compHom P
          ((MulAut.conjNormal (H := (P : Subgroup H))).comp C.subtype)
      have hfree :
          ∀ c : C, c ≠ 1 →
            ∀ x : (P : Subgroup H), c • x = x → x = 1 := by
        intro c hc x hfix
        by_contra hx
        have hconj :
            (c : H) * (x : H) * (c : H)⁻¹ = (x : H) := by
          have hconj' := congrArg Subtype.val hfix
          change (c : H) * (x : H) * (c : H)⁻¹ = (x : H) at hconj'
          exact hconj'
        exact hCfixedPointFree c hc x hx hconj
      have hdiv := h826_card_actor_dvd_group_card_sub_one hfree
      rwa [hPm] at hdiv
    have h826_complement_order_divides_ambient :
        Nat.card C ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 := by
      rw [← hFcard]
      exact hCdiv
    exact ⟨Nat.card C, h826_complement_order_divides_sylow,
      h826_complement_order_divides_ambient, P, C, hPnormal,
      hPelementary, hPm, hCcyclic, rfl, hPCdisjoint, hPCsup⟩
  have h826_A5_order_sixty
      (hcard60 : Nat.card H = 60)
      (hSylow5 : Nat.card (Sylow 5 H) = 6)
      (hfaithful : Function.Injective
        (MulAction.toPermHom H (Sylow 5 H))) :
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : FaithfulSMul H (Sylow 5 H) := by
      rw [faithfulSMul_iff]
      intro g hg
      apply hfaithful
      apply DFunLike.ext _ _
      intro Q
      simpa using hg Q
    exact huppert_II_8_25_transitive_degree_six_order_sixty
      (Sylow.isPretransitive_of_finite (p := 5) (G := H)) hSylow5 hcard60
  rcases h826_counting_shapes with hsemidirect | hA5 | hPGL | hPSL
  · obtain ⟨t, ht_subfield, ht_ambient, N, C, hNnormal, hNelem,
      hNcard, hCcyclic, hCcard, hdisjoint, hsup⟩ :=
      h826_semidirect_structure hsemidirect
    exact Or.inl ⟨m, t, ht_subfield, ht_ambient, N, C, hNnormal,
      hNelem, hNcard, hCcyclic, hCcard, hdisjoint, hsup⟩
  · rcases hA5 with
      ⟨hpm3, hcard60, hrestriction, hSylow5, hfaithful⟩
    have hHA5 := h826_A5_order_sixty hcard60 hSylow5 hfaithful
    exact Or.inr (Or.inl ⟨m, hpm3, hrestriction, hHA5⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨m, hm_ne_zero, hPGL.1, hPGL.2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨m, hm_ne_zero, hPSL.1, hPSL.2⟩))

end Dickson
end Glauberman


end Source18

end CFSGPackCase826
