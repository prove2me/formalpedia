-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_22_dickson_counting
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T12:41:49.774982+00:00
-- url     : https://prove2.me/submissions/8e77f930-6513-4379-958f-09317f02f1d3

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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorems.Thm_Glauberman_Dickson_h84_nonsplit_torus_data
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_partition_count_of_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_2_a_sylow_equiv_additive
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_3_split_torus_reflection_data
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_5_a_psl2_partition

set_option autoImplicit false
namespace Glauberman.Dickson
end Glauberman.Dickson
namespace CFSGPackCounting
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

section Source10
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonNonsplitTorus.lean
/-!
# Nonsplit tori in PSL(2,q)

This module isolates Huppert II.8.4 and its quadratic-extension model from the
rest of Dickson's classification.
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise
universe u v

-- Omitted: outside declaration proof/source closure.
set_option maxHeartbeats 1000000 in

/-- Huppert II.8.4(a,b), retaining the Frobenius reflection and its inversion
action on the standard nonsplit torus. -/
theorem huppert_II_8_4_nonsplit_torus_reflection_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      ∃ w : PSL2MatrixGroup F,
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      w ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
      w ∉ S ∧
      w * w = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (S ⊔ Subgroup.zpowers w :
        Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card S ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          S ⊔ Subgroup.zpowers w := by
  obtain ⟨S, hS_cyclic, hS_card, _hS_normalizer,
      ⟨w, hwN, hwS, hwsq, hwinv, hcandidate_card, hnormalizer⟩,
      _hweakTI, _hcover⟩ := h84_nonsplit_torus_data hFcard
  exact ⟨S, w, hS_cyclic, hS_card, hwN, hwS, hwsq, hwinv,
    hcandidate_card, hnormalizer⟩

-- Omitted: outside declaration proof/source closure.

end Dickson
end Glauberman


end Source10

section Source11
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCoprimeOrders.lean
/-!
# Coprime order lemmas for Dickson families
-/

namespace Glauberman
namespace Dickson

universe u

theorem hmem_eq_one_of_coprime_card
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card B))
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) :
    x = 1 := by
  have horder_A : orderOf x ∣ Nat.card A := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxA⟩ : A))
  have horder_B : orderOf x ∣ Nat.card B := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxB⟩ : B))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcoprime horder_A horder_B)

theorem hq_coprime_split_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q - 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_sub_right hq).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (q - 1) 2)

theorem hq_coprime_nonsplit_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q + 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_add_right).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  apply Nat.div_dvd_of_dvd
  convert Nat.dvd_add (Nat.gcd_dvd_left (q - 1) 2)
    (Nat.gcd_dvd_right (q - 1) 2) using 1
  all_goals omega

theorem hsplit_nonsplit_order_coprime (q : ℕ) (hq : 2 ≤ q) :
    Nat.Coprime
      ((q - 1) / Nat.gcd (q - 1) 2)
      ((q + 1) / Nat.gcd (q - 1) 2) := by
  by_cases hq_even : Even q
  · have hq_sub_one_odd : Odd (q - 1) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      have hparity := (Nat.even_sub (by omega : 1 ≤ q)).mp heven
      exact Nat.not_even_one (hparity.mp hq_even)
    have hgcd : Nat.gcd (q - 1) 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
    rw [hgcd]
    simp only [Nat.div_one]
    have hcop : Nat.Coprime (q - 1) ((q - 1) + 2) :=
      (Nat.coprime_self_add_right).mpr hq_sub_one_odd.coprime_two_right
    convert hcop using 1
    all_goals omega
  · have hq_odd : Odd q := Nat.not_even_iff_odd.mp hq_even
    have htwo_dvd : 2 ∣ q - 1 := by
      rcases hq_odd with ⟨k, hk⟩
      use k
      omega
    have hgcd : Nat.gcd (q - 1) 2 = 2 :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
    rcases hq_odd with ⟨k, hk⟩
    rw [hgcd]
    have hsub : q - 1 = 2 * k := by omega
    have hadd : q + 1 = 2 * (k + 1) := by omega
    rw [hsub, hadd]
    rw [Nat.mul_div_cancel_left k (by omega),
      Nat.mul_div_cancel_left (k + 1) (by omega)]
    exact (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right k)

end Dickson
end Glauberman



end Source11

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

theorem huppert_II_8_22_maximal_cyclic_representatives
    {H : Type u} [Group H] [Finite H] (p : ℕ) :
    ∃ (r : ℕ) (Z : Fin r → Subgroup H),
      (∀ i, IsCyclic (Z i)) ∧
      (∀ i, 1 < Nat.card (Z i)) ∧
      (∀ i, Nat.Coprime p (Nat.card (Z i))) ∧
      (∀ i (W : Subgroup H), IsCyclic W → Z i ≤ W → W = Z i) ∧
      (∀ W : Subgroup H, IsCyclic W → 1 < Nat.card W →
        Nat.Coprime p (Nat.card W) →
        (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
        ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j g,
        (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) := by
  classical
  let : MulAction H (Subgroup H) :=
    { smul := fun g W => W.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro W
        change W.map (MulAut.conj (1 : H)).toMonoidHom = W
        have h :
            (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H := by
          ext x
          simp
        rw [h, Subgroup.map_id]
      mul_smul := by
        intro g h W
        change W.map (MulAut.conj (g * h)).toMonoidHom =
          (W.map (MulAut.conj h).toMonoidHom).map
            (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have hcyclic_smul (g : H) (W : Subgroup H)
      (hW : IsCyclic W) : IsCyclic ↥(g • W : Subgroup H) := by
    let e : W ≃* ↥(g • W : Subgroup H) :=
      (MulAut.conj g).subgroupMap W
    let : IsCyclic W := hW
    rcases IsCyclic.exists_zpow_surjective (G := W) with ⟨x, hx⟩
    apply IsCyclic.mk
    refine ⟨e x, ?_⟩
    intro y
    obtain ⟨n, hn⟩ := hx (e.symm y)
    refine ⟨n, ?_⟩
    change (e x) ^ n = y
    rw [← map_zpow]
    simpa using congrArg e hn
  have hcard_smul (g : H) (W : Subgroup H) :
      Nat.card ↥(g • W : Subgroup H) = Nat.card W := by
    let e : W ≃* ↥(g • W : Subgroup H) :=
      (MulAut.conj g).subgroupMap W
    exact (Nat.card_congr e.toEquiv).symm
  have helig_smul (g : H) (W : Subgroup H)
      (hW : IsCyclic W ∧ 1 < Nat.card W ∧
        Nat.Coprime p (Nat.card W) ∧
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) :
      IsCyclic ↥(g • W : Subgroup H) ∧
        1 < Nat.card ↥(g • W : Subgroup H) ∧
        Nat.Coprime p (Nat.card ↥(g • W : Subgroup H)) ∧
        ∀ V : Subgroup H, IsCyclic V →
          (g • W : Subgroup H) ≤ V → V = (g • W : Subgroup H) := by
    refine ⟨hcyclic_smul g W hW.1, ?_, ?_, ?_⟩
    · simpa [hcard_smul g W] using hW.2.1
    · simpa [hcard_smul g W] using hW.2.2.1
    · intro V hV hle
      have hback_cyclic : IsCyclic ↥(g⁻¹ • V : Subgroup H) :=
        hcyclic_smul g⁻¹ V hV
      have hback_le : W ≤ (g⁻¹ • V : Subgroup H) := by
        have hmap := Subgroup.map_mono
          (f := (MulAut.conj g⁻¹).toMonoidHom) hle
        change (g⁻¹ • (g • W) : Subgroup H) ≤
          (g⁻¹ • V : Subgroup H) at hmap
        simpa using hmap
      have heq : (g⁻¹ • V : Subgroup H) = W :=
        hW.2.2.2 (g⁻¹ • V : Subgroup H) hback_cyclic hback_le
      have hfront := congrArg (fun T : Subgroup H => g • T) heq
      simpa using hfront
  let C := {W : Subgroup H //
    IsCyclic W ∧ 1 < Nat.card W ∧ Nat.Coprime p (Nat.card W) ∧
      ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W}
  let : MulAction H C :=
    { smul := fun g W =>
        ⟨g • (W : Subgroup H), helig_smul g W W.property⟩
      one_smul := by
        intro W
        apply Subtype.ext
        exact one_smul H (W : Subgroup H)
      mul_smul := by
        intro g h W
        apply Subtype.ext
        exact mul_smul g h (W : Subgroup H) }
  let O := Quotient (MulAction.orbitRel H C)
  let : Fintype O := Fintype.ofFinite O
  let r := Fintype.card O
  let e : Fin r ≃ O := (Fintype.equivFin O).symm
  let Z : Fin r → Subgroup H := fun i => ((e i).out : C)
  refine ⟨r, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((e i).out : C).property.1
  · intro i
    exact ((e i).out : C).property.2.1
  · intro i
    exact ((e i).out : C).property.2.2.1
  · intro i W hW hle
    exact ((e i).out : C).property.2.2.2 W hW hle
  · intro W hW hWcard hWcop hWmax
    let c : C := ⟨W, hW, hWcard, hWcop, hWmax⟩
    let q : O := Quotient.mk (MulAction.orbitRel H C) c
    let i : Fin r := e.symm q
    have heq : e i = q := by simp [i]
    have hquot :
        Quotient.mk (MulAction.orbitRel H C) (e i).out =
          Quotient.mk (MulAction.orbitRel H C) c := by
      rw [Quotient.out_eq, heq]
    have hrel :
        (e i).out ∈ MulAction.orbit H c :=
      Quotient.exact hquot
    rcases MulAction.mem_orbit_iff.mp hrel with ⟨g, hg⟩
    refine ⟨i, g⁻¹, ?_⟩
    have hgval :
        (g • W : Subgroup H) = Z i := by
      have hg' := congrArg Subtype.val hg
      change (g • W : Subgroup H) = ((e i).out : C) at hg'
      exact hg'
    have hback :=
      congrArg (fun T : Subgroup H => g⁻¹ • T) hgval
    change W = (g⁻¹ • Z i : Subgroup H)
    simpa using hback
  · intro i j g hg
    let ci : C := (e i).out
    let cj : C := (e j).out
    have hgc : g • ci = cj := by
      apply Subtype.ext
      exact hg
    have hrel : ci ∈ MulAction.orbit H cj := by
      rw [MulAction.mem_orbit_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [← hgc]
      simp
    have hq : e i = e j := by
      calc
        e i = Quotient.mk (MulAction.orbitRel H C) ci :=
          (Quotient.out_eq (e i)).symm
        _ = Quotient.mk (MulAction.orbitRel H C) cj :=
          Quotient.sound hrel
        _ = e j := Quotient.out_eq (e j)
    exact e.injective hq

theorem cyclic_le_unique_partition_family
    {G : Type*} [Group G]
    (Family : Subgroup G → Prop)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T)
    {x : G} (hx : x ≠ 1)
    {T V : Subgroup G}
    (hxT : x ∈ T) (hTfamily : Family T)
    (hxV : x ∈ V) (hVcyclic : IsCyclic V) :
    V ≤ T := by
  let : IsCyclic V := hVcyclic
  rcases IsCyclic.exists_zpow_surjective (G := V) with ⟨v, hv⟩
  have hv_ne : (v : G) ≠ 1 := by
    intro hv_one
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v ^ n : V) = ⟨x, hxV⟩ := hn
    have hnval' := congrArg Subtype.val hnval
    change ((v : G) ^ n) = x at hnval'
    simp [hv_one] at hnval'
    exact hx hnval'.symm
  obtain ⟨Tv, hvTv, _hTv_unique⟩ := hpartition (v : G) hv_ne
  have hxTv : x ∈ Tv := by
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v : G) ^ n = x := congrArg Subtype.val hn
    have hvpow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
    rwa [hnval] at hvpow
  have hTvT : Tv = T :=
    (hpartition x hx).unique ⟨hxTv, hvTv.2⟩ ⟨hxT, hTfamily⟩
  intro y hyV
  obtain ⟨n, hn⟩ := hv ⟨y, hyV⟩
  have hnval : (v : G) ^ n = y := congrArg Subtype.val hn
  have hypow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
  rw [hTvT, hnval] at hypow
  exact hypow

private theorem equiv_torus_reflection_data
    {G : Type u} [Group G] [Finite G]
    (T0 : Subgroup G) (w0 : G)
    (hcyclic0 : IsCyclic T0)
    (hw0_normalizer : w0 ∈ Subgroup.normalizer (T0 : Set G))
    (hw0_not_mem : w0 ∉ T0) (hw0_sq : w0 * w0 = 1)
    (hw0_inv : ∀ t : G, t ∈ T0 → w0 * t * w0⁻¹ = t⁻¹)
    (hcard0 : Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) =
      2 * Nat.card T0)
    (hnormalizer0 : ∀ R : Subgroup G, R ≤ T0 → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T0 ⊔ Subgroup.zpowers w0)
    (e : G ≃* G) :
    let T := T0.map e.toMonoidHom
    let w := e w0
    IsCyclic T ∧
      w ∈ Subgroup.normalizer (T : Set G) ∧
      w ∉ T ∧
      w * w = 1 ∧
      (∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (T ⊔ Subgroup.zpowers w : Subgroup G) = 2 * Nat.card T ∧
      ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
        Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w := by
  dsimp only
  have hcyclic : IsCyclic (T0.map e.toMonoidHom) := by
    let : IsCyclic T0 := hcyclic0
    exact isCyclic_of_surjective (e.subgroupMap T0).toMonoidHom
      (e.subgroupMap T0).surjective
  have hw_normalizer :
      e w0 ∈ Subgroup.normalizer (T0.map e.toMonoidHom : Set G) := by
    have hw_map : e w0 ∈
        (Subgroup.normalizer (T0 : Set G)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hw0_normalizer
    rwa [Subgroup.map_equiv_normalizer_eq T0 e] at hw_map
  have hw_not_mem : e w0 ∉ T0.map e.toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    simpa using hw0_not_mem
  have hw_sq : e w0 * e w0 = 1 := by
    simpa using congrArg e hw0_sq
  have hw_inv : ∀ t : G, t ∈ T0.map e.toMonoidHom →
      e w0 * t * (e w0)⁻¹ = t⁻¹ := by
    intro t ht
    have ht0 : e.symm t ∈ T0 :=
      Subgroup.mem_map_equiv.mp ht
    simpa using congrArg e (hw0_inv (e.symm t) ht0)
  have hcard : Nat.card
      (T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) : Subgroup G) =
      2 * Nat.card (T0.map e.toMonoidHom) := by
    have heq : (T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom =
        T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) := by
      simpa using
        (Subgroup.map_sup T0 (Subgroup.zpowers w0) e.toMonoidHom).trans
          (congrArg (fun K : Subgroup G => T0.map e.toMonoidHom ⊔ K)
            (MonoidHom.map_zpowers e.toMonoidHom w0))
    calc
      Nat.card (T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) : Subgroup G) =
          Nat.card ((T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom) :=
        congrArg (fun K : Subgroup G => Nat.card K) heq.symm
      _ = Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) := by
        rw [Subgroup.card_map_of_injective e.injective]
      _ = 2 * Nat.card (T0 : Subgroup G) := hcard0
      _ = 2 * Nat.card (T0.map e.toMonoidHom) := by
        rw [Subgroup.card_map_of_injective e.injective]
  refine ⟨hcyclic, hw_normalizer, hw_not_mem, hw_sq, hw_inv, hcard, ?_⟩
  intro R hR_le hR_ne
  let R0 : Subgroup G := R.map e.symm.toMonoidHom
  have hR0_le : R0 ≤ T0 := by
    intro x hx
    have hex : e x ∈ R := by
      change x ∈ R.map e.symm.toMonoidHom at hx
      rwa [Subgroup.mem_map_equiv] at hx
    have hexT : e x ∈ T0.map e.toMonoidHom := hR_le hex
    rw [Subgroup.mem_map_equiv] at hexT
    simpa using hexT
  have hR0_ne : R0 ≠ ⊥ := by
    intro hR0
    apply hR_ne
    apply (Subgroup.map_eq_bot_iff_of_injective R
      (f := e.symm.toMonoidHom) e.symm.injective).mp
    exact hR0
  have hR0_map : R0.map e.toMonoidHom = R := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := R0) (e := e)).mp
    rfl
  have hmap := congrArg
    (fun K : Subgroup G => K.map e.toMonoidHom)
    (hnormalizer0 R0 hR0_le hR0_ne)
  change (Subgroup.normalizer (R0 : Set G)).map e.toMonoidHom =
    (T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom at hmap
  rw [Subgroup.map_equiv_normalizer_eq R0 e, hR0_map,
    Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
  exact hmap

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

private theorem mulEquiv_dihedral_of_cyclic_reflection
    {G : Type u} [Group G] [Finite G]
    (C : Subgroup G) (hC : IsCyclic C) (w : G)
    (hw_not_mem : w ∉ C) (hw_sq : w * w = 1)
    (hw_inv : ∀ c : G, c ∈ C → w * c * w⁻¹ = c⁻¹)
    (hindex : C.index = 2) :
    Nonempty (G ≃* DihedralGroup (Nat.card C)) := by
  classical
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C :=
    zmodCyclicMulEquiv hC
  let rot : ZMod (Nat.card C) → G := fun i =>
    (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C :=
    (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) :
      rot (i + j) = rot i * rot j := by
    exact congrArg Subtype.val (e.map_mul
      (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) :
      rot (-i) = (rot i)⁻¹ := by
    exact congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := by
    exact congrArg Subtype.val e.map_one
  have hw_inv_eq : w⁻¹ = w :=
    (eq_inv_of_mul_eq_one_left hw_sq).symm
  have hw_mul_rot (i : ZMod (Nat.card C)) :
      w * rot i = rot (-i) * w := by
    calc
      w * rot i = (w * rot i * w⁻¹) * w := by
        rw [hw_inv_eq, mul_assoc, hw_sq, mul_one]
      _ = (rot i)⁻¹ * w := by rw [hw_inv (rot i) (hrot_mem i)]
      _ = rot (-i) * w := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) :
      rot i * w = w * rot (-i) := by
    calc
      rot i * w = rot (-(-i)) * w := by rw [neg_neg]
      _ = w * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* G :=
    { toFun := fun x => match x with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => w * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change w * rot (j - i) = rot i * (w * rot j)
          calc
            w * rot (j - i) = w * rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = w * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (w * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * w) * rot j := by rw [hrot_mul_w]
            _ = rot i * (w * rot j) := by rw [mul_assoc]
        · change w * rot (i + j) = (w * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (w * rot i) * (w * rot j)
          calc
            rot (j - i) = rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (w * rot i) * (w * rot j) := by
              calc
                rot (-i) * rot j = (w * w) * (rot (-i) * rot j) := by
                  rw [hw_sq, one_mul]
                _ = (w * (w * rot (-i))) * rot j := by
                  simp only [mul_assoc]
                _ = (w * (rot i * w)) * rot j := by
                  rw [hrot_mul_w]
                _ = (w * rot i) * (w * rot j) := by
                  simp only [mul_assoc] }
  have hhom_injective : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact hij
      exact congrArg Multiplicative.toAdd heq
    · exfalso
      apply hw_not_mem
      change rot i = w * rot j at hij
      have hwrj : w * rot j ∈ C := by
        rw [← hij]
        exact hrot_mem i
      exact (C.mul_mem_cancel_right (hrot_mem j)).mp hwrj
    · exfalso
      apply hw_not_mem
      change w * rot i = rot j at hij
      have hwri : w * rot i ∈ C := by
        rw [hij]
        exact hrot_mem j
      exact (C.mul_mem_cancel_right (hrot_mem i)).mp hwri
    · apply congrArg DihedralGroup.sr
      change w * rot i = w * rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact mul_left_cancel hij
      exact congrArg Multiplicative.toAdd heq
  have hhom_surjective : Function.Surjective hom := by
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      refine ⟨DihedralGroup.r i.toAdd, ?_⟩
      exact congrArg Subtype.val hi
    · have hxw : w * x ∈ C := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        simp [hw_not_mem, hx]
      obtain ⟨i, hi⟩ := e.surjective ⟨w * x, hxw⟩
      refine ⟨DihedralGroup.sr i.toAdd, ?_⟩
      change w * rot i.toAdd = x
      have hi' : rot i.toAdd = w * x := congrArg Subtype.val hi
      rw [hi', ← mul_assoc, hw_sq, one_mul]
  exact ⟨(MulEquiv.ofBijective hom
    ⟨hhom_injective, hhom_surjective⟩).symm⟩

private theorem outside_reflection_of_mem_sup
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) (hT : IsCyclic T) (w g : G)
    (hw_not_mem : w ∉ T) (hw_sq : w * w = 1)
    (hw_inv : ∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹)
    (hg : g ∈ T ⊔ Subgroup.zpowers w) (hg_not_mem : g ∉ T) :
    g * g = 1 ∧ ∀ t : G, t ∈ T → g * t * g⁻¹ = t⁻¹ := by
  let : IsCyclic T := hT
  have hw_inv_eq : w⁻¹ = w :=
    (eq_inv_of_mul_eq_one_left hw_sq).symm
  have hw_ne_one : w ≠ 1 := by
    intro hw
    apply hw_not_mem
    rw [hw]
    exact T.one_mem
  have horder : orderOf w = 2 := by
    have hpow : w ^ 2 = 1 := by simpa [pow_two] using hw_sq
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact (hw_ne_one (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hw_normalizer : w ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hw_inv y hy]
      exact T.inv_mem hy
    · intro hy
      have hdouble : w * (w * y * w⁻¹) * w⁻¹ ∈ T := by
        rw [hw_inv (w * y * w⁻¹) hy]
        exact T.inv_mem hy
      have heq : w * (w * y * w⁻¹) * w⁻¹ = y := by
        calc
          w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w) := by
            rw [hw_inv_eq]
            group
          _ = y := by simp [hw_sq]
      rwa [heq] at hdouble
  have hz_normalizer :
      Subgroup.zpowers w ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.2 hw_normalizer
  have hproduct :
      ((Subgroup.zpowers w : Subgroup G) : Set G) * (T : Set G) =
        (T ⊔ Subgroup.zpowers w : Subgroup G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers w) T hz_normalizer, sup_comm]
  have hg_product :
      g ∈ ((Subgroup.zpowers w : Subgroup G) : Set G) * (T : Set G) := by
    rw [hproduct]
    exact hg
  rcases hg_product with ⟨z, hz, t, ht, hzt⟩
  change z * t = g at hzt
  have hz_eq_one_or_w : z = 1 ∨ z = w := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk]
    have hmod := Int.emod_two_eq_zero_or_one k
    have hreduce : w ^ (k % (orderOf w : ℤ)) = w ^ k :=
      zpow_mod_orderOf w k
    rw [horder] at hreduce
    rcases hmod with hmod | hmod
    · left
      calc
        w ^ k = w ^ (k % (2 : ℤ)) := hreduce.symm
        _ = 1 := by rw [hmod, zpow_zero]
    · right
      calc
        w ^ k = w ^ (k % (2 : ℤ)) := hreduce.symm
        _ = w := by rw [hmod, zpow_one]
  have hz_eq_w : z = w := by
    rcases hz_eq_one_or_w with hz_one | hz_w
    · exfalso
      apply hg_not_mem
      rw [hz_one, one_mul] at hzt
      rwa [← hzt]
    · exact hz_w
  subst z
  have hg_eq : g = w * t := hzt.symm
  have hwt : w * t = t⁻¹ * w := by
    calc
      w * t = (w * t * w⁻¹) * w := by
        rw [hw_inv_eq, mul_assoc, hw_sq, mul_one]
      _ = t⁻¹ * w := by rw [hw_inv t ht]
  constructor
  · rw [hg_eq]
    calc
      (w * t) * (w * t) = (w * t) * (t⁻¹ * w) :=
        congrArg (fun x => (w * t) * x) hwt
      _ = w * (t * t⁻¹) * w := by group
      _ = w * w := by rw [mul_inv_cancel, mul_one]
      _ = 1 := hw_sq
  · intro y hy
    have hcomm : t * y = y * t := setLike_mul_comm ht hy
    rw [hg_eq, mul_inv_rev]
    calc
      w * t * y * (t⁻¹ * w⁻¹) =
          w * (t * y * t⁻¹) * w⁻¹ := by simp only [mul_assoc]
      _ = w * y * w⁻¹ := by rw [hcomm]; simp [mul_assoc]
      _ = y⁻¹ := hw_inv y hy

/-- The torus-normalizer part of Huppert II.8.22. -/
theorem huppert_II_8_22_torus_normalizer_data
    {F : Type u} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i) :
    ∃ s : Fin r → ℕ,
      (∀ i, 0 < s i ∧ s i ≤ 2) ∧
      (∀ i, Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i) ∧
      (∀ i, s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      (∀ i,
        (Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
  classical
  let P0 : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P0
  let Family : Subgroup (PSL2MatrixGroup F) → Prop := fun T =>
    (∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : PSL2MatrixGroup F, x ≠ 1 →
      ∃! T : Subgroup (PSL2MatrixGroup F), x ∈ T ∧ Family T := by
    simpa [Family] using hpartition
  obtain ⟨U0, wU0, hU0cyclic, hU0card, hwU0N, hwU0T,
      hwU0sq, hwU0inv, hU0candidate, hU0normalizer⟩ :=
    huppert_II_8_3_split_torus_reflection_data hFcard
  obtain ⟨S0, wS0, hS0cyclic, hS0card, hwS0N, hwS0T,
      hwS0sq, hwS0inv, hS0candidate, hS0normalizer⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data hFcard
  have hP0card :
      Nat.card (P0 : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P0
    exact (Nat.card_congr eP.toEquiv).symm
  have hU0cardU : Nat.card U0 = Nat.card U := hU0card.trans hUcard.symm
  have hS0cardS : Nat.card S0 = Nat.card S := hS0card.trans hScard.symm
  have hUalign : ∃ g : PSL2MatrixGroup F,
      U0 = U.map (MulAut.conj g).toMonoidHom := by
    by_cases hUbot : U = ⊥
    · have hbotU0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = U0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hU0cardU, hUbot]
      refine ⟨1, ?_⟩
      rw [← hbotU0, hUbot]
      simp
    · have hU0ne : U0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hU0cardU]
        exact (Subgroup.one_lt_card_iff_ne_bot U).2 hUbot
      obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU0ne
      have huG : (u : PSL2MatrixGroup F) ≠ 1 := by
        intro hu
        apply hu_ne
        apply Subtype.ext
        exact hu
      obtain ⟨T, huT, hTfamily⟩ :=
        (hpartition' (u : PSL2MatrixGroup F) huG).exists
      have hU0leT : U0 ≤ T :=
        cyclic_le_unique_partition_family Family hpartition'
          huG huT hTfamily u.property hU0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hP0card, hU0card]
          exact (hq_coprime_split_order
            (Nat.card F) Nat.card_pos).symm
        exact huG (hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
      · refine ⟨g, ?_⟩
        calc
          U0 = T := Subgroup.eq_of_le_of_card_ge hU0leT (by
            rw [hTg, Subgroup.card_map_of_injective
              (MulAut.conj g).injective, hU0cardU])
          _ = U.map (MulAut.conj g).toMonoidHom := hTg
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hScard, hU0card]
          exact hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))
        exact huG (hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
  have hSalign : ∃ g : PSL2MatrixGroup F,
      S0 = S.map (MulAut.conj g).toMonoidHom := by
    by_cases hSbot : S = ⊥
    · have hbotS0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = S0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hS0cardS, hSbot]
      refine ⟨1, ?_⟩
      rw [← hbotS0, hSbot]
      simp
    · have hS0ne : S0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hS0cardS]
        exact (Subgroup.one_lt_card_iff_ne_bot S).2 hSbot
      obtain ⟨s0, hs0_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS0ne
      have hs0G : (s0 : PSL2MatrixGroup F) ≠ 1 := by
        intro hs0
        apply hs0_ne
        apply Subtype.ext
        exact hs0
      obtain ⟨T, hs0T, hTfamily⟩ :=
        (hpartition' (s0 : PSL2MatrixGroup F) hs0G).exists
      have hS0leT : S0 ≤ T :=
        cyclic_le_unique_partition_family Family hpartition'
          hs0G hs0T hTfamily s0.property hS0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hP0card, hS0card]
          exact (hq_coprime_nonsplit_order
            (Nat.card F) Nat.card_pos).symm
        exact hs0G (hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hUcard, hS0card]
          exact (hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))).symm
        exact hs0G (hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · refine ⟨g, ?_⟩
        calc
          S0 = T := Subgroup.eq_of_le_of_card_ge hS0leT (by
            rw [hTg, Subgroup.card_map_of_injective
              (MulAut.conj g).injective, hS0cardS])
          _ = S.map (MulAut.conj g).toMonoidHom := hTg
  obtain ⟨gU, hUalign⟩ := hUalign
  obtain ⟨gS, hSalign⟩ := hSalign
  let eU : PSL2MatrixGroup F ≃* PSL2MatrixGroup F := (MulAut.conj gU).symm
  let eS : PSL2MatrixGroup F ≃* PSL2MatrixGroup F := (MulAut.conj gS).symm
  let wU : PSL2MatrixGroup F := eU wU0
  let wS : PSL2MatrixGroup F := eS wS0
  have hUback : U0.map eU.toMonoidHom = U := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := U)
      (e := MulAut.conj gU)).mpr
    exact hUalign.symm
  have hSback : S0.map eS.toMonoidHom = S := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := S)
      (e := MulAut.conj gS)).mpr
    exact hSalign.symm
  have hUdata :
      IsCyclic U ∧
      wU ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      wU ∉ U ∧
      wU * wU = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U → wU * t * wU⁻¹ = t⁻¹) ∧
      Nat.card (U ⊔ Subgroup.zpowers wU : Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card U ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          U ⊔ Subgroup.zpowers wU := by
    have h := equiv_torus_reflection_data U0 wU0 hU0cyclic hwU0N hwU0T
      hwU0sq hwU0inv hU0candidate hU0normalizer eU
    change IsCyclic (U0.map eU.toMonoidHom) ∧
      wU ∈ Subgroup.normalizer
        (U0.map eU.toMonoidHom : Set (PSL2MatrixGroup F)) ∧
      wU ∉ U0.map eU.toMonoidHom ∧
      wU * wU = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U0.map eU.toMonoidHom →
        wU * t * wU⁻¹ = t⁻¹) ∧
      Nat.card (U0.map eU.toMonoidHom ⊔ Subgroup.zpowers wU :
        Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card (U0.map eU.toMonoidHom) ∧
      ∀ R : Subgroup (PSL2MatrixGroup F),
        R ≤ U0.map eU.toMonoidHom → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            U0.map eU.toMonoidHom ⊔ Subgroup.zpowers wU at h
    rwa [hUback] at h
  have hSdata :
      IsCyclic S ∧
      wS ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
      wS ∉ S ∧
      wS * wS = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S → wS * t * wS⁻¹ = t⁻¹) ∧
      Nat.card (S ⊔ Subgroup.zpowers wS : Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card S ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          S ⊔ Subgroup.zpowers wS := by
    have h := equiv_torus_reflection_data S0 wS0 hS0cyclic hwS0N hwS0T
      hwS0sq hwS0inv hS0candidate hS0normalizer eS
    change IsCyclic (S0.map eS.toMonoidHom) ∧
      wS ∈ Subgroup.normalizer
        (S0.map eS.toMonoidHom : Set (PSL2MatrixGroup F)) ∧
      wS ∉ S0.map eS.toMonoidHom ∧
      wS * wS = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S0.map eS.toMonoidHom →
        wS * t * wS⁻¹ = t⁻¹) ∧
      Nat.card (S0.map eS.toMonoidHom ⊔ Subgroup.zpowers wS :
        Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card (S0.map eS.toMonoidHom) ∧
      ∀ R : Subgroup (PSL2MatrixGroup F),
        R ≤ S0.map eS.toMonoidHom → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            S0.map eS.toMonoidHom ⊔ Subgroup.zpowers wS at h
    rwa [hSback] at h
  rcases hUdata with
    ⟨hUcyclic', hwUN, hwUT, hwUsq, hwUinv, hUcandidate, hUnormalizer⟩
  rcases hSdata with
    ⟨hScyclic', hwSN, hwST, hwSsq, hwSinv, hScandidate, hSnormalizer⟩
  have hmap_subtype_cyclic (A : Subgroup H) (hA : IsCyclic A) :
      IsCyclic (A.map H.subtype) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective A H.subtype H.subtype_injective)).mp hA
  have hcomap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) : IsCyclic (A.comap H.subtype) := by
    let : IsCyclic A := hA
    have hmap_cyclic' : IsCyclic ((A.comap H.subtype).map H.subtype) :=
      Subgroup.isCyclic_of_le (Subgroup.map_comap_le H.subtype A)
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        (A.comap H.subtype) H.subtype H.subtype_injective)).mpr hmap_cyclic'
  have hambient (i : Fin r) :
      ∃ T : Subgroup (PSL2MatrixGroup F),
        ∃ w : PSL2MatrixGroup F,
        (IsCyclic T ∧
          w ∈ Subgroup.normalizer (T : Set (PSL2MatrixGroup F)) ∧
          w ∉ T ∧
          w * w = 1 ∧
          (∀ t : PSL2MatrixGroup F, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
          Nat.card (T ⊔ Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) =
            2 * Nat.card T ∧
          ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ T → R ≠ ⊥ →
            Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
              T ⊔ Subgroup.zpowers w) ∧
        (Z i).map H.subtype ≤ T ∧
        T.comap H.subtype = Z i ∧
        ((Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
    let A : Subgroup (PSL2MatrixGroup F) := (Z i).map H.subtype
    have hZi_ne : Z i ≠ ⊥ :=
      (Subgroup.one_lt_card_iff_ne_bot (Z i)).mp (hnontrivial i)
    have hA_ne : A ≠ ⊥ := by
      intro hA
      apply hZi_ne
      apply (Subgroup.map_eq_bot_iff_of_injective (Z i)
        (f := H.subtype) H.subtype_injective).mp
      exact hA
    have hAcyclic : IsCyclic A := hmap_subtype_cyclic (Z i) (hcyclic i)
    obtain ⟨a, ha_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA_ne
    have haG : (a : PSL2MatrixGroup F) ≠ 1 := by
      intro ha
      apply ha_ne
      apply Subtype.ext
      exact ha
    obtain ⟨T, haT, hTfamily⟩ :=
      (hpartition' (a : PSL2MatrixGroup F) haG).exists
    have hA_le_T : A ≤ T :=
      cyclic_le_unique_partition_family Family hpartition'
        haG haT hTfamily a.property hAcyclic
    have hTcomap (hTcyclic : IsCyclic T) : T.comap H.subtype = Z i := by
      have hWcyclic : IsCyclic (T.comap H.subtype) :=
        hcomap_cyclic T hTcyclic
      have hZ_le : Z i ≤ T.comap H.subtype :=
        Subgroup.map_le_iff_le_comap.mp hA_le_T
      exact hmaximal i (T.comap H.subtype) hWcyclic hZ_le
    rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
    · exfalso
      have hcop : Nat.Coprime (Nat.card A) (Nat.card T) := by
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hP0card, hFcard]
        exact ((hcoprime i).pow_left f).symm
      exact haG (hmem_eq_one_of_coprime_card A T hcop
        a.property (hA_le_T a.property))
    · let w : PSL2MatrixGroup F := MulAut.conj g wU
      have hTdata := equiv_torus_reflection_data U wU hUcyclic' hwUN hwUT
        hwUsq hwUinv hUcandidate hUnormalizer (MulAut.conj g)
      rw [← hTg] at hTdata
      refine ⟨T, w, hTdata, hA_le_T, hTcomap hTdata.1, Or.inl ?_⟩
      · have hdvd := Subgroup.card_dvd_of_le hA_le_T
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hUcard] at hdvd
        exact hdvd
    · let w : PSL2MatrixGroup F := MulAut.conj g wS
      have hTdata := equiv_torus_reflection_data S wS hScyclic' hwSN hwST
        hwSsq hwSinv hScandidate hSnormalizer (MulAut.conj g)
      rw [← hTg] at hTdata
      refine ⟨T, w, hTdata, hA_le_T, hTcomap hTdata.1, Or.inr ?_⟩
      · have hdvd := Subgroup.card_dvd_of_le hA_le_T
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hScard] at hdvd
        exact hdvd
  let s : Fin r → ℕ := fun i =>
    (Z i).relIndex (Subgroup.normalizer (Z i : Set H))
  have hlocal (i : Fin r) :
      (0 < s i ∧ s i ≤ 2) ∧
      Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i ∧
      (s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      ((Nat.card (Z i) ∣
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (Nat.card (Z i) ∣
          (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
    obtain ⟨T, w, hdata, hA_le_T, hTcomap, hdvd⟩ := hambient i
    rcases hdata with
      ⟨hTcyclic, _hwN, hwT, hwsq, hwinv, hcandidate_card, hnormalizer⟩
    let A : Subgroup (PSL2MatrixGroup F) := (Z i).map H.subtype
    let B : Subgroup (PSL2MatrixGroup F) :=
      (Subgroup.normalizer (Z i : Set H)).map H.subtype
    let N : Subgroup (PSL2MatrixGroup F) := T ⊔ Subgroup.zpowers w
    have hA_ne : A ≠ ⊥ := by
      intro hA
      have hZi_bot : Z i = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (Z i)
          (f := H.subtype) H.subtype_injective).mp hA
      exact (hnontrivial i).ne (by rw [hZi_bot]; simp)
    have hB_le : B ≤ N := by
      have hmap : B ≤ Subgroup.normalizer (A : Set (PSL2MatrixGroup F)) :=
        Subgroup.le_normalizer_map H.subtype
      rw [hnormalizer A hA_le_T hA_ne] at hmap
      exact hmap
    have hinter : T ⊓ B = A := by
      apply le_antisymm
      · intro x hx
        rcases hx.2 with ⟨y, hyN, rfl⟩
        have hyT : y ∈ T.comap H.subtype := hx.1
        rw [hTcomap] at hyT
        exact ⟨y, hyT, rfl⟩
      · exact le_inf hA_le_T
          (Subgroup.map_mono Subgroup.le_normalizer)
    have hTindex : T.relIndex N = 2 :=
      relIndex_eq_two_of_card_eq_two_mul T N le_sup_left hcandidate_card
    have hambient_index : A.relIndex B ≤ 2 :=
      relIndex_le_two_of_inter_eq T B N A hB_le hinter hTindex
    have hs_eq : s i = A.relIndex B := by
      exact (Subgroup.relIndex_map_map_of_injective
        (Z i) (Subgroup.normalizer (Z i : Set H))
        H.subtype_injective).symm
    have hs_pos : 0 < s i := by
      rw [hs_eq, Subgroup.relIndex]
      exact Nat.card_pos
    have hs_le : s i ≤ 2 := by
      rw [hs_eq]
      exact hambient_index
    let NH : Subgroup H := Subgroup.normalizer (Z i : Set H)
    let C : Subgroup NH := (Z i).subgroupOf NH
    let eC : C ≃* Z i :=
      Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
    have hCcard : Nat.card C = Nat.card (Z i) :=
      Nat.card_congr eC.toEquiv
    have hnormalizer_card :
        Nat.card (Subgroup.normalizer (Z i : Set H)) =
          Nat.card (Z i) * s i := by
      calc
        Nat.card (Subgroup.normalizer (Z i : Set H)) = Nat.card NH := rfl
        _ = Nat.card C * C.index := C.card_mul_index.symm
        _ = Nat.card (Z i) * s i := by
          rw [hCcard]
          rfl
    have hdihedral (hs_two : s i = 2) :
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i))) := by
      have hCindex : C.index = 2 := by
        change ((Z i).subgroupOf
          (Subgroup.normalizer (Z i : Set H))).index = 2
        exact hs_two
      obtain ⟨a, ha_not, _ha_cosets⟩ :=
        Subgroup.index_eq_two_iff_exists_notMem_and.mp hCindex
      have haB : (((a : NH) : H) : PSL2MatrixGroup F) ∈ B :=
        ⟨((a : NH) : H), a.property, rfl⟩
      have haN : (((a : NH) : H) : PSL2MatrixGroup F) ∈ N := hB_le haB
      have ha_not_T : (((a : NH) : H) : PSL2MatrixGroup F) ∉ T := by
        intro haT
        have ha_comap : ((a : NH) : H) ∈ T.comap H.subtype := haT
        rw [hTcomap] at ha_comap
        apply ha_not
        exact ha_comap
      obtain ⟨ha_sq_ambient, ha_inv_ambient⟩ :=
        outside_reflection_of_mem_sup T hTcyclic w
          (((a : NH) : H) : PSL2MatrixGroup F)
          hwT hwsq hwinv haN ha_not_T
      have ha_sq : a * a = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact ha_sq_ambient
      have ha_inv : ∀ c : NH, c ∈ C → a * c * a⁻¹ = c⁻¹ := by
        intro c hc
        apply Subtype.ext
        apply Subtype.ext
        apply ha_inv_ambient
        apply hA_le_T
        exact ⟨((c : NH) : H), hc, rfl⟩
      have hCcyclic : IsCyclic C :=
        (MulEquiv.isCyclic eC).mpr (hcyclic i)
      have hdih := mulEquiv_dihedral_of_cyclic_reflection
        C hCcyclic a ha_not ha_sq ha_inv hCindex
      rw [hCcard] at hdih
      exact hdih
    exact ⟨⟨hs_pos, hs_le⟩, hnormalizer_card, hdihedral, hdvd⟩
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · exact fun i => (hlocal i).1
  · exact fun i => (hlocal i).2.1
  · exact fun i => (hlocal i).2.2.1
  · exact fun i => (hlocal i).2.2.2

end Dickson
end Glauberman


end Source13

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

/-- The Schur-Zassenhaus part of Huppert II.8.21, separated from the
projective-line argument which makes the complement maximal cyclic in `H`. -/
private theorem h821_schur_zassenhaus_core
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (N : Subgroup H) (hN : N = Subgroup.normalizer (P : Set H))
    (hP_le_N : (P : Subgroup H) ≤ N)
    (PN : Subgroup N) [PN.Normal]
    (hPN : PN = (P : Subgroup H).subgroupOf N)
    (hquotient_cyclic : IsCyclic (N ⧸ PN))
    (hquotient_card_dvd : Nat.card (N ⧸ PN) ∣ Nat.card F - 1)
    (hcomplement_maximal :
      ∀ C : Subgroup N, PN.IsComplement' C → IsCyclic C →
        let W : Subgroup H := C.map N.subtype
        W = ⊥ ∨
          (1 < Nat.card W ∧
            ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W)) :
    ∃ W : Subgroup H,
      IsCyclic W ∧
      Nat.Coprime p (Nat.card W) ∧
      (W = ⊥ ∨
        (1 < Nat.card W ∧
          ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W)) ∧
      Nat.card (Subgroup.normalizer (P : Set H)) =
        Nat.card P * Nat.card W := by
  classical
  have hf_ne_zero : f ≠ 0 := by
    intro hf
    subst f
    have hcard : Nat.card F = 1 := by simpa using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard
  have hp_dvd_cardF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p hf_ne_zero
  have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
    intro hp_sub
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_dvd_cardF hp_sub
      have hcard_pos : 0 < Nat.card F := Nat.card_pos
      have hsub : Nat.card F - (Nat.card F - 1) = 1 := by omega
      rwa [hsub] at h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  have hcop_p_cardF_sub_one : Nat.Coprime p (Nat.card F - 1) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_cardF_sub_one
  have hcop_p_quotient : Nat.Coprime p (Nat.card (N ⧸ PN)) :=
    Nat.Coprime.of_dvd_right hquotient_card_dvd hcop_p_cardF_sub_one
  have hPNcard : Nat.card PN = p ^ m := by
    calc
      Nat.card PN = Nat.card ((P : Subgroup H).subgroupOf N) := by rw [hPN]
      _ = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
      _ = p ^ m := hPcard
  have hPNindex : PN.index = Nat.card (N ⧸ PN) := rfl
  have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
    rw [hPNcard, hPNindex]
    exact hcop_p_quotient.pow_left m
  obtain ⟨C, hPN_C_complement⟩ :=
    Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
  have hC_cyclic : IsCyclic C := by
    let eC : N ⧸ PN ≃* C := hPN_C_complement.symm.QuotientMulEquiv
    let : IsCyclic (N ⧸ PN) := hquotient_cyclic
    exact isCyclic_of_surjective eC eC.surjective
  have hCcard : Nat.card C = Nat.card (N ⧸ PN) := by
    calc
      Nat.card C = PN.index := hPN_C_complement.symm.index_eq_card.symm
      _ = Nat.card (N ⧸ PN) := hPNindex
  let W : Subgroup H := C.map N.subtype
  have hW_cyclic : IsCyclic W := by
    let eW : C ≃* W :=
      Subgroup.equivMapOfInjective C N.subtype N.subtype_injective
    let : IsCyclic C := hC_cyclic
    exact isCyclic_of_surjective eW eW.surjective
  have hWcard : Nat.card W = Nat.card C := by
    dsimp [W]
    exact Subgroup.card_map_of_injective N.subtype_injective
  have hW_coprime : Nat.Coprime p (Nat.card W) := by
    rw [hWcard, hCcard]
    exact hcop_p_quotient
  have hW_boundary :
      W = ⊥ ∨
        (1 < Nat.card W ∧
          ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
    simpa [W] using
      hcomplement_maximal C hPN_C_complement hC_cyclic
  refine ⟨W, hW_cyclic, hW_coprime, hW_boundary, ?_⟩
  rw [← hN]
  calc
    Nat.card N = Nat.card PN * Nat.card C :=
      hPN_C_complement.card_mul_card.symm
    _ = Nat.card P * Nat.card W := by
      rw [hWcard, hPN, Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv]

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
theorem h821_borel_quotient_data
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


private theorem h821_complement_maximal_of_overgroups_coprime
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) (PN C : Subgroup N) [PN.Normal]
    (hcomp : PN.IsComplement' C)
    (hovergroups :
      let W : Subgroup H := C.map N.subtype
      ∀ V : Subgroup H, IsCyclic V → W ≤ V → W ≠ ⊥ →
        V ≤ N ∧ Nat.Coprime (Nat.card PN) (Nat.card V)) :
    let W : Subgroup H := C.map N.subtype
    W = ⊥ ∨
      (1 < Nat.card W ∧
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
  classical
  let W : Subgroup H := C.map N.subtype
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · right
    refine ⟨(Subgroup.one_lt_card_iff_ne_bot W).2 hWbot, ?_⟩
    intro V hVcyclic hWV
    obtain ⟨hV_le_N, hcoprime⟩ :=
      hovergroups V hVcyclic hWV hWbot
    let VN : Subgroup N := V.subgroupOf N
    have hC_le_VN : C ≤ VN := by
      intro c hc
      change (c : H) ∈ V
      apply hWV
      exact Subgroup.mem_map_of_mem N.subtype hc
    have hVNcard : Nat.card VN = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_N).toEquiv
    have hdisjoint : Disjoint PN VN := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hx_order_PN : orderOf x ∣ Nat.card PN := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨x, hx.1⟩ : PN))
      have hx_order_VN : orderOf x ∣ Nat.card VN := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨x, hx.2⟩ : VN))
      have hcoprime' : Nat.Coprime (Nat.card PN) (Nat.card VN) := by
        rw [hVNcard]
        exact hcoprime
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes hcoprime'
      · exact hx_order_PN
      · exact hx_order_VN
    have hsup : PN ⊔ VN = ⊤ := by
      apply top_unique
      rw [← hcomp.sup_eq_top]
      exact sup_le_sup_left hC_le_VN PN
    have hmul : (PN : Set N) * (VN : Set N) = Set.univ := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left PN VN
        Subgroup.le_normalizer_of_normal, hsup]
      rfl
    have hcompV : PN.IsComplement' VN :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint hmul
    have hcardCV : Nat.card C = Nat.card VN := by
      calc
        Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
        _ = Nat.card VN := hcompV.symm.index_eq_card
    have hCV : C = VN :=
      Subgroup.eq_of_le_of_card_ge hC_le_VN (by rw [hcardCV])
    calc
      V = VN.map N.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hV_le_N).symm
      _ = C.map N.subtype := by rw [← hCV]
      _ = W := rfl

private theorem h821_cyclic_overgroup_partition_component
    {G H : Type u} [Group G] [Group H] [Finite H]
    (Family : Subgroup G → Prop)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T)
    (embed : H →* G) (hembed : Function.Injective embed)
    (W : Subgroup H) (A : Subgroup G) (qminus : ℕ)
    (hseed : ∃ x : H, x ∈ W ∧ x ≠ 1 ∧ embed x ∈ A)
    (hAfamily : Family A) (hAcard : Nat.card A ∣ qminus) :
    ∀ V : Subgroup H, IsCyclic V → W ≤ V →
      V.map embed ≤ A ∧ Nat.card V ∣ qminus := by
  intro V hVcyclic hWV
  obtain ⟨x, hxW, hx, hxA⟩ := hseed
  have hxembed : embed x ≠ 1 := by
    intro h
    apply hx
    exact hembed (h.trans (map_one embed).symm)
  have hVmap_cyclic : IsCyclic (V.map embed) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective V embed hembed)).mp hVcyclic
  have hVmap_le : V.map embed ≤ A :=
    cyclic_le_unique_partition_family Family hpartition hxembed
      hxA hAfamily
      (Subgroup.mem_map_of_mem embed (hWV hxW)) hVmap_cyclic
  refine ⟨hVmap_le, ?_⟩
  have hmapcard : Nat.card (V.map embed) = Nat.card V :=
    Subgroup.card_map_of_injective hembed
  rw [← hmapcard]
  exact dvd_trans (Subgroup.card_dvd_of_le hVmap_le) hAcard


/-- An injective embedding into a commutative ambient `p`-subgroup reflects
normalization of that ambient subgroup back to a Sylow subgroup. -/
private theorem sylow_mem_normalizer_of_embed_mem_normalizer
    {H : Type u} {G : Type v} [Group H] [Finite H] [Group G]
    {p : ℕ} [Fact p.Prime]
    (embed : H →* G) (hembed : Function.Injective embed)
    (P : Sylow p H) (U B : Subgroup G)
    (hU_comm : IsMulCommutative U)
    (hP_le_U : (P : Subgroup H).map embed ≤ U)
    (hB_le : B ≤ Subgroup.normalizer (U : Set G))
    (y : H) (hyB : embed y ∈ B) :
    y ∈ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
  let : IsMulCommutative U := hU_comm
  let K : Subgroup H :=
    (P : Subgroup H).map (MulAut.conj y).toMonoidHom
  have hyN : embed y ∈ Subgroup.normalizer (U : Set G) := hB_le hyB
  have hK_map_le_U : K.map embed ≤ U := by
    intro z hz
    rcases hz with ⟨k, hkK, rfl⟩
    rcases hkK with ⟨x, hxP, rfl⟩
    have hxU : embed x ∈ U :=
      hP_le_U (Subgroup.mem_map_of_mem embed hxP)
    have hconjU : embed y * embed x * (embed y)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hyN (embed x)).mp hxU
    simpa [MulAut.conj_apply] using hconjU
  have hK_p : IsPGroup p K :=
    P.isPGroup'.map (MulAut.conj y).toMonoidHom
  have hK_le_normalizer :
      K ≤ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
    intro k hkK
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    change (P : Subgroup H).map (MulAut.conj k).toMonoidHom =
      (P : Subgroup H)
    apply Subgroup.eq_of_le_of_card_ge
    · intro z hz
      rcases hz with ⟨x, hxP, rfl⟩
      have hkU : embed k ∈ U :=
        hK_map_le_U (Subgroup.mem_map_of_mem embed hkK)
      have hxU : embed x ∈ U :=
        hP_le_U (Subgroup.mem_map_of_mem embed hxP)
      have hcomm_embed : embed k * embed x = embed x * embed k :=
        setLike_mul_comm hkU hxU
      have hcomm : k * x = x * k := hembed (by simpa using hcomm_embed)
      change k * x * k⁻¹ ∈ (P : Subgroup H)
      rw [hcomm, mul_inv_cancel_right]
      exact hxP
    · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
  have hsup_p : IsPGroup p ((P : Subgroup H) ⊔ K : Subgroup H) :=
    P.isPGroup'.to_sup_of_normal_left' hK_p hK_le_normalizer
  have hsup_eq : (P : Subgroup H) ⊔ K = (P : Subgroup H) :=
    P.is_maximal' hsup_p le_sup_left
  have hK_le_P : K ≤ (P : Subgroup H) := by
    rw [← hsup_eq]
    exact le_sup_right
  have hK_card : Nat.card K = Nat.card (P : Subgroup H) := by
    exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hK_eq : K = (P : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hK_le_P (by rw [hK_card])
  rw [← Subgroup.conjAct_pointwise_smul_iff]
  change K = (P : Subgroup H)
  exact hK_eq


/-- A nonidentity element of a cyclic split torus can only lie in the split
component of the II.8.5 partition. Exact split order then identifies that
component with the original torus. -/
private theorem h821_split_partition_seed
    {G : Type u} [Group G] [Finite G]
    (P U S T₀ B : Subgroup G)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! A : Subgroup G, x ∈ A ∧
        ((∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, A = S.map (MulAut.conj g).toMonoidHom)))
    (hT₀cyclic : IsCyclic T₀) (hT₀B : T₀ ≤ B)
    (hP_T₀_coprime : Nat.Coprime (Nat.card P) (Nat.card T₀))
    (hT₀_U_card : Nat.card T₀ = Nat.card U)
    (hT₀_S_coprime : Nat.Coprime (Nat.card T₀) (Nat.card S))
    {x : G} (hx : x ≠ 1) (hxT₀ : x ∈ T₀) :
    ∃ A : Subgroup G, x ∈ A ∧
      ((∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, A = S.map (MulAut.conj g).toMonoidHom)) ∧
      A ≤ B ∧ Nat.card A = Nat.card T₀ := by
  let Family : Subgroup G → Prop := fun A =>
    (∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, A = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ y : G, y ≠ 1 →
      ∃! A : Subgroup G, y ∈ A ∧ Family A := by
    simpa [Family] using hpartition
  obtain ⟨A, hxA, hAfamily⟩ := (hpartition' x hx).exists
  have hT₀_le_A : T₀ ≤ A :=
    cyclic_le_unique_partition_family Family hpartition'
      hx hxA hAfamily hxT₀ hT₀cyclic
  rcases hAfamily with ⟨g, hAg⟩ | ⟨g, hAg⟩ | ⟨g, hAg⟩
  · exfalso
    have hcop : Nat.Coprime (Nat.card T₀) (Nat.card A) := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hP_T₀_coprime.symm
    exact hx (hmem_eq_one_of_coprime_card T₀ A hcop
      hxT₀ (hT₀_le_A hxT₀))
  · have hcard : Nat.card T₀ = Nat.card A := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hT₀_U_card
    have hT₀_eq_A : T₀ = A :=
      Subgroup.eq_of_le_of_card_ge hT₀_le_A (by rw [hcard])
    refine ⟨A, hxA, Or.inr (Or.inl ⟨g, hAg⟩), ?_, hcard.symm⟩
    rw [← hT₀_eq_A]
    exact hT₀B
  · exfalso
    have hcop : Nat.Coprime (Nat.card T₀) (Nat.card A) := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hT₀_S_coprime
    exact hx (hmem_eq_one_of_coprime_card T₀ A hcop
      hxT₀ (hT₀_le_A hxT₀))


set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Sylow-normalizer part of Huppert II.8.22, with the nontrivial
boundary from II.8.21 made explicit. -/
theorem huppert_II_8_22_sylow_normalizer_shape
    {F : Type u} [Field F] [Finite F] {p f m r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H)
    (_hcyclic : ∀ i, IsCyclic (Z i))
    (_hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (_hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) :
    1 < p ^ m →
      (Nat.card (Subgroup.normalizer (P : Set H)) = p ^ m ∨
        ∃ i, Nat.card (Subgroup.normalizer (P : Set H)) =
          p ^ m * Nat.card (Z i)) := by
  classical
  intro hPcard_gt
  have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
    exact hPcard_gt
  let N : Subgroup H := Subgroup.normalizer (P : Set H)
  have hN : N = Subgroup.normalizer (P : Set H) := rfl
  have hP_le_N : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
  let PN : Subgroup N := (P : Subgroup H).subgroupOf N
  let : PN.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      simp [N])
  obtain ⟨hquotient_cyclic, hquotient_card_dvd,
      _hNormalizer_fixedPointFree, U, T, embed, hembed, _hembed_conj,
      hU_comm, hT_cyclic, hTcard,
      _hT_fixedPointFree, hP_map_le_U, hB_le_normalizer, hB_conjugate_torus,
      hN_maps_B, hU_preimage, _hcoordinates⟩ :=
    h821_borel_quotient_data hFcard H P hP_ne_bot N hN PN rfl
  have hquotient_card_dvd_sub_one :
      Nat.card (N ⧸ PN) ∣ Nat.card F - 1 :=
    dvd_trans hquotient_card_dvd
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
  let P₀ : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U₈₅, S₈₅, hU₈₅_cyclic, hU₈₅_card,
      hS₈₅_cyclic, hS₈₅_card, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P₀
  let Family : Subgroup (PSL2MatrixGroup F) → Prop := fun A =>
    (∃ g, A = (P₀ : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj g).toMonoidHom) ∨
    (∃ g, A = U₈₅.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, A = S₈₅.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : PSL2MatrixGroup F, x ≠ 1 →
      ∃! A : Subgroup (PSL2MatrixGroup F), x ∈ A ∧ Family A := by
    simpa [Family] using hpartition
  have hP₀card :
      Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP₀⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P₀
    exact (Nat.card_congr eP₀.toEquiv).symm
  have hP₀_T_coprime :
      Nat.Coprime
        (Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)))
        (Nat.card T) := by
    rw [hP₀card, hTcard]
    exact hq_coprime_split_order (Nat.card F) Nat.card_pos
  have hT_U₈₅_card : Nat.card T = Nat.card U₈₅ := by
    rw [hTcard, hU₈₅_card]
  have hT_S₈₅_coprime : Nat.Coprime (Nat.card T) (Nat.card S₈₅) := by
    rw [hTcard, hS₈₅_card]
    exact hsplit_nonsplit_order_coprime
      (Nat.card F) (Finite.one_lt_card (α := F))
  have hTcard_dvd : Nat.card T ∣ Nat.card F - 1 := by
    rw [hTcard]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hp_dvd_cardF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p hf_ne_zero
  have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
    intro hp_sub
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_dvd_cardF hp_sub
      have hcard_pos : 0 < Nat.card F := Nat.card_pos
      have hsub : Nat.card F - (Nat.card F - 1) = 1 := by omega
      rwa [hsub] at h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  have hcop_p_cardF_sub_one : Nat.Coprime p (Nat.card F - 1) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      hp_not_dvd_cardF_sub_one
  have hPNcard : Nat.card PN = p ^ m := by
    calc
      Nat.card PN = Nat.card P :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
      _ = p ^ m := hPcard
  have hcomplement_maximal :
      ∀ C : Subgroup N, PN.IsComplement' C → IsCyclic C →
        let W : Subgroup H := C.map N.subtype
        W = ⊥ ∨
          (1 < Nat.card W ∧
            ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
    intro C hcomp hC_cyclic
    let W : Subgroup H := C.map N.subtype
    have hovergroups :
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → W ≠ ⊥ →
          V ≤ N ∧ Nat.Coprime (Nat.card PN) (Nat.card V) := by
      intro V hV_cyclic hWV hW_ne_bot
      obtain ⟨w, hw_ne⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hW_ne_bot
      rcases w.property with ⟨c, hcC, hcw⟩
      have hc_ne : (c : H) ≠ 1 := by
        intro hc_one
        apply hw_ne
        apply Subtype.ext
        exact hcw.symm.trans hc_one
      have hc_not_U : embed (c : H) ∉ U := by
        intro hcU
        have hcPN : c ∈ PN := (hU_preimage c).mp hcU
        have hc_one : c = 1 :=
          Subgroup.disjoint_def.mp hcomp.disjoint hcPN hcC
        apply hc_ne
        simpa using congrArg Subtype.val hc_one
      obtain ⟨u, huU, hcuT⟩ :=
        hB_conjugate_torus (embed (c : H)) (hN_maps_B c) hc_not_U
      let T₀ : Subgroup (PSL2MatrixGroup F) :=
        T.map (MulAut.conj u).toMonoidHom
      have hT₀_cyclic : IsCyclic T₀ := by
        exact (MulEquiv.isCyclic
          (Subgroup.equivMapOfInjective T
            (MulAut.conj u).toMonoidHom
            (MulAut.conj u).injective)).mp hT_cyclic
      have hT₀card : Nat.card T₀ = Nat.card T :=
        Subgroup.card_map_of_injective (MulAut.conj u).injective
      have hT₀_le_B : T₀ ≤ U ⊔ T := by
        rw [Subgroup.map_le_iff_le_comap]
        intro t htT
        change u * t * u⁻¹ ∈ U ⊔ T
        exact (U ⊔ T).mul_mem
          ((U ⊔ T).mul_mem
            ((show U ≤ U ⊔ T from le_sup_left) huU)
            ((show T ≤ U ⊔ T from le_sup_right) htT))
          ((U ⊔ T).inv_mem ((show U ≤ U ⊔ T from le_sup_left) huU))
      have hP₀_T₀_coprime :
          Nat.Coprime
            (Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)))
            (Nat.card T₀) := by
        rw [hT₀card]
        exact hP₀_T_coprime
      have hT₀_U₈₅_card : Nat.card T₀ = Nat.card U₈₅ := by
        rw [hT₀card]
        exact hT_U₈₅_card
      have hT₀_S₈₅_coprime :
          Nat.Coprime (Nat.card T₀) (Nat.card S₈₅) := by
        rw [hT₀card]
        exact hT_S₈₅_coprime
      have hc_embed_ne : embed (c : H) ≠ 1 := by
        intro hc_one
        apply hc_ne
        exact hembed (hc_one.trans (map_one embed).symm)
      obtain ⟨A, hcA, hAfamily, hA_le_B, hAcard⟩ :=
        h821_split_partition_seed
          (P₀ : Subgroup (PSL2MatrixGroup F)) U₈₅ S₈₅ T₀
          (U ⊔ T) hpartition hT₀_cyclic hT₀_le_B
          hP₀_T₀_coprime hT₀_U₈₅_card hT₀_S₈₅_coprime
          hc_embed_ne hcuT
      have hAfamily' : Family A := by
        simpa [Family] using hAfamily
      have hAcard_dvd : Nat.card A ∣ Nat.card F - 1 := by
        rw [hAcard, hT₀card]
        exact hTcard_dvd
      have hseed :
          ∃ x : H, x ∈ W ∧ x ≠ 1 ∧ embed x ∈ A := by
        refine ⟨(c : H), ?_, hc_ne, hcA⟩
        exact Subgroup.mem_map_of_mem N.subtype hcC
      obtain ⟨hVmap_le_A, hVcard_dvd⟩ :=
        h821_cyclic_overgroup_partition_component
          Family hpartition' embed hembed W A (Nat.card F - 1)
          hseed hAfamily' hAcard_dvd V hV_cyclic hWV
      have hV_le_N : V ≤ N := by
        intro y hyV
        rw [hN]
        apply sylow_mem_normalizer_of_embed_mem_normalizer
          embed hembed P U (U ⊔ T) hU_comm hP_map_le_U
          hB_le_normalizer y
        exact hA_le_B
          (hVmap_le_A (Subgroup.mem_map_of_mem embed hyV))
      have hcoprime_V :
          Nat.Coprime (Nat.card PN) (Nat.card V) := by
        rw [hPNcard]
        exact Nat.Coprime.of_dvd_right hVcard_dvd
          (hcop_p_cardF_sub_one.pow_left m)
      exact ⟨hV_le_N, hcoprime_V⟩
    exact h821_complement_maximal_of_overgroups_coprime N PN C hcomp
      hovergroups
  obtain ⟨W, hW_cyclic, hW_coprime, hW_boundary, hnormalizer_card⟩ :=
    h821_schur_zassenhaus_core hFcard H P hPcard N hN hP_le_N
      PN rfl hquotient_cyclic hquotient_card_dvd_sub_one hcomplement_maximal
  rcases hW_boundary with hW_bot | ⟨hW_card, hW_maximal⟩
  · left
    rw [hnormalizer_card, hPcard, hW_bot, Subgroup.card_bot, mul_one]
  · obtain ⟨i, g, hWrep⟩ :=
      hrepresentative W hW_cyclic hW_card hW_coprime hW_maximal
    right
    refine ⟨i, ?_⟩
    rw [hnormalizer_card, hPcard, hWrep,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]


end Dickson
end Glauberman


end Source15

section Source16
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCounting.lean
/-!
# Counting the three Dickson families

This module isolates the unique-family orbit counts and the Huppert II.8.22
counting equation.
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

/-- The disjoint-union count in Huppert II.8.22. -/
theorem huppert_II_8_22_counting_equation
    {F : Type u} [Field F] [Finite F] {p f m r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H) (s : Fin r → ℕ)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j)
    (hnormalizer : ∀ i,
      Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i) :
    Nat.card H =
      1 + ((p ^ m - 1) * Nat.card H) /
          Nat.card (Subgroup.normalizer (P : Set H)) +
        ∑ i, ((Nat.card (Z i) - 1) * Nat.card H) /
          (Nat.card (Z i) * s i) := by
  classical
  have hpartition_count :
      Nat.card H =
        1 + (p ^ m - 1) *
            (Subgroup.normalizer (P : Set H)).index +
          ∑ i, (Nat.card (Z i) - 1) *
            (Subgroup.normalizer (Z i : Set H)).index := by
    apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
    intro x hx
    convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
      hcoprime hmaximal hrepresentative hdistinct x hx using 1
    funext A
    rcases A with Q | z <;> rfl
  have hPindex :
      (Subgroup.normalizer (P : Set H)).index =
        Nat.card H /
          Nat.card (Subgroup.normalizer (P : Set H)) :=
    Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.normalizer (P : Set H)).index_mul_card
  have hZindex :
      ∀ i, (Subgroup.normalizer (Z i : Set H)).index =
        Nat.card H /
          Nat.card (Subgroup.normalizer (Z i : Set H)) := by
    intro i
    exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.normalizer (Z i : Set H)).index_mul_card
  nth_rewrite 1 [hpartition_count]
  congr 1
  · rw [Nat.mul_div_assoc _ (Subgroup.card_subgroup_dvd_card
      (Subgroup.normalizer (P : Set H))), ← hPindex]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← hnormalizer i,
      Nat.mul_div_assoc _ (Subgroup.card_subgroup_dvd_card
        (Subgroup.normalizer (Z i : Set H))), ← hZindex i]

/-- Huppert II.8.22: the counting equation for maximal cyclic `p`-prime subgroups. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) :
    ∃ (r : ℕ) (Z : Fin r → Subgroup H) (s : Fin r → ℕ),
      (∀ i, IsCyclic (Z i)) ∧
      (∀ i, 1 < Nat.card (Z i)) ∧
      (∀ i, Nat.Coprime p (Nat.card (Z i))) ∧
      (∀ i (W : Subgroup H), IsCyclic W → Z i ≤ W → W = Z i) ∧
      (∀ W : Subgroup H, IsCyclic W → 1 < Nat.card W →
        Nat.Coprime p (Nat.card W) →
        (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
        ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j g,
        (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) ∧
      (∀ i, 0 < s i ∧ s i ≤ 2) ∧
      (∀ i,
        Nat.card (Subgroup.normalizer (Z i : Set H)) = Nat.card (Z i) * s i) ∧
      (∀ i, s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      (1 < p ^ m →
        (Nat.card (Subgroup.normalizer (P : Set H)) = p ^ m ∨
          ∃ i, Nat.card (Subgroup.normalizer (P : Set H)) =
            p ^ m * Nat.card (Z i))) ∧
      (∀ i,
        (Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H =
        1 + ((p ^ m - 1) * Nat.card H) /
            Nat.card (Subgroup.normalizer (P : Set H)) +
          ∑ i, ((Nat.card (Z i) - 1) * Nat.card H) /
            (Nat.card (Z i) * s i) := by
  rcases huppert_II_8_22_maximal_cyclic_representatives (H := H) p with
    ⟨r, Z, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct⟩
  rcases huppert_II_8_22_torus_normalizer_data
      hFcard H Z hcyclic hnontrivial hcoprime hmaximal with
    ⟨s, hs, hnormalizer, hdihedral, hdivides⟩
  refine ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
    hrepresentative, hdistinct, hs, hnormalizer, hdihedral, ?_, hdivides, ?_⟩
  · exact huppert_II_8_22_sylow_normalizer_shape
      hFcard H P hPcard Z hcyclic hcoprime hmaximal hrepresentative
  · exact huppert_II_8_22_counting_equation
      hFcard H P hPcard Z s hcyclic hnontrivial hcoprime hmaximal
        hrepresentative hdistinct hnormalizer
end Dickson
end Glauberman


end Source16

end CFSGPackCounting
