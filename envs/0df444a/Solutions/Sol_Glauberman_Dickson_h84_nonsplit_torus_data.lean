-- Prove2me | solution 1 for Glauberman.Dickson.h84_nonsplit_torus_data
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T11:22:50.769382+00:00
-- url     : https://prove2.me/submissions/9b142b0d-5204-4272-83d8-f8c0a855709f

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
namespace CFSGPackNonsplit

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

theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card (Subgroup.normalizer (S : Set (PSL2MatrixGroup F))) =
        2 * Nat.card S ∧
      (∃ w : PSL2MatrixGroup F,
        w ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
        w ∉ S ∧
        w * w = 1 ∧
        (∀ t : PSL2MatrixGroup F, t ∈ S → w * t * w⁻¹ = t⁻¹) ∧
        Nat.card (S ⊔ Subgroup.zpowers w :
          Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card S ∧
        ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            S ⊔ Subgroup.zpowers w) ∧
      (∀ y : PSL2MatrixGroup F, y ∈ S → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ S →
            g ∈ Subgroup.normalizer
              (S : Set (PSL2MatrixGroup F))) ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 ≠ (4 : F) →
        (¬ ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) →
        ∃ g : PSL2MatrixGroup F,
          (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
            S.map (MulAut.conj g).toMonoidHom := by
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
  let E := FiniteField.Extension F p 2
  let : Fintype E := Fintype.ofFinite E
  let normUnits : Eˣ →* Fˣ := Units.map (Algebra.norm F)
  let K : Subgroup Eˣ := normUnits.ker
  have hnormUnits_surjective : Function.Surjective normUnits := by
    exact FiniteField.unitsMap_norm_surjective F E
  have hnormUnits_range : normUnits.range = ⊤ :=
    MonoidHom.range_eq_top.mpr hnormUnits_surjective
  have hK_index : K.index = Nat.card F - 1 := by
    calc
      K.index = Nat.card normUnits.range := Subgroup.index_ker normUnits
      _ = Nat.card Fˣ := by rw [hnormUnits_range]; simp
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
  have hE_card : Nat.card E = Nat.card F ^ 2 := by
    exact FiniteField.natCard_extension F p 2
  have hK_mul_card :
      (Nat.card F - 1) * Nat.card K = Nat.card F ^ 2 - 1 := by
    calc
      (Nat.card F - 1) * Nat.card K = K.index * Nat.card K := by rw [hK_index]
      _ = Nat.card Eˣ := K.index_mul_card
      _ = Nat.card E - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := E))
      _ = Nat.card F ^ 2 - 1 := by rw [hE_card]
  have hq_factor :
      (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    simpa [mul_comm] using
      (Nat.pow_two_sub_pow_two (Nat.card F) 1).symm
  have hdegree_exp :
      (Nat.card E - 1) / (Nat.card F - 1) = Nat.card F + 1 := by
    rw [hE_card, ← hq_factor]
    simpa [mul_comm] using Nat.mul_div_left (Nat.card F + 1)
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
  have hfrob_inv (x : K) :
      FiniteField.Extension.frob F p 2 (x.1 : E) = ((x.1 : E)⁻¹) := by
    have hxker := x.property
    change normUnits x.1 = 1 at hxker
    have hxnorm := congrArg Units.val hxker
    change Algebra.norm F (x.1 : E) = 1 at hxnorm
    have hpow : (x.1 : E) ^ (Nat.card F + 1) = 1 := by
      have h := FiniteField.algebraMap_norm_eq_pow
        (K := F) (K' := E) (x := (x.1 : E))
      rw [hxnorm, map_one, hdegree_exp] at h
      exact h.symm
    rw [FiniteField.Extension.frob_apply]
    apply mul_right_cancel₀ (x.1.ne_zero)
    calc
      (x.1 : E) ^ Nat.card F * (x.1 : E) =
          (x.1 : E) ^ (Nat.card F + 1) := (pow_succ _ _).symm
      _ = 1 := hpow
      _ = (x.1 : E)⁻¹ * (x.1 : E) := by
        rw [inv_mul_cancel₀ x.1.ne_zero]
  have hK_card : Nat.card K = Nat.card F + 1 := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
    exact hK_mul_card.trans hq_factor.symm
  have hK_cyclic : IsCyclic K := isCyclic_subgroup_units K
  have hidx :
      Fintype.card (Module.Free.ChooseBasisIndex F E) =
        Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Fintype.card_fin]
    simpa [E] using (FiniteField.finrank_extension F p 2)
  let eidx : Module.Free.ChooseBasisIndex F E ≃ Fin 2 :=
    Fintype.equivOfCardEq hidx
  let b : Module.Basis (Fin 2) F E :=
    (Module.Free.chooseBasis F E).reindex eidx
  let nonsplitSL : K →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun x =>
        ⟨Algebra.leftMulMatrix b (x.1 : E), by
          rw [← Algebra.norm_eq_matrix_det b]
          have hxker := x.property
          change normUnits x.1 = 1 at hxker
          simpa [normUnits] using congrArg Units.val hxker⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (Algebra.leftMulMatrix b) ((x.1 : E) * (y.1 : E)) =
          (Algebra.leftMulMatrix b) (x.1 : E) * (Algebra.leftMulMatrix b) (y.1 : E)
        exact (Algebra.leftMulMatrix b).map_mul _ _ }
  have hnonsplitSL_injective : Function.Injective nonsplitSL := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    apply Algebra.leftMulMatrix_injective b
    have hmat := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F)) hxy
    change Algebra.leftMulMatrix b (x.1 : E) =
      Algebra.leftMulMatrix b (y.1 : E) at hmat
    exact hmat
  let nonsplitTorus : K →* PSL2MatrixGroup F :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
        nonsplitSL
  have hnonsplit_mem_ker_iff (x : K) :
      x ∈ nonsplitTorus.ker ↔
        ∃ r : F, r ^ 2 = 1 ∧ algebraMap F E r = (x.1 : E) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hcenter : nonsplitSL x ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (nonsplitSL x)).mp hx
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hcenter
      rcases hcenter with ⟨r, hr, hscalar⟩
      refine ⟨r, by simpa using hr, ?_⟩
      apply Algebra.leftMulMatrix_injective b
      calc
        Algebra.leftMulMatrix b (algebraMap F E r) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r :=
          (Algebra.leftMulMatrix b).commutes r
        _ = Matrix.scalar (Fin 2) r := rfl
        _ = (nonsplitSL x : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
        _ = Algebra.leftMulMatrix b (x.1 : E) := rfl
    · rintro ⟨r, hr, hxr⟩
      apply (QuotientGroup.eq_one_iff (nonsplitSL x)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨r, by simpa using hr, ?_⟩
      change Matrix.scalar (Fin 2) r = Algebra.leftMulMatrix b (x.1 : E)
      rw [← hxr]
      calc
        Matrix.scalar (Fin 2) r =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = Algebra.leftMulMatrix b (algebraMap F E r) :=
          ((Algebra.leftMulMatrix b).commutes r).symm
  let RootF := {r : F // r ^ 2 = 1}
  let kerScalar (x : nonsplitTorus.ker) : F :=
    Classical.choose ((hnonsplit_mem_ker_iff x.1).mp x.property)
  have hkerScalar_spec (x : nonsplitTorus.ker) :
      kerScalar x ^ 2 = 1 ∧
        algebraMap F E (kerScalar x) = (x.1.1 : E) :=
    Classical.choose_spec ((hnonsplit_mem_ker_iff x.1).mp x.property)
  let scalarK (r : RootF) : K :=
    ⟨Units.map (algebraMap F E)
        (Units.mk0 r.1 (by
          intro hr0
          have hr := r.property
          simp [hr0] at hr)), by
      change normUnits
        (Units.map (algebraMap F E)
          (Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr))) = 1
      apply Units.ext
      change Algebra.norm F (algebraMap F E r.1) = 1
      rw [Algebra.norm_algebraMap_of_basis b]
      simpa using r.property⟩
  let scalarKer (r : RootF) : nonsplitTorus.ker :=
    ⟨scalarK r, (hnonsplit_mem_ker_iff (scalarK r)).mpr
      ⟨r.1, r.property, by simp [scalarK]⟩⟩
  let eKerRoot : nonsplitTorus.ker ≃ RootF :=
    { toFun := fun x => ⟨kerScalar x, (hkerScalar_spec x).1⟩
      invFun := scalarKer
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        simpa [scalarKer, scalarK] using (hkerScalar_spec x).2
      right_inv := by
        intro r
        apply Subtype.ext
        apply (algebraMap F E).injective
        calc
          algebraMap F E (kerScalar (scalarKer r)) =
              ((scalarKer r).1.1 : E) :=
            (hkerScalar_spec (scalarKer r)).2
          _ = algebraMap F E r.1 := by simp [scalarKer, scalarK] }
  let rootVal : rootsOfUnity 2 F ≃ RootF :=
    { toFun := fun a =>
        ⟨(a.1 : F), by simpa using congrArg Units.val a.property⟩
      invFun := fun r =>
        ⟨Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr),
          by
            rw [mem_rootsOfUnity]
            apply Units.ext
            simpa using r.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        rfl }
  have hnonsplit_ker_card :
      Nat.card nonsplitTorus.ker =
        Nat.gcd (Nat.card F - 1) 2 := by
    calc
      Nat.card nonsplitTorus.ker = Nat.card RootF :=
        Nat.card_congr eKerRoot
      _ = Nat.card (rootsOfUnity 2 F) :=
        (Nat.card_congr rootVal).symm
      _ = Nat.gcd (Nat.card F - 1) 2 := hcard_roots
  have hnonsplit_range_mul :
      Nat.card nonsplitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F + 1 := by
    calc
      Nat.card nonsplitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          nonsplitTorus.ker.index * Nat.card nonsplitTorus.ker := by
        rw [Subgroup.index_ker, hnonsplit_ker_card]
      _ = Nat.card K := nonsplitTorus.ker.index_mul_card
      _ = Nat.card F + 1 := hK_card
  have hnonsplit_range_card :
      Nat.card nonsplitTorus.range =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hnonsplit_range_mul
  have hnonsplitTorus_cyclic : IsCyclic nonsplitTorus.range := by
    let : IsCyclic K := hK_cyclic
    exact isCyclic_of_surjective nonsplitTorus.rangeRestrict
      nonsplitTorus.rangeRestrict_surjective
  let sigma : E ≃ₐ[F] E :=
    FiniteField.Extension.frob F p 2
  have hsigma_sq (x : E) : sigma (sigma x) = x := by
    change FiniteField.Extension.frob F p 2
      (FiniteField.Extension.frob F p 2 x) = x
    rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply,
      ← pow_mul]
    have hcard : Nat.card F * Nat.card F = Fintype.card E := by
      rw [← pow_two, ← FiniteField.natCard_extension F p 2,
        Nat.card_eq_fintype_card]
    rw [hcard]
    exact FiniteField.pow_card x
  have hsigma_ne_one : sigma ≠ 1 := by
    intro hsigma
    change FiniteField.Extension.frob F p 2 = 1 at hsigma
    have hall : ∀ g : E ≃ₐ[F] E, g = 1 := by
      intro g
      obtain ⟨i, hi, hpow⟩ :=
        FiniteField.Extension.exists_frob_pow_eq
          (k := F) (p := p) (n := 2) g
      rw [← hpow, hsigma, one_pow]
    let : Subsingleton (E ≃ₐ[F] E) :=
      ⟨fun a d => (hall a).trans (hall d).symm⟩
    have hone : Nat.card (E ≃ₐ[F] E) = 1 := Nat.card_unique
    have htwo : Nat.card (E ≃ₐ[F] E) = 2 :=
      FiniteField.natCard_algEquiv_extension F p 2
    omega
  let sigmaMat : Matrix (Fin 2) (Fin 2) F :=
    LinearMap.toMatrix b b sigma.toLinearEquiv
  have hsigma_inv (x : K) :
      sigma (x.1 : E) = ((x⁻¹ : K).1 : E) := by
    rw [show sigma = FiniteField.Extension.frob F p 2 from rfl,
      hfrob_inv x]
    simp
  have hsigmaMat_mul (x : E) :
      sigmaMat * Algebra.leftMulMatrix b x =
        Algebra.leftMulMatrix b (sigma x) * sigmaMat := by
    dsimp [sigmaMat]
    rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
      ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext y
    simp [LinearMap.comp_apply, Algebra.lmul]
  have hsigmaMat_sq : sigmaMat * sigmaMat = 1 := by
    dsimp [sigmaMat]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext x
    exact hsigma_sq x
  have hsigma_det_unit : IsUnit (Matrix.det sigmaMat) := by
    simpa [sigmaMat] using
      (LinearEquiv.isUnit_det sigma.toLinearEquiv b b)
  have hsigma_det_ne : Matrix.det sigmaMat ≠ 0 :=
    hsigma_det_unit.ne_zero
  obtain ⟨c, hc⟩ :=
    FiniteField.norm_surjective F E (Matrix.det sigmaMat)⁻¹
  have hc_ne : c ≠ 0 := by
    intro hc0
    subst c
    simp only [Algebra.norm_zero] at hc
    exact hsigma_det_ne (inv_eq_zero.mp hc.symm)
  let frobSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨Algebra.leftMulMatrix b c * sigmaMat, by
      rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b, hc]
      exact inv_mul_cancel₀ hsigma_det_ne⟩
  have hc_sigma :
      c * sigma c = algebraMap F E (Algebra.norm F c) := by
    have h := FiniteField.algebraMap_norm_eq_pow
      (K := F) (K' := E) (x := c)
    rw [hdegree_exp] at h
    calc
      c * sigma c = c * c ^ Nat.card F := by
        change c * FiniteField.Extension.frob F p 2 c = _
        rw [FiniteField.Extension.frob_apply]
      _ = c ^ (Nat.card F + 1) := by rw [pow_succ, mul_comm]
      _ = algebraMap F E (Algebra.norm F c) := h.symm
  have hfrobSL_sq_matrix :
      ((frobSL * frobSL : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b
          (algebraMap F E (Algebra.norm F c)) := by
    change (Algebra.leftMulMatrix b c * sigmaMat) *
        (Algebra.leftMulMatrix b c * sigmaMat) =
      Algebra.leftMulMatrix b
        (algebraMap F E (Algebra.norm F c))
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          (Algebra.leftMulMatrix b c * sigmaMat) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b c) * sigmaMat := by
              simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma c) * sigmaMat) *
              sigmaMat := by rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma c)) *
              (sigmaMat * sigmaMat) := by
                simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b (c * sigma c) := by
            rw [hsigmaMat_sq, mul_one, ← map_mul]
      _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) := by rw [hc_sigma]
  have hfrobSL_sq_center :
      frobSL * frobSL ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨Algebra.norm F c, ?_, ?_⟩
    · have hdet := (frobSL * frobSL).property
      rw [hfrobSL_sq_matrix] at hdet
      have hscalar :
          Algebra.leftMulMatrix b
              (algebraMap F E (Algebra.norm F c)) =
            Matrix.scalar (Fin 2) (Algebra.norm F c) := by
        calc
          _ = algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) :=
            (Algebra.leftMulMatrix b).commutes (Algebra.norm F c)
          _ = _ := rfl
      rw [hscalar] at hdet
      simpa [Matrix.det_fin_two, pow_two] using hdet
    · calc
        Matrix.scalar (Fin 2) (Algebra.norm F c) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) := rfl
        _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) :=
          ((Algebra.leftMulMatrix b).commutes (Algebra.norm F c)).symm
        _ = ((frobSL * frobSL :
            Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) := hfrobSL_sq_matrix.symm
  have hleftMul_comm (a d : E) :
      Algebra.leftMulMatrix b a * Algebra.leftMulMatrix b d =
        Algebra.leftMulMatrix b d * Algebra.leftMulMatrix b a := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hfrobSL_mul (x : K) :
      frobSL * nonsplitSL x = nonsplitSL x⁻¹ * frobSL := by
    apply Subtype.ext
    change (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
        Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
          (Algebra.leftMulMatrix b c * sigmaMat)
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b (x.1 : E)) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma (x.1 : E)) * sigmaMat) := by
              rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma (x.1 : E))) * sigmaMat := by
              rw [Matrix.mul_assoc]
      _ = (Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            Algebra.leftMulMatrix b c) * sigmaMat := by
              rw [hleftMul_comm]
      _ = Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [hsigma_inv]
  have hfrobSL_conj (x : K) :
      frobSL * nonsplitSL x * frobSL⁻¹ = nonsplitSL x⁻¹ := by
    calc
      frobSL * nonsplitSL x * frobSL⁻¹ =
          nonsplitSL x⁻¹ * (frobSL * frobSL⁻¹) := by
        rw [hfrobSL_mul, mul_assoc]
      _ = nonsplitSL x⁻¹ := by rw [mul_inv_cancel, mul_one]
  let frobPSL : PSL2MatrixGroup F :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL
  have hfrobPSL_sq : frobPSL ^ 2 = 1 := by
    change (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL) ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (frobSL ^ 2)).mpr
    simpa [pow_two] using hfrobSL_sq_center
  have hfrobPSL_not_mem_torus :
      frobPSL ∉ nonsplitTorus.range := by
    rintro ⟨x, hx⟩
    change (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          (nonsplitSL x) =
      (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          frobSL at hx
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hx with
      ⟨z, hz_center, hz_eq⟩
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz_center (0 : Fin 2)
    let r : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalar' :
        Matrix.scalar (Fin 2) r =
          (z : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
    have hmat := congrArg Subtype.val hz_eq
    change Algebra.leftMulMatrix b (x.1 : E) *
        (z : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix b c * sigmaMat at hmat
    rw [← hscalar'] at hmat
    have hscalarLM :
        Matrix.scalar (Fin 2) r =
          Algebra.leftMulMatrix b (algebraMap F E r) := by
      calc
        _ = algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = _ := ((Algebra.leftMulMatrix b).commutes r).symm
    rw [hscalarLM, ← map_mul] at hmat
    rw [Algebra.leftMulMatrix_apply] at hmat
    change (LinearMap.toMatrix b b)
        (Algebra.lmul F E ((x.1 : E) * algebraMap F E r)) =
      Algebra.leftMulMatrix b c *
        (LinearMap.toMatrix b b) sigma.toLinearEquiv at hmat
    rw [Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff] at hmat
    have hone := LinearMap.congr_fun hmat (1 : E)
    have hxr : (x.1 : E) * algebraMap F E r = c := by
      simpa [LinearMap.comp_apply, Algebra.lmul] using hone
    have hall : ∀ y : E, sigma y = y := by
      intro y
      have hy := LinearMap.congr_fun hmat y
      change ((x.1 : E) * algebraMap F E r) * y =
        c * sigma y at hy
      rw [hxr] at hy
      exact (mul_left_cancel₀ hc_ne hy).symm
    apply hsigma_ne_one
    ext y
    exact hall y
  have hfrobPSL_conj (x : K) :
      frobPSL * nonsplitTorus x * frobPSL⁻¹ =
        nonsplitTorus x⁻¹ := by
    simpa [frobPSL, nonsplitTorus] using congrArg
      (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F)))
      (hfrobSL_conj x)
  have hfrobPSL_mem_normalizer :
      frobPSL ∈ Subgroup.normalizer (nonsplitTorus.range : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, (hfrobPSL_conj x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x⁻¹, ?_⟩
      calc
        nonsplitTorus x⁻¹ =
            frobPSL⁻¹ *
              (frobPSL * nonsplitTorus x⁻¹ * frobPSL⁻¹) *
                frobPSL := by simp [mul_assoc]
        _ = frobPSL⁻¹ * nonsplitTorus x * frobPSL := by
          rw [hfrobPSL_conj]
          rw [inv_inv]
        _ = y := by rw [hx]; simp [mul_assoc]
  let nonsplitDihedralCandidate : Subgroup (PSL2MatrixGroup F) :=
    nonsplitTorus.range ⊔ Subgroup.zpowers frobPSL
  have hnonsplitCandidate_le_normalizer :
      nonsplitDihedralCandidate ≤
        Subgroup.normalizer (nonsplitTorus.range : Set _) := by
    apply sup_le Subgroup.le_normalizer
    exact Subgroup.zpowers_le.2 hfrobPSL_mem_normalizer
  rcases hreflection_candidate_data nonsplitTorus.range frobPSL
      hfrobPSL_mem_normalizer (by simpa [pow_two] using hfrobPSL_sq)
        hfrobPSL_not_mem_torus with
    ⟨hfrob_zpowers_card, hnonsplit_torus_zpowers_disjoint,
      hnonsplitCandidate_card_raw⟩
  have hnonsplitCandidate_card :
      Nat.card nonsplitDihedralCandidate =
        2 * ((Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2) := by
    have hraw :
        Nat.card nonsplitDihedralCandidate =
          2 * Nat.card nonsplitTorus.range := by
      simpa [nonsplitDihedralCandidate] using hnonsplitCandidate_card_raw
    rw [hnonsplit_range_card] at hraw
    exact hraw
  have hnonsplit_lift_classification_of_conj
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (aK : K) (haK_not_ker : aK ∉ nonsplitTorus.ker)
      (hconj_mem :
        (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A *
              nonsplitTorus aK *
                ((QuotientGroup.mk' (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F))) A)⁻¹ ∈
          nonsplitTorus.range) :
      (∃ x : K, A = nonsplitSL x) ∨
        ∃ x : K, A = nonsplitSL x * frobSL := by
    have haK_not_scalar (r : F) :
        algebraMap F E r ≠ (aK.1 : E) := by
      intro hr
      apply haK_not_ker
      apply (hnonsplit_mem_ker_iff aK).2
      refine ⟨r, ?_, hr⟩
      have hker := aK.property
      change normUnits aK.1 = 1 at hker
      have hv := congrArg Units.val hker
      change Algebra.norm F (aK.1 : E) = 1 at hv
      rw [← hr, Algebra.norm_algebraMap_of_basis b] at hv
      simpa using hv
    rcases hconj_mem with ⟨bK, hbK⟩
    have hq :
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) (nonsplitSL bK) =
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F)))
            (A * nonsplitSL aK * A⁻¹) := by
      simpa [nonsplitTorus] using hbK
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA : nonsplitSL bK * z * A = A * nonsplitSL aK := by
      calc
        nonsplitSL bK * z * A = (A * nonsplitSL aK * A⁻¹) * A := by
          rw [hzeq]
        _ = A * nonsplitSL aK := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (0 : Fin 2)
    let rz : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalarLM :
        Matrix.scalar (Fin 2) rz =
          Algebra.leftMulMatrix b (algebraMap F E rz) := by
      calc
        Matrix.scalar (Fin 2) rz =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) rz := rfl
        _ = Algebra.leftMulMatrix b (algebraMap F E rz) :=
          ((Algebra.leftMulMatrix b).commutes rz).symm
    let yE : E := (bK.1 : E) * algebraMap F E rz
    have hmat :
        Algebra.leftMulMatrix b yE *
            (A : Matrix (Fin 2) (Fin 2) F) =
          (A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E) := by
      have hm := congrArg Subtype.val hzeqA
      change Algebra.leftMulMatrix b (bK.1 : E) *
            (z : Matrix (Fin 2) (Fin 2) F) *
              (A : Matrix (Fin 2) (Fin 2) F) =
          (A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E) at hm
      rw [← hscalar] at hm
      rw [hscalarLM, ← map_mul] at hm
      exact hm
    have hAunit :
        IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) F)) := by
      rw [A.property]
      exact isUnit_one
    let Aeq : E ≃ₗ[F] E :=
      Matrix.toLinearEquiv b (A : Matrix (Fin 2) (Fin 2) F) hAunit
    have hA_intertwine (x : E) :
        Aeq ((aK.1 : E) * x) = yE * Aeq x := by
      have hfun := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) F => Matrix.toLin b b M x) hmat
      change Matrix.toLin b b (Algebra.leftMulMatrix b yE *
            (A : Matrix (Fin 2) (Fin 2) F)) x =
          Matrix.toLin b b ((A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E)) x at hfun
      rw [Matrix.toLin_mul_apply b b b (Algebra.leftMulMatrix b yE)
            (A : Matrix (Fin 2) (Fin 2) F) x,
        Matrix.toLin_mul_apply b b b (A : Matrix (Fin 2) (Fin 2) F)
            (Algebra.leftMulMatrix b (aK.1 : E)) x] at hfun
      simp only [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix] at hfun
      change yE * Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) x =
          Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F)
            ((aK.1 : E) * x) at hfun
      simpa [Aeq, Matrix.toLinearEquiv_apply] using hfun.symm
    have hfin : Module.finrank F E = 2 := by
      simpa [E] using FiniteField.finrank_extension F p 2
    have hcoeff : ∀ z : E, ∃ u v : F,
        u • (aK.1 : E) + v • (1 : E) = z := by
      have hLI : LinearIndependent F
          (![(aK.1 : E), 1] : Fin 2 → E) := by
        rw [linearIndependent_fin2]
        exact ⟨one_ne_zero, by
          intro r hr
          exact haK_not_scalar r (by simpa [Algebra.smul_def] using hr)⟩
      have hspan :
          Submodule.span F
              (Set.range (![(aK.1 : E), 1] : Fin 2 → E)) = ⊤ :=
        hLI.span_eq_top_of_card_eq_finrank (by simpa using hfin.symm)
      have hrange :
          Set.range (![(aK.1 : E), 1] : Fin 2 → E) =
            ({(aK.1 : E), 1} : Set E) := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
        · intro hz
          rcases hz with (rfl | hz)
          · exact ⟨0, by simp⟩
          · have : z = 1 := hz
            exact ⟨1, by simp [this]⟩
      intro z
      rw [hrange] at hspan
      apply Submodule.mem_span_pair.mp
      rw [hspan]
      exact Submodule.mem_top
    let d : E := Aeq 1
    have hd : d ≠ 0 := by
      intro hd0
      have h10 : (1 : E) = 0 := Aeq.injective (by simp [d, hd0])
      exact one_ne_zero h10
    let du : Eˣ := Units.mk0 d hd
    let phiLin : E →ₗ[F] E :=
      (Aeq.trans ((du⁻¹).mulLeftLinearEquiv F E)).toLinearMap
    have hphi_apply (z : E) : phiLin z = d⁻¹ * Aeq z := by
      change ((du.mulLeftLinearEquiv F E).symm) (Aeq z) = _
      rw [Units.symm_mulLeftLinearEquiv_apply]
      rfl
    have hphi_one : phiLin 1 = 1 := by
      rw [hphi_apply]
      change d⁻¹ * d = 1
      exact inv_mul_cancel₀ hd
    have hphi_a : phiLin (aK.1 : E) = yE := by
      rw [hphi_apply]
      have ha1 := hA_intertwine 1
      simp only [mul_one] at ha1
      rw [ha1]
      change d⁻¹ * (yE * d) = yE
      calc
        d⁻¹ * (yE * d) = d⁻¹ * (d * yE) := by rw [mul_comm yE d]
        _ = (d⁻¹ * d) * yE := by rw [mul_assoc]
        _ = yE := by rw [inv_mul_cancel₀ hd, one_mul]
    have hphi_a_mul (z : E) :
        phiLin ((aK.1 : E) * z) = phiLin (aK.1 : E) * phiLin z := by
      rw [hphi_apply, hphi_a, hphi_apply, hA_intertwine]
      ac_rfl
    have hphi_mul (z w : E) :
        phiLin (z * w) = phiLin z * phiLin w := by
      obtain ⟨u, v, hz⟩ := hcoeff z
      rw [← hz]
      simp only [add_mul, smul_mul_assoc, map_add, map_smul, hphi_a_mul,
        one_mul, hphi_one]
    let phiHom : E →ₐ[F] E := AlgHom.ofLinearMap phiLin hphi_one hphi_mul
    have hbij : Function.Bijective phiHom := by
      change Function.Bijective phiLin
      exact (Aeq.trans ((du⁻¹).mulLeftLinearEquiv F E)).bijective
    let phi : E ≃ₐ[F] E := AlgEquiv.ofBijective phiHom hbij
    have hphi (z : E) : phi z = d⁻¹ * Aeq z := by
      simpa [phi, phiHom] using hphi_apply z
    obtain ⟨i, hi, hpow⟩ :=
      FiniteField.Extension.exists_frob_pow_eq
        (k := F) (p := p) (n := 2) phi
    have hphi_cases : phi = 1 ∨ phi = sigma := by
      have hi_cases : i = 0 ∨ i = 1 := by omega
      rcases hi_cases with rfl | rfl
      · left
        simpa using hpow.symm
      · right
        simpa [sigma] using hpow.symm
    have hAeq_linear : Aeq.toLinearMap =
        Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) := by
      ext z
      simp [Aeq, Matrix.toLinearEquiv_apply]
    have hAeq_matrix :
        LinearMap.toMatrix b b Aeq.toLinearMap =
          (A : Matrix (Fin 2) (Fin 2) F) := by
      rw [hAeq_linear]
      exact LinearMap.toMatrix_toLin b b _
    rcases hphi_cases with hphi_id | hphi_sigma
    · have hAeq_mul (z : E) : Aeq z = d * z := by
        calc
          Aeq z = d * (d⁻¹ * Aeq z) := by
            rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
          _ = d * phi z := by rw [hphi]
          _ = d * z := by rw [hphi_id]; rfl
      have hAmatrix :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b d := by
        rw [← hAeq_matrix, Algebra.leftMulMatrix_apply]
        apply congrArg (LinearMap.toMatrix b b)
        ext z
        simpa [Algebra.lmul] using hAeq_mul z
      have hd_norm : Algebra.norm F d = 1 := by
        have hdet := A.property
        rw [hAmatrix, ← Algebra.norm_eq_matrix_det b] at hdet
        exact hdet
      let x : K :=
        ⟨Units.mk0 d hd, by
          change normUnits (Units.mk0 d hd) = 1
          apply Units.ext
          simpa [normUnits] using hd_norm⟩
      left
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change (A : Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b d
      exact hAmatrix
    · have hAeq_mul_sigma (z : E) : Aeq z = d * sigma z := by
        calc
          Aeq z = d * (d⁻¹ * Aeq z) := by
            rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
          _ = d * phi z := by rw [hphi]
          _ = d * sigma z := by rw [hphi_sigma]
      have hAmatrix :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b d * sigmaMat := by
        apply (Matrix.toLin b b).injective
        ext z
        rw [Matrix.toLin_mul_apply b b b (Algebra.leftMulMatrix b d)
          sigmaMat z]
        simp only [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
        change Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) z =
          d * Matrix.toLin b b sigmaMat z
        rw [show Matrix.toLin b b sigmaMat z = sigma z by
          simp [sigmaMat]]
        rw [← hAeq_mul_sigma z]
        rfl
      let u : E := d * c⁻¹
      have hu_ne : u ≠ 0 := mul_ne_zero hd (inv_ne_zero hc_ne)
      have hfactor :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b u *
              (frobSL : Matrix (Fin 2) (Fin 2) F) := by
        rw [hAmatrix]
        change Algebra.leftMulMatrix b d * sigmaMat =
          Algebra.leftMulMatrix b u *
            (Algebra.leftMulMatrix b c * sigmaMat)
        calc
          Algebra.leftMulMatrix b d * sigmaMat =
              Algebra.leftMulMatrix b ((d * c⁻¹) * c) * sigmaMat := by
                rw [show (d * c⁻¹) * c = d by
                  rw [mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]]
          _ = (Algebra.leftMulMatrix b (d * c⁻¹) *
              Algebra.leftMulMatrix b c) * sigmaMat := by rw [map_mul]
          _ = Algebra.leftMulMatrix b (d * c⁻¹) *
              (Algebra.leftMulMatrix b c * sigmaMat) := by
                rw [Matrix.mul_assoc]
      have hu_norm : Algebra.norm F u = 1 := by
        have hdet := congrArg Matrix.det hfactor
        rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b,
          A.property, frobSL.property, mul_one] at hdet
        exact hdet.symm
      let x : K :=
        ⟨Units.mk0 u hu_ne, by
          change normUnits (Units.mk0 u hu_ne) = 1
          apply Units.ext
          simpa [normUnits] using hu_norm⟩
      right
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change (A : Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b u *
          (frobSL : Matrix (Fin 2) (Fin 2) F)
      exact hfactor
  have hnonsplit_normalizer_lift_classification
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (hA :
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
            Subgroup.normalizer (nonsplitTorus.range : Set _)) :
      (∃ x : K, A = nonsplitSL x) ∨
        ∃ x : K, A = nonsplitSL x * frobSL := by
    have hnonsplit_range_one_lt : 1 < Nat.card nonsplitTorus.range := by
      rw [hnonsplit_range_card]
      have hq_one : 1 < Nat.card F := Finite.one_lt_card
      have hdpos : 0 < Nat.gcd (Nat.card F - 1) 2 :=
        Nat.gcd_pos_of_pos_right _ (by norm_num)
      by_cases hq2 : Nat.card F = 2
      · have hq2' : Fintype.card F = 2 := by
          simpa [Nat.card_eq_fintype_card] using hq2
        norm_num [hq2']
      · have hq3 : 3 ≤ Nat.card F := by omega
        have hdle : Nat.gcd (Nat.card F - 1) 2 ≤ 2 :=
          Nat.gcd_le_right _ (by norm_num)
        have hmul :
            2 * Nat.gcd (Nat.card F - 1) 2 ≤ Nat.card F + 1 := by omega
        have htwo :
            2 ≤ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 :=
          (Nat.le_div_iff_mul_le hdpos).2 hmul
        omega
    let : IsCyclic nonsplitTorus.range := hnonsplitTorus_cyclic
    obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := nonsplitTorus.range)
    have ht_ne : t ≠ 1 := by
      intro ht_one
      have hall_one : ∀ u : nonsplitTorus.range, u = 1 := by
        intro u
        simpa [ht_one] using ht u
      have : Subsingleton nonsplitTorus.range :=
        ⟨fun u v => (hall_one u).trans (hall_one v).symm⟩
      have hcard_one : Nat.card nonsplitTorus.range = 1 := Nat.card_unique
      omega
    rcases t.property with ⟨aK, haK⟩
    have haK_not_ker : aK ∉ nonsplitTorus.ker := by
      intro hak
      apply ht_ne
      apply Subtype.ext
      change (t : PSL2MatrixGroup F) = 1
      rw [← haK]
      exact hak
    have hconj_mem :
        (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A *
              nonsplitTorus aK *
                ((QuotientGroup.mk' (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F))) A)⁻¹ ∈
          nonsplitTorus.range :=
      (Subgroup.mem_normalizer_iff.mp hA (nonsplitTorus aK)).mp
        ⟨aK, rfl⟩
    exact hnonsplit_lift_classification_of_conj
      A aK haK_not_ker hconj_mem
  have hnonsplit_normalizer_sub_candidate :
      Subgroup.normalizer (nonsplitTorus.range : Set _) ≤
        nonsplitDihedralCandidate := by
    intro g hg
    refine QuotientGroup.induction_on g ?_ hg
    intro A hA
    rcases hnonsplit_normalizer_lift_classification A hA with
      ⟨x, hx⟩ | ⟨x, hx⟩
    · have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      change (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
          nonsplitDihedralCandidate
      rw [hx]
      exact (show nonsplitTorus.range ≤ nonsplitDihedralCandidate from
        le_sup_left) hxT
    · have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      have hfrob : frobPSL ∈ Subgroup.zpowers frobPSL :=
        Subgroup.mem_zpowers frobPSL
      change (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
          nonsplitDihedralCandidate
      rw [hx]
      change nonsplitTorus x * frobPSL ∈ nonsplitDihedralCandidate
      exact nonsplitDihedralCandidate.mul_mem
        ((show nonsplitTorus.range ≤ nonsplitDihedralCandidate from
          le_sup_left) hxT)
        ((show Subgroup.zpowers frobPSL ≤ nonsplitDihedralCandidate from
          le_sup_right) hfrob)
  have hnonsplit_normalizer_eq_candidate :
      Subgroup.normalizer (nonsplitTorus.range : Set _) =
        nonsplitDihedralCandidate :=
    le_antisymm hnonsplit_normalizer_sub_candidate
      hnonsplitCandidate_le_normalizer
  have hnonsplit_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ nonsplitTorus.range → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ nonsplitTorus.range →
            g ∈ Subgroup.normalizer
              (nonsplitTorus.range : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨aK, rfl⟩
    have haK_not_ker : aK ∉ nonsplitTorus.ker := by
      intro haK
      apply hy_ne
      exact haK
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hnonsplit_lift_classification_of_conj
        A aK haK_not_ker hAconj with ⟨x, hx⟩ | ⟨x, hx⟩
    · change (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      rw [hx]
      change nonsplitTorus x ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      exact Subgroup.le_normalizer ⟨x, rfl⟩
    · change (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      rw [hx]
      change nonsplitTorus x * frobPSL ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      have hxN : nonsplitTorus x ∈
          Subgroup.normalizer
            (nonsplitTorus.range : Set (PSL2MatrixGroup F)) :=
        Subgroup.le_normalizer hxT
      have hfrobN : frobPSL ∈ Subgroup.normalizer
          (nonsplitTorus.range : Set (PSL2MatrixGroup F)) :=
        hfrobPSL_mem_normalizer
      exact (Subgroup.normalizer
          (nonsplitTorus.range : Set (PSL2MatrixGroup F))).mul_mem
        hxN hfrobN
  have hnonsplit_comm {x y : PSL2MatrixGroup F}
      (hx : x ∈ nonsplitTorus.range)
      (hy : y ∈ nonsplitTorus.range) : Commute x y := by
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    change nonsplitTorus a * nonsplitTorus b =
      nonsplitTorus b * nonsplitTorus a
    simp only [← map_mul]
    rw [mul_comm]
  have hnonsplit_normalizer_eq_candidate_of_le
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ nonsplitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) =
        nonsplitDihedralCandidate := by
    apply le_antisymm
    · intro g hg
      apply hnonsplit_normalizer_sub_candidate
      obtain ⟨r, hr_ne_one⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
      have hr_ne_one' : (r : PSL2MatrixGroup F) ≠ 1 := by
        intro hr
        apply hr_ne_one
        apply Subtype.ext
        exact hr
      have hgr : g * (r : PSL2MatrixGroup F) * g⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hg (r : PSL2MatrixGroup F)).mp
          r.property
      exact hnonsplit_weakTI (r : PSL2MatrixGroup F)
        (hR_le r.property) hr_ne_one' g (hR_le hgr)
    · apply sup_le
      · intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hnonsplit_comm ht (hR_le hy)
          simpa [hcomm.eq, mul_assoc] using hy
        · intro hy
          have hy' : y = t⁻¹ * (t * y * t⁻¹) * t := by
            simp [mul_assoc]
          have hconjR : t * y * t⁻¹ ∈ R := hy
          have hcomm := hnonsplit_comm
            (nonsplitTorus.range.inv_mem ht) (hR_le hconjR)
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
          have hconj : frobPSL * y * frobPSL⁻¹ = y⁻¹ := by
            rw [← ha]
            simpa using hfrobPSL_conj a
          rw [hconj]
          exact hy_inv
        · intro hy
          have hyT : frobPSL * y * frobPSL⁻¹ ∈
              nonsplitTorus.range := hR_le hy
          rcases hyT with ⟨a, ha⟩
          have hrecover : y = nonsplitTorus a⁻¹ := by
            calc
              y = frobPSL⁻¹ *
                  (frobPSL * y * frobPSL⁻¹) * frobPSL := by
                    simp [mul_assoc]
              _ = frobPSL⁻¹ * nonsplitTorus a * frobPSL := by
                    rw [← ha]
              _ = nonsplitTorus a⁻¹ := by
                have hfrob_inv : frobPSL⁻¹ = frobPSL :=
                  (eq_inv_of_mul_eq_one_left
                    (by simpa [pow_two] using hfrobPSL_sq)).symm
                simpa [hfrob_inv] using hfrobPSL_conj a
          have hy_inv : (frobPSL * y * frobPSL⁻¹)⁻¹ ∈ R :=
            R.inv_mem hy
          rw [hrecover]
          rw [← ha] at hy_inv
          simpa using hy_inv
  refine ⟨nonsplitTorus.range, hnonsplitTorus_cyclic,
    hnonsplit_range_card, ?_, ?_, hnonsplit_weakTI, ?_⟩
  · rw [hnonsplit_normalizer_eq_candidate, hnonsplitCandidate_card,
      hnonsplit_range_card]
  · refine ⟨frobPSL, hfrobPSL_mem_normalizer,
      hfrobPSL_not_mem_torus, ?_, ?_, ?_, ?_⟩
    · simpa [pow_two] using hfrobPSL_sq
    · intro t ht
      rcases ht with ⟨a, rfl⟩
      simpa using hfrobPSL_conj a
    · simpa [nonsplitDihedralCandidate] using
        hnonsplitCandidate_card_raw
    · intro R hR hRne
      simpa [nonsplitDihedralCandidate] using
        hnonsplit_normalizer_eq_candidate_of_le R hR hRne
  · intro A _hdisc_nonzero heigen
    let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
      QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))
    let M : Matrix (Fin 2) (Fin 2) F := A
    let χ : Polynomial F := M.charpoly
    have hχdeg : χ.natDegree = 2 := by
      simp [χ, M]
    have hχne : χ ≠ 0 := by
      exact (Matrix.charpoly_monic M).ne_zero
    have hno_root (μ : F) : ¬ χ.IsRoot μ := by
      intro hroot
      have hdet_zero :
          (Matrix.scalar (Fin 2) μ - M).det = 0 := by
        rw [← Matrix.eval_charpoly]
        exact hroot
      obtain ⟨v, hv_ne, hv⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
      apply heigen
      refine ⟨μ, v, hv_ne, ?_⟩
      have hscalar :
          (Matrix.scalar (Fin 2) μ).mulVec v = μ • v := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [Matrix.sub_mulVec, hscalar] at hv
      exact (sub_eq_zero.mp hv).symm
    have hχroots : χ.roots = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro μ hμ
      exact hno_root μ ((Polynomial.mem_roots hχne).mp hμ)
    have hχirreducible : Irreducible χ := by
      apply ((Matrix.charpoly_monic M).irreducible_iff_roots_eq_zero_of_degree_le_three
        (by rw [hχdeg]) (by rw [hχdeg]; norm_num)).mpr
      exact hχroots
    have : Fact (Irreducible χ) := ⟨hχirreducible⟩
    let : Algebra F (AdjoinRoot χ) := AdjoinRoot.instAlgebra χ
    let : Module F (AdjoinRoot χ) := Algebra.toModule
    have hfinrankL : Module.finrank F (AdjoinRoot χ) = 2 := by
      calc
        Module.finrank F (AdjoinRoot χ) =
            (AdjoinRoot.powerBasis hχne).dim :=
          (AdjoinRoot.powerBasis hχne).finrank
        _ = χ.natDegree := AdjoinRoot.powerBasis_dim hχne
        _ = 2 := hχdeg
    let eL : AdjoinRoot χ ≃ₐ[F] E :=
      FiniteField.algEquivExtension F p 2 (AdjoinRoot χ) hfinrankL
    let α : E := eL (AdjoinRoot.root χ)
    have hα_root : (χ.map (algebraMap F E)).IsRoot α := by
      have hrootL := AdjoinRoot.isRoot_root χ
      have hrootE :
          ((χ.map (AdjoinRoot.of χ)).map eL.toRingEquiv.toRingHom).IsRoot
            (eL (AdjoinRoot.root χ)) := hrootL.map
      rw [Polynomial.map_map] at hrootE
      convert hrootE using 1
      congr 1
      ext r
      simp [eL]
    have hα_not_scalar (r : F) : algebraMap F E r ≠ α := by
      intro hr
      apply hno_root r
      apply (Polynomial.isRoot_map_iff
        ((algebraMap F E).injective)).mp
      rw [hr]
      exact hα_root
    have hdetA : M.det = 1 := by
      exact A.property
    have hα_poly : α ^ 2 - algebraMap F E (Matrix.trace M) * α + 1 = 0 := by
      have h := hα_root
      simpa [Polynomial.IsRoot, χ, Matrix.charpoly_fin_two, hdetA] using h
    have hα_sq : α * α = algebraMap F E (Matrix.trace M) * α - 1 := by
      rw [pow_two] at hα_poly
      linear_combination hα_poly
    let αfamily : Fin 2 → E := ![α, 1]
    have hαLI : LinearIndependent F αfamily := by
      rw [linearIndependent_fin2]
      refine ⟨one_ne_zero, ?_⟩
      intro r hr
      exact hα_not_scalar r (by
        simpa [αfamily, Algebra.smul_def] using hr)
    have hfinrankE : Module.finrank F E = 2 := by
      simpa [E] using FiniteField.finrank_extension F p 2
    let bα : Module.Basis (Fin 2) F E :=
      basisOfLinearIndependentOfCardEqFinrank hαLI (by
        simp [hfinrankE])
    let v : Fin 2 → F := ![1, 0]
    let w : Fin 2 → F := M.mulVec v
    have hv_ne : v ≠ 0 := by
      intro hv
      have := congrFun hv 0
      simp [v] at this
    let Afamily : Fin 2 → (Fin 2 → F) := ![w, v]
    have hALI : LinearIndependent F Afamily := by
      rw [linearIndependent_fin2]
      refine ⟨hv_ne, ?_⟩
      intro μ hμ
      apply heigen
      refine ⟨μ, v, hv_ne, ?_⟩
      simpa [Afamily, w] using hμ.symm
    let bA : Module.Basis (Fin 2) F (Fin 2 → F) :=
      basisOfLinearIndependentOfCardEqFinrank hALI (by simp)
    have hbα_zero : bα 0 = α := by
      simp [bα, αfamily]
    have hbα_one : bα 1 = 1 := by
      simp [bα, αfamily]
    have hbA_zero : bA 0 = w := by
      simp [bA, Afamily]
    have hbA_one : bA 1 = v := by
      simp [bA, Afamily]
    let H : E ≃ₗ[F] (Fin 2 → F) := bα.equiv bA (Equiv.refl (Fin 2))
    have hH_basis (i : Fin 2) : H (bα i) = bA i := by
      simp [H]
    have hH_alpha : H α = w := by
      rw [← hbα_zero, hH_basis, hbA_zero]
    have hH_one : H 1 = v := by
      rw [← hbα_one, hH_basis, hbA_one]
    have hdet_coord :
        M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hdetA
    have hAw : M.mulVec w = Matrix.trace M • w - v := by
      ext i
      fin_cases i
      · simp [w, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
        linear_combination -hdet_coord
      · simp [w, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
        ring
    have hlin :
        H.toLinearMap.comp (Algebra.lmul F E α) =
          M.mulVecLin.comp H.toLinearMap := by
      apply Module.Basis.ext bα
      intro i
      fin_cases i
      · change H (α * bα 0) = M.mulVec (H (bα 0))
        rw [hbα_zero, hH_alpha]
        calc
          H (α * α) = H (algebraMap F E (Matrix.trace M) * α - 1) :=
            congrArg H hα_sq
          _ = Matrix.trace M • H α - H 1 := by
            change H (Matrix.trace M • α - 1) = _
            rw [map_sub, map_smul]
          _ = Matrix.trace M • w - v := by rw [hH_alpha, hH_one]
          _ = M.mulVec w := hAw.symm
      · change H (α * bα 1) = M.mulVec (H (bα 1))
        rw [hbα_one, mul_one, hH_alpha, hH_one]
    let std : Module.Basis (Fin 2) F (Fin 2 → F) := Pi.basisFun F (Fin 2)
    let D : Matrix (Fin 2) (Fin 2) F :=
      LinearMap.toMatrix b std H.toLinearMap
    let B : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix b α
    have hMmatrix : LinearMap.toMatrix std std M.mulVecLin = M := by
      change LinearMap.toMatrix' (Matrix.toLin' M) = M
      exact LinearMap.toMatrix'_toLin' M
    have hMD : M * D = D * B := by
      calc
        M * D =
            LinearMap.toMatrix std std M.mulVecLin *
              LinearMap.toMatrix b std H.toLinearMap := by rw [hMmatrix]
        _ = LinearMap.toMatrix b std
            (M.mulVecLin.comp H.toLinearMap) :=
          (LinearMap.toMatrix_comp b std std M.mulVecLin H.toLinearMap).symm
        _ = LinearMap.toMatrix b std
            (H.toLinearMap.comp (Algebra.lmul F E α)) := by rw [hlin]
        _ = LinearMap.toMatrix b std H.toLinearMap *
            LinearMap.toMatrix b b (Algebra.lmul F E α) :=
          LinearMap.toMatrix_comp b b std H.toLinearMap (Algebra.lmul F E α)
        _ = D * B := by rfl
    have hDunit : IsUnit D.det := by
      change IsUnit (LinearMap.toMatrix b std H.toLinearMap).det
      exact H.isUnit_det b std
    have hDne : D.det ≠ 0 := hDunit.ne_zero
    have hdet_eq := congrArg Matrix.det hMD
    rw [Matrix.det_mul, Matrix.det_mul] at hdet_eq
    have hBdet : B.det = 1 := by
      apply mul_left_cancel₀ hDne
      calc
        D.det * B.det = M.det * D.det := hdet_eq.symm
        _ = 1 * D.det := by rw [hdetA]
        _ = D.det * 1 := by simp
    have hnormα : Algebra.norm F α = 1 := by
      calc
        Algebra.norm F α = B.det := by
          simpa [B] using Algebra.norm_eq_matrix_det b α
        _ = 1 := hBdet
    have hαne : α ≠ 0 := by
      intro hα
      have := hnormα
      rw [hα, Algebra.norm_zero] at this
      exact zero_ne_one this
    let αunit : Eˣ := Units.mk0 α hαne
    let xK : K := ⟨αunit, by
      change normUnits αunit = 1
      apply Units.ext
      simpa [normUnits, αunit] using hnormα⟩
    obtain ⟨d, hd⟩ := hDunit
    obtain ⟨c, hc⟩ := hnormUnits_surjective d⁻¹
    have hcval : Algebra.norm F (c : E) = (d⁻¹ : Fˣ) := by
      have hc' := congrArg Units.val hc
      simpa [normUnits] using hc'
    let Lc : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix b (c : E)
    let Gmat : Matrix (Fin 2) (Fin 2) F := D * Lc
    have hGdet : Gmat.det = 1 := by
      change (D * Lc).det = 1
      rw [Matrix.det_mul]
      change D.det * (Algebra.leftMulMatrix b (c : E)).det = 1
      rw [← Algebra.norm_eq_matrix_det b, hcval, ← hd]
      exact Units.mul_inv d
    let G : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Gmat, hGdet⟩
    have hBLc : B * Lc = Lc * B := by
      calc
        B * Lc = Algebra.leftMulMatrix b (α * (c : E)) := by
          simp [B, Lc]
        _ = Algebra.leftMulMatrix b ((c : E) * α) := by rw [mul_comm]
        _ = Lc * B := by simp [B, Lc]
    have hMG : M * Gmat = Gmat * B := by
      calc
        M * Gmat = (M * D) * Lc := by simp [Gmat, Matrix.mul_assoc]
        _ = (D * B) * Lc := by rw [hMD]
        _ = D * (B * Lc) := by rw [Matrix.mul_assoc]
        _ = D * (Lc * B) := by rw [hBLc]
        _ = (D * Lc) * B := by rw [Matrix.mul_assoc]
        _ = Gmat * B := rfl
    have hxB :
        (nonsplitSL xK : Matrix.SpecialLinearGroup (Fin 2) F) =
          ⟨B, hBdet⟩ := by
      apply Subtype.ext
      rfl
    have hMGsl : A * G = G * nonsplitSL xK := by
      apply Subtype.ext
      change M * Gmat = Gmat * (nonsplitSL xK : Matrix.SpecialLinearGroup (Fin 2) F).1
      rw [hxB]
      exact hMG
    have hA_factor : A = G * nonsplitSL xK * G⁻¹ := by
      calc
        A = (A * G) * G⁻¹ := by simp
        _ = (G * nonsplitSL xK) * G⁻¹ := by rw [hMGsl]
    refine ⟨qSL G, ?_⟩
    refine ⟨nonsplitTorus xK, ⟨xK, rfl⟩, ?_⟩
    change qSL G * nonsplitTorus xK * (qSL G)⁻¹ = qSL A
    rw [hA_factor]
    simp [nonsplitTorus, qSL]
-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

end Dickson
end Glauberman


end Source10

end CFSGPackNonsplit
