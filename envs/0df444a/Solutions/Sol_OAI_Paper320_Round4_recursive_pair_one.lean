-- Prove2me | solution 1 for OAI.Paper320.Round4.recursive_pair_one
-- status  : ACCEPTED   (prove)
-- author  : @Leo Shaposhnik
-- created : 2026-10-17T14:15:02.280112+00:00
-- url     : https://prove2.me/submissions/0ede80f0-97b1-434b-a6f6-dcc13438c67c

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity continuation commit 032868f.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Credit: Robin Kothari, accepted Prove2Me2.05 amplifier, theorem
4807ab9c-ddde-49d8-83cf-3532a7f795c3; construction adapted with
the local sharp gate refinement and complete verification.
Original modules used in this file:
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveProfiles.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveDefinitions.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Basic.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveFlips.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveSets.lean
  lean/round2-sharp/Round4/PairTransfer.lean
Modifications: mechanical skeleton subtraction, import rewriting,
and a root solution alias with the same elaborated theorem type.
Copied upstream files previously received only the documented Lean
conditional-proof lemma-name port; mathematical definitions and
statements were preserved. This generated file is local staging.

Upstream Apache2 license (full text):
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

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity continuation commit 032868f.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Credit: Robin Kothari, accepted Prove2Me2.05 amplifier, theorem
4807ab9c-ddde-49d8-83cf-3532a7f795c3; construction adapted with
the local sharp gate refinement and complete verification.
Original modules used in this file:
  lean/round2-sharp/Round4/PairTransfer.lean
Modifications: mechanical skeleton subtraction, import rewriting,
and a root solution alias with the same elaborated theorem type.
Copied upstream files previously received only the documented Lean
conditional-proof lemma-name port; mathematical definitions and
statements were preserved. This generated file is local staging.

Upstream Apache2 license (full text):
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

import Definitions.Def_BS2055_Round4_SeedB

open scoped Classical



namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320



theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this





















end Paper320

end

end OAI




namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320







theorem gateIndex_antitone {h : ℕ} {q q' : Fin h} (hqq : q ≤ q') :
    gateIndex q' ≤ gateIndex q := by
  exact Fin.rev_le_rev.mpr hqq













theorem rowClause_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) {q q' : Fin h} (hqq : q ≤ q')
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : rowClause T label F q' x i = true) : rowClause T label F q x i = true := by
  rw [rowClause_eq_true_iff] at hi ⊢
  refine ⟨hi.1, fun j hij => ?_⟩
  exact hF.rejects_of_le (gateIndex_antitone hqq) (hi.2 j hij)







end Paper320

end

end OAI




namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}











theorem flip_prod_same (x : J × I → Bool) (j : J) (i : I) :
    (fun a => flip x {(j, i)} (j, a)) = flip (fun a => x (j, a)) {i} := by
  funext a
  simp [flip]

theorem flip_prod_other (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [flip, hk]



section Finite

variable [Fintype I]































end Finite
end Paper320

end

end OAI




namespace OAI

/-! A raw bit belongs to one child and changes at most one condition of a clause. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (flip x {((j, c), a)}) j c = flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

theorem rowClause_eq_of_conditions {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x y : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (ht : ∀ c, F (Fin.last h) (recursiveChild x i c) =
      F (Fin.last h) (recursiveChild y i c))
    (hg : ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) =
      F (gateIndex q) (recursiveChild y j (label i j))) :
    rowClause T label F q x i = rowClause T label F q y i := by
  apply Bool.eq_iff_iff.mpr
  rw [rowClause_eq_true_iff, rowClause_eq_true_iff]
  constructor
  · rintro ⟨hxt, hxg⟩
    exact ⟨fun c => (ht c).symm.trans (hxt c),
      fun j hij => (hg j hij).symm.trans (hxg j hij)⟩
  · rintro ⟨hyt, hyg⟩
    exact ⟨fun c => (ht c).trans (hyt c),
      fun j hij => (hg j hij).trans (hyg j hij)⟩

theorem rowClause_flip_eq {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (ht : j = i → F (Fin.last h) (flip (recursiveChild x j c) {a}) =
      F (Fin.last h) (recursiveChild x j c))
    (hg : T.Adj i j → c = label i j →
      F (gateIndex q) (flip (recursiveChild x j c) {a}) =
        F (gateIndex q) (recursiveChild x j c)) :
    rowClause T label F q (flip x {((j, c), a)}) i = rowClause T label F q x i := by
  apply rowClause_eq_of_conditions
  · intro c'
    by_cases heq : (i, c') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact ht rfl
    · rw [recursiveChild_flip_other x j i c c' a heq]
  · intro j' hij'
    by_cases heq : (j', label i j') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact hg hij' rfl
    · rw [recursiveChild_flip_other x j j' c (label i j') a heq]

theorem rowClause_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c)) := by
  by_contra hn
  apply hc
  apply rowClause_flip_eq
  · intro hji
    by_contra hne
    exact hn (Or.inl ⟨hji, hne⟩)
  · intro hij hcl
    by_contra hne
    exact hn (Or.inr ⟨hij, hcl, hne⟩)

end Paper320

end

end OAI




namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320















theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

theorem rowClause_joint_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q q' : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i)
    (hc' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c) ∧
      F (gateIndex q') (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q') (recursiveChild x j c)) := by
  rcases rowClause_flip_change T label F q x i j c a hc with ht | ⟨hij, hcl, hq⟩
  · exact Or.inl ht
  · rcases rowClause_flip_change T label F q' x i j c a hc' with ht | hg
    · exact False.elim ((T.ne_of_adj hij) ht.1.symm)
    · exact Or.inr ⟨hij, hcl, hq, hg.2.2⟩

end Paper320

end

end OAI




/-!
Arbitrary forbidden-set thresholds and pair-indexed sensitivity transfer.
Adapted from Robin Kothari's accepted Prove2Me 2.05 proof:
https://prove2.me/theorems/4807ab9c-ddde-49d8-83cf-3532a7f795c3
and OpenAI/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a
(Apache-2.0), together with the local Sharp gate-sink refinement. Original
OpenAI and contributing authors retain their attribution. The zero transfer
uses at most one nonsink when a sink exists, and needs no comparison between
its two pair-profile budgets. These are generic pointwise transfer lemmas.
-/
namespace OAI.Paper320.Round4
noncomputable section
open scoped Classical





theorem PairBound.self {h : ℕ} {I : Type} [Fintype I]
    {F : Fin h → (I → Bool) → Bool} {b : Bool} {V : Fin h → Fin h → ℕ}
    (hV : PairBound F b V) (q : Fin h) (x : I → Bool) (hx : F q x = b) :
    sensitivityAt (F q) x ≤ V q q := by
  simpa only [jointSensitivityAt, and_self, sensitivityAt] using hV q q le_rfl x hx hx







theorem recursive_pair_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (Z Y : Fin (h + 1) → Fin (h + 1) → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (q q' : Fin h) (hqq : q ≤ q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * Z (gateIndex q') (gateIndex q) + r * Y (Fin.last h) (Fin.last h) := by
  obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx'
  have hi := rowClause_nested T label F hF hqq x i hi'
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  have hcond' := (rowClause_eq_true_iff T label F q' x i).mp hi'
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion fun j =>
    childJointChanges F (gateIndex q') (gateIndex q) x j (label i j)
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T label F q (flip x {p}) ≠ recursiveFamily T label F q x ∧
      recursiveFamily T label F q' (flip x {p}) ≠ recursiveFamily T label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hf : recursiveFamily T label F q (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.1 (hy.trans hx.symm))
    have hf' : recursiveFamily T label F q' (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q' (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
    have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
    have hif' := (recursiveFamily_eq_false_iff T label F q' _).mp hf' i
    have hic : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
      simp [hi, hif]
    have hic' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i := by
      simp [hi', hif']
    rcases rowClause_joint_flip_change T label F q q' x i j c a hic hic' with
      ⟨rfl, ht⟩ | ⟨hij, rfl, hg, hg'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        by simpa [childJointChanges] using And.intro hg' hg⟩
  have hU : U.card ≤ r * Y (Fin.last h) (Fin.last h) := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (Y (Fin.last h) (Fin.last h))
      (fun c _ => by
        rw [childChanges_card]
        exact PairBound.self hY (Fin.last h) _ (hcond.1 c))
  have hV : V.card ≤ o * Z (gateIndex q') (gateIndex q) := by
    simpa only [V, ho i] using card_biUnion_le_mul (Finset.univ.filter (T.Adj i))
      (fun j => childJointChanges F (gateIndex q') (gateIndex q) x j (label i j))
      (Z (gateIndex q') (gateIndex q)) (fun j hj => by
        have hij := (Finset.mem_filter.mp hj).2
        rw [childJointChanges_card]
        exact hZ _ _ (gateIndex_antitone hqq) _ (hcond'.2 j hij) (hcond.2 j hij))
  calc
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
        (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ r * Y (Fin.last h) (Fin.last h) + o * Z (gateIndex q') (gateIndex q) := Nat.add_le_add hU hV
    _ = _ := Nat.add_comm _ _







end
end OAI.Paper320.Round4


theorem solution :
  ∀ {k r h : ℕ} {I : Type} [inst : Fintype I] (T : OAI.Paper320.Tournament k) (label : Fin k → Fin k → Fin r)
  (F : Fin (h + 1) → (I → Bool) → Bool),
  OAI.Paper320.NestedFamily F →
    ∀ (o : ℕ),
      (∀ (i : Fin k), (Finset.filter (T.Adj i) Finset.univ).card = o) →
        ∀ (Z Y : Fin (h + 1) → Fin (h + 1) → ℕ),
          OAI.Paper320.Round4.PairBound F Bool.false Z →
            OAI.Paper320.Round4.PairBound F Bool.true Y →
              ∀ (q q' : Fin h),
                q ≤ q' →
                  ∀ (x : (Fin k × Fin r) × I → Bool),
                    OAI.Paper320.recursiveFamily T label F q x = Bool.true →
                      OAI.Paper320.recursiveFamily T label F q' x = Bool.true →
                        OAI.Paper320.jointSensitivityAt (OAI.Paper320.recursiveFamily T label F q)
                            (OAI.Paper320.recursiveFamily T label F q') x ≤
                          o * Z (OAI.Paper320.gateIndex q') (OAI.Paper320.gateIndex q) + r * Y (Fin.last h) (Fin.last h) := @OAI.Paper320.Round4.recursive_pair_one
