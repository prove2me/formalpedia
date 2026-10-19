-- Prove2me | solution 1 for OAI.Paper320.Round4.achieves_2055
-- status  : ACCEPTED   (prove)
-- author  : @Leo Shaposhnik
-- created : 2026-10-17T14:27:21.132897+00:00
-- url     : https://prove2.me/submissions/d7ca477e-71fb-48b4-8695-9a284976a5e5

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
  lean/round2-sharp/Round4/PairTransfer.lean
  lean/round2-sharp/Round4/Base.lean
  lean/round2-sharp/Round4/Amplifier.lean
  lean/round2-sharp/Round4/Arithmetic.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Reindex.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Iterates.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Or.lean
  lean/round2-growth/Growth.lean
  lean/round2-sharp/Round4/Result.lean
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
  lean/round2-sharp/Round4/Result.lean
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
import Theorems.Thm_OAI_Paper320_Round2Growth_ZeroBranch_reindex
import Theorems.Thm_OAI_Paper320_Round2Growth_iterate_zeroBranch
import Theorems.Thm_OAI_Paper320_Round2Growth_or_zeroBranch
import Theorems.Thm_OAI_Paper320_Round4_base_bounds
import Theorems.Thm_OAI_Paper320_Round4_recursive_pair_one
import Theorems.Thm_OAI_Paper320_Round4_recursive_pair_zero
import Theorems.Thm_OAI_Paper320_power_amplification

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









theorem flip_insert (x : I → Bool) (i : I) (B : Finset I) (hi : i ∉ B) :
    flip x (insert i B) = flip (flip x B) {i} := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flip, hi]
  · simp [flip, hji]







section Finite

variable [Fintype I]

theorem flip_differences (x y : I → Bool) :
    flip x (Finset.univ.filter fun i => x i ≠ y i) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [flip, hx, hy]

theorem sensitivityAt_le_card (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ Fintype.card I :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem sensitivityAt_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem sensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, sensitivityAt f x ≤ n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x

theorem sensitivityAt_eq_zero_iff (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x = 0 ↔ ∀ i, f (flip x {i}) = f x := by
  simp [sensitivityAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]





theorem blockSensitivityAt_le_blockSensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f :=
  Finset.le_sup (Finset.mem_univ x)





theorem blockSensitivityAt_le (f : (I → Bool) → Bool) (x : I → Bool) {n : ℕ}
    (h : ∀ blocks : Finset (Finset I),
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) →
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) → blocks.card ≤ n) :
    blockSensitivityAt f x ≤ n := by
  apply Finset.sup_le
  intro blocks _
  split_ifs with hb
  · exact h blocks hb.1 hb.2
  · exact Nat.zero_le _





theorem eq_of_singleton_invariant (f : (I → Bool) → Bool)
    (h : ∀ x i, f (flip x {i}) = f x) (x y : I → Bool) : f x = f y := by
  have hflip (B : Finset I) : f (flip x B) = f x := by
    induction B using Finset.induction with
    | empty => simp
    | @insert i B hi ih => rw [flip_insert x i B hi, h, ih]
  rw [← flip_differences x y, hflip]

theorem sensitivity_pos_of_nonconstant (f : (I → Bool) → Bool)
    (h : ∃ x y, f x ≠ f y) : 0 < sensitivity f := by
  by_contra hn
  have hz : sensitivity f = 0 := Nat.eq_zero_of_not_pos hn
  have hi (x : I → Bool) (i : I) : f (flip x {i}) = f x := by
    apply (sensitivityAt_eq_zero_iff f x).mp _ i
    exact Nat.eq_zero_of_le_zero ((sensitivityAt_le_sensitivity f x).trans_eq hz)
  obtain ⟨x, y, hxy⟩ := h
  exact hxy (eq_of_singleton_invariant f hi x y)

end Finite
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















end
end OAI.Paper320.Round4




/-! Three nested thresholds preserve disjoint block witnesses while producing
zero off-diagonal pair sensitivity. This is a generic base for amplification. -/
namespace OAI.Paper320.Round4





set_option maxRecDepth 100000
set_option maxHeartbeats 0









noncomputable section
open scoped Classical



theorem threshold_nested : NestedFamily threshold := by
  constructor
  intro q q' x hqq hx
  simp only [threshold, decide_eq_true_eq] at hx ⊢
  exact le_trans (by omega) hx







theorem base_nested {I : Type} (g : (I → Bool) → Bool) : NestedFamily (base g) := by
  constructor
  intro q q' x hqq hx
  exact threshold_nested.accepts_of_le hqq hx

















end
end OAI.Paper320.Round4




/-! Repeatable threshold amplifier, adapted from Robin Kothari's accepted
Prove2Me 2.05 solution (theorem 4807ab9c-ddde-49d8-83cf-3532a7f795c3),
read 17 October 2026. The threshold reset and block lifting are that source's
construction. The gate max bound is the Round4 refinement of our Sharp proof.
Upstream OpenAI/math source: 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
Apache-2.0. Attribution is retained; no independent novelty claim is made. -/
namespace OAI.Paper320.Round4
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048













theorem clip_mono : Monotone clip := by
  intro i j hij
  change min i.val 2 ≤ min j.val 2
  exact min_le_min_right 2 hij
@[simp] theorem clip_gate (q : Fin 3) : clip (gateIndex q) = Fin.rev q := by
  fin_cases q <;> rfl
@[simp] theorem clip_last : clip (Fin.last 3) = 2 := rfl
@[simp] theorem clip_three : clip 3 = 2 := rfl


theorem extend_nested {I : Type} {F : Fin 3 → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (extend F) := by
  constructor
  intro q q' x hqq hx
  exact hF.accepts_of_le (clip_mono hqq) hx



theorem step_nested {I : Type} {F : Fin 3 → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (step F) := by
  constructor
  intro q q' x hqq hx
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff _ _ _ _ _).mp hx
  apply (recursiveFamily_eq_true_iff _ _ _ _ _).mpr
  exact ⟨i, rowClause_nested _ _ _ (extend_nested hF) hqq x i hi⟩



private theorem max_mul_nat (a b u : ℕ) : max (a*u) (b*u) = max a b * u := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, max_eq_right (Nat.mul_le_mul_right u hab)]
  · have hba : b ≤ a := by omega
    rw [max_eq_left hba, max_eq_left (Nat.mul_le_mul_right u hba)]

private theorem max_sum_scale (a b u : ℕ) :
    max (a*u+b*u) (3*(b*u)) = max (a+b) (3*b)*u := by
  rw [← Nat.add_mul, ← Nat.mul_assoc, max_mul_nat]

theorem step_bounds {I : Type} [Fintype I]
    (F : Fin 3 → (I → Bool) → Bool) (hF : NestedFamily F) (d u : ℕ)
    (hz : PairBound F false (fun i j => (profiles d).1 i j*u))
    (hy : PairBound F true (fun i j => (profiles d).2 i j*u)) :
    PairBound (step F) false (fun i j => (profiles (d+1)).1 i j*u) ∧
    PairBound (step F) true (fun i j => (profiles (d+1)).2 i j*u) := by
  have hz' : PairBound (extend F) false
      (fun i j => (profiles d).1 (clip i) (clip j)*u) := by
    intro i j hij x hx hx'; exact hz _ _ (clip_mono hij) x hx hx'
  have hy' : PairBound (extend F) true
      (fun i j => (profiles d).2 (clip i) (clip j)*u) := by
    intro i j hij x hx hx'; exact hy _ _ (clip_mono hij) x hx hx'
  constructor
  · intro q q' hqq x hx hx'
    have hh := recursive_pair_zero tournament labeling (extend F) (extend_nested hF)
      (by norm_num) _ _ hz' hy' q q' hqq x hx hx'
    simpa [step, profiles, Nat.add_mul, Nat.mul_assoc, max_sum_scale] using hh
  · intro q q' hqq x hx hx'
    have hh := recursive_pair_one tournament labeling.label (extend F) (extend_nested hF)
      H (cyclicTournament_outdegree H) _ _ hz' hy' q q' hqq x hx hx'
    simpa [step, profiles, Nat.add_mul, Nat.mul_assoc] using hh




theorem levels_nested {I : Type} (g : (I → Bool) → Bool) (d : ℕ) :
    NestedFamily (levels g d) := by
  induction d with
  | zero => exact base_nested g
  | succ d ih => exact step_nested ih
theorem levels_bounds {I : Type} [Fintype I] (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ C*u) (d : ℕ) :
    PairBound (levels g d) false (fun i j => (profiles d).1 i j*u) ∧
    PairBound (levels g d) true (fun i j => (profiles d).2 i j*u) := by
  induction d with
  | zero => exact base_bounds g u C h0 h1
  | succ d ih => exact step_bounds (levels g d) (levels_nested g d) d u ih.1 ih.2


theorem amplify_bounds {I : Type} [Fintype I] (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ C*u) :
    (∀ x, amplify g x = false → sensitivityAt (amplify g) x ≤ L*u) ∧
    (∀ x, amplify g x = true → sensitivityAt (amplify g) x ≤ C*(L*u)) := by
  have hh := levels_bounds g u h0 h1 8
  constructor
  · intro x hx
    exact (hh.1.self 1 x hx).trans (Nat.mul_le_mul_right u (by decide))
  · intro x hx
    have hb : (profiles 8).2 1 1 ≤ C*L := by decide
    exact (hh.2.self 1 x hx).trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right u hb)









theorem iter_sides (m : ℕ) :
    (∀ x, iter m x = false → sensitivityAt (iter m) x ≤ L^m) ∧
    (∀ x, iter m x = true → sensitivityAt (iter m) x ≤ C*L^m) := by
  induction m with
  | zero =>
    constructor <;> intro x hx
    · exact (sensitivityAt_le_card _ _).trans (by simp [IterCoord])
    · exact (sensitivityAt_le_card _ _).trans (by norm_num [IterCoord, C])
  | succ m ih =>
    simpa [iter, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      amplify_bounds (iter m) (L^m) ih.1 ih.2
theorem iter_blocksensitivity (m : ℕ) : B^m ≤ blockSensitivityAt (iter m) (fun _ => false) := by
  have w := iterBlocks m
  simpa only [Fintype.card_fin] using
    le_blockSensitivityAt_of_family (iter m) (fun _ => false) w.sets w.nonempty w.disjoint
      (fun i => by rw [w.on 0 i, w.zero 0]; decide)

end
end OAI.Paper320.Round4




/-! Exact, factored certificate arithmetic for the Round4 amplifier.
The two small integer comparisons are kernel checked. The very large final
powers are related symbolically, rather than expanded as integer numerals.
Constants come from the generic pair-profile construction in Amplifier.lean,
adapted from Robin Kothari's accepted Prove2Me 2.05 proof and the local Sharp
refinement; upstream OpenAI/math material retains its Apache-2.0 attribution.
-/
namespace OAI.Paper320.Round4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0




private theorem L_pos : 0 < L := by decide


/-- First small kernel certificate; about 40 thousand bits, not the final power. -/
theorem certificate_scale : 16384 * L^411 ≤ B^200 := by
  decide +kernel

/-- The scale supplies enough slack for the outer two-copy OR. -/
theorem certificate_slack : (2*C)^411 < 2^200 * 16384^512 := by
  decide +kernel

theorem seedA_gt_one : 1 < seedA := by
  have hp : 1 ≤ L^512 := Nat.one_le_pow _ _ L_pos
  have hc : 1 < 2*C := by decide
  exact lt_of_lt_of_le hc (by simpa [seedA] using Nat.mul_le_mul_left (2*C) hp)



/-- Avoid expanding the roughly twenty-million-bit integer on either side. -/
theorem seed_power_gap : seedA^411 < seedB^200 := by
  calc
    seedA^411 = (2*C)^411 * (L^411)^512 := by
      simp only [seedA, mul_pow, ← pow_mul]
    _ < (2^200 * 16384^512) * (L^411)^512 :=
      Nat.mul_lt_mul_of_pos_right certificate_slack (pow_pos (pow_pos L_pos _) _)
    _ = 2^200 * (16384 * L^411)^512 := by rw [mul_pow]; ring
    _ ≤ 2^200 * (B^200)^512 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left certificate_scale 512)
    _ = seedB^200 := by
      simp only [seedB, mul_pow, ← pow_mul]

theorem seed_square_gap : seedA^2 < seedB := by
  by_contra hn
  have hb : seedB ≤ seedA^2 := by omega
  have hp := Nat.pow_le_pow_left hb 200
  have he : (seedA^2)^200 ≤ seedA^411 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by have := seedA_gt_one; omega) (by decide)
  exact (not_lt_of_ge (hp.trans he)) seed_power_gap

theorem log_exponent_gt_target :
    (411 : ℝ)/200 < Real.log (seedB : ℝ) / Real.log (seedA : ℝ) := by
  have hAr : 1 < (seedA : ℝ) := by exact_mod_cast seedA_gt_one
  have hAp : 0 < (seedA : ℝ) := by linarith
  have hlogA : 0 < Real.log (seedA : ℝ) := Real.log_pos hAr
  have hgapR : (seedA : ℝ)^411 < (seedB : ℝ)^200 := by exact_mod_cast seed_power_gap
  have hlog := Real.log_lt_log (pow_pos hAp 411) hgapR
  rw [Real.log_pow, Real.log_pow] at hlog
  apply (lt_div_iff₀ hlogA).mpr
  norm_num only [Nat.cast_ofNat] at hlog
  linarith









end OAI.Paper320.Round4




namespace OAI

/-! Coordinate equivalences preserve the two literal Boolean complexity measures. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J : Type}



theorem flip_reindex (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => flip x (B.map e.toEmbedding) (e i)) =
      flip (fun i => x (e i)) B := by
  funext i
  simp [flip]

theorem flip_reindex_singleton (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => flip x {e i} (e a)) = flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}



section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  have hs : (Finset.univ.filter fun j =>
      reindex e f (flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  apply Nat.le_antisymm
  · apply sensitivity_le
    intro x
    rw [sensitivityAt_reindex]
    exact sensitivityAt_le_sensitivity f _
  · apply sensitivity_le
    intro x
    have h := sensitivityAt_le_sensitivity (reindex e f) (fun j => x (e.symm j))
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

theorem blockSensitivityAt_le_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt f (fun i => x (e i)) ≤ blockSensitivityAt (reindex e f) x := by
  apply blockSensitivityAt_le
  intro blocks hd hb
  have h := le_blockSensitivityAt_of_family (reindex e f) x
    (fun B : blocks => B.val.map e.toEmbedding)
    (fun B => (hb B.val B.property).1.map (f := e.toEmbedding))
    (by
      intro A B hAB
      apply (Finset.disjoint_map e.toEmbedding).mpr
      exact hd A.val A.property B.val B.property (fun h => hAB (Subtype.ext h)))
    (by
      intro B
      change f (fun i => flip x (B.val.map e.toEmbedding) (e i)) ≠ _
      rw [flip_reindex]
      exact (hb B.val B.property).2)
  simpa only [Fintype.card_coe] using h

theorem blockSensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt (reindex e f) x = blockSensitivityAt f (fun i => x (e i)) := by
  apply Nat.le_antisymm
  · have h := blockSensitivityAt_le_reindex e.symm (reindex e f) (fun i => x (e i))
    simpa only [Equiv.apply_symm_apply, reindex_symm] using h
  · exact blockSensitivityAt_le_reindex e f x



end Finite
end Paper320

end

end OAI




namespace OAI

/-! Repeated disjoint composition with explicit finite raw-coordinate types. -/

noncomputable section
open scoped Classical

namespace Paper320











variable {I : Type} [Fintype I]















theorem nonconstant_of_blockSensitivityAt_pos (f : (I → Bool) → Bool) (x : I → Bool)
    (h : 0 < blockSensitivityAt f x) : ∃ y z, f y ≠ f z := by
  obtain ⟨blocks, hc, _, hb⟩ := exists_blockSensitivityAt_family f x
  have hn : blocks.Nonempty := Finset.card_pos.mp (hc.symm ▸ h)
  obtain ⟨B, hB⟩ := hn
  exact ⟨flip x B, x, (hb B hB).2⟩



end Paper320

end

end OAI




namespace OAI

/-! Balancing the zero and one sensitivities by an OR of disjoint copies. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I K : Type} [Fintype K]













theorem orCopies_zero (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false) :
    orCopies (K := K) f (fun _ => false) = false := by
  rw [orCopies, compose_zero _ _ hf, orBits_zero]

variable [Fintype I]



theorem card_le_blockSensitivityAt_orBits_zero :
    Fintype.card K ≤ blockSensitivityAt (orBits (K := K)) (fun _ => false) := by
  apply le_blockSensitivityAt_of_family orBits (fun _ => false) (fun k : K => {k})
  · intro k
    simp
  · intro k l hkl
    simpa using hkl
  · intro k
    have h : orBits (flip (fun _ : K => false) {k}) = true :=
      (orBits_eq_true _).mpr ⟨k, by simp⟩
    simp [h]

theorem blockSensitivityAt_orCopies_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) :
    Fintype.card K * blockSensitivityAt f (fun _ => false) ≤
      blockSensitivityAt (orCopies (K := K) f) (fun _ => false) := by
  exact (Nat.mul_le_mul_right _ card_le_blockSensitivityAt_orBits_zero).trans
    (blockSensitivityAt_compose_zero_le orBits f hf)

end Paper320

end

end OAI




namespace OAI.Paper320.Round2Growth
noncomputable section
open scoped Classical
open OAI.Paper320





theorem ZeroBranch.sensitivity_le {I : Type} [Fintype I]
    {f : (I → Bool) → Bool} {k : ℕ} (h : ZeroBranch f k) :
    k ≤ sensitivity f := by
  obtain ⟨x,C,hx,hk,hC⟩ := h
  apply hk.trans
  apply le_trans _ (sensitivityAt_le_sensitivity f x)
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [(hC i hi).2, hx]⟩









theorem sensitivity_iterateFin_ge {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) {k : ℕ} (hk : 0 < k) (hf : ZeroBranch f k) (m : ℕ) :
    k^m ≤ sensitivity (iterateFin f m) := by
  rw [iterateFin,sensitivity_reindex]
  exact (iterate_zeroBranch f hk hf m).sensitivity_le



/-- Divergence is a consequence of direct zero-branch multiplication. -/
theorem sensitivity_iterateFin_tendsto {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) {k : ℕ} (hk : 1 < k) (hf : ZeroBranch f k) :
    Filter.Tendsto (fun m : ℕ => (sensitivity (iterateFin f m) : ℝ))
      Filter.atTop Filter.atTop := by
  have hpow : Filter.Tendsto (fun m : ℕ => (k : ℝ)^m)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hk)
  apply Filter.tendsto_atTop_mono (fun m => ?_) hpow
  exact_mod_cast sensitivity_iterateFin_ge f (by omega) hf m

theorem accepts_of_positive_bs {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) (hb : 0 < blockSensitivityAt f x) :
    ∃ y, f y = true := by
  obtain ⟨y,z,hyz⟩ := nonconstant_of_blockSensitivityAt_pos f x hb
  cases hy : f y <;> cases hz : f z <;> simp_all
  · exact ⟨z,hz⟩
  · exact ⟨y,hy⟩












end
end OAI.Paper320.Round2Growth




/-! Campaign interface copied literally from the existing campaign definition.
The construction builds on Robin Kothari's accepted 2.05 amplifier and the
OpenAI/math Boolean library. This file supplies a direct growing family, without
assuming the campaign's finite-certificate theorem or any unproved result. -/
namespace SensitivityCampaign

end SensitivityCampaign

namespace OAI.Paper320.Round4
noncomputable section
open scoped Classical
open OAI.Paper320.Round2Growth
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem finite_seed (m : ℕ) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      f (fun _ => false) = false ∧ sensitivity f ≤ 2*C*L^m ∧
      2*B^m ≤ blockSensitivityAt f (fun _ => false) ∧ ZeroBranch f 2 := by
  let raw := orCopies (K := Fin 2) (iter m)
  let e := Fintype.equivFin (Fin 2 × IterCoord m)
  have hz : raw (fun _ => false) = false :=
    orCopies_zero (iter m) ((iterBlocks m).zero 0)
  have hs : sensitivity raw ≤ 2*C*L^m := by
    have hb := sensitivity_orCopies_le (K := Fin 2) (iter m)
      (L^m) (C*L^m) (iter_sides m).1 (iter_sides m).2
    apply hb.trans
    simp only [Fintype.card_fin]
    norm_num only [C]
    omega
  have hb : 2*B^m ≤ blockSensitivityAt raw (fun _ => false) := by
    have hh := blockSensitivityAt_orCopies_zero (K := Fin 2) (iter m)
      ((iterBlocks m).zero 0)
    rw [Fintype.card_fin] at hh
    exact (Nat.mul_le_mul_left 2 (iter_blocksensitivity m)).trans hh
  have hbr : ZeroBranch raw 2 := by
    apply or_zeroBranch (iter m) ((iterBlocks m).zero 0)
    apply accepts_of_positive_bs (iter m) (fun _ => false)
    apply lt_of_lt_of_le _ (iter_blocksensitivity m)
    exact pow_pos (by norm_num [B, K, H]) _
  refine ⟨_, reindex e raw, hz, ?_, ?_, hbr.reindex e⟩
  · rw [sensitivity_reindex]; exact hs
  · rw [blockSensitivityAt_reindex]; exact hb

theorem rational_family_2055 :
    ∃ (n : ℕ) (seed : (Fin n → Bool) → Bool),
    (∀ m : ℕ,
      (sensitivity (iterateFin seed m) : ℝ)^((411 : ℝ)/200) ≤
        (blockSensitivityAt (iterateFin seed m) (fun _ => false) : ℝ)) ∧
    Filter.Tendsto (fun m : ℕ => (sensitivity (iterateFin seed m) : ℝ))
      Filter.atTop Filter.atTop := by
  obtain ⟨n, seed, seed_zero, seed_sensitivity, seed_blocksensitivity, seed_branch⟩ :=
    finite_seed 512
  change sensitivity seed ≤ seedA at seed_sensitivity
  change seedB ≤ blockSensitivityAt seed (fun _ => false) at seed_blocksensitivity
  refine ⟨n, seed, ?_⟩
  obtain ⟨_, hall, _⟩ := power_amplification seed seed_zero seedA seedB
    seed_sensitivity seed_blocksensitivity seedA_gt_one seed_square_gap
  constructor
  · intro m
    obtain ⟨_, _, hnc, hp, _⟩ := hall m
    have hpos := sensitivity_pos_of_nonconstant (iterateFin seed m) hnc
    have hone : 1 ≤ (sensitivity (iterateFin seed m) : ℝ) := by
      exact_mod_cast (show 1 ≤ sensitivity (iterateFin seed m) by omega)
    exact (Real.rpow_le_rpow_of_exponent_le hone log_exponent_gt_target.le).trans hp
  · exact sensitivity_iterateFin_tendsto seed (by norm_num : 1 < (2 : ℕ)) seed_branch

theorem achieves_2055 : SensitivityCampaign.AchievesExponent (2.055 : ℝ) := by
  intro ε hε S hS
  obtain ⟨n, seed, hall, ht⟩ := rational_family_2055
  have he : ∀ᶠ m : ℕ in Filter.atTop,
      (S : ℝ) ≤ (sensitivity (iterateFin seed m) : ℝ) :=
    ht.eventually (Filter.eventually_ge_atTop (S : ℝ))
  obtain ⟨m, hm⟩ := he.exists
  have hsn : S ≤ sensitivity (iterateFin seed m) := by exact_mod_cast hm
  refine ⟨_, iterateFin seed m, hsn, ?_⟩
  have hone : 1 ≤ (sensitivity (iterateFin seed m) : ℝ) := by
    exact_mod_cast (show 1 ≤ sensitivity (iterateFin seed m) by omega)
  have hexp : (2.055 : ℝ)-ε ≤ (411 : ℝ)/200 := by
    have heq : (2.055 : ℝ) = (411 : ℝ)/200 := by norm_num
    rw [heq]
    linarith only [hε]
  exact ((Real.rpow_le_rpow_of_exponent_le hone hexp).trans
    (hall m)).trans
      (by exact_mod_cast blockSensitivityAt_le_blockSensitivity (iterateFin seed m) (fun _ => false))

end
end OAI.Paper320.Round4


theorem solution :
  SensitivityCampaign.AchievesExponent 2.055 := @OAI.Paper320.Round4.achieves_2055
