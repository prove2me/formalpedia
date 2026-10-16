-- Prove2me | solution 1 for OAI.Paper320.tower_four_recurrences_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Leo Shaposhnik
-- created : 2026-10-16T00:03:20.903933+00:00
-- url     : https://prove2.me/submissions/39939df5-160c-4c73-be45-3bf898fd72d6

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveProfiles.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveDefinitions.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveOne.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Tower.lean
  lean/round2-sharp/Sharp/RecursiveZero.lean
  lean/round2-sharp/Sharp/RecursiveJointZero.lean
  lean/round2-sharp/Sharp/Tower.lean
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
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2-sharp/Sharp/Tower.lean
Modifications: mechanical skeleton subtraction, import rewriting,
and a root solution alias with the same elaborated theorem type.
Copied upstream files previously received only the documented Lean
conditional-proof lemma-name port; mathematical definitions and
statements were preserved. This generated file is local staging.
-/

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Iterates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Theorems.Thm_OAI_Paper320_Tournament_card_badLabelings_le
import Theorems.Thm_OAI_Paper320_Tournament_card_internalEdges
import Theorems.Thm_OAI_Paper320_Tournament_card_le_three_of_outdegree_le_one
import Theorems.Thm_OAI_Paper320_Tournament_labelingConstraint_iff
import Theorems.Thm_OAI_Paper320_ballPredicate_sensitivityAt_zero_le
import Theorems.Thm_OAI_Paper320_blockSensitivityAt_compose_zero_le
import Theorems.Thm_OAI_Paper320_coupled_profiles_bound
import Theorems.Thm_OAI_Paper320_exists_blockSensitivityAt_family
import Theorems.Thm_OAI_Paper320_initialFamily_joint
import Theorems.Thm_OAI_Paper320_le_blockSensitivityAt_of_family
import Theorems.Thm_OAI_Paper320_normalized_profiles_step
import Theorems.Thm_OAI_Paper320_quantitative_profile_bounds
import Theorems.Thm_OAI_Paper320_quantitative_separation
import Theorems.Thm_OAI_Paper320_recursive_joint_one_at
import Theorems.Thm_OAI_Paper320_recursive_joint_zero_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_one_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at
import Theorems.Thm_OAI_Paper320_rowClause_repair_cases
import Theorems.Thm_OAI_Paper320_sensitivity_orCopies_le
import Theorems.Thm_OAI_Paper320_towerFamily_blocks
import Theorems.Thm_OAI_Paper320_tower_four_recurrences
import Theorems.Thm_SensitivityCampaign_baseline
import Theorems.Thm_SensitivityCampaign_baseline_arithmetic
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_openai_seed_bounds
import Definitions.Def_BS20205_Round2_Bounds
import Definitions.Def_BS20205_Round2_GeneralSeed
import Definitions.Def_BS20205_Sharp_Bounds
import Definitions.Def_BS20205_Sharp_Arithmetic
import Theorems.Thm_OAI_Paper320_recursive_joint_zero_at_sharp
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at_sharp

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









theorem sideSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q x, F q x = b → sensitivityAt (F q) x ≤ B) :
    sideSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q x hx
  · exact Nat.zero_le _



theorem jointSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q q' x, q < q' → F q x = b → F q' x = b →
      jointSensitivityAt (F q) (F q') x ≤ B) : jointSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro q' _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q q' x hx.1 hx.2.1 hx.2.2
  · exact Nat.zero_le _







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







theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]



theorem rowClause_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) {q q' : Fin h} (hqq : q ≤ q')
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : rowClause T label F q' x i = true) : rowClause T label F q x i = true := by
  rw [rowClause_eq_true_iff] at hi ⊢
  refine ⟨hi.1, fun j hij => ?_⟩
  exact hF.rejects_of_le (gateIndex_antitone hqq) (hi.2 j hij)

theorem recursiveFamily_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) : NestedFamily (recursiveFamily T label F) := by
  constructor
  intro q q' x hqq hx
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx
  exact (recursiveFamily_eq_true_iff T label F q x).mpr
    ⟨i, rowClause_nested T label F hF hqq x i hi⟩





end Paper320

end

end OAI




namespace OAI

/-! The two recurrences for inputs at which the parent predicates accept. -/

noncomputable section
open scoped Classical

namespace Paper320



theorem recursive_side_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o) :
    sideSensitivity (recursiveFamily T label F) true ≤
      o * sideSensitivity F false + r * sideSensitivity F true := by
  apply sideSensitivity_le
  exact fun q x hx => recursive_sensitivity_one_at T label F o ho q x hx



theorem recursive_joint_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o) :
    jointSensitivity (recursiveFamily T label F) true ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  apply jointSensitivity_le
  exact fun q q' x hqq hx hx' => recursive_joint_one_at T label F hF o ho q q' hqq x hx hx'

end Paper320

end

end OAI




namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320



























theorem towerFamily_nested {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (n h : ℕ) (hbase : NestedFamily (base (h + n))) :
    NestedFamily (towerFamily T label base n h) := by
  induction n generalizing h with
  | zero =>
    change NestedFamily (base h)
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_nested
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase





end Paper320

end

end OAI




namespace OAI

/-! The zero-side recurrence separates the unique possible gate-list sink. -/

noncomputable section
open scoped Classical

namespace Paper320



theorem recursive_side_zero_sharp {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    sideSensitivity (recursiveFamily T A.label F) false ≤
      15 * sideSensitivity F false + max (sideSensitivity F true + jointSensitivity F true) (3 * jointSensitivity F true) := by
  apply sideSensitivity_le
  exact fun q x hx => recursive_sensitivity_zero_at_sharp T A F hF hr q x hx

end Paper320

end

end OAI




namespace OAI

/-! The joint zero recurrence uses the fixed weaker-threshold failure lists. -/

noncomputable section
open scoped Classical

namespace Paper320



theorem recursive_joint_zero_sharp {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    jointSensitivity (recursiveFamily T A.label F) false ≤
      15 * sideSensitivity F false + 3 * jointSensitivity F true := by
  apply jointSensitivity_le
  exact fun q q' x hqq hx hx' => recursive_joint_zero_at_sharp T A F hF hr q q' hqq x hx hx'

end Paper320

end

end OAI




namespace OAI.Paper320
noncomputable section
open scoped Classical

theorem recursive_four_recurrences_sharp {M r h : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    let P := recursiveFamily T.toTournament A.label F
    (sideSensitivity P true ≤ M ^ 2 * sideSensitivity F false + r * sideSensitivity F true) ∧
    (jointSensitivity P true ≤ M ^ 2 * jointSensitivity F false + r * sideSensitivity F true) ∧
    (sideSensitivity P false ≤ 15 * sideSensitivity F false + max (sideSensitivity F true + jointSensitivity F true)
      (3 * jointSensitivity F true)) ∧
    (jointSensitivity P false ≤ 15 * sideSensitivity F false + 3 * jointSensitivity F true) := by
  exact ⟨recursive_side_one T.toTournament A.label F (M ^ 2) T.outdegree,
    recursive_joint_one T.toTournament A.label F hF (M ^ 2) T.outdegree,
    recursive_side_zero_sharp T.toTournament A F hF hr,
    recursive_joint_zero_sharp T.toTournament A F hF hr⟩

theorem tower_four_recurrences_sharp {M r : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (hn : n < D) (hr : 0 < r) (hbase : NestedFamily (base D)) :
    (towerSide T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerSide T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerJoint T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerJoint T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerSide T.toTournament A.label base D (n + 1) false ≤
      15 * towerSide T.toTournament A.label base D n false +
      max (towerSide T.toTournament A.label base D n true +
        towerJoint T.toTournament A.label base D n true)
        (3 * towerJoint T.toTournament A.label base D n true)) ∧
    (towerJoint T.toTournament A.label base D (n + 1) false ≤
      15 * towerSide T.toTournament A.label base D n false +
      3 * towerJoint T.toTournament A.label base D n true) := by
  have he : (D - (n + 1) + 1) + n = D := by omega
  have hf : NestedFamily (towerFamily T.toTournament A.label base n (D - (n + 1) + 1)) := by
    apply towerFamily_nested
    rwa [he]
  have H := recursive_four_recurrences_sharp T A
    (towerFamily T.toTournament A.label base n (D - (n + 1) + 1)) hf hr
  dsimp only at H
  change (sideSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) true ≤ _) ∧
    (jointSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) true ≤ _) ∧
    (sideSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) false ≤ _) ∧
    (jointSensitivity (towerFamily T.toTournament A.label base (n + 1) (D - (n + 1))) false ≤ _) at H
  have hcount : D - (n + 1) + 1 = D - n := by omega
  rw [hcount] at H
  exact H



end
end OAI.Paper320


theorem solution :
  ∀ {M r : ℕ} {I : Type} [inst : Fintype I] (T : OAI.Paper320.RegularTournament M)
  (A : OAI.Paper320.GoodLabeling T.toTournament r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool) (D n : ℕ),
  n < D →
    0 < r →
      OAI.Paper320.NestedFamily (base D) →
        OAI.Paper320.towerSide T.toTournament A.label base D (n + 1) Bool.true ≤
            M ^ 2 * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.false +
              r * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.true ∧
          OAI.Paper320.towerJoint T.toTournament A.label base D (n + 1) Bool.true ≤
              M ^ 2 * OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.false +
                r * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.true ∧
            OAI.Paper320.towerSide T.toTournament A.label base D (n + 1) Bool.false ≤
                15 * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.false +
                  Max.max
                    (OAI.Paper320.towerSide T.toTournament A.label base D n Bool.true +
                      OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.true)
                    (3 * OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.true) ∧
              OAI.Paper320.towerJoint T.toTournament A.label base D (n + 1) Bool.false ≤
                15 * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.false +
                  3 * OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.true := @OAI.Paper320.tower_four_recurrences_sharp
