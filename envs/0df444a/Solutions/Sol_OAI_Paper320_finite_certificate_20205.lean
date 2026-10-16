-- Prove2me | solution 1 for OAI.Paper320.finite_certificate_20205
-- status  : ACCEPTED   (prove)
-- author  : @Leo Shaposhnik
-- created : 2026-10-16T00:07:24.556655+00:00
-- url     : https://prove2.me/submissions/4c8a0a9a-cb73-4b32-bde4-2b4a3f6d7f2c

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2/OAI/Combinatorics/Sensitivity/Basic.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Composition.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Reindex.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Or.lean
  lean/round2/OAI/Combinatorics/Sensitivity/HammingBase.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveProfiles.lean
  lean/round2/OAI/Combinatorics/Sensitivity/InitialPredicates.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveDefinitions.lean
  lean/round2/OAI/Combinatorics/Sensitivity/RecursiveBlocks.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Tower.lean
  lean/round2/OAI/Combinatorics/Sensitivity/Construction.lean
  lean/round2/Round2/GeneralSeed.lean
  lean/round2-sharp/Sharp/Profiles.lean
  lean/round2-sharp/Sharp/Seed.lean
  lean/round2-sharp/Sharp/Arithmetic.lean
  lean/round2-sharp/Sharp/Certificate.lean
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
  lean/round2-sharp/Sharp/Certificate.lean
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
import Theorems.Thm_OAI_Paper320_Tournament_goodLabeling_exists_of_power_bound
import Theorems.Thm_OAI_Paper320_tower_four_recurrences_sharp

open scoped Classical



namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

















section Finite

variable [Fintype I]



theorem sensitivityAt_le_card (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ Fintype.card I :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem sensitivityAt_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem sensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, sensitivityAt f x ≤ n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x













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









end Finite
end Paper320

end

end OAI




namespace OAI

/-! Disjoint Boolean composition, with each child retaining its own raw coordinates. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I J : Type}





theorem compose_zero (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (hg : g (fun _ => false) = false) :
    compose f g (fun _ => false) = f (fun _ => false) := by
  simp [compose, hg]



section Finite
variable [Fintype I] [Fintype J]







end Finite
end Paper320

end

end OAI




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




namespace OAI

/-! Hamming balls used by the initial nested predicates. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I C : Type} [Fintype I]











theorem ballPredicate_eq_true [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) :
    ballPredicate centers R x = true ↔ ∃ c, hammingDist x (centers c) ≤ R := by
  simp [ballPredicate]

theorem ballPredicate_nested [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R ≤ S) (x : I → Bool)
    (h : ballPredicate centers R x = true) : ballPredicate centers S x = true := by
  rcases (ballPredicate_eq_true centers R x).1 h with ⟨c, hc⟩
  exact (ballPredicate_eq_true centers S x).2 ⟨c, hc.trans hRS⟩

















end Paper320

end

end OAI




namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320











theorem sensitivityAt_le_sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q : Fin h) (x : I → Bool)
    (hx : F q x = b) : sensitivityAt (F q) x ≤ sideSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hx]

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











end Paper320

end

end OAI




namespace OAI

/-! The separated Hamming-ball predicates and their explicit sensitive blocks. -/

noncomputable section
open scoped Classical

namespace Paper320







theorem baseBlock_card {M L : ℕ} (j : Fin M) : (baseBlock (L := L) j).card = L := by
  have h : (baseBlock (L := L) j).card = (Finset.univ : Finset (Fin L)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p _
      exact Finset.mem_univ _
    · intro p hp q hq hpq
      exact Prod.ext (((mem_baseBlock j p).mp hp).trans ((mem_baseBlock j q).mp hq).symm) hpq
    · intro b _
      exact ⟨(j, b), (mem_baseBlock j (j, b)).mpr rfl, rfl⟩
  simpa using h

theorem baseBlock_nonempty {M L : ℕ} (hL : 0 < L) (j : Fin M) :
    (baseBlock (L := L) j).Nonempty := by
  rw [← Finset.card_pos, baseBlock_card]
  exact hL

theorem baseBlock_disjoint {M L : ℕ} :
    Pairwise fun i j : Fin M => Disjoint (baseBlock (L := L) i) (baseBlock j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  rintro ⟨a, b⟩ hi hj
  simp only [mem_baseBlock] at hi hj
  exact hij (hi.symm.trans hj)

theorem flip_zero_baseBlock {M L : ℕ} (j : Fin M) :
    flip (fun _ : Fin M × Fin L => false) (baseBlock j) = blockCenter j := by
  ext p
  simp [flip, blockCenter]

theorem hammingDist_zero_blockCenter {M L : ℕ} (j : Fin M) :
    hammingDist (fun _ : Fin M × Fin L => false) (blockCenter j) = L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L => false ≠ blockCenter j p) =
      baseBlock j := by
    ext p
    simp [blockCenter]
  rw [hammingDist, hs, baseBlock_card]

theorem hammingDist_blockCenter {M L : ℕ} (i j : Fin M) (hij : i ≠ j) :
    hammingDist (blockCenter (L := L) i) (blockCenter j) = 2 * L := by
  have hs : (Finset.univ.filter fun p : Fin M × Fin L =>
      blockCenter i p ≠ blockCenter j p) =
      baseBlock i ∪ baseBlock j := by
    ext ⟨a, b⟩
    by_cases ha : a = i <;> by_cases hb : a = j <;> simp_all [blockCenter]
  rw [hammingDist, hs]
  rw [Finset.card_union_of_disjoint (baseBlock_disjoint hij), baseBlock_card, baseBlock_card]
  omega



theorem initialFamily_nested (d M : ℕ) : NestedFamily (initialFamily d M) := by
  constructor
  intro q q' x hqq hx
  exact ballPredicate_nested blockCenter (by omega) x hx

theorem initialFamily_zero (d M : ℕ) (q : Fin (d + 1)) :
    initialFamily d M q (fun _ => false) = false := by
  have hn : ¬ ∃ c : Fin M,
      hammingDist (fun _ : Fin M × Fin (d + 2) => false) (blockCenter c) ≤ d - q.val := by
    rintro ⟨c, hc⟩
    rw [hammingDist_zero_blockCenter] at hc
    omega
  simp [initialFamily, ballPredicate, hn]

theorem initialFamily_baseBlock (d M : ℕ) (q : Fin (d + 1)) (j : Fin M) :
    initialFamily d M q (flip (fun _ => false) (baseBlock j)) = true := by
  rw [flip_zero_baseBlock]
  apply (ballPredicate_eq_true blockCenter (d - q.val) (blockCenter j)).2
  exact ⟨j, by simp⟩

theorem initialFamily_side_zero (d M : ℕ) :
    sideSensitivity (initialFamily d M) false ≤ d + 2 := by
  apply sideSensitivity_le
  intro q x hx
  have hs : ∀ a b : Fin M, a ≠ b →
      2 * ((d - q.val) + 1) < hammingDist (blockCenter (L := d + 2) a) (blockCenter b) := by
    intro a b hab
    rw [hammingDist_blockCenter a b hab]
    omega
  exact (ballPredicate_sensitivityAt_zero_le blockCenter (d - q.val) hs x hx).trans
    (by omega)

theorem initialFamily_side_one (d M : ℕ) :
    sideSensitivity (initialFamily d M) true ≤ (d + 2) * M := by
  apply sideSensitivity_le
  intro q x _
  simpa [Nat.mul_comm] using sensitivityAt_le_card (initialFamily d M q) x





end Paper320

end

end OAI




namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320















theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]



theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]





theorem recursiveFamily_zero {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hr : 0 < r) (hzero : ∀ q, F q (fun _ => false) = false) (q : Fin h) :
    recursiveFamily T label F q (fun _ => false) = false := by
  rw [recursiveFamily_eq_false_iff]
  intro i
  cases hi : rowClause T label F q (fun _ => false) i
  · rfl
  · have ht := ((rowClause_eq_true_iff T label F q (fun _ => false) i).mp hi).1
      (⟨0, hr⟩ : Fin r)
    have hz := hzero (Fin.last h)
    change F (Fin.last h) (fun _ => false) = true at ht
    simp [hz] at ht



end Paper320

end

end OAI




namespace OAI

/-! Disjoint zero-input blocks lift to every column of a chosen row. -/

noncomputable section
open scoped Classical

namespace Paper320







theorem rowLift_nonempty {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (hr : 0 < r) (hB : B.Nonempty) : (rowLift (r := r) i B).Nonempty := by
  obtain ⟨a, ha⟩ := hB
  exact ⟨((i, ⟨0, hr⟩), a), (mem_rowLift i B _).mpr ⟨rfl, ha⟩⟩

theorem rowLift_disjoint_of_ne {k r : ℕ} {I : Type} (i j : Fin k)
    (B C : Finset I) (hij : i ≠ j) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hij (((mem_rowLift i B p).mp hp).1.symm.trans ((mem_rowLift j C p).mp hq).1)

theorem rowLift_disjoint {k r : ℕ} {I : Type} (i j : Fin k) (B C : Finset I)
    (hBC : Disjoint B C) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp hBC ((mem_rowLift i B p).mp hp).2
    ((mem_rowLift j C p).mp hq).2

theorem rowLift_family_disjoint {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hB : Pairwise fun a b => Disjoint (blocks a) (blocks b)) :
    Pairwise fun a b : Fin k × K =>
      Disjoint (rowLift (r := r) a.1 (blocks a.2)) (rowLift b.1 (blocks b.2)) := by
  intro a b hab
  by_cases hrow : a.1 = b.1
  · apply rowLift_disjoint
    apply hB
    intro hcol
    exact hab (Prod.ext hrow hcol)
  · exact rowLift_disjoint_of_ne _ _ _ _ hrow







end Paper320

end

end OAI




namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320



















theorem tower_block_index_card {k : ℕ} {K : Type} [Fintype K] (n : ℕ) :
    Fintype.card (TowerBlockIndex k K n) = k ^ n * Fintype.card K := by
  induction n with
  | zero =>
    change Fintype.card K = k ^ 0 * Fintype.card K
    simp
  | succ n ih =>
    change Fintype.card (Fin k × TowerBlockIndex k K n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring



theorem towerBlocks_nonempty {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hr : 0 < r) (hne : ∀ b, (blocks b).Nonempty) (n : ℕ) (b : TowerBlockIndex k K n) :
    (towerBlocks (r := r) blocks n b).Nonempty := by
  induction n with
  | zero => exact hne b
  | succ n ih => exact rowLift_nonempty b.1 _ hr (ih b.2)

theorem towerBlocks_pairwise {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hd : Pairwise fun a b => Disjoint (blocks a) (blocks b)) (n : ℕ) :
    Pairwise fun a b => Disjoint (towerBlocks (k := k) (r := r) blocks n a) (towerBlocks blocks n b) := by
  induction n with
  | zero => exact hd
  | succ n ih => exact rowLift_family_disjoint (towerBlocks blocks n) ih



theorem towerFamily_zero {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (hr : 0 < r) (n h : ℕ) (hbase : ∀ q, base (h + n) q (fun _ => false) = false) :
    ∀ q, towerFamily T label base n h q (fun _ => false) = false := by
  induction n generalizing h with
  | zero =>
    change ∀ q, base h q (fun _ => false) = false
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_zero T label _ hr
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase



end Paper320

end

end OAI




namespace OAI

/-! The initial family, recursively constructed predicates, and final OR. -/

noncomputable section
open scoped Classical

namespace Paper320







theorem construction_base_nested (d M : ℕ) :
    NestedFamily (constructionBase d M (d + 1)) := by
  simpa only [constructionBase, baseExtension_same] using initialFamily_nested d M

theorem construction_base_zero (d M : ℕ) :
    ∀ q, constructionBase d M (1 + d) q (fun _ => false) = false := by
  rw [Nat.add_comm 1 d]
  simpa only [constructionBase, baseExtension_same] using initialFamily_zero d M

theorem construction_base_blocks (d M : ℕ) :
    ∀ b q, constructionBase d M (1 + d) q
      (flip (fun _ => false) (baseBlock b)) = true := by
  rw [Nat.add_comm 1 d]
  intro b q
  simpa only [constructionBase, baseExtension_same] using initialFamily_baseBlock d M q b

theorem terminalPredicate_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    terminalPredicate d T A (fun _ => false) = false :=
  towerFamily_zero T.toTournament A.label (constructionBase d M) hr d 1
    (construction_base_zero d M) 0

theorem terminalPredicate_blocks {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r)
    (b : TowerBlockIndex (2 * M ^ 2 + 1) (Fin M) d) :
    terminalPredicate d T A (flip (fun _ => false)
      (towerBlocks (r := r) (baseBlock (L := d + 2)) d b)) = true :=
  towerFamily_blocks T.toTournament A.label (constructionBase d M)
    (baseBlock (L := d + 2)) hr d 1 (construction_base_zero d M)
    (construction_base_blocks d M) b 0

theorem terminalPredicate_blockSensitivity {M r : ℕ} (d : ℕ)
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (terminalPredicate d T A) (fun _ => false) := by
  have h := le_blockSensitivityAt_of_family (terminalPredicate d T A) (fun _ => false)
    (towerBlocks (r := r) (baseBlock (L := d + 2)) d)
    (towerBlocks_nonempty (baseBlock (L := d + 2)) hr
      (baseBlock_nonempty (by omega)) d)
    (towerBlocks_pairwise (baseBlock (L := d + 2)) baseBlock_disjoint d)
    (fun b => by rw [terminalPredicate_blocks d T A hr, terminalPredicate_zero d T A hr]; decide)
  simpa only [tower_block_index_card, Fintype.card_fin, Nat.mul_comm] using h



























end Paper320

end

end OAI



namespace OAI.Paper320
noncomputable section
open scoped Classical



theorem orWitness_zero {M r : ℕ} (d K : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    orWitness d K T A (fun _ => false) = false :=
  orCopies_zero _ (terminalPredicate_zero d T A hr)



theorem orWitness_blocks {M r : ℕ} (d K : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    K*M*(2*M^2+1)^d ≤ blockSensitivityAt (orWitness d K T A) (fun _ => false) := by
  rw [orWitness, blockSensitivityAt_reindex]
  have H := (Nat.mul_le_mul_left K (terminalPredicate_blockSensitivity d T A hr)).trans
    (by simpa only [Fintype.card_fin] using
      blockSensitivityAt_orCopies_zero (K := Fin K) _ (terminalPredicate_zero d T A hr))
  simpa only [Nat.mul_assoc] using H




end
end OAI.Paper320




namespace OAI.Paper320
noncomputable section
open scoped Classical

theorem tower_sharp_bounds {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    ∀ n ≤ d,
      towerSide T.toTournament A.label (constructionBase d M) (d+1) n false ≤
        (sharpBounds M r (d+2) n).s0 ∧
      towerSide T.toTournament A.label (constructionBase d M) (d+1) n true ≤
        (sharpBounds M r (d+2) n).s1 ∧
      towerJoint T.toTournament A.label (constructionBase d M) (d+1) n false ≤
        (sharpBounds M r (d+2) n).j0 ∧
      towerJoint T.toTournament A.label (constructionBase d M) (d+1) n true ≤
        (sharpBounds M r (d+2) n).j1 := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa only [towerSide_zero, towerJoint_zero, constructionBase, baseExtension_same,
        sharpBounds] using And.intro (initialFamily_side_zero d M)
          (And.intro (initialFamily_side_one d M)
            (And.intro (le_of_eq (initialFamily_joint d M false))
              (le_of_eq (initialFamily_joint d M true))))
  | succ n ih =>
      intro hn
      obtain ⟨h0,h1,hj0,hj1⟩ := ih (by omega)
      have H := tower_four_recurrences_sharp T A (constructionBase d M) (d+1) n
        (by omega) hr (construction_base_nested d M)
      simp only [sharpBounds, sharpStep]
      refine ⟨H.2.2.1.trans ?_, H.1.trans ?_, H.2.2.2.trans ?_, H.2.1.trans ?_⟩
      all_goals gcongr

theorem terminal_sharp_sensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    (∀ x, terminalPredicate d T A x = false →
      sensitivityAt (terminalPredicate d T A) x ≤ (sharpBounds M r (d+2) d).s0) ∧
    (∀ x, terminalPredicate d T A x = true →
      sensitivityAt (terminalPredicate d T A) x ≤ (sharpBounds M r (d+2) d).s1) := by
  obtain ⟨h0,h1,_,_⟩ := tower_sharp_bounds d T A hr d (le_refl d)
  have he : d+1-d = 1 := by omega
  simp only [towerSide] at h0 h1
  rw [he] at h0 h1
  exact ⟨fun x hx => (sensitivityAt_le_sideSensitivity _ false 0 x hx).trans h0,
    fun x hx => (sensitivityAt_le_sideSensitivity _ true 0 x hx).trans h1⟩



end
end OAI.Paper320




namespace OAI.Paper320
noncomputable section
open scoped Classical

theorem orWitness_sharp_sensitivity {M r : ℕ} (d K : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    sensitivity (orWitness d K T A) ≤
      max (K*(sharpBounds M r (d+2) d).s0) (sharpBounds M r (d+2) d).s1 := by
  obtain ⟨h0,h1⟩ := terminal_sharp_sensitivity d T A hr
  rw [orWitness, sensitivity_reindex]
  simpa only [Fintype.card_fin] using
    sensitivity_orCopies_le (K := Fin K) (terminalPredicate d T A) _ _ h0 h1

theorem exists_general_sharp_seed (d M r K : ℕ) (hM : 0 < M) (hr : 0 < r)
    (hK : 0 < K) (hl : 120 ≤ (2*M^2+1)*(2*M^2+1))
    (hp : (2*M^2+1)^16 < r^104) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      sensitivity f ≤ max (K*(sharpBounds M r (d+2) d).s0) (sharpBounds M r (d+2) d).s1 ∧
      K*M*(2*M^2+1)^d ≤ blockSensitivityAt f (fun _ => false) := by
  obtain ⟨A⟩ := (regularCyclicTournament M).toTournament.goodLabeling_exists_of_power_bound
    hr hl hp
  refine ⟨_, orWitness d K (regularCyclicTournament M) A, ?_,
    orWitness_zero d K (regularCyclicTournament M) A hr,
    orWitness_sharp_sensitivity d K (regularCyclicTournament M) A hr,
    orWitness_blocks d K (regularCyclicTournament M) A hr⟩
  simp only [Fintype.card_prod, tower_coordinates_card, Fintype.card_fin]
  positivity


end
end OAI.Paper320



namespace OAI.Paper320
set_option maxRecDepth 1000000
set_option maxHeartbeats 0







theorem sharp_parameters : 0 < sharpM ∧ 0 < sharpR ∧ 1 < sharpK ∧
    120 ≤ (2*sharpM^2+1)*(2*sharpM^2+1) ∧ (2*sharpM^2+1)^16 < sharpR^104 := by
  decide +kernel

theorem sharp_gap : 1 < sharpA ∧ sharpA^2 < sharpB ∧ sharpA^4041 < sharpB^2000 := by
  decide +kernel



end OAI.Paper320




namespace OAI.Paper320
noncomputable section
open scoped Classical

/-- Finite total Boolean certificate at exponent 4041/2000=2.0205. -/
theorem finite_certificate_20205 :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      sensitivity f ≤ sharpA ∧ sharpB ≤ blockSensitivityAt f (fun _ => false) ∧
      1 < sharpA ∧ sharpA^2 < sharpB ∧ sharpA^4041 < sharpB^2000 := by
  obtain ⟨hM, hr, hK, hl, hp⟩ := sharp_parameters
  obtain ⟨n, f, hn, hz, hs, hb⟩ := exists_general_sharp_seed 17 sharpM sharpR sharpK
    hM hr (by omega) hl hp
  exact ⟨n, f, hn, hz, hs, hb, sharp_gap⟩




end
end OAI.Paper320


theorem solution :
  ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
  0 < n ∧
    (f fun (x : Fin n) => Bool.false) = Bool.false ∧
      OAI.Paper320.sensitivity f ≤ OAI.Paper320.sharpA ∧
        (OAI.Paper320.sharpB ≤ OAI.Paper320.blockSensitivityAt f fun (x : Fin n) => Bool.false) ∧
          1 < OAI.Paper320.sharpA ∧
            OAI.Paper320.sharpA ^ 2 < OAI.Paper320.sharpB ∧ OAI.Paper320.sharpA ^ 4041 < OAI.Paper320.sharpB ^ 2000 := @OAI.Paper320.finite_certificate_20205
