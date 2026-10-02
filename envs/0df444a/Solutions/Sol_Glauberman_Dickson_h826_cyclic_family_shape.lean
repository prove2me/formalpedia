-- Prove2me | solution 1 for Glauberman.Dickson.h826_cyclic_family_shape
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:43:09.203389+00:00
-- url     : https://prove2.me/submissions/0a70d1bb-7a3b-4ad4-8f91-ee3ad0cbaad7

/- Original formalization: Qiuzhen-CFSG/CFSG, Glauberman/DicksonClassification.lean,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0.
Lifted from hpre_shape inside Huppert II.8.26.
arexychen: theorem extraction, explicit parameterization, replay and validation.
The same counting proof is retained; Q abbreviates the original p^m.
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
set_option autoImplicit false
universe u
theorem solution {H : Type u} [Group H] [Finite H]
    (Q r : ℕ) (NP : Subgroup H) (Z NZ : Fin r → Subgroup H)
    (s term : Fin r → ℕ) (i0 : Fin r)
    (hpm_gt : 1 < Q) (hfamily_bound : r ≤ 3)
    (hnontrivial : ∀ j, 1 < Nat.card (Z j))
    (hs : ∀ j, 1 ≤ s j ∧ s j ≤ 2)
    (hpartition_count : Nat.card H = 1 + (Q - 1) * NP.index + ∑ j, term j)
    (hz_index_factor : ∀ j, (Nat.card (Z j) * s j) * (NZ j).index = Nat.card H)
    (hterm_factor : ∀ j, term j + (NZ j).index = Nat.card (Z j) * (NZ j).index)
    (hterm_bound : ∀ j, Nat.card H ≤ 4 * term j)
    (hNP_index_factor : (Q * Nat.card (Z i0)) * NP.index = Nat.card H) :
    Nat.card H = Nat.card NP ∨ (r = 2 ∧ ∀ j, s j = 2) := by
  classical
  let rest : Fin r → ℕ := fun i =>
    ∑ j ∈ Finset.univ.erase i, term j
  have hsum_rest (i : Fin r) :
      (∑ j, term j) = term i + rest i := by
    exact (Finset.sum_erase_add Finset.univ term (Finset.mem_univ i)).symm.trans
      (Nat.add_comm _ _)
  have hNPindex_pos : 0 < NP.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hNZindex_pos (i : Fin r) : 0 < (NZ i).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hq_ge_two : 2 ≤ Q := hpm_gt
  have hindex_one (hsi : s i0 = 1) :
      (NZ i0).index = Q * NP.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z i0))
    calc
      Nat.card (Z i0) * (NZ i0).index = Nat.card H := by
        simpa [hsi] using hz_index_factor i0
      _ = (Q * Nat.card (Z i0)) * NP.index :=
        hNP_index_factor.symm
      _ = Nat.card (Z i0) * (Q * NP.index) := by ring
  have hindex_two (hsi : s i0 = 2) :
      Q * NP.index = 2 * (NZ i0).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z i0))
    calc
      Nat.card (Z i0) * (Q * NP.index) = Nat.card H := by
        rw [← hNP_index_factor]
        ring
      _ = (Nat.card (Z i0) * 2) * (NZ i0).index := by
        simpa [hsi] using (hz_index_factor i0).symm
      _ = Nat.card (Z i0) * (2 * (NZ i0).index) := by ring
  have hq_term :
      (Q - 1) * NP.index + NP.index = Q * NP.index := by
    calc
      (Q - 1) * NP.index + NP.index =
          (Q - 1 + 1) * NP.index := by ring
      _ = Q * NP.index := by
        rw [Nat.sub_add_cancel hpm_gt.le]
  have hrest_eq_of_one (hsi : s i0 = 1) :
      NP.index = 1 + rest i0 := by
    have hcount := hpartition_count
    rw [hsum_rest i0] at hcount
    have hzfactor :
        Nat.card (Z i0) * (NZ i0).index = Nat.card H := by
      simpa [hsi] using hz_index_factor i0
    have hidx := hindex_one hsi
    have hrel := hterm_factor i0
    omega
  have hrest_lt_of_two (hsi : s i0 = 2) :
      rest i0 < Nat.card (Z i0) * (NZ i0).index := by
    have hcount := hpartition_count
    rw [hsum_rest i0] at hcount
    have hzfactor :
        2 * (Nat.card (Z i0) * (NZ i0).index) = Nat.card H := by
      calc
        2 * (Nat.card (Z i0) * (NZ i0).index) =
            (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
        _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by rw [hsi]
        _ = Nat.card H := hz_index_factor i0
    have hidx := hindex_two hsi
    have hNPindex_le : NP.index ≤ (NZ i0).index := by
      have hmul := Nat.mul_le_mul_right NP.index hq_ge_two
      rw [hidx] at hmul
      omega
    have hrel := hterm_factor i0
    omega
  have hother_lower_one (hsi : s i0 = 1)
      (j : Fin r) (hji : j ≠ i0) : NP.index ≤ term j := by
    have hfour_le :
        4 * NP.index ≤ Nat.card H := by
      have hqz : 4 ≤ Q * Nat.card (Z i0) :=
        Nat.mul_le_mul hq_ge_two (hnontrivial i0)
      calc
        4 * NP.index ≤
            (Q * Nat.card (Z i0)) * NP.index :=
          Nat.mul_le_mul_right NP.index hqz
        _ = Nat.card H := hNP_index_factor
    have hj := hterm_bound j
    omega
  have hother_lower_two (hsi : s i0 = 2)
      (j : Fin r) (hji : j ≠ i0) :
      Nat.card (Z i0) * (NZ i0).index ≤ 2 * term j := by
    have hzfactor :
        2 * (Nat.card (Z i0) * (NZ i0).index) = Nat.card H := by
      calc
        2 * (Nat.card (Z i0) * (NZ i0).index) =
            (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
        _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by rw [hsi]
        _ = Nat.card H := hz_index_factor i0
    have hj := hterm_bound j
    omega
  have hr_pos : 0 < r := Nat.zero_lt_of_lt i0.isLt
  have hr_cases : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr_cases with hr_one | hr_two | hr_three
  · subst r
    have hi0 : i0 = (0 : Fin 1) := Subsingleton.elim _ _
    subst i0
    rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
      hs0 | hs0
    · left
      have hrest : rest 0 = 0 := by simp [rest]
      have hindex : NP.index = 1 := by
        have h : NP.index = 1 + rest 0 := by
          simpa using hrest_eq_of_one hs0
        omega
      calc
        Nat.card H = Nat.card NP * NP.index := NP.card_mul_index.symm
        _ = Nat.card NP := by rw [hindex, mul_one]
    · exfalso
      have hcount := hpartition_count
      rw [hsum_rest 0] at hcount
      have hrest : rest 0 = 0 := by simp [rest]
      have hzfactor :
          2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
          _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by rw [hs0]
          _ = Nat.card H := hz_index_factor 0
      have hidx : Q * NP.index = 2 * (NZ 0).index := by
        simpa using hindex_two hs0
      have hNPindex_le : NP.index ≤ (NZ 0).index := by
        have hmul := Nat.mul_le_mul_right NP.index hq_ge_two
        rw [hidx] at hmul
        omega
      have hrel := hterm_factor 0
      have hz_lower :
          2 * (NZ 0).index ≤ Nat.card (Z 0) * (NZ 0).index :=
        Nat.mul_le_mul_right (NZ 0).index (hnontrivial 0)
      omega
  · right
    refine ⟨hr_two, ?_⟩
    subst r
    fin_cases i0
    · have hs0_two : s 0 = 2 := by
        rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
          hs0 | hs0
        · have hrest : NP.index = 1 + rest 0 := by
            simpa using hrest_eq_of_one hs0
          have hlower := hother_lower_one hs0 1 (by decide)
          have hrest_term : rest 0 = term 1 := by
            change (∑ j ∈ Finset.univ.erase (0 : Fin 2), term j) = term 1
            rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide]
            simp
          omega
        · exact hs0
      have hs1_two : s 1 = 2 := by
        rcases (show s 1 = 1 ∨ s 1 = 2 by have h := hs 1; omega) with
          hs1 | hs1
        · have hrest_lt :
              rest 0 < Nat.card (Z 0) * (NZ 0).index := by
            simpa using hrest_lt_of_two hs0_two
          have hrest_term : rest 0 = term 1 := by
            change (∑ j ∈ Finset.univ.erase (0 : Fin 2), term j) = term 1
            rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide]
            simp
          have hzfactor0 :
              2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
            calc
              2 * (Nat.card (Z 0) * (NZ 0).index) =
                  (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
              _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by rw [hs0_two]
              _ = Nat.card H := hz_index_factor 0
          have hzfactor1 :
              Nat.card (Z 1) * (NZ 1).index = Nat.card H := by
            simpa [hs1] using hz_index_factor 1
          have hrel1 := hterm_factor 1
          have hk1_bound :
              2 * (NZ 1).index ≤ Nat.card H := by
            calc
              2 * (NZ 1).index ≤
                  Nat.card (Z 1) * (NZ 1).index :=
                Nat.mul_le_mul_right (NZ 1).index (hnontrivial 1)
              _ = Nat.card H := hzfactor1
          omega
        · exact hs1
      intro i
      fin_cases i
      · exact hs0_two
      · exact hs1_two
    · have hs1_two : s 1 = 2 := by
        rcases (show s 1 = 1 ∨ s 1 = 2 by have h := hs 1; omega) with
          hs1 | hs1
        · have hrest : NP.index = 1 + rest 1 := by
            simpa using hrest_eq_of_one hs1
          have hlower := hother_lower_one hs1 0 (by decide)
          have hrest_term : rest 1 = term 0 := by
            change (∑ j ∈ Finset.univ.erase (1 : Fin 2), term j) = term 0
            rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
            simp
          omega
        · exact hs1
      have hs0_two : s 0 = 2 := by
        rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
          hs0 | hs0
        · have hrest_lt :
              rest 1 < Nat.card (Z 1) * (NZ 1).index := by
            simpa using hrest_lt_of_two hs1_two
          have hrest_term : rest 1 = term 0 := by
            change (∑ j ∈ Finset.univ.erase (1 : Fin 2), term j) = term 0
            rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
            simp
          have hzfactor1 :
              2 * (Nat.card (Z 1) * (NZ 1).index) = Nat.card H := by
            calc
              2 * (Nat.card (Z 1) * (NZ 1).index) =
                  (Nat.card (Z 1) * 2) * (NZ 1).index := by ring
              _ = (Nat.card (Z 1) * s 1) * (NZ 1).index := by rw [hs1_two]
              _ = Nat.card H := hz_index_factor 1
          have hzfactor0 :
              Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
            simpa [hs0] using hz_index_factor 0
          have hrel0 := hterm_factor 0
          have hk0_bound :
              2 * (NZ 0).index ≤ Nat.card H := by
            calc
              2 * (NZ 0).index ≤
                  Nat.card (Z 0) * (NZ 0).index :=
                Nat.mul_le_mul_right (NZ 0).index (hnontrivial 0)
              _ = Nat.card H := hzfactor0
          omega
        · exact hs0
      intro i
      fin_cases i
      · exact hs0_two
      · exact hs1_two
  · exfalso
    subst r
    rcases (show s i0 = 1 ∨ s i0 = 2 by have h := hs i0; omega) with
      hsi | hsi
    · have hrest := hrest_eq_of_one hsi
      have hlower : 2 * NP.index ≤ rest i0 := by
        calc
          2 * NP.index =
              ∑ j ∈ Finset.univ.erase i0, NP.index := by simp
          _ ≤ ∑ j ∈ Finset.univ.erase i0, term j :=
            Finset.sum_le_sum fun j hj =>
              hother_lower_one hsi j (Finset.ne_of_mem_erase hj)
          _ = rest i0 := rfl
      omega
    · have hrest := hrest_lt_of_two hsi
      have hlower :
          Nat.card (Z i0) * (NZ i0).index ≤ rest i0 := by
        have hsum :
            2 * (Nat.card (Z i0) * (NZ i0).index) ≤
              2 * rest i0 := by
          calc
            2 * (Nat.card (Z i0) * (NZ i0).index) =
                ∑ j ∈ Finset.univ.erase i0,
                  Nat.card (Z i0) * (NZ i0).index := by simp
            _ ≤ ∑ j ∈ Finset.univ.erase i0, 2 * term j :=
              Finset.sum_le_sum fun j hj =>
                hother_lower_two hsi j (Finset.ne_of_mem_erase hj)
            _ = 2 * rest i0 := by simp [rest, Finset.mul_sum]
        omega
      omega
