-- Prove2me | solution 1 for Glauberman.Dickson.h826_group_order_cases
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:34:37.772417+00:00
-- url     : https://prove2.me/submissions/d75670e0-bf6f-4a3b-9f18-75fad5bbfd2b

/-
Original formalization: Qiuzhen-CFSG/CFSG and original source authors.
Commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; Apache-2.0.
arexychen: declaration extraction, exact-environment replay, packaging and validation.
Original mathematical statement and proof architecture are retained.
Source scopes and upload names are adapted. nlinarith inputs are restricted
to existing premises, with Nat.sub_add_cancel made explicit in one step.
These tactic-context changes are independently kernel-checked; see metadata.

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
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

set_option autoImplicit false
namespace CFSGPackGroupOrderCases

section Source18
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean
/-!
# Huppert II.8.27

Dickson's subgroup classification for subgroups of PSL(2,p^f).
-/

namespace Glauberman
namespace Dickson

open scoped Pointwise
universe u v

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

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem _root_.solution
    (q a b n u v w : ℕ)
    (hq : 1 < q) (ha : 1 < a) (hb : 1 < b)
    (hqa : Nat.Coprime q a) (hqb : Nat.Coprime q b)
    (hadiv : a ∣ q - 1) (hgcd : Nat.gcd a b ∣ 2)
    (hnlcm : n = Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)))
    (hqu : (q * a) * u = n)
    (hav : (2 * a) * v = n)
    (hbw : (2 * b) * w = n)
    (hcount :
      n = 1 + (q - 1) * u + (a - 1) * v + (b - 1) * w) :
    (q = 3 ∧ a = 2 ∧ b = 5 ∧ n = 60) ∨
      (a = q - 1 ∧ b = q + 1 ∧
        n = (q + 1) * q * (q - 1)) ∨
      (Nat.Coprime q 2 ∧
        a = (q - 1) / 2 ∧ b = (q + 1) / 2 ∧
        n = ((q + 1) * q * (q - 1)) / Nat.gcd (q - 1) 2) := by
  have hqpos : 0 < q := by omega
  have hap : 0 < a := by omega
  have hbp : 0 < b := by omega
  have hab_dvd_inner : a * b ∣ Nat.lcm (2 * a) (2 * b) := by
    calc
      a * b = Nat.gcd a b * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
      _ ∣ 2 * Nat.lcm a b :=
        Nat.mul_dvd_mul_right hgcd (Nat.lcm a b)
      _ = Nat.lcm (2 * a) (2 * b) := (Nat.lcm_mul_left 2 a b).symm
  have hab_dvd_c :
      a * b ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    dvd_trans hab_dvd_inner (Nat.dvd_lcm_right _ _)
  have hq_dvd_c :
      q ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    dvd_trans (dvd_mul_right q a) (Nat.dvd_lcm_left _ _)
  have hqab_dvd_c :
      q * (a * b) ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    (hqa.mul_right hqb).mul_dvd_of_dvd_of_dvd hq_dvd_c hab_dvd_c
  have hc_dvd_twoqab :
      Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) ∣
        2 * q * a * b := by
    apply Nat.lcm_dvd
    · exact ⟨2 * b, by ring⟩
    · apply Nat.lcm_dvd
      · exact ⟨q * b, by ring⟩
      · exact ⟨q * a, by ring⟩
  have hnshape : n = q * a * b ∨ n = 2 * q * a * b := by
    let c := Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b))
    have hqab_dvd : q * a * b ∣ c := by
      simpa [c, mul_assoc] using hqab_dvd_c
    obtain ⟨k, hk⟩ := hqab_dvd
    have hc_dvd : c ∣ 2 * (q * a * b) := by
      simpa [c, mul_assoc] using hc_dvd_twoqab
    have hk_dvd_two : k ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_left
        (by positivity : 0 < q * a * b)
      have : (q * a * b) * k ∣ (q * a * b) * 2 := by
        rw [← hk]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hc_dvd
      exact this
    have hcpos : 0 < c :=
      Nat.lcm_pos (by positivity)
        (Nat.lcm_pos (by positivity) (by positivity))
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hkzero, mul_zero] at hk
      exact (Nat.ne_of_gt hcpos) hk
    have hkcases : k = 1 ∨ k = 2 := by
      have hkle : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk_dvd_two
      omega
    rcases hkcases with rfl | rfl
    · left
      rw [hnlcm]
      simpa [c, mul_assoc] using hk
    · right
      rw [hnlcm]
      convert hk using 1
      all_goals ring
  rcases hnshape with hn | hn
  · have hu : u = b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q * a)
      calc
        (q * a) * u = n := hqu
        _ = (q * a) * b := by simpa [mul_assoc] using hn
    have hv : 2 * v = q * b := by
      apply Nat.eq_of_mul_eq_mul_left hap
      calc
        a * (2 * v) = (2 * a) * v := by ring
        _ = n := hav
        _ = a * (q * b) := by rw [hn]; ring
    have hw : 2 * w = q * a := by
      apply Nat.eq_of_mul_eq_mul_left hbp
      calc
        b * (2 * w) = (2 * b) * w := by ring
        _ = n := hbw
        _ = b * (q * a) := by rw [hn]; ring
    have hrel : q * a + 2 * (b - 1) = q * b := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have hasub : a - 1 + 1 = a := Nat.sub_add_cancel ha.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hn hu hv hw hcount hqsub hasub hbsub htwosub hq ha hb ⊢
      nlinarith only [hn, hu, hv, hw, hcount, hqsub, hasub, hbsub, htwosub, hq, ha, hb]
    have hab : a < b := by
      by_contra hnot
      have hle : b ≤ a := by omega
      have hmul_le := Nat.mul_le_mul_left q hle
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hrel hle hmul_le hbsub hq ha hb ⊢
      nlinarith only [hrel, hle, hmul_le, hbsub, hq, ha, hb]
    have hrel' : (b - a) * q = 2 * (b - 1) := by
      have hsub : b - a + a = b := Nat.sub_add_cancel hab.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hrel hsub hbsub hq ha hb ⊢
      nlinarith only [hrel, hsub, hbsub, hq, ha, hb]
    have hq_dvd_twice : q ∣ 2 * (b - 1) :=
      ⟨b - a, by simpa [mul_comm] using hrel'.symm⟩
    have hq_dvd_bsub : q ∣ b - 1 := by
      rcases Nat.coprime_or_dvd_of_prime Nat.prime_two q with h2q | h2q
      · exact h2q.symm.dvd_of_dvd_mul_left hq_dvd_twice
      · have ha_not_even : ¬ Even a := by
          intro hae
          have htwo_one : 2 ∣ 1 := by
            rw [← hqa.gcd_eq_one]
            exact Nat.dvd_gcd h2q (even_iff_two_dvd.mp hae)
          norm_num at htwo_one
        have hb_not_even : ¬ Even b := by
          intro hbe
          have htwo_one : 2 ∣ 1 := by
            rw [← hqb.gcd_eq_one]
            exact Nat.dvd_gcd h2q (even_iff_two_dvd.mp hbe)
          norm_num at htwo_one
        have hdelta_even : 2 ∣ b - a := by
          rw [← even_iff_two_dvd, Nat.even_sub hab.le]
          constructor
          · exact fun hbe => (hb_not_even hbe).elim
          · exact fun hae => (ha_not_even hae).elim
        obtain ⟨k, hk⟩ := hdelta_even
        refine ⟨k, ?_⟩
        have hcancel : k * q = b - 1 := by
          rw [hk] at hrel'
          have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
          zify at hrel' hbsub ⊢
          nlinarith
        simpa [mul_comm] using hcancel.symm
    obtain ⟨k, hk⟩ := hq_dvd_bsub
    have hbk : b = 1 + q * k := by
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hk hbsub hq ha hb ⊢
      nlinarith only [hk, hbsub, hq, ha, hb]
    have hdelta : b - a = 2 * k := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      calc
        (b - a) * q = 2 * (b - 1) := hrel'
        _ = 2 * (q * k) := by rw [hk]
        _ = (2 * k) * q := by ring
    have hale : a ≤ q - 1 := Nat.le_of_dvd (by omega) hadiv
    have hq3 : 3 ≤ q := by omega
    have hqsub_two : q - 2 + 2 = q :=
      Nat.sub_add_cancel (by omega : 2 ≤ q)
    have hak : a = 1 + k * (q - 2) := by
      have hba : b - a + a = b := Nat.sub_add_cancel hab.le
      zify at hbk hdelta hqsub_two hba hq ha hb ⊢
      nlinarith only [hbk, hdelta, hqsub_two, hba, hq, ha, hb]
    have hkpos : 0 < k := by omega
    have hk_le_one : k ≤ 1 := by
      have hmul_le : k * (q - 2) ≤ 1 * (q - 2) := by
        have hqsub_one : q - 2 + 1 = q - 1 := by omega
        zify at hak hale hqsub_one hq ha hb ⊢
        nlinarith only [hak, hale, hqsub_one, hq, ha, hb]
      exact (Nat.mul_le_mul_right_iff (by omega : 0 < q - 2)).mp hmul_le
    have hkone : k = 1 := by omega
    right
    left
    have haeq : a = q - 1 := by
      simp [hkone] at hak
      omega
    have hbeq : b = q + 1 := by omega
    refine ⟨haeq, hbeq, ?_⟩
    rw [hn, haeq, hbeq]
    ring
  · have hqodd : Nat.Coprime q 2 := by
      rcases Nat.coprime_or_dvd_of_prime Nat.prime_two q with h2q | h2q
      · exact h2q.symm
      · exfalso
        have hc_dvd_qab :
            Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) ∣
              q * a * b := by
          apply Nat.lcm_dvd
          · exact ⟨b, by ring⟩
          · apply Nat.lcm_dvd
            · obtain ⟨q2, hq2⟩ := h2q
              exact ⟨q2 * b, by rw [hq2]; ring⟩
            · obtain ⟨q2, hq2⟩ := h2q
              exact ⟨q2 * a, by rw [hq2]; ring⟩
        have hdiv : 2 * q * a * b ∣ q * a * b := by
          rw [← hn, hnlcm]
          exact hc_dvd_qab
        have hpos : 0 < q * a * b := by positivity
        have hle := Nat.le_of_dvd hpos hdiv
        have hdouble : 2 * (q * a * b) ≤ q * a * b := by
          simpa [mul_assoc] using hle
        omega
    have hu : u = 2 * b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q * a)
      calc
        (q * a) * u = n := hqu
        _ = (q * a) * (2 * b) := by rw [hn]; ring
    have hv : v = q * b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * a)
      calc
        (2 * a) * v = n := hav
        _ = (2 * a) * (q * b) := by rw [hn]; ring
    have hw : w = q * a := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * b)
      calc
        (2 * b) * w = n := hbw
        _ = (2 * b) * (q * a) := by rw [hn]; ring
    have hrel : q * a + (2 * b - 1) = q * b := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have hasub : a - 1 + 1 = a := Nat.sub_add_cancel ha.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hn hu hv hw hcount hqsub hasub hbsub htwosub hq ha hb ⊢
      nlinarith only [hn, hu, hv, hw, hcount, hqsub, hasub, hbsub, htwosub, hq, ha, hb]
    have hab : a < b := by
      by_contra hnot
      have hle : b ≤ a := by omega
      have hmul_le := Nat.mul_le_mul_left q hle
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hrel hle hmul_le htwosub hq ha hb ⊢
      nlinarith only [hrel, hle, hmul_le, htwosub, hq, ha, hb]
    have hrel' : (b - a) * q = 2 * b - 1 := by
      have hsub : b - a + a = b := Nat.sub_add_cancel hab.le
      have htwob : 1 ≤ 2 * b := by omega
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel htwob
      zify at hrel hsub htwosub hq ha hb ⊢
      nlinarith only [hrel, hsub, htwosub, hq, ha, hb]
    have hq_dvd : q ∣ 2 * b - 1 :=
      ⟨b - a, by simpa [mul_comm] using hrel'.symm⟩
    obtain ⟨k, hk⟩ := hq_dvd
    have htwo_b : 2 * b = 1 + q * k := by omega
    have hdelta : b - a = k := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      calc
        (b - a) * q = 2 * b - 1 := hrel'
        _ = q * k := hk
        _ = k * q := by ring
    have hak : a + k = b := by omega
    have hale : a ≤ q - 1 := Nat.le_of_dvd (by omega) hadiv
    have hkpos : 0 < k := by omega
    have hqodd' : Odd q := hqodd.odd_of_right
    have hkodd : Odd k := by
      rw [← Nat.not_even_iff_odd]
      intro hkeven
      have hqkeven : Even (q * k) := hkeven.mul_left q
      rcases hqkeven with ⟨r, hr⟩
      omega
    have hkle : k ≤ 3 := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at htwo_b hak hale hqsub htwosub hq ha hb ⊢
      nlinarith only [htwo_b, hak, hale, hqsub, htwosub, hq, ha, hb]
    have hkcases : k = 1 ∨ k = 3 := by
      rcases hkodd with ⟨j, hj⟩
      omega
    rcases hkcases with hk1 | hk3
    · right
      right
      have hqgcd : Nat.gcd (q - 1) 2 = 2 := by
        apply Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        apply Nat.dvd_gcd
        · rcases hqodd' with ⟨r, hr⟩
          exact ⟨r, by simp [hr]⟩
        · exact dvd_refl 2
      have htwoa : 2 * a = q - 1 := by
        have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
        zify at hk1 hak htwo_b hqsub hq ha hb ⊢
        nlinarith only [hk1, hak, htwo_b, hqsub, hq, ha, hb]
      have htwobb : 2 * b = q + 1 := by
        zify at hk1 htwo_b hq ha hb ⊢
        nlinarith only [hk1, htwo_b, hq, ha, hb]
      have hqsub_even : 2 ∣ q - 1 := ⟨a, htwoa.symm⟩
      have hqadd_even : 2 ∣ q + 1 := ⟨b, htwobb.symm⟩
      have haeq : a = (q - 1) / 2 := by
        rw [← htwoa]
        simp
      have hbeq : b = (q + 1) / 2 := by
        rw [← htwobb]
        simp
      refine ⟨hqodd, haeq, hbeq, ?_⟩
      rw [hn, hqgcd, haeq, hbeq]
      obtain ⟨x, hx⟩ := hqsub_even
      obtain ⟨y, hy⟩ := hqadd_even
      rw [hx, hy]
      simp
      rw [show 2 * y * q * (2 * x) = (2 * q * x * y) * 2 by ring]
      simp
    · left
      have hqle : q ≤ 3 := by
        have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
        have hqsub_two : q - 2 + 2 = q :=
          Nat.sub_add_cancel (by omega : 2 ≤ q)
        simp [hk3] at hak htwo_b
        zify at hak htwo_b hale hqsub hqsub_two hq ha hb ⊢
        nlinarith only [hak, htwo_b, hale, hqsub, hqsub_two, hq, ha, hb]
      have hqeq : q = 3 := by omega
      subst q
      have haeq : a = 2 := by omega
      have hbeq : b = 5 := by omega
      exact ⟨rfl, haeq, hbeq, by simp [hn, haeq, hbeq]⟩

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
end Dickson
end Glauberman


end Source18

end CFSGPackGroupOrderCases
