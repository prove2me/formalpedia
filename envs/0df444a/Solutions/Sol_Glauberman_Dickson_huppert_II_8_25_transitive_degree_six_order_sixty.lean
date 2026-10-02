-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:31:02.666838+00:00
-- url     : https://prove2.me/submissions/ddf9ed15-45a3-4b42-ac9b-a1662bcc0c66

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
namespace CFSGPackCase825

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

/-- Huppert II.4.7, in the degree-six, order-sixty case used by II.8.25:
a faithful primitive permutation group of degree six and order sixty is `A5`. -/
theorem huppert_II_4_7_primitive_degree_six_order_sixty
    {G Ω : Type u} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω]
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (hΩcard : Nat.card Ω = 6) (hGcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype Ω := Fintype.ofFinite Ω
  have : MulAction.IsPreprimitive G Ω := hprimitive
  have hΩfcard : Fintype.card Ω = 6 := by
    simpa [Nat.card_eq_fintype_card] using hΩcard
  let : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩfcard]; norm_num)
  have hnormal_transitive
      (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
      MulAction.IsPretransitive N Ω := by
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply hN_ne_bot
    apply le_antisymm
    · intro g hg
      have hg_one : g = 1 :=
        (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G Ω)) g fun x =>
          (show x ∈ MulAction.fixedPoints N Ω by simp [hfixed]) ⟨g, hg⟩
      simp [hg_one]
    · exact bot_le
  have hnormal_card_dvd_six
      (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
      6 ∣ Nat.card N := by
    let : MulAction.IsPretransitive N Ω := hnormal_transitive N hN_ne_bot
    let a : Ω := Classical.arbitrary Ω
    have hdiv := (MulAction.stabilizer N a).index_dvd_card
    rw [MulAction.index_stabilizer_of_transitive, hΩcard] at hdiv
    exact hdiv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := default
  have hfac60_two : (Nat.factorization 60) 2 = 2 := by
    have hle : 2 ≤ (Nat.factorization 60) 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp
        (by norm_num)
    have hnle : ¬ 3 ≤ (Nat.factorization 60) 2 := by
      intro h
      have hdvd :=
        (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
      norm_num at hdvd
    omega
  have hPcard : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hGcard]
    rw [hfac60_two]
    norm_num
  have hPindex : P.index = 15 := by
    have hmul := P.card_mul_index
    rw [hPcard, hGcard] at hmul
    omega
  have hSylow2_dvd : Nat.card (Sylow 2 G) ∣ 15 := by
    simpa [hPindex] using P.card_dvd_index
  have hSylow2_not_even : ¬ 2 ∣ Nat.card (Sylow 2 G) :=
    not_dvd_card_sylow 2 G
  have hSylow2_cases :
      Nat.card (Sylow 2 G) = 1 ∨
        Nat.card (Sylow 2 G) = 3 ∨
        Nat.card (Sylow 2 G) = 5 ∨
        Nat.card (Sylow 2 G) = 15 := by
    have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
    have hle : Nat.card (Sylow 2 G) ≤ 15 :=
      Nat.le_of_dvd (by norm_num) hSylow2_dvd
    interval_cases h : Nat.card (Sylow 2 G) <;> norm_num [h] at *
  have hSylow2card5 : Nat.card (Sylow 2 G) = 5 := by
    rcases hSylow2_cases with hcard1 | hcard3 | hcard5 | hcard15
    · have : Subsingleton (Sylow 2 G) :=
        (Nat.card_eq_one_iff_unique.mp hcard1).1
      let : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
      have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
        norm_num
      have hdiv := hnormal_card_dvd_six (P : Subgroup G) hP_ne_bot
      rw [hPcard] at hdiv
      norm_num at hdiv
    · let act3 := MulAction.toPermHom G (Sylow 2 G)
      have hker_le_normalizer (Q : Sylow 2 G) :
          act3.ker ≤
            Subgroup.normalizer (Q : Set G) := by
        intro x hx
        have hxperm : act3 x = 1 := hx
        have hxfix : x • Q = Q := by
          have h := DFunLike.congr_fun hxperm Q
          simpa [act3] using h
        exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
      have hnormalizer_card_twenty :
          Nat.card (Subgroup.normalizer (P : Set G)) = 20 := by
        have hindex :
            (Subgroup.normalizer (P : Set G)).index = 3 := by
          calc
            (Subgroup.normalizer (P : Set G)).index =
                Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
            _ = 3 := hcard3
        have hmul :=
          (Subgroup.normalizer (P : Set G)).card_mul_index
        rw [hindex, hGcard] at hmul
        omega
      have hker_card_dvd_twenty : Nat.card act3.ker ∣ 20 := by
        have hcard := Subgroup.card_dvd_of_le (hker_le_normalizer P)
        rw [hnormalizer_card_twenty] at hcard
        exact hcard
      have hker_bot : act3.ker = ⊥ := by
        by_contra hker
        have hdiv6 := hnormal_card_dvd_six act3.ker hker
        have : 6 ∣ 20 := dvd_trans hdiv6 hker_card_dvd_twenty
        norm_num at this
      have hact3_inj : Function.Injective act3 := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact hker_bot
      let : Fintype (Sylow 2 G) := Fintype.ofFinite (Sylow 2 G)
      have hSylow2fcard : Fintype.card (Sylow 2 G) = 3 := by
        simpa [Nat.card_eq_fintype_card] using hcard3
      have hcard_le := Nat.card_le_card_of_injective act3 hact3_inj
      have hperm_card : Nat.card (Equiv.Perm (Sylow 2 G)) = 6 := by
        rw [Nat.card_eq_fintype_card]
        simp [Fintype.card_perm, hSylow2fcard, Nat.factorial]
      rw [hGcard, hperm_card] at hcard_le
      omega
    · exact hcard5
    · have hnormalizer_card_four :
          Nat.card (Subgroup.normalizer (P : Set G)) = 4 := by
        have hindex :
            (Subgroup.normalizer (P : Set G)).index = 15 := by
          calc
            (Subgroup.normalizer (P : Set G)).index =
                Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
            _ = 15 := hcard15
        have hmul :=
          (Subgroup.normalizer (P : Set G)).card_mul_index
        rw [hindex, hGcard] at hmul
        omega
      have hnormalizer_eq :
          Subgroup.normalizer (P : Set G) =
            (P : Subgroup G) := by
        symm
        apply Subgroup.eq_of_le_of_card_ge
          (show (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G) from
            Subgroup.le_normalizer)
        rw [hnormalizer_card_four, hPcard]
      have hnormalizer_le_centralizer :
          Subgroup.normalizer (P : Set G) ≤
            Subgroup.centralizer (P : Set G) := by
        rw [hnormalizer_eq]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        let xP : P := ⟨x, hx⟩
        let yP : P := ⟨y, hy⟩
        let : IsMulCommutative P :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by
            calc
              Nat.card P = 4 := by simpa only [P.coe_coe] using hPcard
              _ = 2 ^ 2 := by norm_num)
        exact congrArg Subtype.val
          ((@IsMulCommutative.is_comm P _ inferInstance).comm yP xP)
      let K : Subgroup G :=
        (MonoidHom.transferSylow P hnormalizer_le_centralizer).ker
      let : K.Normal := inferInstance
      have hcomp : K.IsComplement' P := by
        exact MonoidHom.ker_transferSylow_isComplement'
          P hnormalizer_le_centralizer
      have hKcard : Nat.card K = 15 := by
        have hmul := hcomp.card_mul_card
        rw [hPcard, hGcard] at hmul
        omega
      have hK_ne_bot : K ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hKcard]
        norm_num
      have hdiv := hnormal_card_dvd_six K hK_ne_bot
      rw [hKcard] at hdiv
      norm_num at hdiv
  let act2 := MulAction.toPermHom G (Sylow 2 G)
  have hker_le_normalizer (Q : Sylow 2 G) :
      act2.ker ≤ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    have hxperm : act2 x = 1 := hx
    have hxfix : x • Q = Q := by
      have h := DFunLike.congr_fun hxperm Q
      simpa [act2] using h
    exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
  have hnormalizer_card_twelve :
      Nat.card (Subgroup.normalizer (P : Set G)) = 12 := by
    have hindex :
        (Subgroup.normalizer (P : Set G)).index = 5 := by
      calc
        (Subgroup.normalizer (P : Set G)).index =
            Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
        _ = 5 := hSylow2card5
    have hmul :=
      (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hindex, hGcard] at hmul
    omega
  have hker_card_dvd_twelve : Nat.card act2.ker ∣ 12 := by
    have hcard := Subgroup.card_dvd_of_le (hker_le_normalizer P)
    rw [hnormalizer_card_twelve] at hcard
    exact hcard
  have hker_bot : act2.ker = ⊥ := by
    by_contra hker_ne_bot
    have hdiv6 := hnormal_card_dvd_six act2.ker hker_ne_bot
    have hker_cases : Nat.card act2.ker = 6 ∨ Nat.card act2.ker = 12 := by
      have hpos : 0 < Nat.card act2.ker := Nat.card_pos
      have hle : Nat.card act2.ker ≤ 12 :=
        Nat.le_of_dvd (by norm_num) hker_card_dvd_twelve
      interval_cases h : Nat.card act2.ker <;> norm_num [h] at *
    rcases hker_cases with hker6 | hker12
    · let K : Subgroup G := act2.ker
      let : K.Normal := inferInstance
      let : Fact (Nat.Prime 3) := ⟨by decide⟩
      let Q : Sylow 3 K := default
      have hfac6_three : (Nat.factorization 6) 3 = 1 := by
        rw [show 6 = 3 * 2 by norm_num,
          Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 2),
          Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
      have hQcard : Nat.card Q = 3 := by
        rw [Q.card_eq_multiplicity, show Nat.card K = 6 from hker6]
        rw [hfac6_three]
        norm_num
      have hQindex : Q.index = 2 := by
        have hmul := Q.card_mul_index
        rw [hQcard, show Nat.card K = 6 from hker6] at hmul
        omega
      have hSylow3_dvd : Nat.card (Sylow 3 K) ∣ 2 := by
        simpa [hQindex] using Q.card_dvd_index
      have hSylow3_mod := card_sylow_modEq_one 3 K
      have hSylow3card1 : Nat.card (Sylow 3 K) = 1 := by
        have hpos : 0 < Nat.card (Sylow 3 K) := Nat.card_pos
        have hle : Nat.card (Sylow 3 K) ≤ 2 :=
          Nat.le_of_dvd (by norm_num) hSylow3_dvd
        interval_cases h : Nat.card (Sylow 3 K)
        · rfl
        · have hfalse : ¬(2 : ℕ) ≡ 1 [MOD 3] := by decide
          exact (hfalse (h ▸ hSylow3_mod)).elim
      have : Subsingleton (Sylow 3 K) :=
        (Nat.card_eq_one_iff_unique.mp hSylow3card1).1
      let : (Q : Subgroup K).Characteristic :=
        Sylow.characteristic_of_subsingleton Q
      let QG : Subgroup G := (Q : Subgroup K).map K.subtype
      let : QG.Normal := inferInstance
      have hQGcard : Nat.card QG = 3 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
      have hQG_ne_bot : QG ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hQGcard]
        norm_num
      have hdiv := hnormal_card_dvd_six QG hQG_ne_bot
      rw [hQGcard] at hdiv
      norm_num at hdiv
    · let K : Subgroup G := act2.ker
      let : K.Normal := inferInstance
      let Q : Sylow 2 K := default
      have hfac12_two : (Nat.factorization 12) 2 = 2 := by
        have hle : 2 ≤ (Nat.factorization 12) 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp
            (by norm_num)
        have hnle : ¬ 3 ≤ (Nat.factorization 12) 2 := by
          intro h
          have hdvd :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
          norm_num at hdvd
        omega
      have hQcard : Nat.card Q = 4 := by
        rw [Q.card_eq_multiplicity, show Nat.card K = 12 from hker12]
        rw [hfac12_two]
        norm_num
      obtain ⟨R, hQR⟩ := Q.exists_comap_subtype_eq
      have hK_le_normalizer : K ≤ Subgroup.normalizer (R : Set G) :=
        hker_le_normalizer R
      have hQnormal : (Q : Subgroup K).Normal := by
        rw [← hQR]
        change (R.subgroupOf K).Normal
        exact Subgroup.normal_subgroupOf_of_le_normalizer hK_le_normalizer
      let : (Q : Subgroup K).Characteristic :=
        Sylow.characteristic_of_normal Q hQnormal
      let QG : Subgroup G := (Q : Subgroup K).map K.subtype
      let : QG.Normal := inferInstance
      have hQGcard : Nat.card QG = 4 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
      have hQG_ne_bot : QG ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hQGcard]
        norm_num
      have hdiv := hnormal_card_dvd_six QG hQG_ne_bot
      rw [hQGcard] at hdiv
      norm_num at hdiv
  have hact2_inj : Function.Injective act2 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hker_bot
  let : Fintype (Sylow 2 G) := Fintype.ofFinite (Sylow 2 G)
  have hSylow2fcard : Fintype.card (Sylow 2 G) = 5 := by
    simpa [Nat.card_eq_fintype_card] using hSylow2card5
  let eΩ2 : Sylow 2 G ≃ Fin 5 := Fintype.equivFinOfCardEq hSylow2fcard
  let actFin2 : G →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom eΩ2).toMonoidHom.comp act2
  have hactFin2_inj : Function.Injective actFin2 := by
    intro x y hxy
    apply hact2_inj
    apply (Equiv.permCongrHom eΩ2).injective
    simpa [actFin2] using hxy
  let A : Subgroup (Equiv.Perm (Fin 5)) := actFin2.range
  let eRange : G ≃* A :=
    MulEquiv.ofBijective actFin2.rangeRestrict
      ⟨fun x y hxy => hactFin2_inj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective actFin2⟩
  have hAcard : Nat.card A = 60 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hperm5card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hAindex : A.index = 2 := by
    have hmul := A.index_mul_card
    rw [hAcard, hperm5card] at hmul
    omega
  have hAalt : A = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hAindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hAalt)⟩

/-- Huppert II.8.25: a faithful transitive permutation group of degree six
and order sixty is `A5`. -/
theorem _root_.solution
    {G Ω : Type u} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω]
    (htransitive : MulAction.IsPretransitive G Ω)
    (hΩcard : Nat.card Ω = 6) (hGcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2 := by
    classical
    let := Fintype.ofFinite Ω
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hΩfcard : Fintype.card Ω = 6 := by
      simpa [Nat.card_eq_fintype_card] using hΩcard
    have hfive : 5 ∣ Nat.card G := by
      rw [hGcard]
      norm_num
    obtain ⟨g, hgorder⟩ := exists_prime_orderOf_dvd_card' 5 hfive
    let σ : Equiv.Perm Ω := MulAction.toPerm g
    have hσorder : orderOf σ = 5 := by
      calc
        orderOf σ = orderOf g :=
          orderOf_injective (MulAction.toPermHom G Ω)
            (MulAction.toPerm_injective : Function.Injective
              (MulAction.toPerm : G → Equiv.Perm Ω)) g
        _ = 5 := hgorder
    have hσcycle : σ.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order'
        (by simpa [hσorder] using (Fact.out : Nat.Prime 5))
        (by rw [hΩfcard, hσorder]; norm_num)
    have hfixed_card : Nat.card (Function.fixedPoints σ) = 1 := by
      rw [Nat.card_eq_fintype_card, σ.card_fixedPoints, hσcycle.cycleType,
        Multiset.sum_singleton, ← hσcycle.orderOf, hσorder, hΩfcard]
    have hfixed_nonempty : Nonempty (Function.fixedPoints σ) :=
      Finite.card_pos_iff.mp (by rw [hfixed_card]; norm_num)
    obtain ⟨x, hx⟩ := hfixed_nonempty
    have hσx : σ x = x := hx
    have hfixed_unique {y : Ω} (hy : σ y = y) : y = x := by
      have hsub : Subsingleton (Function.fixedPoints σ) :=
        (Nat.card_eq_one_iff_unique.mp hfixed_card).1
      exact congrArg Subtype.val
        (hsub.elim (⟨y, hy⟩ : Function.fixedPoints σ) ⟨x, hx⟩)
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨u, hu⟩ := htransitive.exists_smul_eq a x
    obtain ⟨v, hv⟩ := htransitive.exists_smul_eq x c
    have hub_ne : u • b ≠ x := by
      intro hub
      exact hab (smul_left_cancel u (hu.trans hub.symm))
    have hvd_ne : v⁻¹ • d ≠ x := by
      intro hvd
      apply hcd
      calc
        c = v • x := hv.symm
        _ = v • (v⁻¹ • d) := by rw [hvd]
        _ = d := smul_inv_smul v d
    have hσub : σ (u • b) ≠ u • b := by
      intro hfix
      exact hub_ne (hfixed_unique hfix)
    have hσvd : σ (v⁻¹ • d) ≠ v⁻¹ • d := by
      intro hfix
      exact hvd_ne (hfixed_unique hfix)
    obtain ⟨n, hn⟩ := hσcycle.exists_pow_eq hσub hσvd
    have hperm_pow : MulAction.toPerm (g ^ n) = σ ^ n := by
      change (MulAction.toPermHom G Ω) (g ^ n) = σ ^ n
      rw [map_pow]
      rfl
    have hgpow_b : (g ^ n) • (u • b) = v⁻¹ • d := by
      change (MulAction.toPerm (g ^ n)) (u • b) = v⁻¹ • d
      rw [hperm_pow]
      exact hn
    have hσpow_x (k : ℕ) : (σ ^ k) x = x := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, Equiv.Perm.mul_apply, hσx, ih]
    have hgpow_x : (g ^ n) • x = x := by
      change (MulAction.toPerm (g ^ n)) x = x
      rw [hperm_pow]
      exact hσpow_x n
    refine ⟨v * g ^ n * u, ?_, ?_⟩
    · simp only [mul_smul]
      rw [hu, hgpow_x, hv]
    · simp only [mul_smul]
      rw [hgpow_b, smul_inv_smul]
  have hprimitive : MulAction.IsPreprimitive G Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo_transitive
  exact huppert_II_4_7_primitive_degree_six_order_sixty
    hprimitive hΩcard hGcard

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
-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
end Dickson
end Glauberman


end Source18

end CFSGPackCase825
