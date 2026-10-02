-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_23_dickson_case_p_part_normalizer_self
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:22:21.281428+00:00
-- url     : https://prove2.me/submissions/bbc4b206-e81d-430a-85a9-11c09709305e

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
import Definitions.Def_cfsg_elementary_abelian
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_dickson_counting
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_partition_count_of_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_2_a_sylow_equiv_additive

set_option autoImplicit false
namespace Glauberman.Dickson
end Glauberman.Dickson
namespace CFSGPackCase823
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

section Source5
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonSmallAlternating.lean
/-!
# Small alternating and symmetric recognition lemmas

These low-order action arguments form an independent Dickson-classification
compilation boundary.
-/

namespace Glauberman
namespace Dickson

universe u

/-- Huppert II.8.17(b): a group of order twelve with four Sylow `3`-subgroups is `A₄`. -/
theorem huppert_II_8_17_b_order_twelve_four_sylow_three
    {G : Type u} [Group G] [Finite G]
    (hGcard : Nat.card G = 12) (hSylow : Nat.card (Sylow 3 G) = 4) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
  let Ω := Sylow 3 G
  let := Fintype.ofFinite Ω
  have hΩcard : Fintype.card Ω = 4 := by
    simpa [Ω, Nat.card_eq_fintype_card] using hSylow
  have hfac12 : (Nat.factorization 12) 3 = 1 := by
    rw [show 12 = 3 * 4 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
  have hnormalizer_eq :
      ∀ P : Ω, Subgroup.normalizer (P : Set G) =
        (P : Subgroup G) := by
    intro P
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hindex :
        (Subgroup.normalizer (P : Set G)).index = 4 := by
      rw [← P.card_eq_index_normalizer, hSylow]
    have hNcard :
        Nat.card (Subgroup.normalizer (P : Set G)) = 3 := by
      have hmul :=
        (Subgroup.normalizer (P : Set G)).card_mul_index
      rw [hindex, hGcard] at hmul
      omega
    exact
      (Subgroup.eq_of_le_of_card_ge
        (show (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G) from
          Subgroup.le_normalizer) (by omega)).symm
  let act := MulAction.toPermHom G Ω
  have hker_le : ∀ P : Ω, act.ker ≤ (P : Subgroup G) := by
    intro P x hx
    have hxperm : act x = 1 := hx
    have hxfix : x • P = P := by
      have h := DFunLike.congr_fun hxperm P
      simpa [act] using h
    have hxstab : x ∈ MulAction.stabilizer G P := hxfix
    rw [Sylow.stabilizer_eq_normalizer, hnormalizer_eq P] at hxstab
    exact hxstab
  have hact_inj : Function.Injective act := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    let P : Ω := default
    obtain ⟨Q, hQP⟩ :=
      Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Ω) P
    have hxP : x ∈ (P : Subgroup G) := hker_le P hx
    have hxQ : x ∈ (Q : Subgroup G) := hker_le Q hx
    by_contra hxone
    let I : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G)
    have hxI : x ∈ I := ⟨hxP, hxQ⟩
    have hIcard_ne_one : Nat.card I ≠ 1 := by
      intro hIcard
      have hIbot : I = ⊥ := Subgroup.card_eq_one.mp hIcard
      rw [hIbot, Subgroup.mem_bot] at hxI
      exact hxone hxI
    have hPcard : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hQcard : Nat.card Q = 3 := by
      rw [Q.card_eq_multiplicity, hGcard]
      rw [hfac12]
      norm_num
    have hIdivP : Nat.card I ∣ Nat.card P := by
      rw [← Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (show I ≤ (P : Subgroup G) from inf_le_left)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card (I.subgroupOf (P : Subgroup G))
    have hIcard : Nat.card I = 3 := by
      have hdiv3 : Nat.card I ∣ 3 := by simpa [hPcard] using hIdivP
      rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
      · exact (hIcard_ne_one h).elim
      · exact h
    have hIP : I = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hIQ : I = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    apply hQP
    exact Sylow.ext (hIQ.symm.trans hIP)
  let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq hΩcard
  let actFin : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom eΩ).toMonoidHom.comp act
  have hactFin_inj : Function.Injective actFin := by
    intro x y hxy
    apply hact_inj
    apply (Equiv.permCongrHom eΩ).injective
    simpa [actFin] using hxy
  let K : Subgroup (Equiv.Perm (Fin 4)) := actFin.range
  have hrange_inj : Function.Injective actFin.rangeRestrict := by
    intro x y hxy
    exact hactFin_inj (congrArg Subtype.val hxy)
  let eRange : G ≃* K :=
    MulEquiv.ofBijective actFin.rangeRestrict
      ⟨hrange_inj, MonoidHom.rangeRestrict_surjective actFin⟩
  have hKcard : Nat.card K = 12 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hpermcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hKindex : K.index = 2 := by
    have hmul := K.index_mul_card
    rw [hKcard, hpermcard] at hmul
    omega
  have hKalt : K = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hKindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hKalt)⟩

-- Omitted: outside declaration proof/source closure.

end Dickson
end Glauberman


end Source5

section Source17
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCase823.lean
/-!
# Dickson case II.8.23
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise

universe u

/-- Huppert II.8.23: the Dickson case with a nontrivial self-normalizing Sylow p-subgroup. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) (hpm : 1 < p ^ m)
    (hnormalizer : Subgroup.normalizer (P : Set H) = (P : Subgroup H)) :
    (Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∨
    (p ^ m = 2 ∧ ∃ z : ℕ, ¬ 2 ∣ z ∧
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    (p ^ m = 3 ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) := by
  classical
  rcases huppert_II_8_22_dickson_counting hFcard H P hPcard with
    ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct, hs, hnormalizerZ, hdihedral,
      _hnormalizerP, hdivides, _hcounting⟩
  let NP := Subgroup.normalizer (P : Set H)
  let NZ : Fin r → Subgroup H := fun i => Subgroup.normalizer (Z i : Set H)
  have h823_partition_count :
      Nat.card H =
        1 + (p ^ m - 1) * NP.index +
          ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    dsimp only [NP, NZ]
    apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
    intro x hx
    convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
      hcoprime hmaximal hrepresentative hdistinct x hx using 1
    funext A
    rcases A with Q | z <;> rfl
  have h823_p_index_factor : p ^ m * NP.index = Nat.card H := by
    have hNPcard : Nat.card NP = p ^ m := by
      dsimp only [NP]
      rw [hnormalizer, hPcard]
    calc
      p ^ m * NP.index = Nat.card NP * NP.index := by rw [hNPcard]
      _ = Nat.card H := NP.card_mul_index
  have h823_z_index_factor :
      ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
    intro i
    have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
      dsimp only [NZ]
      exact hnormalizerZ i
    calc
      (Nat.card (Z i) * s i) * (NZ i).index =
          Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
      _ = Nat.card H := (NZ i).card_mul_index
  have h823_index_count :
      NP.index =
        1 + ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hsplit :
        (p ^ m - 1) * NP.index + NP.index = p ^ m * NP.index := by
      calc
        (p ^ m - 1) * NP.index + NP.index =
            (p ^ m - 1 + 1) * NP.index := by ring
        _ = p ^ m * NP.index := by rw [Nat.sub_add_cancel hpm.le]
    have hcancel :
        (p ^ m - 1) * NP.index + NP.index =
          (p ^ m - 1) * NP.index + (1 + T) := by
      calc
        (p ^ m - 1) * NP.index + NP.index =
            p ^ m * NP.index := hsplit
        _ = Nat.card H := h823_p_index_factor
        _ = 1 + (p ^ m - 1) * NP.index + T := by
          simpa only [T] using h823_partition_count
        _ = (p ^ m - 1) * NP.index + (1 + T) := by omega
    change NP.index = 1 + T
    exact Nat.add_left_cancel hcancel
  have h823_range_bound : r * p ^ m < 4 := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hterm (i : Fin r) :
        Nat.card H ≤ 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by
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
          (h823_z_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by ring
    have hrs : r * Nat.card H ≤ 4 * T := by
      calc
        r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
        _ ≤ Finset.univ.sum fun i : Fin r =>
            4 * ((Nat.card (Z i) - 1) * (NZ i).index) :=
          Finset.sum_le_sum fun i _hi => hterm i
        _ = 4 * T := by simp [T, Finset.mul_sum]
    have hcountT : NP.index = 1 + T := by
      simpa only [T] using h823_index_count
    have hT_lt_index : T < NP.index := by omega
    have hscaled_lt : p ^ m * T < Nat.card H := by
      calc
        p ^ m * T < p ^ m * NP.index :=
          (Nat.mul_lt_mul_left (by omega : 0 < p ^ m)).2 hT_lt_index
        _ = Nat.card H := h823_p_index_factor
    have hcancel : (r * p ^ m) * Nat.card H < 4 * Nat.card H := by
      calc
        (r * p ^ m) * Nat.card H = p ^ m * (r * Nat.card H) := by ring
        _ ≤ p ^ m * (4 * T) := Nat.mul_le_mul_left (p ^ m) hrs
        _ = 4 * (p ^ m * T) := by ring
        _ < 4 * Nat.card H :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hscaled_lt
    exact (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
  have h823_small_cases :
      r = 0 ∨ (r = 1 ∧ (p ^ m = 2 ∨ p ^ m = 3)) := by
    have hr_le : r ≤ r * p ^ m := by
      simpa using Nat.mul_le_mul_left r hpm.le
    have hr_lt : r < 4 := lt_of_le_of_lt hr_le h823_range_bound
    interval_cases r <;> omega
  have h823_case_zero (hr : r = 0) :
      Nat.card H = p ^ m ∧ IsElementaryAbelian p H := by
    subst r
    have hNPindex : NP.index = 1 := by
      simpa using h823_index_count
    have hPindex : (P : Subgroup H).index = 1 := by
      dsimp only [NP] at hNPindex
      rwa [hnormalizer] at hNPindex
    have hPtop : (P : Subgroup H) = ⊤ := Subgroup.index_eq_one.mp hPindex
    have hHcard : Nat.card H = p ^ m := by
      have h := hPcard
      rw [hPtop] at h
      simpa using h
    let : Fintype F := Fintype.ofFinite F
    let : CharP F p :=
      charP_of_card_eq_prime_pow (by simpa using hFcard)
    obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
    have hHleQ : H ≤ (Q : Subgroup (PSL2MatrixGroup F)) := by
      intro x hx
      change (⟨x, hx⟩ : H) ∈ (Q : Subgroup _).comap H.subtype
      rw [hQcomap, hPtop]
      simp
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
    have hHElementary : IsElementaryAbelian p H := by
      let : IsElementaryAbelian p Q := hQElementary
      refine
        { toIsMulCommutative :=
            { is_comm := ⟨fun x y =>
                Subtype.ext <|
                  setLike_mul_comm (hHleQ x.2) (hHleQ y.2)⟩ }
          exponent_dvd_p := ?_ }
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      let xQ : Q := ⟨(x : PSL2MatrixGroup F), hHleQ x.2⟩
      have hxpow : xQ ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p Q) xQ
      simpa [xQ] using congrArg Subtype.val hxpow
    exact ⟨hHcard, hHElementary⟩
  have h823_case_two (hr : r = 1) (hpm2 : p ^ m = 2) :
      ∃ z : ℕ, ¬ 2 ∣ z ∧
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z) := by
    subst r
    have hcount0 :
        NP.index =
          1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
      simpa using h823_index_count
    have hPfactor2 : 2 * NP.index = Nat.card H := by
      calc
        2 * NP.index = p ^ m * NP.index :=
          congrArg (fun a => a * NP.index) hpm2.symm
        _ = Nat.card H := h823_p_index_factor
    have hZfactor0 :
        (Nat.card (Z 0) * s 0) * (NZ 0).index = Nat.card H :=
      h823_z_index_factor 0
    have hs0_two : s 0 = 2 := by
      have hs0 := hs 0
      rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
      · have hzbound :
            Nat.card (Z 0) ≤ 2 * (Nat.card (Z 0) - 1) := by
          have hz := hnontrivial 0
          omega
        have hlt :
            Nat.card (Z 0) * (NZ 0).index < 2 * NP.index := by
          calc
            Nat.card (Z 0) * (NZ 0).index ≤
                (2 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
              Nat.mul_le_mul_right (NZ 0).index hzbound
            _ = 2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
            _ < 2 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
              omega
            _ = 2 * NP.index := by rw [← hcount0]
        have hbad : Nat.card H < Nat.card H := by
          calc
            Nat.card H = Nat.card (Z 0) * (NZ 0).index := by
              simpa [hs0_one] using hZfactor0.symm
            _ < 2 * NP.index := hlt
            _ = Nat.card H := hPfactor2
        exact (Nat.lt_irrefl _ hbad).elim
      · exact hs0_two
    have hk0_one : (NZ 0).index = 1 := by
      have hZfactor2 :
          2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
          _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hs0_two]
          _ = Nat.card H := hZfactor0
      have hindex_eq : NP.index = Nat.card (Z 0) * (NZ 0).index := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
        exact hPfactor2.trans hZfactor2.symm
      have hzsplit :
          Nat.card (Z 0) * (NZ 0).index =
            (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
        calc
          Nat.card (Z 0) * (NZ 0).index =
              (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by
            rw [Nat.sub_add_cancel (hnontrivial 0).le]
          _ = (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
            ring
      have hcancel :
          (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
            (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by
        calc
          (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
              Nat.card (Z 0) * (NZ 0).index := hzsplit.symm
          _ = NP.index := hindex_eq.symm
          _ = 1 + (Nat.card (Z 0) - 1) * (NZ 0).index := hcount0
          _ = (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by omega
      exact Nat.add_left_cancel hcancel
    have hHcard2 : Nat.card H = 2 * Nat.card (Z 0) := by
      calc
        Nat.card H = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
          hZfactor0.symm
        _ = 2 * Nat.card (Z 0) := by rw [hs0_two, hk0_one]; ring
    have hp_eq_two : p = 2 := by
      have hm_ne_zero : m ≠ 0 := by
        intro hm
        subst m
        norm_num at hpm2
      have hp_dvd : p ∣ 2 := by
        have hp_pow : p ∣ p ^ m := dvd_pow_self p hm_ne_zero
        exact hpm2 ▸ hp_pow
      exact
        (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp_dvd
    have hzodd : ¬ 2 ∣ Nat.card (Z 0) := by
      apply Nat.prime_two.coprime_iff_not_dvd.mp
      simpa [hp_eq_two] using hcoprime 0
    have hNZtop : NZ 0 = ⊤ := by
      exact Subgroup.index_eq_one.mp hk0_one
    have hHequiv : Nonempty (H ≃* DihedralGroup (Nat.card (Z 0))) := by
      obtain ⟨eD⟩ := hdihedral 0 hs0_two
      let eH : NZ 0 ≃* H :=
        (MulEquiv.subgroupCongr hNZtop).trans
          (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
      exact ⟨eH.symm.trans eD⟩
    exact ⟨Nat.card (Z 0), hzodd, hdivides 0, hHcard2, hHequiv⟩
  have h823_case_three (hr : r = 1) (hpm3 : p ^ m = 3) :
      Nonempty (H ≃* alternatingGroup (Fin 4)) := by
    subst r
    have hcount0 :
        NP.index =
          1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
      simpa using h823_index_count
    have hPfactor3 : 3 * NP.index = Nat.card H := by
      calc
        3 * NP.index = p ^ m * NP.index :=
          congrArg (fun a => a * NP.index) hpm3.symm
        _ = Nat.card H := h823_p_index_factor
    have hZfactor0 :
        (Nat.card (Z 0) * s 0) * (NZ 0).index = Nat.card H :=
      h823_z_index_factor 0
    have hs0_two : s 0 = 2 := by
      have hs0 := hs 0
      rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
      · have hzbound :
            Nat.card (Z 0) ≤ 3 * (Nat.card (Z 0) - 1) := by
          have hz := hnontrivial 0
          omega
        have hlt :
            Nat.card (Z 0) * (NZ 0).index < 3 * NP.index := by
          calc
            Nat.card (Z 0) * (NZ 0).index ≤
                (3 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
              Nat.mul_le_mul_right (NZ 0).index hzbound
            _ = 3 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
            _ < 3 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
              omega
            _ = 3 * NP.index := by rw [← hcount0]
        have hbad : Nat.card H < Nat.card H := by
          calc
            Nat.card H = Nat.card (Z 0) * (NZ 0).index := by
              simpa [hs0_one] using hZfactor0.symm
            _ < 3 * NP.index := hlt
            _ = Nat.card H := hPfactor3
        exact (Nat.lt_irrefl _ hbad).elim
      · exact hs0_two
    have hz0_two : Nat.card (Z 0) = 2 := by
      have hZfactor2 :
          2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
          _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hs0_two]
          _ = Nat.card H := hZfactor0
      have hfactor_eq :
          3 * NP.index = 2 * (Nat.card (Z 0) * (NZ 0).index) :=
        hPfactor3.trans hZfactor2.symm
      by_contra hz_ne_two
      have hz_ge_three : 3 ≤ Nat.card (Z 0) := by
        have hz := hnontrivial 0
        omega
      have hzbound :
          2 * Nat.card (Z 0) ≤ 3 * (Nat.card (Z 0) - 1) := by
        omega
      have hlt :
          2 * (Nat.card (Z 0) * (NZ 0).index) < 3 * NP.index := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (2 * Nat.card (Z 0)) * (NZ 0).index := by ring
          _ ≤ (3 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
            Nat.mul_le_mul_right (NZ 0).index hzbound
          _ = 3 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
          _ < 3 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
            omega
          _ = 3 * NP.index := by rw [← hcount0]
      exact (Nat.lt_irrefl _ (hlt.trans_eq hfactor_eq)).elim
    have hk0_three : (NZ 0).index = 3 := by
      have hcount' : NP.index = 1 + (NZ 0).index := by
        simpa [hz0_two] using hcount0
      have hZfactor4 : 4 * (NZ 0).index = Nat.card H := by
        calc
          4 * (NZ 0).index =
              (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hz0_two, hs0_two]
          _ = Nat.card H := hZfactor0
      have hfactor' : 3 * NP.index = 4 * (NZ 0).index :=
        hPfactor3.trans hZfactor4.symm
      omega
    have hHcard12 : Nat.card H = 12 := by
      calc
        Nat.card H = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
          hZfactor0.symm
        _ = 12 := by rw [hz0_two, hs0_two, hk0_three]
    have hp_eq_three : p = 3 := by
      have hm_ne_zero : m ≠ 0 := by
        intro hm
        subst m
        norm_num at hpm3
      have hp_dvd : p ∣ 3 := by
        have hp_pow : p ∣ p ^ m := dvd_pow_self p hm_ne_zero
        exact hpm3 ▸ hp_pow
      exact
        (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hp_dvd
    subst p
    have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
      have hPindex4 : NP.index = 4 := by
        simpa [hz0_two, hk0_three] using hcount0
      calc
        Nat.card (Sylow 3 H) =
            (Subgroup.normalizer (P : Set H)).index :=
          P.card_eq_index_normalizer
        _ = NP.index := by rfl
        _ = 4 := hPindex4
    exact huppert_II_8_17_b_order_twelve_four_sylow_three hHcard12 hSylow4
  rcases h823_small_cases with hr | ⟨hr, hpm2 | hpm3⟩
  · exact Or.inl (h823_case_zero hr)
  · exact Or.inr (Or.inl ⟨hpm2, h823_case_two hr hpm2⟩)
  · exact Or.inr (Or.inr ⟨hpm3, h823_case_three hr hpm3⟩)

end Dickson
end Glauberman


end Source17

end CFSGPackCase823
