-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:13:04.273107+00:00
-- url     : https://prove2.me/submissions/82c3a1fb-df8b-40fa-8ea1-c1e4a39d7c8d

import Theorems.Thm_Glauberman_Dickson_h824_alternating_five_of_cyclic_family
import Theorems.Thm_Glauberman_Dickson_h824_symmetric_four_of_cyclic_family
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
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_dickson_counting
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_partition_count_of_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_unique_family

set_option autoImplicit false
namespace Glauberman.Dickson
end Glauberman.Dickson
namespace CFSGPackNoP
open _root_.Glauberman.Dickson

section Source0
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/BenderSuzuki/PFAppendixIII/Basic.lean
/-!
# Appendix III Suzuki two-group interfaces
-/

namespace BenderSuzuki
namespace PFAppendixIII

section BasicGroup

/-- Local instance for the prime `2`, shared by Suzuki two-group coordinates and matrix models. -/
instance instFactNatPrimeTwo : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

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

end BasicGroup

-- Omitted: outside declaration proof/source closure.

universe u v

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
/-!
# Appendix III Suzuki two-group coordinate interfaces
-/
-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

end PFAppendixIII
end BenderSuzuki


end Source0

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

section Source18
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean
/-!
# Huppert II.8.27

Dickson's subgroup classification for subgroups of PSL(2,p^f).
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise
universe u v

set_option maxHeartbeats 1600000 in
/-- Huppert II.8.24: the Dickson case in which p does not divide the subgroup order. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (hp_not_dvd_card_H : ¬ p ∣ Nat.card H) :
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = z ∧ IsCyclic H) ∨
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) := by
  classical
  let P : Sylow p H := default
  have hPcard : Nat.card P = p ^ 0 := by
    rw [P.card_eq_multiplicity,
      Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_card_H, pow_zero]
  rcases huppert_II_8_22_dickson_counting
      (m := 0) hFcard H P hPcard with
    ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct, hs, hnormalizerZ, hdihedral,
      _hnormalizerP, hdivides, _hcounting⟩
  let NZ : Fin r → Subgroup H := fun i => Subgroup.normalizer (Z i : Set H)
  have h824_partition_count :
      Nat.card H =
        1 + ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    have hraw :
        Nat.card H =
          1 + (p ^ 0 - 1) *
              (Subgroup.normalizer (P : Set H)).index +
            ∑ i, (Nat.card (Z i) - 1) *
              (Subgroup.normalizer (Z i : Set H)).index := by
      apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
      intro x hx
      convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
        hcoprime hmaximal hrepresentative hdistinct x hx using 1
      funext A
      rcases A with Q | z <;> rfl
    simpa only [pow_zero, Nat.reduceSubDiff, zero_mul, add_zero, NZ] using hraw
  have h824_z_index_factor :
      ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
    intro i
    have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
      dsimp only [NZ]
      exact hnormalizerZ i
    calc
      (Nat.card (Z i) * s i) * (NZ i).index =
          Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
      _ = Nat.card H := (NZ i).card_mul_index
  have h824_family_bound : r ≤ 3 := by
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
          (h824_z_index_factor i).symm
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
    have hcountT : Nat.card H = 1 + T := by
      simpa only [T] using h824_partition_count
    have hTlt : T < Nat.card H := by omega
    have hcancel : r * Nat.card H < 4 * Nat.card H :=
      hrs.trans_lt
        ((Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hTlt)
    have hrlt : r < 4 :=
      (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
    omega
  have h824_shape :
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
    by_cases hr_zero : r = 0
    · subst r
      have hHcard : Nat.card H = 1 := by
        simpa using h824_partition_count
      have hHcyclic : IsCyclic H := by
        let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hHcard).1
        exact isCyclic_of_subsingleton
      exact Or.inl ⟨1, Or.inl (one_dvd _), hHcard, hHcyclic⟩
    · have h824_positive_shape :
          (∃ z : ℕ,
            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
            Nat.card H = z ∧ IsCyclic H) ∨
          (∃ z : ℕ,
            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
            Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
          Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
          Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (H ≃* alternatingGroup (Fin 5)) := by
        by_cases hr_one : r = 1
        · subst r
          have hs0_one : s 0 = 1 := by
            have hs0 := hs 0
            rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
            · exact hs0_one
            · have hkpos : 0 < (NZ 0).index :=
                Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
              have hzpos : 0 < Nat.card (Z 0) := Nat.card_pos
              have hle :
                  1 + (Nat.card (Z 0) - 1) * (NZ 0).index ≤
                    Nat.card (Z 0) * (NZ 0).index := by
                calc
                  1 + (Nat.card (Z 0) - 1) * (NZ 0).index ≤
                      (NZ 0).index +
                        (Nat.card (Z 0) - 1) * (NZ 0).index := by omega
                  _ = (Nat.card (Z 0) - 1) * (NZ 0).index +
                      (NZ 0).index := Nat.add_comm _ _
                  _ = (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by ring
                  _ = Nat.card (Z 0) * (NZ 0).index := by
                    rw [Nat.sub_add_cancel (hnontrivial 0).le]
              have hlt :
                  Nat.card (Z 0) * (NZ 0).index <
                    (Nat.card (Z 0) * 2) * (NZ 0).index := by
                have hprodpos :
                    0 < Nat.card (Z 0) * (NZ 0).index :=
                  Nat.mul_pos hzpos hkpos
                calc
                  Nat.card (Z 0) * (NZ 0).index <
                      2 * (Nat.card (Z 0) * (NZ 0).index) := by omega
                  _ = (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
              have hbad : Nat.card H < Nat.card H := by
                calc
                  Nat.card H =
                      1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
                    simpa using h824_partition_count
                  _ ≤ Nat.card (Z 0) * (NZ 0).index := hle
                  _ < (Nat.card (Z 0) * 2) * (NZ 0).index := hlt
                  _ = Nat.card H := by
                    calc
                      (Nat.card (Z 0) * 2) * (NZ 0).index =
                          (Nat.card (Z 0) * s 0) * (NZ 0).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 0) * a) * (NZ 0).index) hs0_two.symm
                      _ = Nat.card H := h824_z_index_factor 0
              exact (Nat.lt_irrefl _ hbad).elim
          have hcount0 :
              Nat.card H =
                1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
            simpa using h824_partition_count
          have hfactor0 :
              Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
            simpa [hs0_one] using h824_z_index_factor 0
          have hk_one : (NZ 0).index = 1 := by
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
                _ = Nat.card H := hfactor0
                _ = 1 + (Nat.card (Z 0) - 1) * (NZ 0).index := hcount0
                _ = (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by omega
            exact Nat.add_left_cancel hcancel
          have hHcard : Nat.card H = Nat.card (Z 0) := by
            calc
              Nat.card H = Nat.card (Z 0) * (NZ 0).index := hfactor0.symm
              _ = Nat.card (Z 0) := by rw [hk_one, mul_one]
          have hZtop : Z 0 = ⊤ :=
            Subgroup.eq_top_of_card_eq (H := Z 0) hHcard.symm
          have hHcyclic : IsCyclic H := by
            have htopcyclic : IsCyclic (⊤ : Subgroup H) :=
              (MulEquiv.subgroupCongr hZtop).isCyclic.mp (hcyclic 0)
            exact (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isCyclic.mp htopcyclic
          exact Or.inl ⟨Nat.card (Z 0), hdivides 0, hHcard, hHcyclic⟩
        · have h824_two_or_three_shape :
              (∃ z : ℕ,
                ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                  (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                Nat.card H = z ∧ IsCyclic H) ∨
              (∃ z : ℕ,
                ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                  (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
              Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
              Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
              Nonempty (H ≃* alternatingGroup (Fin 5)) := by
            by_cases hr_two : r = 2
            · have h824_two_shape :
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = z ∧ IsCyclic H) ∨
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
                  Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                subst r
                have hnot_one_one (hs0 : s 0 = 1) (hs1 : s 1 = 1) : False := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index := by
                    simpa [add_assoc] using h824_partition_count
                  have hfactor0 :
                      Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
                    simpa [hs0] using h824_z_index_factor 0
                  have hfactor1 :
                      Nat.card (Z 1) * (NZ 1).index = Nat.card H := by
                    simpa [hs1] using h824_z_index_factor 1
                  have hrel0 :
                      (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                          (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by ring
                      _ = Nat.card (Z 0) * (NZ 0).index := by
                        rw [Nat.sub_add_cancel (hnontrivial 0).le]
                      _ = Nat.card H := hfactor0
                  have hrel1 :
                      (Nat.card (Z 1) - 1) * (NZ 1).index + (NZ 1).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z 1) - 1) * (NZ 1).index + (NZ 1).index =
                          (Nat.card (Z 1) - 1 + 1) * (NZ 1).index := by ring
                      _ = Nat.card (Z 1) * (NZ 1).index := by
                        rw [Nat.sub_add_cancel (hnontrivial 1).le]
                      _ = Nat.card H := hfactor1
                  have hbound0 : 2 * (NZ 0).index ≤ Nat.card H := by
                    calc
                      2 * (NZ 0).index ≤ Nat.card (Z 0) * (NZ 0).index :=
                        Nat.mul_le_mul_right (NZ 0).index (by
                          have hz := hnontrivial 0
                          omega)
                      _ = Nat.card H := hfactor0
                  have hbound1 : 2 * (NZ 1).index ≤ Nat.card H := by
                    calc
                      2 * (NZ 1).index ≤ Nat.card (Z 1) * (NZ 1).index :=
                        Nat.mul_le_mul_right (NZ 1).index (by
                          have hz := hnontrivial 1
                          omega)
                      _ = Nat.card H := hfactor1
                  omega
                have hnot_two_two (hs0 : s 0 = 2) (hs1 : s 1 = 2) : False := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index := by
                    simpa [add_assoc] using h824_partition_count
                  have hfactor0 :
                      2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z 0) * (NZ 0).index) =
                          (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
                      _ = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 0) * a) * (NZ 0).index) hs0.symm
                      _ = Nat.card H := h824_z_index_factor 0
                  have hfactor1 :
                      2 * (Nat.card (Z 1) * (NZ 1).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z 1) * (NZ 1).index) =
                          (Nat.card (Z 1) * 2) * (NZ 1).index := by ring
                      _ = (Nat.card (Z 1) * s 1) * (NZ 1).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 1) * a) * (NZ 1).index) hs1.symm
                      _ = Nat.card H := h824_z_index_factor 1
                  have hrel0 :
                      2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) +
                          2 * (NZ 0).index = Nat.card H := by
                    calc
                      2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) +
                          2 * (NZ 0).index =
                          2 * ((Nat.card (Z 0) - 1 + 1) * (NZ 0).index) := by
                            ring
                      _ = 2 * (Nat.card (Z 0) * (NZ 0).index) := by
                        rw [Nat.sub_add_cancel (hnontrivial 0).le]
                      _ = Nat.card H := hfactor0
                  have hrel1 :
                      2 * ((Nat.card (Z 1) - 1) * (NZ 1).index) +
                          2 * (NZ 1).index = Nat.card H := by
                    calc
                      2 * ((Nat.card (Z 1) - 1) * (NZ 1).index) +
                          2 * (NZ 1).index =
                          2 * ((Nat.card (Z 1) - 1 + 1) * (NZ 1).index) := by
                            ring
                      _ = 2 * (Nat.card (Z 1) * (NZ 1).index) := by
                        rw [Nat.sub_add_cancel (hnontrivial 1).le]
                      _ = Nat.card H := hfactor1
                  have hk0pos : 0 < (NZ 0).index :=
                    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
                  have hk1pos : 0 < (NZ 1).index :=
                    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
                  omega
                have hmixed (i j : Fin 2) (hij : i ≠ j)
                    (hsi : s i = 1) (hsj : s j = 2) :
                    (∃ z : ℕ,
                      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                    Nonempty (H ≃* alternatingGroup (Fin 4)) := by
                  have hsum :
                      (∑ k, (Nat.card (Z k) - 1) * (NZ k).index) =
                        (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                    fin_cases i <;> fin_cases j
                    · exact (hij rfl).elim
                    · simp
                    · simp [add_comm]
                    · exact (hij rfl).elim
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                    calc
                      Nat.card H =
                          1 + ∑ k, (Nat.card (Z k) - 1) * (NZ k).index :=
                        h824_partition_count
                      _ = 1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                        rw [hsum]
                        simp [add_assoc]
                  have hfactor_i :
                      Nat.card (Z i) * (NZ i).index = Nat.card H := by
                    simpa [hsi] using h824_z_index_factor i
                  have hfactor_j :
                      2 * (Nat.card (Z j) * (NZ j).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z j) * (NZ j).index) =
                          (Nat.card (Z j) * 2) * (NZ j).index := by ring
                      _ = (Nat.card (Z j) * s j) * (NZ j).index :=
                        congrArg (fun a =>
                          (Nat.card (Z j) * a) * (NZ j).index) hsj.symm
                      _ = Nat.card H := h824_z_index_factor j
                  have hrel_i :
                      (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
                          (Nat.card (Z i) - 1 + 1) * (NZ i).index := by ring
                      _ = Nat.card (Z i) * (NZ i).index := by
                        rw [Nat.sub_add_cancel (hnontrivial i).le]
                      _ = Nat.card H := hfactor_i
                  have hindex_eq :
                      (NZ i).index =
                        1 + (Nat.card (Z j) - 1) * (NZ j).index := by
                    omega
                  by_cases hzi_two : Nat.card (Z i) = 2
                  · have hdihedral_case :
                        ∃ z : ℕ,
                          ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                            (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                          Nat.card H = 2 * z ∧
                            Nonempty (H ≃* DihedralGroup z) := by
                      have hfactor_i_two : 2 * (NZ i).index = Nat.card H := by
                        calc
                          2 * (NZ i).index = Nat.card (Z i) * (NZ i).index :=
                            congrArg (fun a => a * (NZ i).index) hzi_two.symm
                          _ = Nat.card H := hfactor_i
                      have hindex_i_eq :
                          (NZ i).index = Nat.card (Z j) * (NZ j).index := by
                        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                        exact hfactor_i_two.trans hfactor_j.symm
                      have hzsplit :
                          Nat.card (Z j) * (NZ j).index =
                            (Nat.card (Z j) - 1) * (NZ j).index +
                              (NZ j).index := by
                        calc
                          Nat.card (Z j) * (NZ j).index =
                              (Nat.card (Z j) - 1 + 1) * (NZ j).index := by
                            rw [Nat.sub_add_cancel (hnontrivial j).le]
                          _ = (Nat.card (Z j) - 1) * (NZ j).index +
                              (NZ j).index := by ring
                      have hk_j_one : (NZ j).index = 1 := by
                        have hcancel :
                            (Nat.card (Z j) - 1) * (NZ j).index +
                                (NZ j).index =
                              (Nat.card (Z j) - 1) * (NZ j).index + 1 := by
                          calc
                            (Nat.card (Z j) - 1) * (NZ j).index +
                                (NZ j).index =
                                Nat.card (Z j) * (NZ j).index := hzsplit.symm
                            _ = (NZ i).index := hindex_i_eq.symm
                            _ = 1 + (Nat.card (Z j) - 1) * (NZ j).index :=
                              hindex_eq
                            _ = (Nat.card (Z j) - 1) * (NZ j).index + 1 := by
                              omega
                        exact Nat.add_left_cancel hcancel
                      have hHcard : Nat.card H = 2 * Nat.card (Z j) := by
                        calc
                          Nat.card H =
                              2 * (Nat.card (Z j) * (NZ j).index) :=
                            hfactor_j.symm
                          _ = 2 * Nat.card (Z j) := by rw [hk_j_one, mul_one]
                      have hNZtop : NZ j = ⊤ :=
                        Subgroup.index_eq_one.mp hk_j_one
                      obtain ⟨eD⟩ := hdihedral j hsj
                      let eH : NZ j ≃* H :=
                        (MulEquiv.subgroupCongr hNZtop).trans
                          (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
                      exact
                        ⟨Nat.card (Z j), hdivides j, hHcard,
                          ⟨eH.symm.trans eD⟩⟩
                    exact Or.inl hdihedral_case
                  · have hA4_case :
                        Nonempty (H ≃* alternatingGroup (Fin 4)) := by
                      have hzi_ge_three : 3 ≤ Nat.card (Z i) := by
                        have hzi := hnontrivial i
                        omega
                      have hterm_lt :
                          (Nat.card (Z j) - 1) * (NZ j).index < (NZ i).index := by
                        omega
                      have hfactor_eq :
                          Nat.card (Z i) * (NZ i).index =
                            2 * (Nat.card (Z j) * (NZ j).index) :=
                        hfactor_i.trans hfactor_j.symm
                      have hzi_lt_four : Nat.card (Z i) < 4 := by
                        by_contra hnot
                        have hzi_ge_four : 4 ≤ Nat.card (Z i) := by omega
                        have hcoeff :
                            2 * Nat.card (Z j) ≤
                              Nat.card (Z i) * (Nat.card (Z j) - 1) := by
                          calc
                            2 * Nat.card (Z j) ≤
                                4 * (Nat.card (Z j) - 1) := by
                              have hzj := hnontrivial j
                              omega
                            _ ≤ Nat.card (Z i) * (Nat.card (Z j) - 1) :=
                              Nat.mul_le_mul_right (Nat.card (Z j) - 1) hzi_ge_four
                        have hbad :
                            2 * (Nat.card (Z j) * (NZ j).index) <
                              2 * (Nat.card (Z j) * (NZ j).index) := by
                          calc
                            2 * (Nat.card (Z j) * (NZ j).index) =
                                (2 * Nat.card (Z j)) * (NZ j).index := by ring
                            _ ≤ (Nat.card (Z i) * (Nat.card (Z j) - 1)) *
                                (NZ j).index :=
                              Nat.mul_le_mul_right (NZ j).index hcoeff
                            _ = Nat.card (Z i) *
                                ((Nat.card (Z j) - 1) * (NZ j).index) := by ring
                            _ < Nat.card (Z i) * (NZ i).index :=
                              (Nat.mul_lt_mul_left (by omega : 0 < Nat.card (Z i))).2
                                hterm_lt
                            _ = 2 * (Nat.card (Z j) * (NZ j).index) := hfactor_eq
                        exact (Nat.lt_irrefl _ hbad).elim
                      have hzi_three : Nat.card (Z i) = 3 := by omega
                      have hfactor_eq_three :
                          3 * (NZ i).index =
                            2 * (Nat.card (Z j) * (NZ j).index) := by
                        calc
                          3 * (NZ i).index = Nat.card (Z i) * (NZ i).index :=
                            congrArg (fun a => a * (NZ i).index) hzi_three.symm
                          _ = 2 * (Nat.card (Z j) * (NZ j).index) := hfactor_eq
                      have hzj_two : Nat.card (Z j) = 2 := by
                        by_contra hzj_ne_two
                        have hzj_ge_three : 3 ≤ Nat.card (Z j) := by
                          have hzj := hnontrivial j
                          omega
                        have hcoeff :
                            2 * Nat.card (Z j) ≤
                              3 * (Nat.card (Z j) - 1) := by omega
                        have hbad :
                            2 * (Nat.card (Z j) * (NZ j).index) <
                              2 * (Nat.card (Z j) * (NZ j).index) := by
                          calc
                            2 * (Nat.card (Z j) * (NZ j).index) =
                                (2 * Nat.card (Z j)) * (NZ j).index := by ring
                            _ ≤ (3 * (Nat.card (Z j) - 1)) * (NZ j).index :=
                              Nat.mul_le_mul_right (NZ j).index hcoeff
                            _ = 3 * ((Nat.card (Z j) - 1) * (NZ j).index) := by ring
                            _ < 3 * (NZ i).index :=
                              (Nat.mul_lt_mul_left (by norm_num : 0 < 3)).2 hterm_lt
                            _ = 2 * (Nat.card (Z j) * (NZ j).index) :=
                              hfactor_eq_three
                        exact (Nat.lt_irrefl _ hbad).elim
                      have hindex' : (NZ i).index = 1 + (NZ j).index := by
                        simpa [hzj_two] using hindex_eq
                      have hfactor' : 3 * (NZ i).index = 4 * (NZ j).index := by
                        calc
                          3 * (NZ i).index =
                              2 * (Nat.card (Z j) * (NZ j).index) :=
                            hfactor_eq_three
                          _ = 4 * (NZ j).index := by rw [hzj_two]; ring
                      have hkj_three : (NZ j).index = 3 := by omega
                      have hki_four : (NZ i).index = 4 := by omega
                      have hHcard12 : Nat.card H = 12 := by
                        calc
                          Nat.card H = Nat.card (Z i) * (NZ i).index :=
                            hfactor_i.symm
                          _ = 12 := by rw [hzi_three, hki_four]
                      have hZiIndex4 : (Z i).index = 4 := by
                        have hmul := (Z i).card_mul_index
                        rw [hzi_three, hHcard12] at hmul
                        omega
                      let hZiP : IsPGroup 3 (Z i) :=
                        IsPGroup.of_card (n := 1) (by simpa using hzi_three)
                      let Q : Sylow 3 H := hZiP.toSylow (by
                        rw [hZiIndex4]
                        norm_num)
                      have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
                        calc
                          Nat.card (Sylow 3 H) =
                              (Subgroup.normalizer (Q : Set H)).index :=
                            Q.card_eq_index_normalizer
                          _ = (NZ i).index := by rfl
                          _ = 4 := hki_four
                      exact
                        huppert_II_8_17_b_order_twelve_four_sylow_three
                          hHcard12 hSylow4
                    exact Or.inr hA4_case
                have hs0_cases : s 0 = 1 ∨ s 0 = 2 := by
                  have h := hs 0
                  omega
                have hs1_cases : s 1 = 1 ∨ s 1 = 2 := by
                  have h := hs 1
                  omega
                rcases hs0_cases with hs0 | hs0 <;>
                  rcases hs1_cases with hs1 | hs1
                · exact (hnot_one_one hs0 hs1).elim
                · rcases hmixed 0 1 (by decide) hs0 hs1 with hdih | hA4
                  · exact Or.inr (Or.inl hdih)
                  · exact Or.inr (Or.inr (Or.inl hA4))
                · rcases hmixed 1 0 (by decide) hs1 hs0 with hdih | hA4
                  · exact Or.inr (Or.inl hdih)
                  · exact Or.inr (Or.inr (Or.inl hA4))
                · exact (hnot_two_two hs0 hs1).elim
              exact h824_two_shape
            · have hr_three : r = 3 := by omega
              have h824_three_shape :
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = z ∧ IsCyclic H) ∨
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
                  Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                subst r
                have hs_all_two : ∀ i, s i = 2 := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index +
                            (Nat.card (Z 2) - 1) * (NZ 2).index := by
                    simpa only [Fin.sum_univ_three, add_assoc] using
                      h824_partition_count
                  have hquarter (a : Fin 3) :
                      Nat.card H ≤
                        4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                    have hzbound :
                        Nat.card (Z a) * s a ≤ 4 * (Nat.card (Z a) - 1) := by
                      calc
                        Nat.card (Z a) * s a ≤ Nat.card (Z a) * 2 :=
                          Nat.mul_le_mul_left (Nat.card (Z a)) (hs a).2
                        _ ≤ (2 * (Nat.card (Z a) - 1)) * 2 :=
                          Nat.mul_le_mul_right 2 (by
                            have hza := hnontrivial a
                            omega)
                        _ = 4 * (Nat.card (Z a) - 1) := by ring
                    calc
                      Nat.card H =
                          (Nat.card (Z a) * s a) * (NZ a).index :=
                        (h824_z_index_factor a).symm
                      _ ≤ (4 * (Nat.card (Z a) - 1)) * (NZ a).index :=
                        Nat.mul_le_mul_right (NZ a).index hzbound
                      _ = 4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                  have hhalf (a : Fin 3) (hsa : s a = 1) :
                      2 * Nat.card H ≤
                        4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                    have hfactor :
                        Nat.card (Z a) * (NZ a).index = Nat.card H := by
                      simpa [hsa] using h824_z_index_factor a
                    have hzbound :
                        Nat.card (Z a) ≤ 2 * (Nat.card (Z a) - 1) := by
                      have hza := hnontrivial a
                      omega
                    have hle :
                        Nat.card H ≤
                          2 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                      calc
                        Nat.card H = Nat.card (Z a) * (NZ a).index :=
                          hfactor.symm
                        _ ≤ (2 * (Nat.card (Z a) - 1)) * (NZ a).index :=
                          Nat.mul_le_mul_right (NZ a).index hzbound
                        _ = 2 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                    calc
                      2 * Nat.card H ≤
                          2 * (2 * ((Nat.card (Z a) - 1) * (NZ a).index)) :=
                        Nat.mul_le_mul_left 2 hle
                      _ = 4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                  intro i
                  have hsi := hs i
                  rcases (show s i = 1 ∨ s i = 2 by omega) with hsi_one | hsi_two
                  · exfalso
                    fin_cases i
                    · have hh := hhalf 0 hsi_one
                      have hq1 := hquarter 1
                      have hq2 := hquarter 2
                      omega
                    · have hq0 := hquarter 0
                      have hh := hhalf 1 hsi_one
                      have hq2 := hquarter 2
                      omega
                    · have hq0 := hquarter 0
                      have hq1 := hquarter 1
                      have hh := hhalf 2 hsi_one
                      omega
                  · exact hsi_two
                have hordered (i j k : Fin 3)
                    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
                    (hji : Nat.card (Z j) ≤ Nat.card (Z i))
                    (hkj : Nat.card (Z k) ≤ Nat.card (Z j)) :
                    (∃ z : ℕ,
                      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                    Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                  have hsum :
                      (∑ a, (Nat.card (Z a) - 1) * (NZ a).index) =
                        (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                    have huniv :
                        ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                      apply (Finset.card_eq_iff_eq_univ ({i, j, k} : Finset (Fin 3))).mp
                      simp [hij, hik, hjk]
                    calc
                      (∑ a, (Nat.card (Z a) - 1) * (NZ a).index) =
                          ∑ a ∈ ({i, j, k} : Finset (Fin 3)),
                            (Nat.card (Z a) - 1) * (NZ a).index := by
                              rw [huniv]
                      _ = (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                              simp [hij, hik, hjk, add_assoc]
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                    calc
                      Nat.card H =
                          1 + ∑ a, (Nat.card (Z a) - 1) * (NZ a).index :=
                        h824_partition_count
                      _ = 1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                        rw [hsum]
                        simp [add_assoc]
                  have hfactor (a : Fin 3) :
                      2 * (Nat.card (Z a) * (NZ a).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z a) * (NZ a).index) =
                          (Nat.card (Z a) * 2) * (NZ a).index := by ring
                      _ = (Nat.card (Z a) * s a) * (NZ a).index :=
                        congrArg (fun b =>
                          (Nat.card (Z a) * b) * (NZ a).index)
                          (hs_all_two a).symm
                      _ = Nat.card H := h824_z_index_factor a
                  have hqj :
                      Nat.card (Z i) * (NZ i).index =
                        Nat.card (Z j) * (NZ j).index := by
                    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                    exact (hfactor i).trans (hfactor j).symm
                  have hqk :
                      Nat.card (Z i) * (NZ i).index =
                        Nat.card (Z k) * (NZ k).index := by
                    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                    exact (hfactor i).trans (hfactor k).symm
                  have hrel (a : Fin 3) :
                      (Nat.card (Z a) - 1) * (NZ a).index + (NZ a).index =
                        Nat.card (Z a) * (NZ a).index := by
                    calc
                      (Nat.card (Z a) - 1) * (NZ a).index + (NZ a).index =
                          (Nat.card (Z a) - 1 + 1) * (NZ a).index := by ring
                      _ = Nat.card (Z a) * (NZ a).index := by
                        rw [Nat.sub_add_cancel (hnontrivial a).le]
                  have hindex_sum :
                      (NZ i).index + (NZ j).index + (NZ k).index =
                        Nat.card (Z i) * (NZ i).index + 1 := by
                    have hri := hrel i
                    have hrj :
                        (Nat.card (Z j) - 1) * (NZ j).index + (NZ j).index =
                          Nat.card (Z i) * (NZ i).index :=
                      (hrel j).trans hqj.symm
                    have hrk :
                        (Nat.card (Z k) - 1) * (NZ k).index + (NZ k).index =
                          Nat.card (Z i) * (NZ i).index :=
                      (hrel k).trans hqk.symm
                    have htwice :
                        2 * (Nat.card (Z i) * (NZ i).index) =
                          1 + (Nat.card (Z i) - 1) * (NZ i).index +
                            (Nat.card (Z j) - 1) * (NZ j).index +
                              (Nat.card (Z k) - 1) * (NZ k).index :=
                      (hfactor i).trans hcount
                    omega
                  have hclassification :
                      (∃ z : ℕ,
                        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                      Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                    have hki_le_kj : (NZ i).index ≤ (NZ j).index := by
                      by_contra hnot
                      have hlt : (NZ j).index < (NZ i).index := by omega
                      have hprod_lt :
                          Nat.card (Z j) * (NZ j).index <
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          Nat.card (Z j) * (NZ j).index ≤
                              Nat.card (Z i) * (NZ j).index :=
                            Nat.mul_le_mul_right (NZ j).index hji
                          _ < Nat.card (Z i) * (NZ i).index :=
                            (Nat.mul_lt_mul_left
                              (Nat.card_pos (α := Z i))).2 hlt
                      exact (Nat.lt_irrefl _ (hprod_lt.trans_eq hqj)).elim
                    have hqjk :
                        Nat.card (Z j) * (NZ j).index =
                          Nat.card (Z k) * (NZ k).index :=
                      hqj.symm.trans hqk
                    have hkj_le_kk : (NZ j).index ≤ (NZ k).index := by
                      by_contra hnot
                      have hlt : (NZ k).index < (NZ j).index := by omega
                      have hprod_lt :
                          Nat.card (Z k) * (NZ k).index <
                            Nat.card (Z j) * (NZ j).index := by
                        calc
                          Nat.card (Z k) * (NZ k).index ≤
                              Nat.card (Z j) * (NZ k).index :=
                            Nat.mul_le_mul_right (NZ k).index hkj
                          _ < Nat.card (Z j) * (NZ j).index :=
                            (Nat.mul_lt_mul_left
                              (Nat.card_pos (α := Z j))).2 hlt
                      exact (Nat.lt_irrefl _ (hprod_lt.trans_eq hqjk)).elim
                    have hzk_two : Nat.card (Z k) = 2 := by
                      by_contra hne
                      have hzk_ge_three : 3 ≤ Nat.card (Z k) := by
                        have hzk := hnontrivial k
                        omega
                      have hsum_le :
                          (NZ i).index + (NZ j).index + (NZ k).index ≤
                            3 * (NZ k).index := by omega
                      have hthree_le :
                          3 * (NZ k).index ≤
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          3 * (NZ k).index ≤
                              Nat.card (Z k) * (NZ k).index :=
                            Nat.mul_le_mul_right (NZ k).index hzk_ge_three
                          _ = Nat.card (Z i) * (NZ i).index := hqk.symm
                      omega
                    have hzj_lt_four : Nat.card (Z j) < 4 := by
                      by_contra hnot
                      have hzj_ge_four : 4 ≤ Nat.card (Z j) := by omega
                      have hfour_le :
                          4 * (NZ j).index ≤
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          4 * (NZ j).index ≤
                              Nat.card (Z j) * (NZ j).index :=
                            Nat.mul_le_mul_right (NZ j).index hzj_ge_four
                          _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                      have htwo_kj_le_kk :
                          2 * (NZ j).index ≤ (NZ k).index := by
                        have hqk_two :
                            Nat.card (Z i) * (NZ i).index =
                              2 * (NZ k).index := by
                          calc
                            Nat.card (Z i) * (NZ i).index =
                                Nat.card (Z k) * (NZ k).index := hqk
                            _ = 2 * (NZ k).index := by rw [hzk_two]
                        omega
                      have hsum_le :
                          (NZ i).index + (NZ j).index + (NZ k).index ≤
                            2 * (NZ k).index := by omega
                      have hqk_two :
                          Nat.card (Z i) * (NZ i).index =
                            2 * (NZ k).index := by
                        calc
                          Nat.card (Z i) * (NZ i).index =
                              Nat.card (Z k) * (NZ k).index := hqk
                          _ = 2 * (NZ k).index := by rw [hzk_two]
                      omega
                    have hzj_cases :
                        Nat.card (Z j) = 2 ∨ Nat.card (Z j) = 3 := by
                      have hzj_ge_two : 2 ≤ Nat.card (Z j) := by
                        have hzj := hnontrivial j
                        omega
                      omega
                    rcases hzj_cases with hzj_two | hzj_three
                    · have hdihedral_ordered :
                          ∃ z : ℕ,
                            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                            Nat.card H = 2 * z ∧
                              Nonempty (H ≃* DihedralGroup z) := by
                        have hkj_eq_kk : (NZ j).index = (NZ k).index := by
                          have htwo_kj_eq_two_kk :
                              2 * (NZ j).index = 2 * (NZ k).index := by
                            calc
                              2 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_two]
                              _ = Nat.card (Z k) * (NZ k).index := hqjk
                              _ = 2 * (NZ k).index := by rw [hzk_two]
                          omega
                        have hki_one : (NZ i).index = 1 := by
                          have htwo_kj :
                              2 * (NZ j).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              2 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_two]
                              _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                          omega
                        have hHcard :
                            Nat.card H = 2 * Nat.card (Z i) := by
                          calc
                            Nat.card H =
                                2 * (Nat.card (Z i) * (NZ i).index) :=
                              (hfactor i).symm
                            _ = 2 * Nat.card (Z i) := by rw [hki_one, mul_one]
                        have hNZtop : NZ i = ⊤ :=
                          Subgroup.index_eq_one.mp hki_one
                        obtain ⟨eD⟩ := hdihedral i (hs_all_two i)
                        let eH : NZ i ≃* H :=
                          (MulEquiv.subgroupCongr hNZtop).trans
                            (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
                        exact
                          ⟨Nat.card (Z i), hdivides i, hHcard,
                            ⟨eH.symm.trans eD⟩⟩
                      exact Or.inl hdihedral_ordered
                    · have hexceptional :
                          Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                            Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                        have hzi_lt_six : Nat.card (Z i) < 6 := by
                          by_contra hnot
                          have hzi_ge_six : 6 ≤ Nat.card (Z i) := by omega
                          have hsix_le_q :
                              6 * (NZ i).index ≤
                                Nat.card (Z i) * (NZ i).index :=
                            Nat.mul_le_mul_right (NZ i).index hzi_ge_six
                          have hthree_j :
                              3 * (NZ j).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              3 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_three]
                              _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                          have htwo_k :
                              2 * (NZ k).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              2 * (NZ k).index =
                                  Nat.card (Z k) * (NZ k).index := by
                                rw [hzk_two]
                              _ = Nat.card (Z i) * (NZ i).index := hqk.symm
                          omega
                        have hzi_cases :
                            Nat.card (Z i) = 3 ∨ Nat.card (Z i) = 4 ∨
                              Nat.card (Z i) = 5 := by
                          have hzi_ge_three : 3 ≤ Nat.card (Z i) := by
                            rw [← hzj_three]
                            exact hji
                          omega
                        rcases hzi_cases with hzi_three | hzi_four | hzi_five
                        · have hindices_three :
                              (NZ i).index = 2 ∧ (NZ j).index = 2 ∧
                                (NZ k).index = 3 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_three, hzj_three] at hijq
                            rw [hzi_three, hzk_two] at hikq
                            rw [hzi_three] at hsumq
                            omega
                          have hHcard12 : Nat.card H = 12 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 12 := by rw [hzi_three, hindices_three.1]
                          have hZiIndex4 : (Z i).index = 4 := by
                            have hmul := (Z i).card_mul_index
                            rw [hzi_three, hHcard12] at hmul
                            omega
                          have hZjIndex4 : (Z j).index = 4 := by
                            have hmul := (Z j).card_mul_index
                            rw [hzj_three, hHcard12] at hmul
                            omega
                          let hZiP : IsPGroup 3 (Z i) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzi_three)
                          let hZjP : IsPGroup 3 (Z j) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzj_three)
                          let Qi : Sylow 3 H := hZiP.toSylow (by
                            rw [hZiIndex4]
                            norm_num)
                          let Qj : Sylow 3 H := hZjP.toSylow (by
                            rw [hZjIndex4]
                            norm_num)
                          obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Qi Qj
                          have hconj :
                              (Z i).map (MulAut.conj g).toMonoidHom = Z j := by
                            have hg' := congrArg
                              (fun Q : Sylow 3 H => (Q : Subgroup H)) hg
                            exact hg'
                          exact (hij (hdistinct i j g hconj)).elim
                        · left
                          have hindices_four :
                              (NZ i).index = 3 ∧ (NZ j).index = 4 ∧
                                (NZ k).index = 6 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_four, hzj_three] at hijq
                            rw [hzi_four, hzk_two] at hikq
                            rw [hzi_four] at hsumq
                            omega
                          have hHcard24 : Nat.card H = 24 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 24 := by rw [hzi_four, hindices_four.1]
                          exact Glauberman.Dickson.h824_symmetric_four_of_cyclic_family hFcard H Z hcyclic hnontrivial hcoprime hmaximal
                            hrepresentative hdistinct P hPcard s hnormalizerZ hs_all_two
                            i j k hij hik hjk
                            hzi_four hzj_three hzk_two hindices_four hHcard24
                        · right
                          have hindices_five :
                              (NZ i).index = 6 ∧ (NZ j).index = 10 ∧
                                (NZ k).index = 15 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_five, hzj_three] at hijq
                            rw [hzi_five, hzk_two] at hikq
                            rw [hzi_five] at hsumq
                            omega
                          have hHcard60 : Nat.card H = 60 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 60 := by rw [hzi_five, hindices_five.1]
                          exact Glauberman.Dickson.h824_alternating_five_of_cyclic_family hFcard H Z hcyclic hnontrivial hcoprime hmaximal
                            hrepresentative hdistinct P hPcard s hnormalizerZ hs_all_two
                            i j k hij hik hjk
                            hzi_five hzj_three hzk_two hindices_five hHcard60
                      exact Or.inr hexceptional
                  exact hclassification
                by_cases h01 : Nat.card (Z 0) ≤ Nat.card (Z 1)
                · by_cases h12 : Nat.card (Z 1) ≤ Nat.card (Z 2)
                  · rcases hordered 2 1 0 (by decide) (by decide) (by decide)
                        h12 h01 with hdih | hS4 | hA5
                    · exact Or.inr (Or.inl hdih)
                    · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                  · by_cases h02 : Nat.card (Z 0) ≤ Nat.card (Z 2)
                    · rcases hordered 1 2 0 (by decide) (by decide) (by decide)
                          (by omega) h02 with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                    · rcases hordered 1 0 2 (by decide) (by decide) (by decide)
                          h01 (by omega) with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                · by_cases h02 : Nat.card (Z 0) ≤ Nat.card (Z 2)
                  · rcases hordered 2 0 1 (by decide) (by decide) (by decide)
                        h02 (by omega) with hdih | hS4 | hA5
                    · exact Or.inr (Or.inl hdih)
                    · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                  · by_cases h12 : Nat.card (Z 1) ≤ Nat.card (Z 2)
                    · rcases hordered 0 2 1 (by decide) (by decide) (by decide)
                          (by omega) h12 with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                    · rcases hordered 0 1 2 (by decide) (by decide) (by decide)
                          (by omega) (by omega) with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
              exact h824_three_shape
          exact h824_two_or_three_shape
      exact h824_positive_shape
  have h824_A4_restriction
      (hA4 : Nonempty (H ≃* alternatingGroup (Fin 4))) :
      p ≠ 2 ∨ Even f := by
    left
    intro hp2
    subst p
    apply hp_not_dvd_card_H
    have hc := Nat.card_congr hA4.some.toEquiv
    have hA4card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc, hA4card]
    norm_num
  have h824_S4_restriction
      (hS4 : Nonempty (H ≃* Equiv.Perm (Fin 4))) :
      16 ∣ p ^ (2 * f) - 1 := by
    have hS4_p_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      apply hp_not_dvd_card_H
      have hHcard : Nat.card H = 24 := by
        calc
          Nat.card H = Nat.card (Equiv.Perm (Fin 4)) :=
            Nat.card_congr hS4.some.toEquiv
          _ = 24 := by norm_num [Fintype.card_perm, Nat.factorial]
      rw [hHcard]
      norm_num
    have hS4_cycle_four : ∃ x : H, orderOf x = 4 := by
      refine ⟨hS4.some.symm (Fin.cycleRange (3 : Fin 4)), ?_⟩
      rw [hS4.some.symm.orderOf_eq]
      rw [← Equiv.Perm.lcm_cycleType,
        Fin.cycleType_cycleRange (by decide : (3 : Fin 4) ≠ 0)]
      norm_num
    have hS4_cycle_four_family :
        ∃ a : Fin r, 4 ∣ Nat.card (Z a) := by
      obtain ⟨x, hxorder⟩ := hS4_cycle_four
      have hxne : x ≠ 1 := by
        intro hx
        rw [hx, orderOf_one] at hxorder
        norm_num at hxorder
      obtain ⟨A, hxA, _hAunique⟩ :=
        huppert_II_8_22_unique_family hFcard H Z
          hcyclic hnontrivial hcoprime hmaximal
          hrepresentative hdistinct x hxne
      rcases A with Qp | z
      · have hxdvd : orderOf x ∣ Nat.card Qp :=
          (Qp : Subgroup H).orderOf_dvd_natCard hxA
        have hQpcard : Nat.card Qp = 1 := by
          calc
            Nat.card Qp = Nat.card P :=
              Nat.card_congr (Sylow.equiv Qp P).toEquiv
            _ = 1 := by simpa using hPcard
        rw [hxorder, hQpcard] at hxdvd
        norm_num at hxdvd
      · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
          z.2.1.orderOf_dvd_natCard hxA
        obtain ⟨g, hg⟩ := z.2.2
        have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        refine ⟨z.1, ?_⟩
        simpa [hxorder, hzcard] using hxdvd
    have hS4_four_torus :
        4 ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∨
          4 ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
      obtain ⟨a, ha⟩ := hS4_cycle_four_family
      rcases hdivides a with hsplit | hnonsplit
      · exact Or.inl (dvd_trans ha hsplit)
      · exact Or.inr (dvd_trans ha hnonsplit)
    have hS4_q_odd : Odd (Nat.card F) := by
      rw [hFcard]
      exact ((Fact.out : p.Prime).odd_of_ne_two hS4_p_ne_two).pow
    have hS4_two_dvd_sub : 2 ∣ Nat.card F - 1 := by
      rcases hS4_q_odd with ⟨k, hk⟩
      use k
      omega
    have hS4_two_dvd_add : 2 ∣ Nat.card F + 1 := by
      exact hS4_q_odd.add_one.two_dvd
    have hS4_gcd_two : Nat.gcd (Nat.card F - 1) 2 = 2 := by
      exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd hS4_two_dvd_sub (dvd_refl 2))
    have hS4_eight_torus :
        8 ∣ Nat.card F - 1 ∨ 8 ∣ Nat.card F + 1 := by
      rw [hS4_gcd_two] at hS4_four_torus
      rcases hS4_four_torus with hminus | hplus
      · left
        obtain ⟨a, ha⟩ := hminus
        use a
        calc
          Nat.card F - 1 = (Nat.card F - 1) / 2 * 2 :=
            (Nat.div_mul_cancel hS4_two_dvd_sub).symm
          _ = (4 * a) * 2 := by rw [ha]
          _ = 8 * a := by ring
      · right
        obtain ⟨a, ha⟩ := hplus
        use a
        calc
          Nat.card F + 1 = (Nat.card F + 1) / 2 * 2 :=
            (Nat.div_mul_cancel hS4_two_dvd_add).symm
          _ = (4 * a) * 2 := by rw [ha]
          _ = 8 * a := by ring
    have hS4_sixteen_q_sq_sub_one :
        16 ∣ Nat.card F ^ 2 - 1 := by
      have hfactor :
          Nat.card F ^ 2 - 1 =
            (Nat.card F - 1) * (Nat.card F + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
      rw [hfactor]
      rcases hS4_eight_torus with hminus | hplus
      · have hmul := Nat.mul_dvd_mul hminus hS4_two_dvd_add
        norm_num at hmul
        exact hmul
      · have hmul := Nat.mul_dvd_mul hS4_two_dvd_sub hplus
        norm_num at hmul
        exact hmul
    rw [hFcard, ← pow_mul] at hS4_sixteen_q_sq_sub_one
    simpa [mul_comm] using hS4_sixteen_q_sq_sub_one
  have h824_A5_restriction
      (hA5 : Nonempty (H ≃* alternatingGroup (Fin 5))) :
      p = 5 ∨ 5 ∣ p ^ (2 * f) - 1 := by
    have hA5_cycle_five : ∃ x : H, orderOf x = 5 := by
      let y : alternatingGroup (Fin 5) :=
        ⟨Fin.cycleRange (4 : Fin 5), by
          rw [Equiv.Perm.mem_alternatingGroup, Fin.sign_cycleRange]
          decide⟩
      refine ⟨hA5.some.symm y, ?_⟩
      rw [hA5.some.symm.orderOf_eq, ← Subgroup.orderOf_coe y]
      change orderOf (Fin.cycleRange (4 : Fin 5)) = 5
      rw [← Equiv.Perm.lcm_cycleType,
        Fin.cycleType_cycleRange (by decide : (4 : Fin 5) ≠ 0)]
      norm_num
    have hA5_cycle_five_family :
        ∃ a : Fin r, 5 ∣ Nat.card (Z a) := by
      obtain ⟨x, hxorder⟩ := hA5_cycle_five
      have hxne : x ≠ 1 := by
        intro hx
        rw [hx, orderOf_one] at hxorder
        norm_num at hxorder
      obtain ⟨A, hxA, _hAunique⟩ :=
        huppert_II_8_22_unique_family hFcard H Z
          hcyclic hnontrivial hcoprime hmaximal
          hrepresentative hdistinct x hxne
      rcases A with Qp | z
      · have hxdvd : orderOf x ∣ Nat.card Qp :=
          (Qp : Subgroup H).orderOf_dvd_natCard hxA
        have hQpcard : Nat.card Qp = 1 := by
          calc
            Nat.card Qp = Nat.card P :=
              Nat.card_congr (Sylow.equiv Qp P).toEquiv
            _ = 1 := by simpa using hPcard
        rw [hxorder, hQpcard] at hxdvd
        norm_num at hxdvd
      · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
          z.2.1.orderOf_dvd_natCard hxA
        obtain ⟨g, hg⟩ := z.2.2
        have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        refine ⟨z.1, ?_⟩
        simpa [hxorder, hzcard] using hxdvd
    have hA5_five_torus_quotient :
        5 ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∨
          5 ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
      obtain ⟨a, ha⟩ := hA5_cycle_five_family
      rcases hdivides a with hsplit | hnonsplit
      · exact Or.inl (dvd_trans ha hsplit)
      · exact Or.inr (dvd_trans ha hnonsplit)
    have hA5_five_torus_factor :
        5 ∣ Nat.card F - 1 ∨ 5 ∣ Nat.card F + 1 := by
      have hq : 1 ≤ Nat.card F :=
        (Finite.one_lt_card (α := F)).le
      have hdvd_sub : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F - 1 :=
        Nat.gcd_dvd_left _ _
      have hdvd_two : Nat.gcd (Nat.card F - 1) 2 ∣ 2 :=
        Nat.gcd_dvd_right _ _
      have hdvd_add : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
        have h := Nat.dvd_add hdvd_sub hdvd_two
        convert h using 1
        all_goals omega
      rcases hA5_five_torus_quotient with hminus | hplus
      · exact Or.inl
          (dvd_trans hminus (Nat.div_dvd_of_dvd hdvd_sub))
      · exact Or.inr
          (dvd_trans hplus (Nat.div_dvd_of_dvd hdvd_add))
    have hA5_five_q_sq_sub_one :
        5 ∣ Nat.card F ^ 2 - 1 := by
      have hfactor :
          Nat.card F ^ 2 - 1 =
            (Nat.card F - 1) * (Nat.card F + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
      rw [hfactor]
      rcases hA5_five_torus_factor with hminus | hplus
      · exact dvd_mul_of_dvd_left hminus _
      · exact dvd_mul_of_dvd_right hplus _
    right
    rw [hFcard, ← pow_mul] at hA5_five_q_sq_sub_one
    simpa [mul_comm] using hA5_five_q_sq_sub_one
  rcases h824_shape with hcyc | hdih | hA4 | hS4 | hA5
  · exact Or.inl hcyc
  · exact Or.inr (Or.inl hdih)
  · exact Or.inr (Or.inr (Or.inl ⟨h824_A4_restriction hA4, hA4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h824_S4_restriction hS4, hS4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h824_A5_restriction hA5, hA5⟩)))

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
-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
end Dickson
end Glauberman


end Source18

end CFSGPackNoP
