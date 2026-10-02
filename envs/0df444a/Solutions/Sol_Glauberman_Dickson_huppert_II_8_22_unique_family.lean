-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_22_unique_family
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T12:18:40.946476+00:00
-- url     : https://prove2.me/submissions/a1afdc4b-26ab-4a4c-a898-a9b9e0c1f6d2

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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_5_a_psl2_partition

set_option autoImplicit false
namespace Glauberman.Dickson
end Glauberman.Dickson
namespace CFSGPackUniqueFamily
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

section Source11
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCoprimeOrders.lean
/-!
# Coprime order lemmas for Dickson families
-/

namespace Glauberman
namespace Dickson

universe u

theorem hmem_eq_one_of_coprime_card
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card B))
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) :
    x = 1 := by
  have horder_A : orderOf x ∣ Nat.card A := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxA⟩ : A))
  have horder_B : orderOf x ∣ Nat.card B := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxB⟩ : B))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcoprime horder_A horder_B)

theorem hq_coprime_split_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q - 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_sub_right hq).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (q - 1) 2)

theorem hq_coprime_nonsplit_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q + 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_add_right).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  apply Nat.div_dvd_of_dvd
  convert Nat.dvd_add (Nat.gcd_dvd_left (q - 1) 2)
    (Nat.gcd_dvd_right (q - 1) 2) using 1
  all_goals omega

-- Omitted: outside declaration proof/source closure.

end Dickson
end Glauberman



end Source11

section Source16
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCounting.lean
/-!
# Counting the three Dickson families

This module isolates the unique-family orbit counts and the Huppert II.8.22
counting equation.
-/

namespace Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise

universe u v

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

/-- The subgroup form of the unique partition used in Huppert II.8.22. -/
theorem _root_.solution
    {F : Type u} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (_hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) :
    ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H) := by
  classical
  let : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
  let P0 : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P0
  have hmap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) (g : PSL2MatrixGroup F) :
      IsCyclic (A.map (MulAut.conj g).toMonoidHom) := by
    let : IsCyclic A := hA
    let e := (MulAut.conj g).subgroupMap A
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hcyclic_le_family
      {x : PSL2MatrixGroup F} (hx : x ≠ 1)
      {T V : Subgroup (PSL2MatrixGroup F)}
      (hxT : x ∈ T)
      (hTfamily :
        (∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = S.map (MulAut.conj g).toMonoidHom))
      (hxV : x ∈ V) (hVcyclic : IsCyclic V) : V ≤ T := by
    let : IsCyclic V := hVcyclic
    rcases IsCyclic.exists_zpow_surjective (G := V) with ⟨v, hv⟩
    have hv_ne : (v : PSL2MatrixGroup F) ≠ 1 := by
      intro hv_one
      obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
      have hnval : (v ^ n : V) = ⟨x, hxV⟩ := hn
      have hnval' := congrArg Subtype.val hnval
      change ((v : PSL2MatrixGroup F) ^ n) = x at hnval'
      simp [hv_one] at hnval'
      exact hx hnval'.symm
    obtain ⟨Tv, hvTv, _hTv_unique⟩ :=
      hpartition (v : PSL2MatrixGroup F) hv_ne
    have hxTv : x ∈ Tv := by
      obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
      have hnval : (v : PSL2MatrixGroup F) ^ n = x :=
        congrArg Subtype.val hn
      have hvpow : (v : PSL2MatrixGroup F) ^ n ∈ Tv :=
        Tv.zpow_mem hvTv.1 n
      rwa [hnval] at hvpow
    have hTvT : Tv = T :=
      (hpartition x hx).unique ⟨hxTv, hvTv.2⟩ ⟨hxT, hTfamily⟩
    intro y hyV
    obtain ⟨n, hn⟩ := hv ⟨y, hyV⟩
    have hnval : (v : PSL2MatrixGroup F) ^ n = y :=
      congrArg Subtype.val hn
    have hypow : (v : PSL2MatrixGroup F) ^ n ∈ Tv :=
      Tv.zpow_mem hvTv.1 n
    rw [hTvT, hnval] at hypow
    exact hypow
  have hmap_cyclic_H (A : Subgroup H) (hA : IsCyclic A) (g : H) :
      IsCyclic (g • A : Subgroup H) := by
    change IsCyclic (A.map (MulAut.conj g).toMonoidHom)
    let : IsCyclic A := hA
    let e := (MulAut.conj g).subgroupMap A
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hconj_maximal (i : Fin r) (g : H) :
      ∀ V : Subgroup H, IsCyclic V →
        (g • Z i : Subgroup H) ≤ V → V = (g • Z i : Subgroup H) := by
    intro V hV hle
    have hback_cyclic : IsCyclic (g⁻¹ • V : Subgroup H) :=
      hmap_cyclic_H V hV g⁻¹
    have hback_le : Z i ≤ (g⁻¹ • V : Subgroup H) := by
      have hmap := Subgroup.map_mono
        (f := (MulAut.conj g⁻¹).toMonoidHom) hle
      change (g⁻¹ • (g • Z i) : Subgroup H) ≤
        (g⁻¹ • V : Subgroup H) at hmap
      simpa using hmap
    have heq : (g⁻¹ • V : Subgroup H) = Z i :=
      hmaximal i (g⁻¹ • V : Subgroup H) hback_cyclic hback_le
    have hfront := congrArg (fun W : Subgroup H => g • W) heq
    simpa using hfront
  have hindices_eq (i j : Fin r) (g h : H)
      (heq :
        (Z i).map (MulAut.conj g).toMonoidHom =
          (Z j).map (MulAut.conj h).toMonoidHom) : i = j := by
    have hcancel :
        ((Z i).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj h).symm.toMonoidHom = Z j :=
      (Subgroup.map_symm_eq_iff_map_eq
        (Z j) (e := MulAut.conj h)).mpr heq.symm
    have hsingle :
        (Z i).map (MulAut.conj (h⁻¹ * g)).toMonoidHom = Z j := by
      calc
        (Z i).map (MulAut.conj (h⁻¹ * g)).toMonoidHom =
            ((Z i).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj h).symm.toMonoidHom := by
                rw [Subgroup.map_map]
                congr 1
                ext y
                simp [MulAut.conj_apply, mul_assoc]
        _ = Z j := hcancel
    exact hdistinct i j (h⁻¹ * g) hsingle
  have hsylow_coprime_conj (Q : Sylow p H) (i : Fin r) (g : H) :
      Nat.Coprime (Nat.card Q) (Nat.card (g • Z i : Subgroup H)) := by
    rcases Q.isPGroup'.exists_card_eq with ⟨n, hQcard⟩
    rw [hQcard]
    change Nat.Coprime (p ^ n)
      (Nat.card ((Z i).map (MulAut.conj g).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact (hcoprime i).pow_left n
  have hmap_subtype_cyclic (A : Subgroup H) (hA : IsCyclic A) :
      IsCyclic (A.map H.subtype) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        A H.subtype H.subtype_injective)).mp hA
  have hcomap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) : IsCyclic (A.comap H.subtype) := by
    let : IsCyclic A := hA
    have hmap_cyclic : IsCyclic ((A.comap H.subtype).map H.subtype) :=
      Subgroup.isCyclic_of_le (Subgroup.map_comap_le H.subtype A)
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        (A.comap H.subtype) H.subtype H.subtype_injective)).mpr hmap_cyclic
  have hcomap_card_dvd (A : Subgroup (PSL2MatrixGroup F)) :
      Nat.card (A.comap H.subtype) ∣ Nat.card A :=
    Subgroup.card_comap_dvd_of_injective
      A H.subtype H.subtype_injective
  intro x hx
  have hxG : (x : PSL2MatrixGroup F) ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    exact h
  obtain ⟨T, hxT, hTfamily⟩ :=
    (hpartition (x : PSL2MatrixGroup F) hxG).exists
  have hambient_sylow_family (R : Sylow p (PSL2MatrixGroup F)) :
      ∃ g, (R : Subgroup (PSL2MatrixGroup F)) =
        (P0 : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom := by
    obtain ⟨g, hg⟩ :=
      MulAction.exists_smul_eq (PSL2MatrixGroup F) P0 R
    refine ⟨g, ?_⟩
    have hg' := congrArg
      (fun Q : Sylow p (PSL2MatrixGroup F) =>
        (Q : Subgroup (PSL2MatrixGroup F))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hg'
    exact hg'.symm
  have hambient_eq_T (R : Sylow p (PSL2MatrixGroup F))
      (hxR : (x : PSL2MatrixGroup F) ∈
        (R : Subgroup (PSL2MatrixGroup F))) :
      (R : Subgroup (PSL2MatrixGroup F)) = T := by
    exact (hpartition (x : PSL2MatrixGroup F) hxG).unique
      ⟨hxR, Or.inl (hambient_sylow_family R)⟩
      ⟨hxT, hTfamily⟩
  have hsylow_eq_of_mem (Q₁ Q₂ : Sylow p H)
      (hx₁ : x ∈ (Q₁ : Subgroup H))
      (hx₂ : x ∈ (Q₂ : Subgroup H)) : Q₁ = Q₂ := by
    obtain ⟨R₁, hR₁⟩ := Q₁.exists_comap_subtype_eq
    obtain ⟨R₂, hR₂⟩ := Q₂.exists_comap_subtype_eq
    have hxR₁ : (x : PSL2MatrixGroup F) ∈
        (R₁ : Subgroup (PSL2MatrixGroup F)) := by
      change x ∈ (R₁ : Subgroup _).comap H.subtype
      rw [hR₁]
      exact hx₁
    have hxR₂ : (x : PSL2MatrixGroup F) ∈
        (R₂ : Subgroup (PSL2MatrixGroup F)) := by
      change x ∈ (R₂ : Subgroup _).comap H.subtype
      rw [hR₂]
      exact hx₂
    apply Sylow.ext
    calc
      (Q₁ : Subgroup H) = (R₁ : Subgroup _).comap H.subtype := hR₁.symm
      _ = T.comap H.subtype := congrArg
        (fun W : Subgroup (PSL2MatrixGroup F) => W.comap H.subtype)
        (hambient_eq_T R₁ hxR₁)
      _ = (R₂ : Subgroup _).comap H.subtype := congrArg
        (fun W : Subgroup (PSL2MatrixGroup F) => W.comap H.subtype)
        (hambient_eq_T R₂ hxR₂).symm
      _ = (Q₂ : Subgroup H) := hR₂
  rcases hTfamily with ⟨g, hTg⟩ | hTtorus
  · have hTp : IsPGroup p T := by
      rw [hTg]
      exact P0.isPGroup'.map (MulAut.conj g).toMonoidHom
    let I : Subgroup H := T.comap H.subtype
    have hIp : IsPGroup p I := hTp.comap_subtype
    obtain ⟨Q, hIQ⟩ := hIp.exists_le_sylow
    have hxI : x ∈ I := by
      change (x : PSL2MatrixGroup F) ∈ T
      exact hxT
    refine ⟨Sum.inl Q, hIQ hxI, ?_⟩
    intro A hA
    rcases A with Q' | z
    · exact congrArg Sum.inl (hsylow_eq_of_mem Q' Q hA (hIQ hxI))
    · rcases z with ⟨i, W, g', hW⟩
      exfalso
      have hcop : Nat.Coprime (Nat.card Q) (Nat.card W) := by
        rw [hW]
        exact hsylow_coprime_conj Q i g'
      exact hx (hmem_eq_one_of_coprime_card
        (Q : Subgroup H) W hcop (hIQ hxI) hA)
  · have hTfamily' :
        ((∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) :=
      Or.inr hTtorus
    have hTcyclic : IsCyclic T := by
      rcases hTtorus with ⟨g, hg⟩ | ⟨g, hg⟩
      · rw [hg]
        exact hmap_cyclic U hUcyclic g
      · rw [hg]
        exact hmap_cyclic S hScyclic g
    have hpF : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p
        (huppert_II_8_27_field_exponent_ne_zero hFcard)
    have hFTcoprime : Nat.Coprime (Nat.card F) (Nat.card T) := by
      rcases hTtorus with ⟨g, hg⟩ | ⟨g, hg⟩
      · rw [hg, Subgroup.card_map_of_injective
            (K := U) (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).injective, hUcard]
        exact hq_coprime_split_order (Nat.card F) Nat.card_pos
      · rw [hg, Subgroup.card_map_of_injective
            (K := S) (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).injective, hScard]
        exact hq_coprime_nonsplit_order (Nat.card F) Nat.card_pos
    have hTcoprime : Nat.Coprime p (Nat.card T) :=
      Nat.Coprime.of_dvd_left hpF hFTcoprime
    let W : Subgroup H := T.comap H.subtype
    have hxW : x ∈ W := by
      change (x : PSL2MatrixGroup F) ∈ T
      exact hxT
    have hWcyclic : IsCyclic W := hcomap_cyclic T hTcyclic
    have hWcard : 1 < Nat.card W := by
      apply (Subgroup.one_lt_card_iff_ne_bot W).2
      intro hW
      exact hx (Subgroup.mem_bot.mp (hW ▸ hxW))
    have hWcoprime : Nat.Coprime p (Nat.card W) :=
      Nat.Coprime.of_dvd_right (hcomap_card_dvd T) hTcoprime
    have hWmax :
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W := by
      intro V hV hWV
      have hVmap_cyclic : IsCyclic (V.map H.subtype) :=
        hmap_subtype_cyclic V hV
      have hxVmap :
          (x : PSL2MatrixGroup F) ∈ V.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (hWV hxW)
      have hVmap_le_T : V.map H.subtype ≤ T :=
        hcyclic_le_family hxG hxT hTfamily' hxVmap hVmap_cyclic
      have hVleW : V ≤ W :=
        Subgroup.map_le_iff_le_comap.mp hVmap_le_T
      exact le_antisymm hVleW hWV
    obtain ⟨i, g, hWrep⟩ :=
      hrepresentative W hWcyclic hWcard hWcoprime hWmax
    refine ⟨Sum.inr ⟨i, ⟨W, g, hWrep⟩⟩, hxW, ?_⟩
    intro A hA
    rcases A with Q | z
    · exfalso
      have hcop : Nat.Coprime (Nat.card Q) (Nat.card W) := by
        rw [hWrep]
        exact hsylow_coprime_conj Q i g
      exact hx (hmem_eq_one_of_coprime_card
        (Q : Subgroup H) W hcop hA hxW)
    · rcases z with ⟨j, W', h, hW'rep⟩
      have hW'cyclic : IsCyclic W' := by
        rw [hW'rep]
        exact hmap_cyclic_H (Z j) (hcyclic j) h
      have hxW'map :
          (x : PSL2MatrixGroup F) ∈ W'.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype hA
      have hW'map_le_T : W'.map H.subtype ≤ T :=
        hcyclic_le_family hxG hxT hTfamily' hxW'map
          (hmap_subtype_cyclic W' hW'cyclic)
      have hW'leW : W' ≤ W :=
        Subgroup.map_le_iff_le_comap.mp hW'map_le_T
      have hW'max :
          ∀ V : Subgroup H, IsCyclic V → W' ≤ V → V = W' := by
        rw [hW'rep]
        exact hconj_maximal j h
      have hWW' : W = W' := hW'max W hWcyclic hW'leW
      have hmaps :
          (Z i).map (MulAut.conj g).toMonoidHom =
            (Z j).map (MulAut.conj h).toMonoidHom := by
        rw [← hWrep, ← hW'rep, hWW']
      have hij : i = j := hindices_eq i j g h hmaps
      subst j
      subst W'
      rfl

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
end Dickson
end Glauberman


end Source16

end CFSGPackUniqueFamily
