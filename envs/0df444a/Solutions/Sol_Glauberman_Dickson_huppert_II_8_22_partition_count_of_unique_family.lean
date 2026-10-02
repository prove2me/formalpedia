-- Prove2me | solution 1 for Glauberman.Dickson.huppert_II_8_22_partition_count_of_unique_family
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T12:24:48.871115+00:00
-- url     : https://prove2.me/submissions/3fb47553-c8f3-4ceb-a538-90eaa08b6092

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
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Transfer

set_option autoImplicit false
namespace CFSGPackPartitionCount

section Source16
-- Original: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCounting.lean
/-!
# Counting the three Dickson families

This module isolates the unique-family orbit counts and the Huppert II.8.22
counting equation.
-/

namespace Glauberman
namespace Dickson

open scoped Pointwise

universe u v

private theorem huppert_II_8_22_punctured_subgroup_card
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) :
    Nat.card {x : A // (x : H) ≠ 1} = Nat.card A - 1 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype {x : A // (x : H) ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

private theorem huppert_II_8_22_conjugacy_orbit_card
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) :
    Nat.card {W : Subgroup H // ∃ g : H,
      W = A.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (A : Set H)).index := by
  classical
  let : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
  have horbit :
      MulAction.orbit H A =
        {W : Subgroup H | ∃ g : H,
          W = A.map (MulAut.conj g).toMonoidHom} := by
    ext W
    constructor
    · intro hW
      rcases hW with ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  have hstab : MulAction.stabilizer H A =
      Subgroup.normalizer (A : Set H) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set H)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := H) (H := Subgroup.normalizer A),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact
      forall_congr' fun h =>
        iff_congr Iff.rfl
          ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
            fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
              MulAut.apply_inv_self H (MulAut.conj g) h⟩⟩
  change Nat.card ↥{W : Subgroup H | ∃ g : H,
    W = A.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer H A, hstab]

theorem _root_.solution
    {H : Type*} [Group H] [Finite H] {p m r : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H)
    (hunique : ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H)) :
    Nat.card H =
      1 + (p ^ m - 1) *
          (Subgroup.normalizer (P : Set H)).index +
        ∑ i, (Nat.card (Z i) - 1) *
          (Subgroup.normalizer (Z i : Set H)).index := by
  classical
  let Family := (Sylow p H) ⊕
    (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
      W = (Z i).map (MulAut.conj g).toMonoidHom})
  let carrier : Family → Subgroup H := fun A =>
    match A with
    | Sum.inl Q => (Q : Subgroup H)
    | Sum.inr z => (z.2.1 : Subgroup H)
  have hunique' : ∀ x : H, x ≠ 1 → ∃! A : Family, x ∈ carrier A := by
    intro x hx
    exact hunique x hx
  let Piece := Σ A : Family, {x : carrier A // (x : H) ≠ 1}
  let decode : Unit ⊕ Piece → H := fun z =>
    match z with
    | Sum.inl _ => 1
    | Sum.inr y => (y.2.1 : H)
  have hdecode_bij : Function.Bijective decode := by
    constructor
    · intro a b hab
      rcases a with _ | a
      · rcases b with _ | b
        · rfl
        · exfalso
          exact b.2.2 (by simpa [decode] using hab.symm)
      · rcases b with _ | b
        · exfalso
          exact a.2.2 (by simpa [decode] using hab)
        · rcases a with ⟨A, x⟩
          rcases b with ⟨B, y⟩
          have hxy : (x.1 : H) = (y.1 : H) := by
            simpa [decode] using hab
          have hAB : A = B := by
            apply (hunique' (x.1 : H) x.2).unique
            · exact x.1.2
            · rw [hxy]
              exact y.1.2
          subst B
          have hxy' : x = y := by
            apply Subtype.ext
            apply Subtype.ext
            exact hxy
          subst y
          rfl
    · intro x
      by_cases hx : x = 1
      · exact ⟨Sum.inl (), by simp [decode, hx]⟩
      · obtain ⟨A, hxA⟩ := (hunique' x hx).exists
        refine ⟨Sum.inr ⟨A, ⟨⟨x, hxA⟩, hx⟩⟩, ?_⟩
        rfl
  let e : Unit ⊕ Piece ≃ H := Equiv.ofBijective decode hdecode_bij
  have hcard_decomp : Nat.card H = 1 + Nat.card Piece := by
    calc
      Nat.card H = Nat.card (Unit ⊕ Piece) := (Nat.card_congr e).symm
      _ = Nat.card Unit + Nat.card Piece := Nat.card_sum
      _ = 1 + Nat.card Piece := by rw [Nat.card_unique]
  have hSylow_card (Q : Sylow p H) : Nat.card Q = p ^ m := by
    calc
      Nat.card Q = Nat.card P := Nat.card_congr (Sylow.equiv Q P).toEquiv
      _ = p ^ m := hPcard
  have hConj_card (i : Fin r) :
      Nat.card {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom} =
        (Subgroup.normalizer (Z i : Set H)).index :=
    huppert_II_8_22_conjugacy_orbit_card (Z i)
  have hConj_subgroup_card (i : Fin r)
      (W : {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}) :
      Nat.card W.1 = Nat.card (Z i) := by
    rcases W.2 with ⟨g, hg⟩
    rw [hg]
    exact Nat.card_congr ((MulAut.conj g).subgroupMap (Z i)).toEquiv.symm
  let PPiece := Σ Q : Sylow p H,
    {x : (Q : Subgroup H) // (x : H) ≠ 1}
  let ZIndex := Σ i : Fin r, {W : Subgroup H // ∃ g : H,
    W = (Z i).map (MulAut.conj g).toMonoidHom}
  let ZPiece := Σ z : ZIndex,
    {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}
  have hPpiece_card :
      Nat.card PPiece = Nat.card (Sylow p H) * (p ^ m - 1) := by
    let : Fintype (Sylow p H) := Fintype.ofFinite (Sylow p H)
    let (Q : Sylow p H) :
        Fintype {x : (Q : Subgroup H) // (x : H) ≠ 1} :=
      Fintype.ofFinite _
    change Nat.card (Σ Q : Sylow p H,
      {x : (Q : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Nat.card_sigma]
    simp_rw [huppert_II_8_22_punctured_subgroup_card, hSylow_card]
    simp
  have hZpiece_card :
      Nat.card ZPiece =
        ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom} *
          (Nat.card (Z i) - 1) := by
    let (i : Fin r) :
        Fintype {W : Subgroup H // ∃ g : H,
          W = (Z i).map (MulAut.conj g).toMonoidHom} :=
      Fintype.ofFinite _
    let : Fintype ZIndex := inferInstance
    let (z : ZIndex) :
        Fintype {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1} :=
      Fintype.ofFinite _
    change Nat.card (Σ z :
      (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}),
      {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Nat.card_sigma]
    change (∑ z :
      (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}),
      Nat.card {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Fintype.sum_sigma]
    simp_rw [huppert_II_8_22_punctured_subgroup_card,
      hConj_subgroup_card]
    simp
    apply Finset.sum_congr rfl
    intro i hi
    let : Fintype {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g)} :=
      Fintype.ofFinite _
    apply congrArg (fun n => n * (Nat.card (Z i) - 1))
    exact Nat.card_eq_fintype_card.symm
  have hPiece_card :
      Nat.card Piece =
        Nat.card (Sylow p H) * (p ^ m - 1) +
          ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
              W = (Z i).map (MulAut.conj g).toMonoidHom} *
            (Nat.card (Z i) - 1) := by
    have hsplit : Nat.card Piece = Nat.card PPiece + Nat.card ZPiece := by
      let esplit := Equiv.sumSigmaDistrib
        (fun A : Family => {x : carrier A // (x : H) ≠ 1})
      calc
        Nat.card Piece = Nat.card (PPiece ⊕ ZPiece) := by
          simpa [Piece, PPiece, ZPiece, ZIndex, Family, carrier] using
            Nat.card_congr esplit
        _ = Nat.card PPiece + Nat.card ZPiece := Nat.card_sum
    rw [hsplit, hPpiece_card, hZpiece_card]
  calc
    Nat.card H = 1 + Nat.card Piece := hcard_decomp
    _ = 1 +
        (Nat.card (Sylow p H) * (p ^ m - 1) +
          ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
              W = (Z i).map (MulAut.conj g).toMonoidHom} *
            (Nat.card (Z i) - 1)) := by rw [hPiece_card]
    _ = 1 + (p ^ m - 1) *
          (Subgroup.normalizer (P : Set H)).index +
        ∑ i, (Nat.card (Z i) - 1) *
          (Subgroup.normalizer (Z i : Set H)).index := by
      rw [P.card_eq_index_normalizer]
      simp_rw [hConj_card]
      ac_rfl

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.

-- Omitted: outside declaration proof/source closure.
end Dickson
end Glauberman


end Source16

end CFSGPackPartitionCount
