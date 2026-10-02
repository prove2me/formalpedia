-- Prove2me | solution 1 for Glauberman.Dickson.h824_alternating_five_of_cyclic_family
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T12:58:36.464823+00:00
-- url     : https://prove2.me/submissions/33d1dcff-d6f6-4ed5-a606-f21322484fd9

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
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_unique_family
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_partition_count_of_unique_family

set_option autoImplicit false
universe u v
open scoped Pointwise
open Glauberman.Dickson
set_option maxHeartbeats 1600000 in
theorem solution
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (Z : Fin 3 → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j)
    (P : Sylow p H) (hPcard : Nat.card P = p ^ 0)
    (s : Fin 3 → ℕ)
    (hnormalizerZ : ∀ a, Nat.card (Subgroup.normalizer (Z a : Set H)) = Nat.card (Z a) * s a)
    (hs_all_two : ∀ a, s a = 2)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi_five : Nat.card (Z i) = 5) (hzj_three : Nat.card (Z j) = 3)
    (hzk_two : Nat.card (Z k) = 2)
    (hindices_five :
      (Subgroup.normalizer (Z i : Set H)).index = 6 ∧
      (Subgroup.normalizer (Z j : Set H)).index = 10 ∧
      (Subgroup.normalizer (Z k : Set H)).index = 15)
    (hHcard60 : Nat.card H = 60) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  classical
  let NZ : Fin 3 → Subgroup H := fun a => Subgroup.normalizer (Z a : Set H)
  have hNZkcard4 : Nat.card (NZ k) = 4 := by
    dsimp only [NZ]
    rw [hnormalizerZ k, hzk_two, hs_all_two k]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hNZkP : IsPGroup 2 (NZ k) :=
    IsPGroup.of_card (n := 2) (by
      simpa using hNZkcard4)
  let P2 : Sylow 2 H := hNZkP.toSylow (by
    rw [hindices_five.2.2]
    norm_num)
  have hSylow2_data :
      Nat.card (Sylow 2 H) = 5 ∧
        ∀ x : H, orderOf x = 2 →
          ∃! R : Sylow 2 H,
            x ∈ (R : Subgroup H) := by
    have hSylow2card4 (R : Sylow 2 H) :
        Nat.card R = 4 := by
      calc
        Nat.card R = Nat.card P2 :=
          Nat.card_congr (Sylow.equiv R P2).toEquiv
        _ = 4 := by
          change Nat.card (NZ k) = 4
          exact hNZkcard4
    have hno_order_four :
        ∀ x : H, orderOf x ≠ 4 := by
      intro x hxorder
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
        have hzcard :
            Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        have huniv :
            ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
          apply
            (Finset.card_eq_iff_eq_univ
              ({i, j, k} : Finset (Fin 3))).mp
          simp [hij, hik, hjk]
        have hz_cases : z.1 = i ∨ z.1 = j ∨ z.1 = k := by
          have hzmem :
              z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
            rw [huniv]
            simp
          simpa [Finset.mem_insert, Finset.mem_singleton]
            using hzmem
        rw [hxorder, hzcard] at hxdvd
        rcases hz_cases with hzi | hzj | hzk
        · rw [hzi, hzi_five] at hxdvd
          norm_num at hxdvd
        · rw [hzj, hzj_three] at hxdvd
          norm_num at hxdvd
        · rw [hzk, hzk_two] at hxdvd
          norm_num at hxdvd
    have hsylow2_order_two (R : Sylow 2 H)
        {x : H} (hxR : x ∈ (R : Subgroup H))
        (hxne : x ≠ 1) : orderOf x = 2 := by
      have hdvd : orderOf x ∣ 4 := by
        simpa [hSylow2card4 R] using
          (R : Subgroup H).orderOf_dvd_natCard hxR
      have hpos : 0 < orderOf x := orderOf_pos x
      have hne_one : orderOf x ≠ 1 :=
        fun h => hxne (orderOf_eq_one_iff.mp h)
      have hne_four : orderOf x ≠ 4 := hno_order_four x
      have hle : orderOf x ≤ 4 :=
        Nat.le_of_dvd (by norm_num) hdvd
      interval_cases orderOf x <;> norm_num at *
    have hinvolution_unique_sylow (x : H)
        (hxorder : orderOf x = 2) :
        ∃! R : Sylow 2 H, x ∈ (R : Subgroup H) := by
      have hxne : x ≠ 1 := by
        intro hx
        rw [hx, orderOf_one] at hxorder
        norm_num at hxorder
      let X : Subgroup H := Subgroup.zpowers x
      have hXcard : Nat.card X = 2 := by
        simpa [X] using
          (Nat.card_zpowers x).trans hxorder
      have hXisP : IsPGroup 2 X :=
        IsPGroup.of_card (n := 1) (by simpa using hXcard)
      obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
      have hxR : x ∈ (R : Subgroup H) :=
        hXR (by exact Subgroup.mem_zpowers x)
      have hnormalizerXcard4 :
          Nat.card (Subgroup.normalizer (X : Set H)) = 4 := by
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
          have hzcard :
              Nat.card z.2.1 = Nat.card (Z z.1) := by
            rw [hg, Subgroup.card_map_of_injective
              (MulAut.conj g).injective]
          have huniv :
              ({i, j, k} : Finset (Fin 3)) =
                Finset.univ := by
            apply
              (Finset.card_eq_iff_eq_univ
                ({i, j, k} : Finset (Fin 3))).mp
            simp [hij, hik, hjk]
          have hz_cases :
              z.1 = i ∨ z.1 = j ∨ z.1 = k := by
            have hzmem :
                z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
              rw [huniv]
              simp
            simpa [Finset.mem_insert,
              Finset.mem_singleton] using hzmem
          rcases hz_cases with hza | hza | hza
          · rw [hxorder, hzcard, hza, hzi_five] at hxdvd
            norm_num at hxdvd
          · rw [hxorder, hzcard, hza, hzj_three] at hxdvd
            norm_num at hxdvd
          · have hgk :
                z.2.1 = (Z k).map
                  (MulAut.conj g).toMonoidHom := by
              simpa [hza] using hg
            have hWcard : Nat.card z.2.1 = 2 := by
              rw [hzcard, hza, hzk_two]
            have hXeqW : X = z.2.1 :=
              Subgroup.eq_of_le_of_card_ge (by
                exact Subgroup.zpowers_le.2 hxA) (by
                  rw [hXcard, hWcard])
            rw [hXeqW, hgk]
            rw [← Subgroup.map_normalizer_eq_of_bijective
              (Z k) (MulAut.conj g).bijective,
              Subgroup.card_map_of_injective
                (MulAut.conj g).injective]
            simpa [NZ] using hNZkcard4
      have hSylow_eq_normalizer (S : Sylow 2 H)
          (hxS : x ∈ (S : Subgroup H)) :
          (S : Subgroup H) =
            Subgroup.normalizer (X : Set H) := by
        have hScard : Nat.card S = 2 ^ 2 := by
          norm_num [hSylow2card4 S]
        let : CommGroup S :=
          IsPGroup.commGroupOfCardEqPrimeSq hScard
        have hXleS : X ≤ (S : Subgroup H) := by
          exact Subgroup.zpowers_le.2 hxS
        have hnormal :
            (X.subgroupOf (S : Subgroup H)).Normal :=
          inferInstance
        have hSle :
            (S : Subgroup H) ≤
              Subgroup.normalizer (X : Set H) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer
            hXleS).mp hnormal
        exact Subgroup.eq_of_le_of_card_ge hSle (by
          rw [hSylow2card4 S, hnormalizerXcard4])
      refine ⟨R, hxR, ?_⟩
      intro S hxS
      apply Sylow.ext
      exact (hSylow_eq_normalizer S hxS).trans
        (hSylow_eq_normalizer R hxR).symm
    let Zodd : Fin 2 → Subgroup H := ![Z i, Z j]
    have hunique2 : ∀ x : H, x ≠ 1 →
        ∃! A : (Sylow 2 H) ⊕
            (Σ a : Fin 2,
              {W : Subgroup H // ∃ g : H,
                W = (Zodd a).map
                  (MulAut.conj g).toMonoidHom}),
          x ∈ match A with
            | Sum.inl R => (R : Subgroup H)
            | Sum.inr z => (z.2.1 : Subgroup H) := by
      intro x hxne
      obtain ⟨A, hxA, hAunique⟩ :=
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
        have hxorder_one : orderOf x = 1 :=
          Nat.eq_one_of_dvd_one (by
            simpa [hQpcard] using hxdvd)
        exact
          (hxne (orderOf_eq_one_iff.mp hxorder_one)).elim
      · obtain ⟨g, hg⟩ := z.2.2
        have hzcard :
            Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        have huniv :
            ({i, j, k} : Finset (Fin 3)) =
              Finset.univ := by
          apply
            (Finset.card_eq_iff_eq_univ
              ({i, j, k} : Finset (Fin 3))).mp
          simp [hij, hik, hjk]
        have hz_cases :
            z.1 = i ∨ z.1 = j ∨ z.1 = k := by
          have hzmem :
              z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
            rw [huniv]
            simp
          simpa [Finset.mem_insert,
            Finset.mem_singleton] using hzmem
        rcases hz_cases with hza | hza | hza
        · let W0 :
              {W : Subgroup H // ∃ g : H,
                W = (![Z i, Z j] 0).map
                  (MulAut.conj g).toMonoidHom} :=
            ⟨z.2.1, by simpa [hza] using z.2.2⟩
          refine ⟨Sum.inr ⟨0, W0⟩, hxA, ?_⟩
          intro B hxB
          rcases B with R | ⟨b, V⟩
          · have hxorder : orderOf x = 2 :=
              hsylow2_order_two R hxB hxne
            have hxdvd :
                orderOf x ∣ Nat.card z.2.1 :=
              z.2.1.orderOf_dvd_natCard hxA
            rw [hxorder, hzcard, hza, hzi_five]
              at hxdvd
            norm_num at hxdvd
          · fin_cases b
            · let V0 :
                  {W : Subgroup H // ∃ g : H,
                    W = (Z i).map
                      (MulAut.conj g).toMonoidHom} :=
                ⟨V.1, by simpa [Zodd] using V.2⟩
              have heq :=
                hAunique (Sum.inr ⟨i, V0⟩) hxB
              cases heq
              rfl
            · let V1 :
                  {W : Subgroup H // ∃ g : H,
                    W = (Z j).map
                      (MulAut.conj g).toMonoidHom} :=
                ⟨V.1, by simpa [Zodd] using V.2⟩
              have heq :=
                hAunique (Sum.inr ⟨j, V1⟩) hxB
              have hjza : j = z.1 :=
                congrArg (fun C => match C with
                  | Sum.inl _ => i
                  | Sum.inr w => w.1) heq
              have hij' : j = i := hjza.trans hza
              exact (hij hij'.symm).elim
        · let W1 :
              {W : Subgroup H // ∃ g : H,
                W = (![Z i, Z j] 1).map
                  (MulAut.conj g).toMonoidHom} :=
            ⟨z.2.1, by simpa [hza] using z.2.2⟩
          refine ⟨Sum.inr ⟨1, W1⟩, hxA, ?_⟩
          intro B hxB
          rcases B with R | ⟨b, V⟩
          · have hxorder : orderOf x = 2 :=
              hsylow2_order_two R hxB hxne
            have hxdvd :
                orderOf x ∣ Nat.card z.2.1 :=
              z.2.1.orderOf_dvd_natCard hxA
            rw [hxorder, hzcard, hza, hzj_three]
              at hxdvd
            norm_num at hxdvd
          · fin_cases b
            · let V0 :
                  {W : Subgroup H // ∃ g : H,
                    W = (Z i).map
                      (MulAut.conj g).toMonoidHom} :=
                ⟨V.1, by simpa [Zodd] using V.2⟩
              have heq :=
                hAunique (Sum.inr ⟨i, V0⟩) hxB
              have hiza : i = z.1 :=
                congrArg (fun C => match C with
                  | Sum.inl _ => j
                  | Sum.inr w => w.1) heq
              have hji' : i = j := hiza.trans hza
              exact (hij hji').elim
            · let V1 :
                  {W : Subgroup H // ∃ g : H,
                    W = (Z j).map
                      (MulAut.conj g).toMonoidHom} :=
                ⟨V.1, by simpa [Zodd] using V.2⟩
              have heq :=
                hAunique (Sum.inr ⟨j, V1⟩) hxB
              cases heq
              rfl
        · have hxdvd :
              orderOf x ∣ Nat.card z.2.1 :=
            z.2.1.orderOf_dvd_natCard hxA
          have hxorder : orderOf x = 2 := by
            have hpos : 0 < orderOf x := orderOf_pos x
            have hne_one : orderOf x ≠ 1 :=
              fun h => hxne (orderOf_eq_one_iff.mp h)
            have hdvd2 : orderOf x ∣ 2 := by
              simpa [hzcard, hza, hzk_two] using hxdvd
            have hle : orderOf x ≤ 2 :=
              Nat.le_of_dvd (by norm_num) hdvd2
            omega
          obtain ⟨R, hxR, hRunique⟩ :=
            hinvolution_unique_sylow x hxorder
          refine ⟨Sum.inl R, hxR, ?_⟩
          intro B hxB
          rcases B with S | ⟨b, V⟩
          · exact congrArg Sum.inl (hRunique S hxB)
          · fin_cases b
            · have hxdvdV :
                  orderOf x ∣ Nat.card V.1 :=
                V.1.orderOf_dvd_natCard hxB
              obtain ⟨a, ha⟩ := V.2
              have hVcard :
                  Nat.card V.1 = Nat.card (Z i) := by
                rw [ha, Subgroup.card_map_of_injective
                  (MulAut.conj a).injective]
                simp [Zodd]
              rw [hxorder, hVcard, hzi_five] at hxdvdV
              norm_num at hxdvdV
            · have hxdvdV :
                  orderOf x ∣ Nat.card V.1 :=
                V.1.orderOf_dvd_natCard hxB
              obtain ⟨a, ha⟩ := V.2
              have hVcard :
                  Nat.card V.1 = Nat.card (Z j) := by
                rw [ha, Subgroup.card_map_of_injective
                  (MulAut.conj a).injective]
                simp [Zodd]
              rw [hxorder, hVcard, hzj_three] at hxdvdV
              norm_num at hxdvdV
    have hP2card : Nat.card P2 = 2 ^ 2 := by
      change Nat.card (NZ k) = 2 ^ 2
      norm_num [hNZkcard4]
    have hcount2 :
        Nat.card H =
          1 + (2 ^ 2 - 1) *
              (Subgroup.normalizer (P2 : Set H)).index +
            ∑ a, (Nat.card (Zodd a) - 1) *
              (Subgroup.normalizer
                (Zodd a : Set H)).index := by
      apply
        huppert_II_8_22_partition_count_of_unique_family
          P2 hP2card Zodd
      intro x hx
      convert hunique2 x hx using 1
      funext A
      rcases A with R | z <;> rfl
    have hP2normalizer_index :
        (Subgroup.normalizer (P2 : Set H)).index =
          Nat.card (Sylow 2 H) :=
      P2.card_eq_index_normalizer.symm
    rw [hP2normalizer_index] at hcount2
    simp [Zodd, Fin.sum_univ_two, NZ, hHcard60,
      hzi_five, hzj_three, hindices_five.1,
      hindices_five.2.1] at hcount2
    constructor
    · omega
    · exact hinvolution_unique_sylow
  have hSylow2card5 : Nat.card (Sylow 2 H) = 5 :=
    hSylow2_data.1
  have hinvolution_unique_sylow :
      ∀ x : H, orderOf x = 2 →
        ∃! R : Sylow 2 H,
          x ∈ (R : Subgroup H) :=
    hSylow2_data.2
  let Ω2 := Sylow 2 H
  let := Fintype.ofFinite Ω2
  have hΩ2card : Fintype.card Ω2 = 5 := by
    simpa [Ω2, Nat.card_eq_fintype_card] using hSylow2card5
  let act2 := MulAction.toPermHom H Ω2
  have hact2_inj : Function.Injective act2 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hker_le_normalizer (R : Sylow 2 H) :
        act2.ker ≤
          Subgroup.normalizer (R : Set H) := by
      intro x hx
      have hxperm : act2 x = 1 := hx
      have hxfix : x • R = R := by
        have h := DFunLike.congr_fun hxperm R
        simpa [act2] using h
      exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
    have hnormalizer_card_twelve :
        Nat.card
            (Subgroup.normalizer (P2 : Set H)) = 12 := by
      have hP2index :
          (Subgroup.normalizer (P2 : Set H)).index = 5 := by
        calc
          (Subgroup.normalizer (P2 : Set H)).index =
              Nat.card (Sylow 2 H) :=
            P2.card_eq_index_normalizer.symm
          _ = 5 := hSylow2card5
      have hmul :=
        (Subgroup.normalizer
          (P2 : Set H)).card_mul_index
      rw [hP2index, hHcard60] at hmul
      omega
    have hker_card_dvd_twelve :
        Nat.card act2.ker ∣ 12 := by
      simpa [hnormalizer_card_twelve] using
        Subgroup.card_dvd_of_le
          (hker_le_normalizer P2)
    have hker_has_no_involution :
        ∀ x : act2.ker, orderOf x ≠ 2 := by
      intro x hxorder
      have hxHorder : orderOf (x : H) = 2 :=
        (Subgroup.orderOf_coe x).trans hxorder
      obtain ⟨R, hxR, hRunique⟩ :=
        hinvolution_unique_sylow (x : H) hxHorder
      obtain ⟨S, hSR⟩ :=
        Fintype.exists_ne_of_one_lt_card
          (by omega : 1 < Fintype.card Ω2) R
      let X : Subgroup H :=
        Subgroup.zpowers (x : H)
      have hXcard : Nat.card X = 2 := by
        simpa [X] using
          (Nat.card_zpowers (x : H)).trans hxHorder
      have hXisP : IsPGroup 2 X :=
        IsPGroup.of_card (n := 1) (by
          simpa using hXcard)
      have hXnormalizesS :
          X ≤ Subgroup.normalizer (S : Set H) := by
        exact Subgroup.zpowers_le.2
          (hker_le_normalizer S x.2)
      have hsupP :
          IsPGroup 2
            (X ⊔ (S : Subgroup H) : Subgroup H) :=
        hXisP.to_sup_of_normal_right'
          S.isPGroup' hXnormalizesS
      have hsup_eq :
          X ⊔ (S : Subgroup H) = S :=
        S.is_maximal' hsupP le_sup_right
      have hxS : (x : H) ∈ (S : Subgroup H) := by
        have hxjoin :
            (x : H) ∈ X ⊔ (S : Subgroup H) :=
          (show X ≤ X ⊔ (S : Subgroup H) from
            le_sup_left) (by
              exact Subgroup.mem_zpowers (x : H))
        rw [hsup_eq] at hxjoin
        exact hxjoin
      exact hSR (hRunique S hxS)
    have htwo_not_dvd_ker :
        ¬ 2 ∣ Nat.card act2.ker := by
      intro htwo
      obtain ⟨x, hxorder⟩ :=
        exists_prime_orderOf_dvd_card' 2 htwo
      exact hker_has_no_involution x hxorder
    have hker_card_cases :
        Nat.card act2.ker = 1 ∨
          Nat.card act2.ker = 3 := by
      have hpos : 0 < Nat.card act2.ker := Nat.card_pos
      have hle : Nat.card act2.ker ≤ 12 :=
        Nat.le_of_dvd (by norm_num)
          hker_card_dvd_twelve
      interval_cases h : Nat.card act2.ker
      · omega
      · exfalso
        apply htwo_not_dvd_ker
        norm_num [h]
      · omega
      · exfalso
        apply htwo_not_dvd_ker
        norm_num [h]
      · norm_num [h] at hker_card_dvd_twelve
      · exfalso
        apply htwo_not_dvd_ker
        norm_num [h]
      · norm_num [h] at hker_card_dvd_twelve
      · exfalso
        apply htwo_not_dvd_ker
        norm_num [h]
      · norm_num [h] at hker_card_dvd_twelve
      · exfalso
        apply htwo_not_dvd_ker
        norm_num [h]
      · norm_num [h] at hker_card_dvd_twelve
      · exfalso
        apply htwo_not_dvd_ker
        norm_num [h]
    rcases hker_card_cases with hker_one | hker_three
    · exact Subgroup.card_eq_one.mp hker_one
    · have hSylow3card10 :
          Nat.card (Sylow 3 H) = 10 := by
        let : Fact (Nat.Prime 3) := ⟨by decide⟩
        have hZjIndex20 : (Z j).index = 20 := by
          have hmul := (Z j).card_mul_index
          rw [hzj_three, hHcard60] at hmul
          omega
        let hZjP : IsPGroup 3 (Z j) :=
          IsPGroup.of_card (n := 1) (by
            simpa using hzj_three)
        let Q3 : Sylow 3 H := hZjP.toSylow (by
          rw [hZjIndex20]
          norm_num)
        calc
          Nat.card (Sylow 3 H) =
              (Subgroup.normalizer
                (Q3 : Set H)).index :=
            Q3.card_eq_index_normalizer
          _ = (NZ j).index := by rfl
          _ = 10 := hindices_five.2.1
      have hker_is_sylow_three :
          ∃ R : Sylow 3 H,
            (R : Subgroup H) = act2.ker := by
        let : Fact (Nat.Prime 3) := ⟨by decide⟩
        have hkerP : IsPGroup 3 act2.ker :=
          IsPGroup.of_card (n := 1) (by
            simpa using hker_three)
        have hkerIndex20 : act2.ker.index = 20 := by
          have hmul := act2.ker.card_mul_index
          rw [hker_three, hHcard60] at hmul
          omega
        let R3 : Sylow 3 H := hkerP.toSylow (by
          rw [hkerIndex20]
          norm_num)
        exact ⟨R3, rfl⟩
      obtain ⟨R3, hR3⟩ := hker_is_sylow_three
      have hR3normal : (R3 : Subgroup H).Normal := by
        rw [hR3]
        exact inferInstance
      let : Unique (Sylow 3 H) :=
        Sylow.unique_of_normal R3 hR3normal
      have hSylow3card1 :
          Nat.card (Sylow 3 H) = 1 := Nat.card_unique
      omega
  let eΩ2 : Ω2 ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hΩ2card
  let actFin2 : H →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom eΩ2).toMonoidHom.comp act2
  have hactFin2_inj : Function.Injective actFin2 := by
    intro x y hxy
    apply hact2_inj
    apply (Equiv.permCongrHom eΩ2).injective
    simpa [actFin2] using hxy
  let K2 : Subgroup (Equiv.Perm (Fin 5)) := actFin2.range
  have hrange2_inj :
      Function.Injective actFin2.rangeRestrict := by
    intro x y hxy
    exact hactFin2_inj (congrArg Subtype.val hxy)
  let eRange2 : H ≃* K2 :=
    MulEquiv.ofBijective actFin2.rangeRestrict
      ⟨hrange2_inj,
        MonoidHom.rangeRestrict_surjective actFin2⟩
  have hK2card : Nat.card K2 = 60 := by
    calc
      Nat.card K2 = Nat.card H :=
        (Nat.card_congr eRange2.toEquiv).symm
      _ = 60 := hHcard60
  have hperm5card :
      Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hK2index : K2.index = 2 := by
    have hmul := K2.index_mul_card
    rw [hK2card, hperm5card] at hmul
    omega
  have hK2alt : K2 = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hK2index
  exact ⟨eRange2.trans (MulEquiv.subgroupCongr hK2alt)⟩
