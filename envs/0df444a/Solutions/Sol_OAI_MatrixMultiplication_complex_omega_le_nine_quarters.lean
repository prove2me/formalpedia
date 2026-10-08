-- Prove2me | solution 1 for OAI.MatrixMultiplication.complex_omega_le_nine_quarters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T05:05:44.317737+00:00
-- url     : https://prove2.me/submissions/b57d8d9d-7446-4954-b328-36fff2fa94e4

/-
Port of OpenAI math, source revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
This proof uses the original arithmetic model, imported from its definition item.

OAI-Lean-Apache-2.0.txt
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


FixedPointTheorems-MIT.txt
Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

-/

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

section CompatibilityAliases

universe u

/- Compatibility aliases: Lean 4.34.1 Init/Core.lean names, proved by their
   Lean 4.33.1 predecessors without changing the source statements. -/
private theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t e : α} : ite c t e = t := if_pos hc
private theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t e : α} : ite c t e = e := if_neg hnc
private theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = t hc := dif_pos hc
private theorem dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c)
    {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = e hnc := dif_neg hnc
/- From Mathlib 4.34.1 Order/Antisymmetrization.lean, unchanged proof. -/
private theorem toAntisymmetrization_eq {α : Type u} (r : α → α → Prop)
    [IsPreorder α r] (a b : α) :
    toAntisymmetrization r a = toAntisymmetrization r b ↔ AntisymmRel r a b :=
  Quotient.eq

end CompatibilityAliases


/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor -/
section FlattenModule000






namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

theorem directSum_zero_of_left_ne {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (x : ι × X) (y : ι × Y) (z : ι × Z)
    (h : x.1 ≠ y.1) : directSum T x y z = 0 := by
  simp [directSum, h]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => u * a i x, b, c, ?_⟩
  funext x y z
  simp [rankOne, Finset.mul_sum, mul_assoc]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  classical
  funext x y z
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

section ComplexTopology

variable {X Y Z X' Y' Z' : Type*}

def BorderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) : Prop :=
  T ∈ closure {S | RankAtMost S r}

def restrictionOrbit [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : Set (Tensor ℂ X' Y' Z') :=
  {U | ∃ (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ),
    U = restrict A B C T}

def DegeneratesTo [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (U : Tensor ℂ X' Y' Z') : Prop :=
  U ∈ closure (restrictionOrbit T)

theorem RankAtMost.borderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : RankAtMost T r) :
    BorderRankAtMost T r := subset_closure h

theorem continuous_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    Continuous (Tensor.restrict A B C) := by
  unfold restrict
  fun_prop

theorem BorderRankAtMost.restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : BorderRankAtMost T r)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    BorderRankAtMost (Tensor.restrict A B C T) r := by
  have hclosed : IsClosed {S : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.restrict A B C S) r} :=
    isClosed_closure.preimage (continuous_restrict A B C)
  have hsubset : {S : Tensor ℂ X Y Z | RankAtMost S r} ⊆
      {S | BorderRankAtMost (Tensor.restrict A B C S) r} := by
    intro S hS
    exact (hS.restrict A B C).borderRankAtMost
  exact closure_minimal hsubset hclosed h

theorem continuous_product_left {U V W : Type*} (S : Tensor ℂ U V W) :
    Continuous (fun T : Tensor ℂ X Y Z => Tensor.product T S) := by
  unfold product
  fun_prop

theorem continuous_product_right {U V W : Type*} (T : Tensor ℂ X Y Z) :
    Continuous (fun S : Tensor ℂ U V W => Tensor.product T S) := by
  unfold product
  fun_prop

theorem BorderRankAtMost.product {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W} {r s : ℕ}
    (hT : BorderRankAtMost T r) (hS : BorderRankAtMost S s) :
    BorderRankAtMost (Tensor.product T S) (r * s) := by
  have hexact : ∀ T' : Tensor ℂ X Y Z, RankAtMost T' r →
      BorderRankAtMost (Tensor.product T' S) (r * s) := by
    intro T' hT'
    have hclosed : IsClosed {S' : Tensor ℂ U V W |
        BorderRankAtMost (Tensor.product T' S') (r * s)} :=
      isClosed_closure.preimage (continuous_product_right T')
    have hsubset : {S' : Tensor ℂ U V W | RankAtMost S' s} ⊆
        {S' | BorderRankAtMost (Tensor.product T' S') (r * s)} := by
      intro S' hS'
      exact (hT'.product hS').borderRankAtMost
    exact closure_minimal hsubset hclosed hS
  have hclosed : IsClosed {T' : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.product T' S) (r * s)} :=
    isClosed_closure.preimage (continuous_product_left S)
  exact closure_minimal hexact hclosed hT

theorem BorderRankAtMost.of_degeneration [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} {r : ℕ}
    (hT : BorderRankAtMost T r) (hTU : DegeneratesTo T U) :
    BorderRankAtMost U r := by
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | BorderRankAtMost S r} := by
    rintro S ⟨A, B, C, rfl⟩
    exact hT.restrict A B C
  exact closure_minimal hsubset isClosed_closure hTU

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule000
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity -/
section FlattenModule001



namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Arithmetic

inductive Gate (Input Register : Type*) where
  | constant : ℂ → Gate Input Register
  | input : Input → Gate Input Register
  | add : Register → Register → Gate Input Register
  | sub : Register → Register → Gate Input Register
  | mul : Register → Register → Gate Input Register

namespace Gate

variable {Input Register : Type*}

def eval (inputs : Input → ℂ) (registers : Register → ℂ) : Gate Input Register → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

def cost : Gate Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (Input : Type*) : ℕ → Type _ where
  | nil : Program Input 0
  | step {r : ℕ} : Program Input r → Gate Input (Fin r) → Program Input (r + 1)

namespace Program

variable {Input : Type*}

def eval : {r : ℕ} → Program Input r → (Input → ℂ) → Fin r → ℂ
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

@[simp] theorem eval_step_zero {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

abbrev MatrixInput (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : MatrixInput n → ℂ
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

structure MatrixAlgorithm (n : ℕ) where
  registers : ℕ
  program : Program (MatrixInput n) registers
  output : Fin n → Fin n → Fin registers

namespace MatrixAlgorithm

def eval {n : ℕ} (P : MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

def Correct {n : ℕ} (P : MatrixAlgorithm n) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ, P.eval A B = A * B

def cost {n : ℕ} (P : MatrixAlgorithm n) : ℕ := P.program.cost

theorem correct_iff_entries {n : ℕ} (P : MatrixAlgorithm n) :
    P.Correct ↔ ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

def scalarAlgorithm : MatrixAlgorithm 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct : scalarAlgorithm.Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost : scalarAlgorithm.cost = 1 := rfl

def AdmissibleExponent (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

noncomputable def omega : ℝ := sInf {τ : ℝ | AdmissibleExponent τ}

end Arithmetic

namespace Tensor

def matrixMultiplication (a b c : ℕ) :
    Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

@[simp] theorem matrixMultiplication_matching (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    matrixMultiplication a b c (i, j) (j, k) (k, i) = 1 := by
  simp [matrixMultiplication]

end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule001
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching -/
section FlattenModule002

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def diagonal (ι : Type*) [DecidableEq ι] : Tensor K ι ι ι :=
  fun i j k => if i = j ∧ i = k then 1 else 0

theorem diagonal_rankAtMost (ι : Type*) [Fintype ι] [DecidableEq ι] :
    RankAtMost (diagonal (K := K) ι) (Fintype.card ι) := by
  let a : ι → ι → K := fun i j => if i = j then 1 else 0
  have heq : diagonal (K := K) ι =
      fun x y z => ∑ i, rankOne (a i) (a i) (a i) x y z := by
    funext x y z
    simp [diagonal, rankOne, a, mul_ite, ite_and]
    split_ifs <;> simp_all
  rw [heq]
  exact rankAtMost_sum_rankOne a a a

theorem RankAtMost.repeat_batch {S : Tensor K U V W} {k r R B : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hfit : R ≤ B * k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (B * r) := by
  classical
  let f : Fin R → Fin B × Fin k := fun i => finProdFinEquiv.symm (Fin.castLE hfit i)
  have hf : Function.Injective f := finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hfit)
  have hbig := (diagonal_rankAtMost (K := K) (Fin B)).product hbatch
  simp only [Fintype.card_fin] at hbig
  rcases hbig with ⟨a, b, c, heq⟩
  let liftU : (Fin R × U) → Fin B × (Fin k × U) := fun x => ((f x.1).1, (f x.1).2, x.2)
  let liftV : (Fin R × V) → Fin B × (Fin k × V) := fun y => ((f y.1).1, (f y.1).2, y.2)
  let liftW : (Fin R × W) → Fin B × (Fin k × W) := fun z => ((f z.1).1, (f z.1).2, z.2)
  refine ⟨fun i x => a i (liftU x), fun i y => b i (liftV y),
    fun i z => c i (liftW z), ?_⟩
  funext x y z
  change directSum (fun _ : Fin R => S) x y z =
    ∑ i, rankOne (a i) (b i) (c i) (liftU x) (liftV y) (liftW z)
  have hentry := congrFun (congrFun (congrFun heq (liftU x)) (liftV y)) (liftW z)
  rw [← hentry]
  by_cases hxy : x.1 = y.1
  · by_cases hxz : x.1 = z.1
    · have hyz : y.1 = z.1 := hxy.symm.trans hxz
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hyz]
    · have hn : f x.1 ≠ f z.1 := fun h => hxz (hf h)
      have hs : (f x.1).1 ≠ (f z.1).1 ∨ (f x.1).2 ≠ (f z.1).2 := by
        by_cases hfirst : (f x.1).1 = (f z.1).1
        · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
        · exact Or.inl hfirst
      rcases hs with hs | hs <;>
        simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxz, hs]
  · have hn : f x.1 ≠ f y.1 := fun h => hxy (hf h)
    have hs : (f x.1).1 ≠ (f y.1).1 ∨ (f x.1).2 ≠ (f y.1).2 := by
      by_cases hfirst : (f x.1).1 = (f y.1).1
      · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
      · exact Or.inl hfirst
    rcases hs with hs | hs <;>
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hs]

theorem RankAtMost.batch_substitute [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r b : ℕ}
    (hT : RankAtMost T r)
    (hbatch : RankAtMost (directSum (fun _ : Fin r => S)) b) :
    RankAtMost (Tensor.product T S) b := by
  classical
  rcases hT with ⟨a, c, e, rfl⟩
  let A : (X × U) → (Fin r × U) → K :=
    fun x i => if x.2 = i.2 then a i.1 x.1 else 0
  let B : (Y × V) → (Fin r × V) → K :=
    fun y i => if y.2 = i.2 then c i.1 y.1 else 0
  let C : (Z × W) → (Fin r × W) → K :=
    fun z i => if z.2 = i.2 then e i.1 z.1 else 0
  have heq : Tensor.restrict A B C (directSum (fun _ : Fin r => S)) =
      Tensor.product (fun x y z => ∑ i, rankOne (a i) (c i) (e i) x y z) S := by
    funext x y z
    simp [Tensor.restrict, directSum, Tensor.product, rankOne, A, B, C,
      Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul]
  rw [← heq]
  exact hbatch.restrict A B C

theorem RankAtMost.batch_product [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r B : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r)
    (hfit : R ≤ B * k) : RankAtMost (Tensor.product T S) (B * r) :=
  hT.batch_substitute (hbatch.repeat_batch hfit)

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule002
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor -/
section FlattenModule003




namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matrixMultiplication_eq_matrixCoefficients (a b c : ℕ) :
    matrixMultiplication a b c = matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) := rfl

theorem contract_matrixCoefficients [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A × B → K) (right : B × C → K) (i : A) (k : C) :
    contract (matrixCoefficients A B C) left right (k, i) =
      ∑ j, left (i, j) * right (j, k) := by
  simp [contract, matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

theorem matrixCoefficients_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

theorem matrixCoefficients_cyclic [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : B × C) (y : C × A) (z : A × B) :
    matrixCoefficients (K := K) A B C z x y = matrixCoefficients B C A x y z := by
  have h : (z.2 = x.1 ∧ x.2 = y.1 ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩
  simp only [matrixCoefficients, h]

theorem matrixCoefficients_rank_of_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r : ℕ}
    (hproduct : RankAtMost (product (matrixCoefficients (K := K) A B C)
      (matrixCoefficients D E F)) r) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) r := by
  have h := hproduct.pullback
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  have heq : pullback
      (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      (product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)) =
      matrixCoefficients (K := K) (A × D) (B × E) (C × F) := by
    funext x y z
    exact matrixCoefficients_product x y z
  rw [heq] at h
  exact h

theorem matrixCoefficients_product_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r s : ℕ}
    (hT : RankAtMost (matrixCoefficients (K := K) A B C) r)
    (hS : RankAtMost (matrixCoefficients (K := K) D E F) s) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) (r * s) :=
  matrixCoefficients_rank_of_product (hT.product hS)

theorem matrixCoefficients_batch_rank [DecidableEq A] [DecidableEq B] [Fintype B]
    {R k r batches : ℕ}
    (houter : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => matrixCoefficients (K := K) B B B)) r)
    (hfit : R ≤ batches * k) :
    RankAtMost (matrixCoefficients (K := K) (A × B) (A × B) (A × B)) (batches * r) :=
  matrixCoefficients_rank_of_product (houter.batch_product hbatch hfit)

theorem matrixCoefficients_power [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (n : ℕ) (x : (Fin n → A) × (Fin n → B))
    (y : (Fin n → B) × (Fin n → C)) (z : (Fin n → C) × (Fin n → A)) :
    Tensor.power (matrixCoefficients (K := K) A B C) n
      (fun i => (x.1 i, x.2 i)) (fun i => (y.1 i, y.2 i)) (fun i => (z.1 i, z.2 i)) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) x y z := by
  simp only [Tensor.power, matrixCoefficients, Fintype.prod_boole, forall_and, ← funext_iff]

theorem matrixCoefficients_cyclic_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {r : ℕ} (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) B C A) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  rw [← matrixCoefficients_cyclic (K := K) x y z]
  rw [congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule003
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening -/
section FlattenModule004


namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

theorem directSum_matrixCoefficients_rank_lower
    {Label A B C : Type*} [Fintype Label] [Fintype A] [Fintype C]
    [DecidableEq Label] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => matrixCoefficients (K := K) A B C)) r) :
    Fintype.card Label * (Fintype.card C * Fintype.card A) ≤ r := by
  classical
  let b₀ : B := Classical.choice inferInstance
  have hminor : ∀ i j : Label × (C × A),
      directSum (fun _ : Label => matrixCoefficients (K := K) A B C)
        (i.1, (i.2.2, b₀)) (i.1, (b₀, i.2.1)) j = if i = j then 1 else 0 := by
    intro i j
    simp only [directSum, matrixCoefficients]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hlower := h.card_le_of_identity
    (fun i : Label × (C × A) => (i.1, (i.2.2, b₀)))
    (fun i : Label × (C × A) => (i.1, (b₀, i.2.1)))
    (fun i : Label × (C × A) => i) hminor
  simpa only [Fintype.card_prod] using hlower

theorem directSum_square_rank_lower (k n r : ℕ) (hn : 0 < n)
    (h : RankAtMost (directSum (fun _ : Fin k =>
      matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    k * n ^ 2 ≤ r := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, pow_two] using directSum_matrixCoefficients_rank_lower h

end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule004
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent -/
section FlattenModule005


namespace OAI

/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y × Z → X → ℂ := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → ℂ := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → ℂ := fun p z => if z = p.2.2 then 1 else 0
  refine ⟨Fintype.card (X × Y × Z), ?_⟩
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- Exact rank of a finite complex coefficient tensor. -/
def exactRank {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank cannot increase under a linear restriction. -/
theorem exactRank_restrict_le {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (A : X' → X → ℂ) (B : Y' → Y → ℂ)
    (C : Z' → Z → ℂ) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have h := exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Tensor product decompositions give the usual submultiplicative rank bound. -/
theorem exactRank_product_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))

/-- Exact rank of the square matrix multiplication tensor. -/
def exactMatrixRank (n : ℕ) : ℕ := exactRank (Tensor.matrixMultiplication n n n)

theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost (Tensor.matrixMultiplication n n n) (exactMatrixRank n) :=
  exactRank_spec _

/-- The ordinary scalar multiplication algorithm uses `n³` simple tensors. -/
theorem matrixMultiplication_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Tensor.matrixMultiplication n n n) (n ^ 3) := by
  classical
  let a : Fin n × Fin n × Fin n → Fin n × Fin n → ℂ :=
    fun p x => if x = (p.1, p.2.1) then 1 else 0
  let b : Fin n × Fin n × Fin n → Fin n × Fin n → ℂ :=
    fun p y => if y = (p.2.1, p.2.2) then 1 else 0
  let c : Fin n × Fin n × Fin n → Fin n × Fin n → ℂ :=
    fun p z => if z = (p.2.2, p.1) then 1 else 0
  have heq : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Tensor.matrixMultiplication,
      Fintype.sum_prod_type, Prod.ext_iff, ite_and, mul_ite]
    split_ifs <;> simp_all
  rw [heq]
  convert Tensor.rankAtMost_sum_rankOne a b c using 1
  simp [Fintype.card_prod, pow_succ, Nat.mul_assoc]

theorem exactMatrixRank_upper (n : ℕ) : exactMatrixRank n ≤ n ^ 3 :=
  exactRank_le (matrixMultiplication_rankAtMost_cubic n)

/-- An identity minor of the output flattening forces the quadratic lower bound. -/
theorem matrixMultiplication_rank_lower {n R : ℕ} (hn : 0 < n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R) : n ^ 2 ≤ R := by
  let j : Fin n := ⟨0, hn⟩
  have hminor : ∀ i k : Fin n × Fin n,
      Tensor.matrixMultiplication n n n (i.2, j) (j, i.1) k =
        if i = k then 1 else 0 := by
    intro i k
    simp [Tensor.matrixMultiplication, Prod.ext_iff, eq_comm]
  have h := hRank.card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, j))
    (fun i : Fin n × Fin n => (j, i.1)) id hminor
  simpa [Fintype.card_prod, pow_two] using h

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank n :=
  matrixMultiplication_rank_lower hn (exactMatrixRank_spec n)

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < exactMatrixRank n :=
  lt_of_lt_of_le (pow_pos hn 2) (exactMatrixRank_lower hn)

@[simp] theorem exactMatrixRank_zero : exactMatrixRank 0 = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using exactMatrixRank_upper 0)

@[simp] theorem exactMatrixRank_one : exactMatrixRank 1 = 1 := by
  apply le_antisymm
  · simpa using exactMatrixRank_upper 1
  · simpa using exactMatrixRank_lower (n := 1) zero_lt_one

/-- The set of finite exact-rank exponents in the definition of `ν`. -/
def exactRankExponentSet : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n (exactMatrixRank n)}

/-- The exact-rank exponent `ν = inf_{n ≥ 2} log(R(Tₙ))/log(n)`. -/
def exactRankExponent : ℝ := sInf exactRankExponentSet

theorem exactRankExponentSet_nonempty : exactRankExponentSet.Nonempty :=
  ⟨Real.logb 2 (exactMatrixRank 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n (exactMatrixRank n) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.le_logb_iff_rpow_le hn1 hr).mpr
  rw [Real.rpow_two]
  exact_mod_cast exactMatrixRank_lower (show 0 < n by omega)

theorem exactMatrixRank_logb_upper {n : ℕ} (hn : 2 ≤ n) :
    Real.logb n (exactMatrixRank n) ≤ 3 := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.logb_le_iff_le_rpow hn1 hr).mpr
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  exact_mod_cast exactMatrixRank_upper n

theorem exactRankExponentSet_bddBelow : BddBelow exactRankExponentSet := by
  refine ⟨2, ?_⟩
  rintro τ ⟨n, hn, rfl⟩
  exact exactMatrixRank_logb_lower hn

theorem exactRankExponent_lower : 2 ≤ exactRankExponent :=
  le_csInf exactRankExponentSet_nonempty (by
    rintro τ ⟨n, hn, rfl⟩
    exact exactMatrixRank_logb_lower hn)

theorem exactRankExponent_le_logb {n : ℕ} (hn : 2 ≤ n) :
    exactRankExponent ≤ Real.logb n (exactMatrixRank n) :=
  csInf_le exactRankExponentSet_bddBelow ⟨n, hn, rfl⟩

theorem exactRankExponent_upper : exactRankExponent ≤ 3 :=
  (exactRankExponent_le_logb (n := 2) le_rfl).trans
    (exactMatrixRank_logb_upper (n := 2) le_rfl)

/-- Each matrix multiplication tensor has rank at least `n^ν`. -/
theorem exactMatrixRank_rpow_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ exactRankExponent ≤ exactMatrixRank n := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.le_logb_iff_rpow_le hn1 hr).mp (exactRankExponent_le_logb hn)

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ exactRankExponent ≤ exactMatrixRank n := by
  by_cases hn2 : 2 ≤ n
  · exact exactMatrixRank_rpow_lower hn2
  · have hn1 : n = 1 := by omega
    simp [hn1]

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ (exactMatrixRank n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt exactRankExponentSet_nonempty hτ
  refine ⟨n, hn, ?_⟩
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.logb_lt_iff_lt_rpow hn1 hr).mp hσ

/-- Finite decompositions approximate the exact-rank exponent with any positive slack. -/
theorem exists_rankAtMost_of_exponent_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ n R : ℕ, 2 ≤ n ∧ Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R ∧
      (R : ℝ) ≤ (n : ℝ) ^ (exactRankExponent + ε) := by
  obtain ⟨n, hn, hR⟩ := exists_exactMatrixRank_lt_rpow (lt_add_of_pos_right _ hε)
  exact ⟨n, exactMatrixRank n, hn, exactMatrixRank_spec n, hR.le⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule005
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Programs -/
section FlattenModule006


namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

variable {Input R S : Type*}

def mapRegister (f : R → S) : Gate Input R → Gate Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

theorem eval_mapRegister (g : Gate Input R) (f : R → S)
    (inputs : Input → ℂ) (registers : S → ℂ) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

@[simp] theorem cost_mapRegister (g : Gate Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

def append {r : ℕ} (p : Program Input r) : {s : ℕ} → Program Input s → Program Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

theorem eval_append_new {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

theorem eval_append_old {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

@[simp] theorem cost_append {r s : ℕ} (p : Program Input r) (q : Program Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

inductive Expression (Input : Type*) where
  | constant : ℂ → Expression Input
  | input : Input → Expression Input
  | add : Expression Input → Expression Input → Expression Input
  | sub : Expression Input → Expression Input → Expression Input
  | mul : Expression Input → Expression Input → Expression Input

namespace Expression

variable {Input : Type*}

def eval (inputs : Input → ℂ) : Expression Input → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

def cost : Expression Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

structure Compiled (e : Expression Input) where
  registers : ℕ
  program : Program Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

def compile : (e : Expression Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression
end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule006
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Programs -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.ProgramComposition -/
section FlattenModule007

namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

variable {Input Input' Register : Type*}

def mapInput (f : Input → Input') : Gate Input Register → Gate Input' Register
  | .constant z => .constant z
  | .input i => .input (f i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapInput (f : Input → Input') (g : Gate Input Register)
    (inputs : Input' → ℂ) (registers : Register → ℂ) :
    (g.mapInput f).eval inputs registers = g.eval (inputs ∘ f) registers := by
  cases g <;> rfl

@[simp] theorem cost_mapInput (f : Input → Input') (g : Gate Input Register) :
    (g.mapInput f).cost = g.cost := by
  cases g <;> rfl

def mapSource (f : Input → Input' ⊕ ℂ) : Gate Input Register → Gate Input' Register
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ ℂ) (g : Gate Input Register)
    (inputs : Input' → ℂ) (registers : Register → ℂ) :
    (g.mapSource f).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, eval]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

@[simp] theorem cost_mapSource (f : Input → Input' ⊕ ℂ) (g : Gate Input Register) :
    (g.mapSource f).cost = g.cost := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, cost]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

end Gate

namespace Program

variable {Input Input' Mid : Type*}

def mapInput (f : Input → Input') : {r : ℕ} → Program Input r → Program Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapInput f).step (g.mapInput f)

@[simp] theorem eval_mapInput (f : Input → Input') {r : ℕ} (p : Program Input r)
    (inputs : Input' → ℂ) :
    ∀ i : Fin r, (p.mapInput f).eval inputs i = p.eval (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapInput, eval_step_zero, Gate.eval_mapInput]
      rw [funext ih]
    · exact ih j

@[simp] theorem cost_mapInput (f : Input → Input') {r : ℕ} (p : Program Input r) :
    (p.mapInput f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapInput, cost_step, Gate.cost_mapInput, ih]

def mapSource (f : Input → Input' ⊕ ℂ) : {r : ℕ} → Program Input r → Program Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapSource f).step (g.mapSource f)

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ ℂ) {r : ℕ}
    (p : Program Input r) (inputs : Input' → ℂ) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapSource, eval_step_zero, Gate.eval_mapSource]
      rw [funext ih]
    · exact ih j

@[simp] theorem cost_mapSource (f : Input → Input' ⊕ ℂ) {r : ℕ}
    (p : Program Input r) : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapSource, cost_step, Gate.cost_mapSource, ih]

structure Substituted {r s : ℕ} (p : Program Input r) (q : Program Mid s)
    (wires : Mid → Fin r) where
  registers : ℕ
  program : Program Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

namespace Substituted

def step {r s : ℕ} {p : Program Input r} {q : Program Mid s}
    {wires : Mid → Fin r} (a : Substituted p q wires)
    (g : Gate Mid (Fin s)) (h : Gate Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => p.eval inputs (wires j))
        (q.eval (fun j => p.eval inputs (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput := fun i => (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := by
    intro inputs i
    exact a.correctOld inputs i
  correct := by
    intro inputs i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heval inputs
    · exact a.correct inputs j
  cost_eq := by
    simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

end Substituted

def substitute {r : ℕ} (p : Program Input r) :
    {s : ℕ} → (q : Program Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { registers := r
      program := p
      oldOutput := id
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := by simp only [cost, Nat.add_zero] }
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      { registers := a.registers
        program := a.program
        oldOutput := a.oldOutput
        output := Fin.cases (a.oldOutput (wires j)) a.output
        correctOld := a.correctOld
        correct := by
          intro inputs i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact a.correctOld inputs (wires j)
          · exact a.correct inputs k
        cost_eq := by
          simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq }
    | .constant z =>
      a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j =>
      a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j =>
      a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j =>
      a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

end Program

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule007
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.ProgramComposition -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.MatrixPadding -/
section FlattenModule008

namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

def zeroPadMatrix {n : ℕ} (m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) = A i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {n m : ℕ} (h : n ≤ m)
    (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    (zeroPadMatrix m A * zeroPadMatrix m B) (Fin.castLE h i) (Fin.castLE h k) =
      (A * B) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin m,
        zeroPadMatrix m A (Fin.castLE h i) j *
          zeroPadMatrix m B j (Fin.castLE h k)) =
        ∑ j : Fin n,
          zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) *
            zeroPadMatrix m B (Fin.castLE h j) (Fin.castLE h k) := by
      apply sum_fin_castLE_of_zero h
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin n, A i j * B j k := by simp

def padSource {n m : ℕ} : MatrixInput m → MatrixInput n ⊕ ℂ
  | .inl (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inr (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0

theorem padSource_eval {n m : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (fun x : MatrixInput m => Sum.elim (matrixInputs A B) id (padSource x)) =
      matrixInputs (zeroPadMatrix m A) (zeroPadMatrix m B) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨i, j⟩
  all_goals
    by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]

namespace MatrixAlgorithm

def pad {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) : MatrixAlgorithm n where
  registers := P.registers
  program := P.program.mapSource (padSource (n := n))
  output := fun i k => P.output (Fin.castLE h i) (Fin.castLE h k)

theorem pad_correct {n m : ℕ} (h : n ≤ m) {P : MatrixAlgorithm m}
    (hP : P.Correct) : (pad h P).Correct := by
  intro A B
  funext i k
  change (P.program.mapSource (padSource (n := n))).eval (matrixInputs A B)
    (P.output (Fin.castLE h i) (Fin.castLE h k)) = (A * B) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix m A) (zeroPadMatrix m B)) (Fin.castLE h i)) (Fin.castLE h k)
  exact hentry.trans (zeroPadMatrix_mul h A B i k)

@[simp] theorem pad_cost_eq {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) :
    (pad h P).cost = P.cost :=
  Program.cost_mapSource (padSource (n := n)) P.program

theorem exists_restrict {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m)
    (hP : P.Correct) : ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad h P, pad_correct h hP, (pad_cost_eq h P).le⟩

end MatrixAlgorithm

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule008
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.MatrixPadding -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexExpressionFamily -/
section FlattenModule009



namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.Expression

variable {Input Output : Type*}

structure CompiledFamily [Fintype Output] (expressions : Output → Expression Input) where
  registers : ℕ
  program : Program Input registers
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

def compileFamily [Fintype Output] (expressions : Output → Expression Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Foundation.Arithmetic.Expression

end

end OAI

end FlattenModule009
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexExpressionFamily -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.RecursiveBlockPrograms -/
section FlattenModule010





namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

namespace LinearExpression

variable {Input : Type*}

def sumFin : (n : ℕ) → (Fin n → Expression Input) → Expression Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin n (fun i => f i.succ))

theorem eval_sumFin (n : ℕ) (f : Fin n → Expression Input) (inputs : Input → ℂ) :
    (sumFin n f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, Expression.eval]
  | succ n ih =>
    simp only [sumFin, Expression.eval, ih, Fin.sum_univ_succ]

theorem cost_sumFin (n : ℕ) (f : Fin n → Expression Input) :
    (sumFin n f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, Expression.cost]
  | succ n ih =>
    simp only [sumFin, Expression.cost, ih, Fin.sum_univ_succ]
    omega

def linear {Term : Type*} [Fintype Term] (a : Term → ℂ) (wire : Term → Input) :
    Expression Input :=
  sumFin (Fintype.card Term) (fun i =>
    .mul (.constant (a ((Fintype.equivFin Term).symm i)))
      (.input (wire ((Fintype.equivFin Term).symm i))))

theorem eval_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) (inputs : Input → ℂ) :
    (linear a wire).eval inputs = ∑ i, a i * inputs (wire i) := by
  rw [linear, eval_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => a i * inputs (wire i))

theorem cost_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) :
    (linear a wire).cost = 2 * Fintype.card Term := by
  simp [linear, cost_sumFin, Expression.cost, two_mul]

end LinearExpression

structure Family (Input Output : Type*) where
  registers : ℕ
  program : Program Input registers
  output : Output → Fin registers

namespace Family

variable {Input Mid Output : Type*}

def eval (p : Family Input Output) (inputs : Input → ℂ) (o : Output) : ℂ :=
  p.program.eval inputs (p.output o)

def cost (p : Family Input Output) : ℕ := p.program.cost

def expressions [Fintype Output] (e : Output → Expression Input) : Family Input Output :=
  let p := Expression.compileFamily e
  ⟨p.registers, p.program, p.output⟩

theorem eval_expressions [Fintype Output] (e : Output → Expression Input)
    (inputs : Input → ℂ) (o : Output) :
    (expressions e).eval inputs o = (e o).eval inputs :=
  (Expression.compileFamily e).correct inputs o

theorem cost_expressions [Fintype Output] (e : Output → Expression Input) :
    (expressions e).cost = ∑ o, (e o).cost :=
  (Expression.compileFamily e).cost_eq

def compose (p : Family Input Mid) (q : Family Mid Output) : Family Input Output :=
  let s := p.program.substitute q.program p.output
  ⟨s.registers, s.program, fun o => s.output (q.output o)⟩

theorem eval_compose (p : Family Input Mid) (q : Family Mid Output)
    (inputs : Input → ℂ) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program p.output).correct inputs (q.output o)

theorem cost_compose (p : Family Input Mid) (q : Family Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  (p.program.substitute q.program p.output).cost_eq

def mapInputs {NewInput : Type*} (f : Input → NewInput) (p : Family Input Output) :
    Family NewInput Output :=
  ⟨p.registers, p.program.mapInput f, p.output⟩

theorem eval_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) (inputs : NewInput → ℂ) (o : Output) :
    (p.mapInputs f).eval inputs o = p.eval (fun i => inputs (f i)) o := by
  exact Program.eval_mapInput f p.program inputs (p.output o)

theorem cost_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) : (p.mapInputs f).cost = p.cost := by
  exact Program.cost_mapInput f p.program

def parallel : (r : ℕ) → (Fin r → Family Input Output) → Family Input (Fin r × Output)
  | 0, _ => ⟨0, Program.nil, fun o => Fin.elim0 o.1⟩
  | r + 1, p =>
    let head := p 0
    let tail := parallel r (fun i => p i.succ)
    { registers := head.registers + tail.registers
      program := head.program.append tail.program
      output := fun o => Fin.cases
        (Program.oldIndex _ _ (head.output o.2))
        (fun i => Program.newIndex _ _ (tail.output (i, o.2))) o.1 }

theorem eval_parallel (r : ℕ) (p : Fin r → Family Input Output)
    (inputs : Input → ℂ) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Program.eval_append_old _ _ inputs _
    · exact (Program.eval_append_new _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

theorem cost_parallel (r : ℕ) (p : Fin r → Family Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost := by
  induction r with
  | zero => simp [parallel, cost, Program.cost]
  | succ r ih =>
    change ((p 0).program.append (parallel r (fun i => p i.succ)).program).cost = _
    rw [Program.cost_append]
    change (p 0).cost + (parallel r (fun i => p i.succ)).cost = _
    rw [ih, Fin.sum_univ_succ]

def copies (r : ℕ) (p : Family Input Output) :
    Family (Fin r × Input) (Fin r × Output) :=
  parallel r (fun i => p.mapInputs (fun x => (i, x)))

theorem eval_copies (r : ℕ) (p : Family Input Output)
    (inputs : Fin r × Input → ℂ) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 := by
  rw [copies, eval_parallel, eval_mapInputs]

theorem cost_copies (r : ℕ) (p : Family Input Output) :
    (copies r p).cost = r * p.cost := by
  simp [copies, cost_parallel, cost_mapInputs]

def ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    Family (MatrixInput m) (Fin m × Fin m) :=
  ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩

@[simp] theorem cost_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    (ofMatrix p).cost = p.cost := rfl

theorem eval_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) (hp : p.Correct)
    (inputs : MatrixInput m → ℂ) (o : Fin m × Fin m) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) := by
  have h := (MatrixAlgorithm.correct_iff_entries p).mp hp
    (fun i j => inputs (.inl (i, j))) (fun j k => inputs (.inr (j, k))) o.1 o.2
  have hi : matrixInputs (fun i j => inputs (.inl (i, j)))
      (fun j k => inputs (.inr (j, k))) = inputs := by
    funext x
    cases x <;> rfl
  rw [hi] at h
  exact h

end Family

section BlockIdentities

variable {n r m : ℕ}

def join (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)

theorem rank_bilinear_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left right : Fin n × Fin n → ℂ) (i k : Fin n) :
    (∑ q, c q (k, i) * (∑ x, a q x * left x) * (∑ y, b q y * right y)) =
      ∑ j, left (i, j) * right (j, k) := by
  rw [← Tensor.contract_matrixCoefficients left right i k]
  change _ = Tensor.contract (Tensor.matrixMultiplication n n n) left right (k, i)
  rw [h]
  simp only [Tensor.contract, Tensor.rankOne, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, c q (k, i) * (a q x * left x) * (b q y * right y)) =
        ∑ q, ∑ x, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ =
        ∑ x, ∑ q, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, a q x * b q y * c q (k, i) * left x * right y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro q hq
      ring

def leftBlock (a : Fin r → Fin n × Fin n → ℂ)
    (A : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun s t => ∑ x, a q x * A (join x.1 s) (join x.2 t)

def rightBlock (b : Fin r → Fin n × Fin n → ℂ)
    (B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun t u => ∑ y, b q y * B (join y.1 t) (join y.2 u)

theorem block_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ)
    (i k : Fin n) (s u : Fin m) :
    (∑ q, c q (k, i) * ((leftBlock a A q) * (rightBlock b B q)) s u) =
      (A * B) (join i s) (join k u) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m) := rank_bilinear_identity a b c h
    (fun x => A (join x.1 s) (join x.2 t))
    (fun y => B (join y.1 t) (join y.2 u)) i k
  simp only [leftBlock, rightBlock]
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j => A (join i s) j * B j (join k u)))

end BlockIdentities

section BlockPrograms

variable {n r m : ℕ}

def inputExpressions (a b : Fin r → Fin n × Fin n → ℂ) :
    Fin r × MatrixInput m → Expression (MatrixInput (n * m))
  | (q, .inl (s, t)) => LinearExpression.linear (a q)
      (fun x => .inl (join x.1 s, join x.2 t))
  | (q, .inr (t, u)) => LinearExpression.linear (b q)
      (fun y => .inr (join y.1 t, join y.2 u))

def inputFamily (a b : Fin r → Fin n × Fin n → ℂ) :
    Family (MatrixInput (n * m)) (Fin r × MatrixInput m) :=
  Family.expressions (inputExpressions a b)

theorem inputFamily_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (x : MatrixInput m) :
    (inputFamily a b).eval (matrixInputs A B) (q, x) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) x := by
  cases x with
  | inl x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, leftBlock]
  | inr x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, rightBlock]

theorem inputFamily_cost (a b : Fin r → Fin n × Fin n → ℂ) :
    (inputFamily (m := m) a b).cost = 4 * r * n ^ 2 * m ^ 2 := by
  rw [inputFamily, Family.cost_expressions]
  have hc (o : Fin r × MatrixInput m) : (inputExpressions a b o).cost = 2 * n ^ 2 := by
    rcases o with ⟨q, o⟩
    cases o <;> simp [inputExpressions, LinearExpression.cost_linear, pow_two]
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_sum, smul_eq_mul]
  ring

def recursiveProducts (a b : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    Family (MatrixInput (n * m)) (Fin r × (Fin m × Fin m)) :=
  (inputFamily a b).compose (Family.copies r (Family.ofMatrix p))

theorem recursiveProducts_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) (hp : p.Correct)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (s u : Fin m) :
    (recursiveProducts a b p).eval (matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u := by
  rw [recursiveProducts, Family.eval_compose, Family.eval_copies,
    Family.eval_ofMatrix _ hp]
  simp only [inputFamily_eval, matrixInputs, Matrix.mul_apply]

theorem recursiveProducts_cost (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (recursiveProducts a b p).cost = 4 * r * n ^ 2 * m ^ 2 + r * p.cost := by
  rw [recursiveProducts, Family.cost_compose, inputFamily_cost,
    Family.cost_copies, Family.cost_ofMatrix]

def outputExpressions (c : Fin r → Fin n × Fin n → ℂ) :
    Fin (n * m) × Fin (n * m) → Expression (Fin r × (Fin m × Fin m)) :=
  fun o => LinearExpression.linear
    (fun q => c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1))
    (fun q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2)))

def outputFamily (c : Fin r → Fin n × Fin n → ℂ) :
    Family (Fin r × (Fin m × Fin m)) (Fin (n * m) × Fin (n * m)) :=
  Family.expressions (outputExpressions c)

theorem outputFamily_eval (c : Fin r → Fin n × Fin n → ℂ)
    (inputs : Fin r × (Fin m × Fin m) → ℂ) (i k : Fin n) (s u : Fin m) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) := by
  simp only [outputFamily, Family.eval_expressions, outputExpressions,
    LinearExpression.eval_linear, join, Equiv.symm_apply_apply]

theorem outputFamily_cost (c : Fin r → Fin n × Fin n → ℂ) :
    (outputFamily (m := m) c).cost = 2 * r * n ^ 2 * m ^ 2 := by
  simp only [outputFamily, Family.cost_expressions, outputExpressions,
    LinearExpression.cost_linear, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring

def algorithm (a b c : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    MatrixAlgorithm (n * m) :=
  let f := (recursiveProducts a b p).compose (outputFamily c)
  ⟨f.registers, f.program, fun i k => f.output (i, k)⟩

theorem algorithm_correct
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm m) (hp : p.Correct) : (algorithm a b c p).Correct := by
  intro A B
  funext i k
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ((recursiveProducts a b p).compose (outputFamily c)).eval
    (matrixInputs A B) (join i s, join k u) = _
  rw [Family.eval_compose, outputFamily_eval]
  simp_rw [recursiveProducts_eval a b p hp A B]
  exact block_identity a b c h A B i k s u

theorem algorithm_cost (a b c : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (algorithm a b c p).cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  change ((recursiveProducts a b p).compose (outputFamily c)).cost = _
  rw [Family.cost_compose, recursiveProducts_cost, outputFamily_cost]
  ring

theorem rank_block_step (h : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) r)
    (p : MatrixAlgorithm m) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm (n * m), q.Correct ∧
      q.cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  rcases h with ⟨a, b, c, h⟩
  exact ⟨algorithm a b c p, algorithm_correct a b c h p hp, algorithm_cost a b c p⟩

end BlockPrograms

end MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

end

end OAI

end FlattenModule010
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.RecursiveBlockPrograms -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Growth -/
section FlattenModule011








namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem exists_power_cover {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ b ^ k ∧ b ^ k ≤ b * n := by
  refine ⟨Nat.log b n + 1, (Nat.lt_pow_succ_log_self (by omega) n).le, ?_⟩
  rw [pow_succ']
  exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))

theorem geometric_cost_recurrence_bound (x : ℕ → ℝ) (a b d q : ℝ)
    (hx : 0 ≤ x 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (haq : a < q) (hdq : d ≤ q)
    (hstep : ∀ k, x (k + 1) ≤ a * x k + b * d ^ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, x k ≤ C * q ^ k := by
  let C := x 0 + b / (q - a) + 1
  have hgap : 0 < q - a := sub_pos.mpr haq
  have hfrac : 0 ≤ b / (q - a) := div_nonneg hb hgap.le
  have hC : 0 < C := by dsimp [C]; linarith
  have hcancel : (q - a) * (b / (q - a)) = b := by
    field_simp [ne_of_gt hgap]
  have hCfrac : b / (q - a) ≤ C := by dsimp [C]; linarith
  have hcoeff : a * C + b ≤ C * q := by
    have hmul := mul_le_mul_of_nonneg_left hCfrac hgap.le
    rw [hcancel] at hmul
    calc
      a * C + b ≤ a * C + (q - a) * C := add_le_add_right hmul _
      _ = C * q := by ring
  refine ⟨C, hC, ?_⟩
  intro k
  induction k with
  | zero => simp only [pow_zero, mul_one]; dsimp [C]; linarith
  | succ k ih =>
    calc
      x (k + 1) ≤ a * x k + b * d ^ k := hstep k
      _ ≤ a * (C * q ^ k) + b * q ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdq k) hb)
      _ = (a * C + b) * q ^ k := by ring
      _ ≤ (C * q) * q ^ k :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (hd.trans hdq) k)
      _ = C * q ^ (k + 1) := by rw [pow_succ]; ring

theorem power_cost_padding_bound
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ s) ^ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  refine ⟨C * (b : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hbpos s), ?_⟩
  intro n hn
  obtain ⟨k, hnk, hkn⟩ := exists_power_cover hb hn
  obtain ⟨P, hP, hcost⟩ := hpower k
  obtain ⟨Q, hQ, hQP⟩ := hpad hnk P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((b : ℝ) ^ s) ^ k := hcost
    _ = C * ((b ^ k : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hbpos.le, Nat.cast_pow]
    _ ≤ C * ((b : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) hs) hC.le
    _ = (C * (b : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hbpos.le (Nat.cast_nonneg n)]
      ring

theorem admissibleExponent_of_uniform_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ C : ℝ} (hτ : 0 ≤ τ) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ τ) ^ k) :
    AdmissibleExponent τ := by
  obtain ⟨D, hD, hall⟩ := power_cost_padding_bound hpad hb hτ hC hpower
  intro ε hε
  refine ⟨D, hD, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hall n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hD.le

theorem admissibleExponent_of_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
        P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ (τ + ε)) ^ k) :
    AdmissibleExponent τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact power_cost_padding_bound hpad hb (by linarith) hC hcost

theorem admissibleExponent_of_recursive_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (P : ∀ k : ℕ, MatrixAlgorithm (b ^ k))
    (hP : ∀ k, (P k).Correct)
    (hstep : ∀ k, (P (k + 1)).cost ≤ R * (P k).cost + K * (b ^ k) ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => ((P k).cost : ℝ)) (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ))
    ((b : ℝ) ^ (τ + ε)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (sq_nonneg _) hrate hquad (fun k => by
      have h := hstep k
      have hcast : ((P (k + 1)).cost : ℝ) ≤
          (R : ℝ) * ((P k).cost : ℝ) + (K : ℝ) * ((b : ℝ) ^ k) ^ 2 := by
        exact_mod_cast h
      simpa only [← pow_mul, Nat.mul_comm k 2] using hcast)
  exact ⟨C, hC, fun k => ⟨P k, hP k, hbound k⟩⟩

def blockRecurrenceCost (b R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2

@[simp] theorem blockRecurrenceCost_zero (b R K : ℕ) :
    blockRecurrenceCost b R K 0 = 1 := rfl

@[simp] theorem blockRecurrenceCost_succ (b R K k : ℕ) :
    blockRecurrenceCost b R K (k + 1) =
      R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2 := rfl

theorem power_programs_of_block_step {b R K : ℕ}
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k), P.Correct ∧
      P.cost ≤ blockRecurrenceCost b R K k := by
  intro k
  induction k with
  | zero =>
    exact ⟨scalarAlgorithm, scalarAlgorithm_correct, by simp⟩
  | succ k ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (b ^ k) P hP
    have hbound : Q.cost ≤ blockRecurrenceCost b R K (k + 1) := by
      exact hQcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _)
    have hresult : ∃ Q : MatrixAlgorithm (b * b ^ k), Q.Correct ∧
        Q.cost ≤ blockRecurrenceCost b R K (k + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' b k).symm ▸ hresult

theorem admissibleExponent_of_block_step_of_padding
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => (blockRecurrenceCost b R K k : ℝ))
    (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ)) ((b : ℝ) ^ (τ + ε))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (sq_nonneg _) hrate hquad (fun k => by
      simp only [blockRecurrenceCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2])
  refine ⟨C, hC, ?_⟩
  intro k
  obtain ⟨P, hP, hcost⟩ := power_programs_of_block_step hstep k
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (blockRecurrenceCost b R K k : ℝ)).trans (hbound k)⟩

theorem admissibleExponent_of_block_step
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ :=
  admissibleExponent_of_block_step_of_padding
    (fun h P hP => MatrixAlgorithm.exists_restrict h P hP) hb hτ hR hstep

theorem admissibleExponent_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_block_step (K := 6 * R * n ^ 2) hn hτ hR
  intro m P hP
  obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
  exact ⟨Q, hQ, hcost.le⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule011
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Growth -/



/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity -/
section FlattenModule013



namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {F Input Register : Type*}

end Gate

namespace Program

variable {F Input : Type*}

@[simp] theorem eval_step_zero [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem correct_iff_entries (P : MatrixAlgorithm F a b c) :
    P.Correct ↔ ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)
      (i : Fin a) (k : Fin c),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

def scalarAlgorithm (F : Type*) [Field F] : MatrixAlgorithm F 1 1 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct (F : Type*) [Field F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost (F : Type*) [Field F] : (scalarAlgorithm F).cost = 1 := rfl

theorem one_le_innerSize {n : ℕ} (hn : 1 ≤ n) (k : ℝ) : 1 ≤ innerSize n k := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) k

@[simp] theorem innerSize_zero (n : ℕ) : innerSize n 0 = 1 := by
  simp [innerSize]

@[simp] theorem innerSize_one (n : ℕ) : innerSize n 1 = n := by
  simp [innerSize]

theorem innerSize_mono {n : ℕ} (hn : 1 ≤ n) {k l : ℝ} (hkl : k ≤ l) :
    innerSize n k ≤ innerSize n l := by
  exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hkl)

theorem innerSize_le_pow {a b n t : ℕ} {k : ℝ} (hk : 0 ≤ k)
    (hn : n ≤ a ^ t) (hab : (a : ℝ) ^ k ≤ b) : innerSize n k ≤ b ^ t := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ k ≤ ((a ^ t : ℕ) : ℝ) ^ k :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hk
    _ = ((a : ℝ) ^ k) ^ t := by
      rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    _ ≤ (b : ℝ) ^ t := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
    _ = ((b ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]

theorem innerSize_cast_le {n : ℕ} (hn : 1 ≤ n) {k : ℝ} (hk : 0 ≤ k) :
    (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  have hpow : 1 ≤ (n : ℝ) ^ k := Real.one_le_rpow (by exact_mod_cast hn) hk
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) k)).le
  change (⌈(n : ℝ) ^ k⌉₊ : ℝ) ≤ _
  linarith

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule013
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.NaiveAlgorithm -/
section FlattenModule014


namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression Input) → Expression Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression Input) (inputs : Input → ℂ) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

def naiveEntry {n : ℕ} (i k : Fin n) : Expression (MatrixInput n) :=
  Expression.sumFin fun j : Fin n =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {n : ℕ} (i k : Fin n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {n : ℕ} (i k : Fin n) :
    (naiveEntry i k).cost = 2 * n := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

def naiveAlgorithm (n : ℕ) : MatrixAlgorithm n :=
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (n : ℕ) : (naiveAlgorithm n).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (n : ℕ) : (naiveAlgorithm n).cost = 2 * n ^ 3 := by
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (n : ℕ) : (naiveAlgorithm n).cost ≤ 2 * n ^ 3 :=
  (naiveAlgorithm_cost n).le

theorem admissibleExponent_three : AdmissibleExponent 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n, naiveAlgorithm_correct n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n ^ 3 : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n ^ 3 : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule014
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.NaiveAlgorithm -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.LowerBound -/
section FlattenModule015



namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Program

theorem eval_eq_constant_or_input_of_cost_eq_zero {Input : Type*} {r : ℕ}
    (p : Program Input r) (hp : p.cost = 0) (i : Fin r) :
    (∃ z : ℂ, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert hp i
  induction p with
  | nil =>
    intro _ i
    exact Fin.elim0 i
  | @step r p g ih =>
    intro hp i
    have hcost : p.cost + g.cost = 0 := hp
    have hp0 : p.cost = 0 := by omega
    have hg0 : g.cost = 0 := by omega
    refine Fin.cases ?_ (fun j => ?_) i
    · cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hg0
      | sub a b => simp [Gate.cost] at hg0
      | mul a b => simp [Gate.cost] at hg0
    · simpa only [eval_step_succ] using ih hp0 j

end Program

namespace MatrixAlgorithm

theorem one_le_cost {n : ℕ} (P : MatrixAlgorithm n) (hn : 1 ≤ n)
    (hP : P.Correct) : 1 ≤ P.cost := by
  by_contra hcost
  have hzero : P.program.cost = 0 := by
    change ¬ 1 ≤ P.program.cost at hcost
    omega
  let i : Fin n := ⟨0, by omega⟩
  have hentry (A B : Matrix (Fin n) (Fin n) ℂ) :
      P.program.eval (matrixInputs A B) (P.output i i) = (A * B) i i :=
    congrFun (congrFun (hP A B) i) i
  rcases P.program.eval_eq_constant_or_input_of_cost_eq_zero hzero (P.output i i)
      with ⟨z, hz⟩ | ⟨a, ha⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry 1 1
      rw [hz] at h
      simpa using h
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (hz0.symm.trans hz1)
  · rcases a with ⟨j, k⟩ | ⟨j, k⟩
    · have h := hentry (Matrix.of fun _ _ => 1) 0
      rw [ha] at h
      simp [matrixInputs, Matrix.mul_apply] at h
    · have h := hentry 0 (Matrix.of fun _ _ => 1)
      rw [ha] at h
      simp [matrixInputs, Matrix.mul_apply] at h

end MatrixAlgorithm

theorem admissibleExponent_nonneg {τ : ℝ} (hτ : AdmissibleExponent τ) : 0 ≤ τ := by
  by_contra hneg
  have hτneg : τ < 0 := lt_of_not_ge hneg
  let ε : ℝ := -τ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsum : τ + ε = -ε := by dsimp [ε]; ring
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hcostone : (1 : ℝ) ≤ P.cost :=
    (Nat.one_le_cast (α := ℝ)).mpr (P.one_le_cost hn1 hP)
  rw [hsum, Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv] at hcost
  have hsmall : C / (n : ℝ) ^ ε < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hnpos ε)).mpr hpow
  exact (not_lt_of_ge (hcostone.trans hcost)) hsmall

theorem admissibleExponent_bddBelow : BddBelow {τ : ℝ | AdmissibleExponent τ} := by
  refine ⟨0, ?_⟩
  intro τ hτ
  exact admissibleExponent_nonneg hτ

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule015
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.LowerBound -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Exponent -/
section FlattenModule016


namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem omega_le_of_admissibleExponent {τ : ℝ} (hτ : AdmissibleExponent τ) :
    omega ≤ τ :=
  csInf_le admissibleExponent_bddBelow hτ

theorem omega_nonneg : 0 ≤ omega :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_nonneg hτ)

theorem omega_le_three : omega ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

theorem omega_admissibleExponent : AdmissibleExponent omega := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt admissibleExponent_nonempty
    (show sInf {σ : ℝ | AdmissibleExponent σ} < omega + ε / 2 from
      lt_add_of_pos_right omega hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent τ ↔ omega ≤ τ :=
  ⟨omega_le_of_admissibleExponent, omega_admissibleExponent.mono⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end OAI

end FlattenModule016
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Exponent -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compatibility -/
section FlattenModule017


namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {Input Register : Type*}

def toLegacy : Gate ℂ Input Register → MatrixMultiplication.Foundation.Arithmetic.Gate Input Register
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

def ofLegacy : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register → Gate ℂ Input Register
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_toLegacy (g : Gate ℂ Input Register)
    (inputs : Input → ℂ) (registers : Register → ℂ) :
    g.toLegacy.eval inputs registers = g.eval inputs registers := by
  cases g <;> rfl

@[simp] theorem cost_toLegacy (g : Gate ℂ Input Register) : g.toLegacy.cost = g.cost := by
  cases g <;> rfl

@[simp] theorem eval_ofLegacy (g : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register)
    (inputs : Input → ℂ) (registers : Register → ℂ) :
    (ofLegacy g).eval inputs registers = g.eval inputs registers := by
  cases g <;> rfl

@[simp] theorem cost_ofLegacy (g : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register) :
    (ofLegacy g).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def toLegacy : {r : ℕ} → Program ℂ Input r → MatrixMultiplication.Foundation.Arithmetic.Program Input r
  | 0, .nil => .nil
  | _ + 1, .step p g => p.toLegacy.step g.toLegacy

def ofLegacy : {r : ℕ} → MatrixMultiplication.Foundation.Arithmetic.Program Input r → Program ℂ Input r
  | 0, .nil => .nil
  | _ + 1, .step p g => (ofLegacy p).step (Gate.ofLegacy g)

@[simp] theorem eval_toLegacy {r : ℕ} (p : Program ℂ Input r) (inputs : Input → ℂ) :
    p.toLegacy.eval inputs = p.eval inputs := by
  induction p with
  | nil => rfl
  | step p g ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_zero,
        eval_step_zero, Gate.eval_toLegacy, ih]
    · simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_succ,
        eval_step_succ, ih]

@[simp] theorem cost_toLegacy {r : ℕ} (p : Program ℂ Input r) : p.toLegacy.cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.cost_step,
      cost_step, Gate.cost_toLegacy, ih]

@[simp] theorem eval_ofLegacy {r : ℕ}
    (p : MatrixMultiplication.Foundation.Arithmetic.Program Input r) (inputs : Input → ℂ) :
    (ofLegacy p).eval inputs = p.eval inputs := by
  induction p with
  | nil => rfl
  | step p g ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_zero,
        eval_step_zero, Gate.eval_ofLegacy, ih]
    · simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_succ,
        eval_step_succ, ih]

@[simp] theorem cost_ofLegacy {r : ℕ}
    (p : MatrixMultiplication.Foundation.Arithmetic.Program Input r) : (ofLegacy p).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.cost_step,
      cost_step, Gate.cost_ofLegacy, ih]

end Program

namespace MatrixAlgorithm

def toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n) :
    MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n :=
  ⟨P.registers, P.program.toLegacy, P.output⟩

def ofLegacy {n : ℕ} (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n) :
    MatrixAlgorithm ℂ n n n :=
  ⟨P.registers, Program.ofLegacy P.program, P.output⟩

@[simp] theorem eval_toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : P.toLegacy.eval A B = P.eval A B := by
  funext i k
  have hin : MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B = matrixInputs A B := by
    funext x
    cases x <;> rfl
  change P.program.toLegacy.eval (MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B)
    (P.output i k) = P.program.eval (matrixInputs A B) (P.output i k)
  rw [hin]
  exact congrFun (P.program.eval_toLegacy (matrixInputs A B)) (P.output i k)

@[simp] theorem eval_ofLegacy {n : ℕ}
    (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : (ofLegacy P).eval A B = P.eval A B := by
  funext i k
  have hin : MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B = matrixInputs A B := by
    funext x
    cases x <;> rfl
  change (Program.ofLegacy P.program).eval (matrixInputs A B) (P.output i k) =
    P.program.eval (MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B) (P.output i k)
  rw [hin]
  exact congrFun (Program.eval_ofLegacy P.program (matrixInputs A B)) (P.output i k)

theorem toLegacy_correct {n : ℕ} {P : MatrixAlgorithm ℂ n n n}
    (hP : P.Correct) : P.toLegacy.Correct := by
  intro A B
  exact (P.eval_toLegacy A B).trans (hP A B)

theorem ofLegacy_correct {n : ℕ} {P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n}
    (hP : P.Correct) : (ofLegacy P).Correct := by
  intro A B
  exact (eval_ofLegacy P A B).trans (hP A B)

@[simp] theorem cost_toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n) :
    P.toLegacy.cost = P.cost := P.program.cost_toLegacy

@[simp] theorem cost_ofLegacy {n : ℕ}
    (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n) :
    (ofLegacy P).cost = P.cost := Program.cost_ofLegacy P.program

end MatrixAlgorithm

theorem complex_admissibleExponent_iff (τ : ℝ) :
    AdmissibleExponent ℂ τ ↔ MatrixMultiplication.Foundation.Arithmetic.AdmissibleExponent τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    obtain ⟨P, hP, hcost⟩ := hbound n hn
    exact ⟨P.toLegacy, MatrixAlgorithm.toLegacy_correct hP, by simpa using hcost⟩
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    obtain ⟨P, hP, hcost⟩ := hbound n hn
    exact ⟨MatrixAlgorithm.ofLegacy P, MatrixAlgorithm.ofLegacy_correct hP,
      by simpa using hcost⟩

theorem complex_omega_eq : omega ℂ = MatrixMultiplication.Foundation.Arithmetic.omega := by
  unfold omega MatrixMultiplication.Foundation.Arithmetic.omega
  congr 1
  ext τ
  exact complex_admissibleExponent_iff τ

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule017
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compatibility -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs -/
section FlattenModule018


namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Gate

variable {Input R S : Type*}

def mapRegister (f : R → S) : Gate F Input R → Gate F Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

theorem eval_mapRegister (g : Gate F Input R) (f : R → S)
    (inputs : Input → F) (registers : S → F) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

omit [Field F] in
@[simp] theorem cost_mapRegister (g : Gate F Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

def append {r : ℕ} (p : Program F Input r) : {s : ℕ} → Program F Input s → Program F Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

theorem eval_append_new {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

theorem eval_append_old {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

omit [Field F] in
@[simp] theorem cost_append {r s : ℕ} (p : Program F Input r) (q : Program F Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

inductive Expression (F Input : Type*) where
  | constant : F → Expression F Input
  | input : Input → Expression F Input
  | add : Expression F Input → Expression F Input → Expression F Input
  | sub : Expression F Input → Expression F Input → Expression F Input
  | mul : Expression F Input → Expression F Input → Expression F Input

namespace Expression

variable {Input : Type*}

def eval (inputs : Input → F) : Expression F Input → F
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

def cost : Expression F Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

structure Compiled (e : Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

def compile : (e : Expression F Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression
end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule018
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily -/
section FlattenModule019



namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic.Expression

variable {F : Type*} [Field F]

variable {Input Output : Type*}

structure CompiledFamily [Fintype Output] (expressions : Output → Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression F Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

def compileFamily [Fintype Output] (expressions : Output → Expression F Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Arithmetic.Expression

end

end OAI

end FlattenModule019
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm -/
section FlattenModule020


namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression F Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

def naiveEntry {a b c : ℕ} (i : Fin a) (k : Fin c) : Expression F (MatrixInput a b c) :=
  Expression.sumFin fun j : Fin b =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {a b c : ℕ} (i : Fin a) (k : Fin c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {a b c : ℕ} (i : Fin a) (k : Fin c) :
    (naiveEntry (F := F) (b := b) i k).cost = 2 * b := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

def naiveAlgorithm (a b c : ℕ) : MatrixAlgorithm F a b c :=
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (b := b) ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (a b c : ℕ) : (naiveAlgorithm (F := F) a b c).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost = 2 * a * b * c := by
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost ≤ 2 * a * b * c :=
  (naiveAlgorithm_cost a b c).le

theorem admissibleExponent_three : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n n n, naiveAlgorithm_correct n n n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          push_cast
          ring
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule020
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound -/
section FlattenModule021




namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Program

variable {F Input : Type*}

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => simp [registerCost, cost]
  | step p g ih => simp [registerCost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Field F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert i
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      change g.cost = 0 at hi
      cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hi
      | sub a b => simp [Gate.cost] at hi
      | mul a b => simp [Gate.cost] at hi
    · intro hi
      simpa only [eval_step_succ] using ih j hi

end Program

section ElementaryMatrices

variable {F : Type*} [Field F] {a b c : ℕ}

def elementaryLeft (i : Fin a) (j : Fin b) : Matrix (Fin a) (Fin b) F :=
  fun x y => if x = i then if y = j then 1 else 0 else 0

def elementaryRight (j : Fin b) (k : Fin c) : Matrix (Fin b) (Fin c) F :=
  fun y z => if z = k then if y = j then 1 else 0 else 0

theorem elementaryProduct (i x : Fin a) (j : Fin b) (k z : Fin c) :
    (elementaryLeft (F := F) i j * elementaryRight (F := F) j k) x z =
      if (x, z) = (i, k) then 1 else 0 := by
  by_cases hi : x = i <;> by_cases hk : z = k <;>
    simp [Matrix.mul_apply, elementaryLeft, elementaryRight, hi, hk]

end ElementaryMatrices

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem output_injective (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : Function.Injective (fun o : Fin a × Fin c => P.output o.1 o.2) := by
  classical
  intro x y hxy
  change P.output x.1 x.2 = P.output y.1 y.2 at hxy
  let j : Fin b := ⟨0, by omega⟩
  let A := elementaryLeft (F := F) x.1 j
  let B := elementaryRight (F := F) j x.2
  have hx := congrFun (congrFun (hP A B) x.1) x.2
  have hy := congrFun (congrFun (hP A B) y.1) y.2
  have heq : (A * B) x.1 x.2 = (A * B) y.1 y.2 := by
    rw [← hx, ← hy]
    change P.program.eval (matrixInputs A B) (P.output x.1 x.2) =
      P.program.eval (matrixInputs A B) (P.output y.1 y.2)
    rw [hxy]
  simp only [A, B, elementaryProduct, Prod.eta, ite_true] at heq
  by_contra hne
  have hyx : y ≠ x := Ne.symm hne
  simp [hyx] at heq

theorem one_le_output_registerCost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    1 ≤ P.program.registerCost (P.output i k) := by
  by_contra hn
  have hzero : P.program.registerCost (P.output i k) = 0 := by omega
  let j : Fin b := ⟨0, by omega⟩
  have hentry (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
      P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun (congrFun (hP A B) i) k
  rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
      (P.output i k) hzero with ⟨z, hz⟩ | ⟨u, hu⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry (elementaryLeft i j) (elementaryRight j k)
      rw [hz] at h
      simpa only [elementaryProduct, ite_true] using h
    exact (zero_ne_one : (0 : F) ≠ 1) (hz0.symm.trans hz1)
  · rcases u with ⟨x, y⟩ | ⟨y, z⟩
    · have h := hentry (Matrix.of fun _ _ => 1) 0
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h
    · have h := hentry 0 (Matrix.of fun _ _ => 1)
      rw [hu] at h
      simp [matrixInputs, Matrix.mul_apply] at h

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  classical
  let f : Fin a × Fin c → Fin P.registers := fun o => P.output o.1 o.2
  have hf : Function.Injective f := P.output_injective hb hP
  calc
    a * c = ∑ _o : Fin a × Fin c, (1 : ℕ) := by simp
    _ ≤ ∑ o : Fin a × Fin c, P.program.registerCost (f o) := by
      apply Finset.sum_le_sum
      intro o ho
      exact P.one_le_output_registerCost hb hP o.1 o.2
    _ = ∑ r ∈ Finset.univ.image f, P.program.registerCost r := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑ r, P.program.registerCost r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = P.cost := P.program.sum_registerCost

end MatrixAlgorithm

theorem rectangularAdmissibleExponent_two_le {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : 2 ≤ τ := by
  by_contra hneg
  have hτlt : τ < 2 := lt_of_not_ge hneg
  let ε : ℝ := (2 - τ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hlower : (n : ℝ) ^ (2 : ℕ) ≤ P.cost := by
    have h : n ^ 2 ≤ P.cost := by
      simpa [pow_two] using P.output_size_le_cost (one_le_innerSize hn1 k) hP
    exact_mod_cast h
  have hstrict : (n : ℝ) ^ (2 : ℕ) < (n : ℝ) ^ (2 : ℕ) := calc
    (n : ℝ) ^ (2 : ℕ) ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hnpos]
      have he : ε + (τ + ε) = 2 := by dsimp [ε]; ring
      rw [he]
      norm_num
  exact (lt_irrefl _ hstrict)

theorem rectangularAdmissibleExponent_bddBelow (F : Type*) [Field F] (k : ℝ) :
    BddBelow {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2, fun _ h => rectangularAdmissibleExponent_two_le h⟩

theorem rectangularOmega_le_of_admissibleExponent {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : rectangularOmega F k ≤ τ :=
  csInf_le (rectangularAdmissibleExponent_bddBelow F k) hτ

theorem admissibleExponent_iff_rectangular_one (F : Type*) [Field F] (τ : ℝ) :
    AdmissibleExponent F τ ↔ RectangularAdmissibleExponent F 1 τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    rw [innerSize_one]
    exact hbound n hn
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hnBound := hbound n hn
    rw [innerSize_one] at hnBound
    exact hnBound

theorem admissibleExponent_two_le {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ :=
  rectangularAdmissibleExponent_two_le ((admissibleExponent_iff_rectangular_one F τ).mp hτ)

theorem admissibleExponent_bddBelow (F : Type*) [Field F] :
    BddBelow {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨2, fun _ h => admissibleExponent_two_le h⟩

theorem omega_le_of_admissibleExponent {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : omega F ≤ τ :=
  csInf_le (admissibleExponent_bddBelow F) hτ

@[simp] theorem rectangularOmega_one (F : Type*) [Field F] :
    rectangularOmega F 1 = omega F := by
  unfold rectangularOmega omega
  congr 1
  ext τ
  exact (admissibleExponent_iff_rectangular_one F τ).symm

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule021
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition -/
section FlattenModule022

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Gate

variable {Input Input' Register : Type*}

def mapInput (f : Input → Input') : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => .input (f i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapInput (f : Input → Input') (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapInput f).eval inputs registers = g.eval (inputs ∘ f) registers := by
  cases g <;> rfl

omit [Field F] in
@[simp] theorem cost_mapInput (f : Input → Input') (g : Gate F Input Register) :
    (g.mapInput f).cost = g.cost := by
  cases g <;> rfl

def mapSource (f : Input → Input' ⊕ F) : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapSource f).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, eval]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

omit [Field F] in
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register) :
    (g.mapSource f).cost = g.cost := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, cost]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

end Gate

namespace Program

variable {Input Input' Mid : Type*}

def mapInput (f : Input → Input') : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapInput f).step (g.mapInput f)

@[simp] theorem eval_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r)
    (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapInput f).eval inputs i = p.eval (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapInput, eval_step_zero, Gate.eval_mapInput]
      rw [funext ih]
    · exact ih j

omit [Field F] in
@[simp] theorem cost_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r) :
    (p.mapInput f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapInput, cost_step, Gate.cost_mapInput, ih]

def mapSource (f : Input → Input' ⊕ F) : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapSource f).step (g.mapSource f)

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapSource, eval_step_zero, Gate.eval_mapSource]
      rw [funext ih]
    · exact ih j

omit [Field F] in
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapSource, cost_step, Gate.cost_mapSource, ih]

structure Substituted {r s : ℕ} (p : Program F Input r) (q : Program F Mid s)
    (wires : Mid → Fin r) where
  registers : ℕ
  program : Program F Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

namespace Substituted

def step {r s : ℕ} {p : Program F Input r} {q : Program F Mid s}
    {wires : Mid → Fin r} (a : Substituted p q wires)
    (g : Gate F Mid (Fin s)) (h : Gate F Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => p.eval inputs (wires j))
        (q.eval (fun j => p.eval inputs (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput := fun i => (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := by
    intro inputs i
    exact a.correctOld inputs i
  correct := by
    intro inputs i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heval inputs
    · exact a.correct inputs j
  cost_eq := by
    simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

end Substituted

def substitute {r : ℕ} (p : Program F Input r) :
    {s : ℕ} → (q : Program F Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { registers := r
      program := p
      oldOutput := id
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := by simp only [cost, Nat.add_zero] }
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      { registers := a.registers
        program := a.program
        oldOutput := a.oldOutput
        output := Fin.cases (a.oldOutput (wires j)) a.output
        correctOld := a.correctOld
        correct := by
          intro inputs i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact a.correctOld inputs (wires j)
          · exact a.correct inputs k
        cost_eq := by
          simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq }
    | .constant z =>
      a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j =>
      a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j =>
      a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j =>
      a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

end Program

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule022
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding -/
section FlattenModule023

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

def zeroPadMatrix {a b : ℕ} (A B : ℕ) (M : Matrix (Fin a) (Fin b) F) :
    Matrix (Fin A) (Fin B) F :=
  fun i j => if hi : i.val < a then
    if hj : j.val < b then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (M : Matrix (Fin a) (Fin b) F) (i : Fin a) (j : Fin b) :
    zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) = M i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → F)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F)
    (i : Fin a) (k : Fin c) :
    (zeroPadMatrix A B M * zeroPadMatrix B C N) (Fin.castLE ha i) (Fin.castLE hc k) =
      (M * N) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin B,
        zeroPadMatrix A B M (Fin.castLE ha i) j *
          zeroPadMatrix B C N j (Fin.castLE hc k)) =
        ∑ j : Fin b,
          zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) *
            zeroPadMatrix B C N (Fin.castLE hb j) (Fin.castLE hc k) := by
      apply sum_fin_castLE_of_zero hb
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin b, M i j * N j k := by simp

def padSource {a b c A B C : ℕ} : MatrixInput A B C → MatrixInput a b c ⊕ F
  | .inl (i, j) => if hi : i.val < a then
      if hj : j.val < b then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (j, k) => if hj : j.val < b then
      if hk : k.val < c then .inl (.inr (⟨j.val, hj⟩, ⟨k.val, hk⟩)) else .inr 0
    else .inr 0

theorem padSource_eval {a b c A B C : ℕ}
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F) :
    (fun x : MatrixInput A B C => Sum.elim (matrixInputs M N) id (padSource x)) =
      matrixInputs (zeroPadMatrix A B M) (zeroPadMatrix B C N) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨j, k⟩
  · by_cases hi : i.val < a <;> by_cases hj : j.val < b <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]
  · by_cases hj : j.val < b <;> by_cases hk : k.val < c <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hj, hk]

namespace MatrixAlgorithm

def pad {a b c A B C : ℕ} (ha : a ≤ A) (_hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : MatrixAlgorithm F a b c where
  registers := P.registers
  program := P.program.mapSource (padSource (a := a) (b := b) (c := c))
  output := fun i k => P.output (Fin.castLE ha i) (Fin.castLE hc k)

theorem pad_correct {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    {P : MatrixAlgorithm F A B C} (hP : P.Correct) : (pad ha hb hc P).Correct := by
  intro M N
  funext i k
  change (P.program.mapSource (padSource (a := a) (b := b) (c := c))).eval
    (matrixInputs M N) (P.output (Fin.castLE ha i) (Fin.castLE hc k)) = (M * N) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix A B M) (zeroPadMatrix B C N)) (Fin.castLE ha i)) (Fin.castLE hc k)
  exact hentry.trans (zeroPadMatrix_mul ha hb hc M N i k)

@[simp] theorem pad_cost_eq {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : (pad ha hb hc P).cost = P.cost :=
  Program.cost_mapSource (padSource (a := a) (b := b) (c := c)) P.program

theorem exists_restrict {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F a b c, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad ha hb hc P, pad_correct ha hb hc hP, (pad_cost_eq ha hb hc P).le⟩

end MatrixAlgorithm

theorem RectangularAdmissibleExponent.mono_aspect {k l τ : ℝ}
    (h : RectangularAdmissibleExponent F l τ) (hkl : k ≤ l) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  obtain ⟨Q, hQ, hcostQ⟩ := MatrixAlgorithm.exists_restrict (le_refl n)
    (innerSize_mono hn hkl) (le_refl n) P hP
  exact ⟨Q, hQ, (Nat.cast_le.mpr hcostQ).trans hcost⟩

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule023
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent -/
section FlattenModule024



namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent F τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent F σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem omega_two_le : 2 ≤ omega F :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_two_le hτ)

theorem omega_nonneg : 0 ≤ omega F := le_trans (by norm_num) omega_two_le

theorem omega_le_three : omega F ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

theorem omega_admissibleExponent : AdmissibleExponent F (omega F) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt admissibleExponent_nonempty
    (show sInf {σ : ℝ | AdmissibleExponent F σ} < omega F + ε / 2 from
      lt_add_of_pos_right (omega F) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent F τ ↔ omega F ≤ τ :=
  ⟨omega_le_of_admissibleExponent, omega_admissibleExponent.mono⟩

theorem RectangularAdmissibleExponent.mono {k τ σ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) (hτσ : τ ≤ σ) :
    RectangularAdmissibleExponent F k σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem rectangularAdmissibleExponent_of_uniform_costs {k τ C : ℝ} (hC : 0 < C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (le_add_of_nonneg_right hε.le)

theorem rectangularAdmissibleExponent_naive (k : ℝ) :
    RectangularAdmissibleExponent F k (2 + max k 0) := by
  apply rectangularAdmissibleExponent_of_uniform_costs (C := 4) (by norm_num)
  intro n hn
  refine ⟨naiveAlgorithm n (innerSize n k) n,
    naiveAlgorithm_correct n (innerSize n k) n, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ max k 0 :=
    (Nat.cast_le.mpr (innerSize_mono hn (le_max_left k 0))).trans
      (innerSize_cast_le hn (le_max_right k 0))
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (n : ℝ) * innerSize n k * n = 2 * (n : ℝ) ^ 2 * innerSize n k := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ max k 0) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * (n : ℝ) ^ (2 + max k 0) := by
      rw [Real.rpow_add hnpos]
      norm_num
      ring

theorem rectangularAdmissibleExponent_nonempty (k : ℝ) :
    Set.Nonempty {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2 + max k 0, rectangularAdmissibleExponent_naive k⟩

theorem rectangularOmega_two_le (k : ℝ) : 2 ≤ rectangularOmega F k :=
  le_csInf (rectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => rectangularAdmissibleExponent_two_le hτ)

theorem rectangularOmega_admissibleExponent (k : ℝ) :
    RectangularAdmissibleExponent F k (rectangularOmega F k) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt (rectangularAdmissibleExponent_nonempty k)
    (show sInf {σ : ℝ | RectangularAdmissibleExponent F k σ} <
        rectangularOmega F k + ε / 2 from lt_add_of_pos_right (rectangularOmega F k) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem rectangularAdmissibleExponent_iff_omega_le {k τ : ℝ} :
    RectangularAdmissibleExponent F k τ ↔ rectangularOmega F k ≤ τ :=
  ⟨rectangularOmega_le_of_admissibleExponent, (rectangularOmega_admissibleExponent k).mono⟩

theorem rectangularOmega_mono {k l : ℝ} (hkl : k ≤ l) :
    rectangularOmega F k ≤ rectangularOmega F l :=
  rectangularOmega_le_of_admissibleExponent
    ((rectangularOmega_admissibleExponent l).mono_aspect hkl)

@[simp] theorem rectangularOmega_zero : rectangularOmega F 0 = 2 := by
  apply le_antisymm _ (rectangularOmega_two_le 0)
  apply rectangularOmega_le_of_admissibleExponent
  simpa using (rectangularAdmissibleExponent_naive (F := F) 0)

theorem complexAlpha_set_nonempty :
    Set.Nonempty {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨0, ⟨by norm_num, by norm_num⟩, rectangularOmega_zero⟩

theorem complexAlpha_set_bddAbove :
    BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨1, fun _ h => h.1.2⟩

theorem le_complexAlpha {k : ℝ} (hk : k ∈ Set.Icc 0 1)
    (hω : rectangularOmega ℂ k = 2) : k ≤ complexAlpha :=
  le_csSup complexAlpha_set_bddAbove ⟨hk, hω⟩

theorem complexAlpha_le_one : complexAlpha ≤ 1 :=
  csSup_le complexAlpha_set_nonempty (fun _ h => h.1.2)

theorem complexAlpha_nonneg : 0 ≤ complexAlpha :=
  le_complexAlpha ⟨le_refl 0, by norm_num⟩ rectangularOmega_zero

end MatrixMultiplication.Arithmetic

end

end OAI

end FlattenModule024
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent -/
section FlattenModule025




namespace OAI

/-!
# From exact tensor rank to arithmetic complexity

This file supplies the arithmetic conversion in Section 6.2.  It uses the
existing division-free straight-line programs over `ℂ`: loading inputs and
constants is free, and each scalar addition, subtraction, or multiplication
costs one.  Correctness means matrix multiplication on every pair of inputs.

The substantive tensor estimates are separate.  Here `omega` is an alias for
the existing arithmetic exponent, and the general bridge proves
`omega ≤ exactRankExponent`.  Thus any independently established upper bound
on the exact-rank exponent gives an arithmetic bound with every positive
exponent slack.  No particular numerical upper bound is assumed or asserted.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- The arithmetic matrix multiplication exponent over the complex numbers,
in the repository's existing scalar-operation model. -/
abbrev omega : ℝ := MatrixMultiplication.Arithmetic.omega ℂ

/-- A uniform scalar-operation bound with arbitrary positive exponent slack. -/
abbrev ArithmeticBound (τ : ℝ) : Prop :=
  MatrixMultiplication.Arithmetic.AdmissibleExponent ℂ τ

/-- The existing arithmetic exponent is itself admissible; hence its infimum
has exactly the expected upper-bound interpretation. -/
theorem arithmeticBound_iff_omega_le {τ : ℝ} :
    ArithmeticBound τ ↔ omega ≤ τ :=
  MatrixMultiplication.Arithmetic.admissibleExponent_iff_omega_le

/-- Expanded form of the arithmetic statement, including its quantifier order
and the correctness and operation cost of the resulting programs. -/
theorem arithmeticComplexity_iff_omega_le {τ : ℝ} :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ P : MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ n n n,
          P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)) ↔ omega ≤ τ :=
  arithmeticBound_iff_omega_le

/-- A finite exact decomposition gives an arithmetic bound by block
substitution, including all the scalar operations in the linear combinations,
followed by padding to arbitrary positive sizes. -/
theorem arithmeticBound_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    ArithmeticBound τ :=
  (MatrixMultiplication.Arithmetic.complex_admissibleExponent_iff τ).mpr
    (MatrixMultiplication.Foundation.Arithmetic.admissibleExponent_of_rankAtMost hn hRank hτ hR)

theorem omega_le_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    omega ≤ τ :=
  arithmeticBound_iff_omega_le.mp (arithmeticBound_of_rankAtMost hn hRank hτ hR)

/-- The quadratic rank lower bound pays for the quadratic block-combination
overhead, including the boundary case of rank exactly `n²`. -/
theorem omega_le_logb_rank {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R) :
    omega ≤ Real.logb (n : ℝ) (R : ℝ) := by
  have hquad : n ^ 2 ≤ R := matrixMultiplication_rank_lower (by omega) hRank
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans hn1
  have hR0 : 0 < (R : ℝ) := by
    have : 0 < n ^ 2 := pow_pos (by omega : 0 < n) _
    exact_mod_cast (this.trans_le hquad)
  have hτ : 2 ≤ Real.logb (n : ℝ) (R : ℝ) := by
    apply (Real.le_logb_iff_rpow_le hn1 hR0).mpr
    simpa only [Real.rpow_two, Nat.cast_pow] using
      (Nat.cast_le.mpr hquad : ((n ^ 2 : ℕ) : ℝ) ≤ (R : ℝ))
  exact omega_le_of_rankAtMost hn hRank hτ
    (Real.rpow_logb hn0 (ne_of_gt hn1) hR0).symm.le

/-- Near-optimal finite blocks suffice: no finite decomposition is required
to attain the limiting exponent. -/
theorem arithmeticBound_of_arbitrarily_close_rankBounds {τ : ℝ} (hτ : 2 ≤ τ)
    (hRank : ∀ δ : ℝ, 0 < δ → ∃ n R : ℕ, 2 ≤ n ∧
      Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R ∧
        (R : ℝ) ≤ (n : ℝ) ^ (τ + δ)) : ArithmeticBound τ := by
  apply arithmeticBound_iff_omega_le.mpr
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨n, R, hn, hRank, hR⟩ := hRank δ hδ
  exact omega_le_of_rankAtMost hn hRank (by linarith) hR

/-- The arithmetic exponent is bounded by each exact finite-block exponent. -/
theorem omega_le_exactMatrixRank_logb {n : ℕ} (hn : 2 ≤ n) :
    omega ≤ Real.logb (n : ℝ) (exactMatrixRank n : ℝ) :=
  omega_le_logb_rank hn (exactMatrixRank_spec n)

/-- General exact-rank-to-arithmetic bridge.  The proof uses a lower bound for
every finite-block exponent, so it does not require attainment of the infimum. -/
theorem omega_le_exactRankExponent : omega ≤ exactRankExponent := by
  apply le_csInf exactRankExponentSet_nonempty
  rintro τ ⟨n, hn, rfl⟩
  exact omega_le_exactMatrixRank_logb hn

theorem arithmeticBound_exactRankExponent : ArithmeticBound exactRankExponent :=
  arithmeticBound_iff_omega_le.mpr omega_le_exactRankExponent

/-- Any upper bound on the exact-rank exponent gives the same arithmetic
exponent bound, with arbitrary positive slack. -/
theorem arithmeticBound_of_exactRankExponent_le {τ : ℝ}
    (hτ : exactRankExponent ≤ τ) : ArithmeticBound τ :=
  arithmeticBound_iff_omega_le.mpr (omega_le_exactRankExponent.trans hτ)

/-- Explicit epsilon-complexity conclusion from an exact-rank exponent bound. -/
theorem arithmeticComplexity_of_exactRankExponent_le {τ : ℝ}
    (hτ : exactRankExponent ≤ τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε) :=
  arithmeticBound_of_exactRankExponent_le hτ ε hε

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule025
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.NormalizedStates -/
section FlattenModule026


namespace OAI

/-!
# Compact convex spaces of normalized additive states

These are the closed linear constraints in Appendix A. The nonemptiness of
this state space, and its instantiation by the tensor restriction semiring,
are separate statements.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- Additive restriction-monotone states with a fixed detector inequality. -/
def normalizedStates (R : S → ℝ) (d : S) (k : ℝ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧
    (∀ x, k * f x ≤ f (d * x))}

theorem normalizedStates_isClosed (R : S → ℝ) (d : S) (k : ℝ) :
    IsClosed (normalizedStates R d k) := by
  unfold normalizedStates
  have hb : IsClosed {f : S → ℝ | ∀ x, 0 ≤ f x ∧ f x ≤ R x} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (continuous_apply x)).inter
      (isClosed_le (continuous_apply x) continuous_const)
  have hn : IsClosed {f : S → ℝ | f 1 = 1} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have ha : IsClosed {f : S → ℝ | ∀ x y, f (x + y) = f x + f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y))
        ((continuous_apply x).add (continuous_apply y))
  have hm : IsClosed {f : S → ℝ | ∀ x y, x ≤ y → f x ≤ f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_le (continuous_apply x) (continuous_apply y)
  have hd : IsClosed {f : S → ℝ | ∀ x, k * f x ≤ f (d * x)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_le (continuous_const.mul (continuous_apply x)) (continuous_apply (d * x))
  exact hb.inter (hn.inter (ha.inter (hm.inter hd)))

theorem normalizedStates_isCompact (R : S → ℝ) (d : S) (k : ℝ) :
    IsCompact (normalizedStates R d k) := by
  apply (isCompact_univ_pi (fun x => isCompact_Icc (a := (0 : ℝ)) (b := R x))).of_isClosed_subset
    (normalizedStates_isClosed R d k)
  intro f hf x _
  exact hf.1 x

theorem normalizedStates_convex (R : S → ℝ) (d : S) (k : ℝ) :
    Convex ℝ (normalizedStates R d k) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ a * f x + b * g x ∧ a * f x + b * g x ≤ R x
    constructor
    · exact add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1)
    · calc
        a * f x + b * g x ≤ a * R x + b * R x :=
          add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha)
            (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)
        _ = R x := by rw [← add_mul, hab, one_mul]
  · change a * f 1 + b * g 1 = 1
    rw [hf.2.1, hg.2.1, mul_one, mul_one, hab]
  · intro x y
    change a * f (x + y) + b * g (x + y) =
      (a * f x + b * g x) + (a * f y + b * g y)
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro x y hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 x y hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 x y hxy) hb)
  · intro x
    change k * (a * f x + b * g x) ≤ a * f (d * x) + b * g (d * x)
    calc
      k * (a * f x + b * g x) = a * (k * f x) + b * (k * g x) := by ring
      _ ≤ a * f (d * x) + b * g (d * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 x) ha)
          (mul_le_mul_of_nonneg_left (hg.2.2.2.2 x) hb)

theorem state_zero {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) : f 0 = 0 := by
  have h := hf.2.2.1 0 0
  rw [zero_add] at h
  linarith

theorem state_nat_mul {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) (n : ℕ) (x : S) :
    f ((n : S) * x) = (n : ℝ) * f x := by
  induction n with
  | zero => simp [state_zero hf]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hf.2.2.1, ih]
    push_cast
    ring

theorem state_one_le {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) {z : S} (hz : 1 ≤ z) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 1 z hz

/-- Translation followed by normalization preserves every state constraint.
The two order hypotheses are exactly those supplied by tensor multiplication
and the finite rank bound in the restriction semiring. -/
theorem state_rescale {R : S → ℕ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates (fun x => (R x : ℝ)) d k) (z : S)
    (hz : 1 ≤ z)
    (hmulmono : ∀ x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ x : S, z * x ≤ (R x : S) * z) :
    (fun x => f (z * x) / f z) ∈ normalizedStates (fun x => (R x : ℝ)) d k := by
  have hfz : 0 < f z := lt_of_lt_of_le zero_lt_one (state_one_le hf hz)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨div_nonneg (hf.1 (z * x)).1 hfz.le, ?_⟩
    apply (div_le_iff₀ hfz).mpr
    have h := hf.2.2.2.1 (z * x) ((R x : S) * z) (hdom x)
    simpa only [state_nat_mul hf] using h
  · simp [mul_one, ne_of_gt hfz]
  · intro x y
    change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · intro x y hxy
    exact div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (hmulmono x y hxy)) hfz.le
  · intro x
    have h := hf.2.2.2.2 (z * x)
    have hc : d * (z * x) = z * (d * x) := by ring
    rw [hc] at h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hfz.le

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule026
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.NormalizedStates -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalSpan -/
section FlattenModule027



namespace OAI

/-!
# Descent of rational linear systems

A rational linear system which has a real solution also has a rational solution.
The proof applies a rational-linear projection from the reals onto the rationals.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- A rational-linear functional on the reals taking `1` to `1`. -/
theorem exists_ratLinear_one :
    ∃ p : ℝ →ₗ[ℚ] ℚ, p 1 = 1 :=
  Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)

/-- A rational-linear projection from the reals to the rationals. -/
theorem exists_ratLinear_retraction :
    ∃ p : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, p (q : ℝ) = q := by
  obtain ⟨p, hp⟩ := exists_ratLinear_one
  refine ⟨p, fun q ↦ ?_⟩
  have h := p.map_smul q (1 : ℝ)
  simpa [hp] using h

/-- Solvability of a finite rational linear system descends from real to rational
coefficients. The set of equations need not be finite. -/
theorem exists_rat_solution_of_real {I : Type*} {J : Type*} [Fintype I]
    (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ q : I → ℚ, ∀ j, ∑ i, q i * A i j = b j := by
  obtain ⟨p, hp⟩ := exists_ratLinear_retraction
  obtain ⟨x, hx⟩ := h
  refine ⟨fun i ↦ p (x i), fun j ↦ ?_⟩
  have heq := congrArg p (hx j)
  simp only [map_sum, hp] at heq
  convert heq using 1
  apply Finset.sum_congr rfl
  intro i _
  have hmul := p.map_smul (A i j) (x i)
  simpa only [Rat.smul_def, smul_eq_mul, mul_comm] using hmul.symm

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule027
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalSpan -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalDenominators -/
section FlattenModule028



namespace OAI

/-!
# Clearing denominators in nonnegative rational families
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Every natural multiple of a denominator clears its nonnegative rational. -/
theorem exists_nat_eq_mul_rat_of_den_dvd {q : ℚ} (hq : 0 ≤ q)
    {D : ℕ} (hD : q.den ∣ D) :
    ∃ c : ℕ, (D : ℚ) * q = (c : ℚ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨k * q.num.toNat, ?_⟩
  have hnum : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  push_cast
  rw [hnum]
  calc
    (q.den : ℚ) * k * q = k * ((q.den : ℚ) * q) := by ring
    _ = k * (q.num : ℚ) := by rw [Rat.den_mul_eq_num]

/-- A finite nonnegative rational family has a common positive denominator
which turns every coefficient into a natural number. -/
theorem exists_nat_mul_eq_nat {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ, ∀ i, (D : ℚ) * q i = (c i : ℚ) := by
  classical
  let D : ℕ := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
  have hc : ∀ i, ∃ c : ℕ, (D : ℚ) * q i = (c : ℚ) := by
    intro i
    exact exists_nat_eq_mul_rat_of_den_dvd (hq i)
      (Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ i))
  choose c hc using hc
  exact ⟨D, hD, c, hc⟩

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule028
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalDenominators -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalCone -/
section FlattenModule029





namespace OAI

/-!+# Rational nonnegative certificates

Finite rational linear systems with a nonnegative real solution have a
nonnegative rational solution. Affinely independent convex representations
allow a rational-linear projection to preserve the coefficients exactly.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Coordinatewise inclusion of rational vectors into real vectors. -/
def rationalVectorCast {J : Type*} (v : J → ℚ) : J → ℝ := fun j ↦ v j

@[simp] theorem rationalVectorCast_apply {J : Type*} (v : J → ℚ) (j : J) :
    rationalVectorCast v j = (v j : ℝ) := rfl

/-- In an affinely independent rational family, the coefficients of a real
convex representation of a rational point are rational. -/
theorem exists_rat_convex_weights_of_affineIndependent
    {I J : Type*} [Fintype I] (v : I → J → ℚ) (b : J → ℚ)
    (w : I → ℝ)
    (hpos : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (heq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast b)
    (hind : AffineIndependent ℝ (fun i ↦ rationalVectorCast (v i))) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      ∑ i, q i • v i = b := by
  classical
  obtain ⟨p, hp⟩ := exists_ratLinear_retraction
  have hpone : p 1 = 1 := by simpa using hp 1
  let q : I → ℚ := fun i ↦ p (w i)
  have hqsum : ∑ i, q i = 1 := by
    simpa only [q, map_sum, hpone] using congrArg p hsum
  have hqeq : ∑ i, q i • v i = b := by
    funext j
    have hj := congrFun heq j
    simp only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] at hj
    have hj' := congrArg p hj
    simp only [map_sum, hp] at hj'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    convert hj' using 1
    apply Finset.sum_congr rfl
    intro i _
    have hm := p.map_smul (v i j) (w i)
    simpa only [q, Rat.smul_def, smul_eq_mul, mul_comm] using hm.symm
  have hqsumReal : ∑ i, (q i : ℝ) = 1 := by exact_mod_cast hqsum
  have hqeqReal :
      ∑ i, (q i : ℝ) • rationalVectorCast (v i) = rationalVectorCast b := by
    funext j
    have hj := congrFun hqeq j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
    simpa only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] using (show (∑ i, (q i : ℝ) * (v i j : ℝ)) = (b j : ℝ) by
        exact_mod_cast hj)
  have hqw : ∀ i, (q i : ℝ) = w i := by
    intro i
    exact hind.eq_of_sum_eq_sum (s := Finset.univ)
      (hqsumReal.trans hsum.symm) (hqeqReal.trans heq.symm) i (Finset.mem_univ i)
  refine ⟨q, ?_, hqsum, hqeq⟩
  intro i
  exact_mod_cast (hqw i ▸ hpos i : 0 ≤ (q i : ℝ))

/-- Taking the convex hull of rational vectors in real space does not create
new rational points. -/
theorem rationalVectorCast_mem_convexHull_descend
    {J : Type*} {s : Set (J → ℚ)} {b : J → ℚ}
    (h : rationalVectorCast b ∈ convexHull ℝ (rationalVectorCast '' s)) :
    b ∈ convexHull ℚ s := by
  classical
  obtain ⟨I, hI, z, w, hz, hind, hpos, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull h
  let : Fintype I := hI
  have hv : ∀ i, ∃ v ∈ s, rationalVectorCast v = z i := by
    intro i
    exact hz (Set.mem_range_self i)
  choose v hv hvc using hv
  obtain ⟨q, hqpos, hqsum, hqeq⟩ :=
    exists_rat_convex_weights_of_affineIndependent v b w (fun i ↦ (hpos i).le)
      hsum (by simpa only [hvc] using heq) (by simpa only [hvc] using hind)
  exact mem_convexHull_of_exists_fintype q v hqpos hqsum hv hqeq

/-- A rational point in the real cone generated by a finite rational family
already lies in the rational cone generated by that family. -/
theorem mem_rationalCone_of_nonneg_real_solution
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (x : I → ℝ) (hxpos : ∀ i, 0 ≤ x i)
    (hxeq : ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    b ∈ PointedCone.hull ℚ (Set.range A) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, x i)
  have hNpos : (0 : ℝ) < N :=
    (Finset.sum_nonneg fun i _ ↦ hxpos i).trans_lt hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hNrat : (N : ℚ) ≠ 0 := by exact_mod_cast hNne
  let scaled : J → ℚ := fun j ↦ b j / N
  let v : Option I → J → ℚ := fun i ↦ match i with
    | none => 0
    | some i => A i
  let w : Option I → ℝ := fun i ↦ match i with
    | none => 1 - (∑ i, x i) / N
    | some i => x i / N
  have hwpos : ∀ i, 0 ≤ w i := by
    intro i
    cases i with
    | none =>
      change 0 ≤ 1 - (∑ i, x i) / N
      exact sub_nonneg.mpr ((div_le_one hNpos).2 hN.le)
    | some i => exact div_nonneg (hxpos i) hNpos.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [Fintype.sum_option, w, ← Finset.sum_div]
    ring
  have hweq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast scaled := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_option, w, v, rationalVectorCast_apply, Pi.zero_apply,
      Rat.cast_zero, mul_zero, zero_add, scaled, Rat.cast_div, Rat.cast_natCast]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hxeq]
  let s : Set (J → ℚ) := insert 0 (Set.range A)
  have hv : ∀ i, rationalVectorCast (v i) ∈ rationalVectorCast '' s := by
    intro i
    refine ⟨v i, ?_, rfl⟩
    cases i with
    | none => exact Set.mem_insert 0 _
    | some i => exact Set.mem_insert_of_mem 0 (Set.mem_range_self i)
  have hcReal : rationalVectorCast scaled ∈
      convexHull ℝ (rationalVectorCast '' s) :=
    mem_convexHull_of_exists_fintype w (fun i ↦ rationalVectorCast (v i))
      hwpos hwsum hv hweq
  have hcRat : scaled ∈ convexHull ℚ s :=
    rationalVectorCast_mem_convexHull_descend hcReal
  have hs : s ⊆ PointedCone.hull ℚ (Set.range A) := by
    intro a ha
    rcases ha with rfl | ha
    · exact Submodule.zero_mem _
    · exact PointedCone.subset_hull ha
  have hscaled : scaled ∈ PointedCone.hull ℚ (Set.range A) :=
    convexHull_min hs (PointedCone.convex _) hcRat
  have hscale : (N : ℚ) • scaled = b := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, scaled]
    field_simp
  rw [← hscale]
  exact PointedCone.smul_mem _ (Nat.cast_nonneg N) hscaled

/-- Nonnegative solvability of a finite rational linear system descends from
real coefficients to rational coefficients. The equation index type may be
infinite. -/
theorem exists_nonneg_rat_solution_of_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∀ j, ∑ i, q i * A i j = b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  have hb := mem_rationalCone_of_nonneg_real_solution A b x hxpos hxeq
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ({x : ℚ // 0 ≤ x})).1 hb
  refine ⟨fun i ↦ (q i : ℚ), fun i ↦ (q i).property, ?_⟩
  intro j
  have hj := congrFun hq j
  simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul, smul_eq_mul] using hj

/-- Clearing denominators turns a nonnegative real solution of a rational
system into a positive integer multiple with natural coefficients. -/
theorem exists_nat_scaled_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℚ) * A i j = (D : ℚ) * b j := by
  obtain ⟨q, hqpos, hqeq⟩ := exists_nonneg_rat_solution_of_real A b h
  obtain ⟨D, hDpos, c, hc⟩ := exists_nat_mul_eq_nat q hqpos
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  calc
    ∑ i, (c i : ℚ) * A i j = ∑ i, ((D : ℚ) * q i) * A i j := by simp only [hc]
    _ = (D : ℚ) * ∑ i, q i * A i j := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ = (D : ℚ) * b j := by rw [hqeq]

/-- Integer form of finite cone certificate extraction. This is the form used
when the selected additive relations have integral coefficients. -/
theorem exists_nat_scaled_int_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℤ) (b : J → ℤ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = (D : ℤ) * b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  obtain ⟨D, hDpos, c, hc⟩ :=
    exists_nat_scaled_solution_of_nonneg_real
      (fun i j ↦ (A i j : ℚ)) (fun j ↦ (b j : ℚ))
      ⟨x, hxpos, by simpa using hxeq⟩
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  exact_mod_cast hc j

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule029
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalCone -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.ConeSupport -/
section FlattenModule030



namespace OAI

/-!
# Independent generators for a finite conical combination

Every conical combination can be expressed using a linearly independent
subfamily of its original generators.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem exists_positive_relation (A : I → E) (s : Finset I)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ g : I → ℝ, (∑ i ∈ s, g i • A i) = 0 ∧ ∃ i ∈ s, 0 < g i := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ :=
    (not_linearIndepOn_finset_iff (R := ℝ) (v := A)).mp h
  rcases lt_or_gt_of_ne hgi with hneg | hpos
  · refine ⟨fun j ↦ -g j, ?_, i, hi, neg_pos.mpr hneg⟩
    simp_rw [neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
  · exact ⟨g, hg, i, hi, hpos⟩

private theorem exists_nonneg_representation_erase [DecidableEq I] (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ i ∈ s, ∃ v : I → ℝ, (∀ j ∈ s.erase i, 0 ≤ v j) ∧
      (∑ j ∈ s.erase i, v j • A j) = ∑ j ∈ s, w j • A j := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ := exists_positive_relation A s h
  let p := s.filter fun i ↦ 0 < g i
  obtain ⟨i₀, hi₀, hmin⟩ :
      ∃ i₀ ∈ p, ∀ j ∈ p, w i₀ / g i₀ ≤ w j / g j := by
    apply p.exists_min_image
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hgi₀ : 0 < g i₀ := (Finset.mem_filter.mp hi₀).2
  let v : I → ℝ := fun j ↦ w j - w i₀ / g i₀ * g j
  have hvi₀ : v i₀ = 0 := by simp [v, ne_of_gt hgi₀]
  refine ⟨i₀, hi₀s, v, ?_, ?_⟩
  · intro j hj
    have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    dsimp [v]
    apply sub_nonneg.mpr
    by_cases hjp : j ∈ p
    · have hgj : 0 < g j := (Finset.mem_filter.mp hjp).2
      exact (le_div_iff₀ hgj).mp (hmin j hjp)
    · have hgj : g j ≤ 0 := by
        simpa only [p, Finset.mem_filter, hjs, true_and, not_lt] using hjp
      exact (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hw i₀ hi₀s) hgi₀.le) hgj).trans (hw j hjs)
  · calc
      (∑ j ∈ s.erase i₀, v j • A j) = ∑ j ∈ s, v j • A j := by
        apply Finset.sum_erase
        rw [hvi₀, zero_smul]
      _ = ∑ j ∈ s, w j • A j := by
        simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib,
          ← Finset.smul_sum, hg, smul_zero, sub_zero]

/-- A nonnegative finite combination uses a linearly independent subfamily
after possibly changing its coefficients. -/
theorem exists_nonneg_representation_linearIndependent (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ t : Finset I, t ⊆ s ∧ LinearIndependent ℝ (fun i : t ↦ A i) ∧
      ∃ v : I → ℝ, (∀ i ∈ t, 0 ≤ v i) ∧
        (∑ i ∈ t, v i • A i) = ∑ i ∈ s, w i • A i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hs : LinearIndependent ℝ (fun i : s ↦ A i)
    · exact ⟨s, Finset.Subset.refl _, hs, w, hw, rfl⟩
    · obtain ⟨i, hi, v, hv, heq⟩ := exists_nonneg_representation_erase A s w hw hs
      obtain ⟨t, hts, ht, z, hz, hzeq⟩ := ih (s.erase i) (Finset.erase_ssubset hi) v hv
      exact ⟨t, hts.trans (Finset.erase_subset _ _), ht, z, hz, hzeq.trans heq⟩

/-- Every element of a finitely generated cone belongs to the cone generated
by some linearly independent subfamily of the given generators. -/
theorem exists_linearIndependent_subcone [Fintype I] (A : I → E) {x : E}
    (hx : x ∈ PointedCone.hull ℝ (Set.range A)) :
    ∃ s : Finset I, LinearIndependent ℝ (fun i : s ↦ A i) ∧
      x ∈ PointedCone.hull ℝ (Set.range (fun i : s ↦ A i)) := by
  classical
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ({x : ℝ // 0 ≤ x})).mp hx
  obtain ⟨s, _, hs, v, hv, heq⟩ :=
    exists_nonneg_representation_linearIndependent A Finset.univ
      (fun i ↦ (w i : ℝ)) (fun i _ ↦ (w i).property)
  refine ⟨s, hs, ?_⟩
  have hsum : (∑ i ∈ s, v i • A i) = x := by
    exact heq.trans (by simpa only [← Nonneg.coe_smul] using hw)
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  exact PointedCone.smul_mem _ (hv i hi)
    (PointedCone.subset_hull ⟨⟨i, hi⟩, rfl⟩)

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule030
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.ConeSupport -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FiniteConeClosed -/
section FlattenModule031




namespace OAI

/-!
# Closed finitely generated cones
-/

open Topology

namespace MatrixMultiplication.AuxiliarySeparation

/-- A finite conic combination is a sum with nonnegative coefficients. -/
theorem mem_pointedCone_hull_range_iff {I E : Type*} [Fintype I]
    [AddCommGroup E] [Module ℝ E] (A : I → E) (x : E) :
    x ∈ PointedCone.hull ℝ (Set.range A) ↔
      ∃ c : I → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • A i = x := by
  rw [PointedCone.hull, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i ↦ (c i : ℝ), fun i ↦ (c i).2, hc⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨fun i ↦ ⟨c i, hc i⟩, hcx⟩

/-- The cone spanned by a finite linearly independent family is closed. -/
theorem isClosed_pointedCone_hull_range_of_linearIndependent
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) (hA : LinearIndependent ℝ A) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  let f := Fintype.linearCombination ℝ A
  have hf : IsClosedEmbedding f :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hA.fintypeLinearCombination_injective)
  have hnonneg : IsClosed {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun i ↦ isClosed_le (continuous_const : Continuous fun _ : I → ℝ ↦ (0 : ℝ)) (continuous_apply i)
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      f '' {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    change x ∈ PointedCone.hull ℝ (Set.range A) ↔ _
    rw [mem_pointedCone_hull_range_iff]
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    rfl
  rw [heq]
  exact hf.isClosedMap _ hnonneg

/-- A cone generated by a finite family of real vectors is closed. -/
theorem isClosed_pointedCone_hull_range
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  classical
  let S := {s : Finset I // LinearIndependent ℝ (fun i : s ↦ A i)}
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      ⋃ s : S, (PointedCone.hull ℝ (Set.range (fun i : s.1 ↦ A i)) : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hx⟩ := exists_linearIndependent_subcone A hx
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
    · intro hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      apply Submodule.span_mono _ hs
      rintro _ ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
  rw [heq]
  exact isClosed_iUnion_of_finite fun s : S ↦
    isClosed_pointedCone_hull_range_of_linearIndependent _ s.2

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule031
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FiniteConeClosed -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.Farkas -/
section FlattenModule032



namespace OAI

/-!
# Finite rational cone duality

A finite family of integral vectors admits a normalized nonnegative linear
functional whenever the negative normalizing vector has no positive integral
multiple in the monoid generated by the family.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Closed-cone separation followed by rational certificate extraction yields
a normalized nonnegative linear functional. -/
theorem exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hclosed : IsClosed (PointedCone.hull ℝ
      (Set.range (fun i j ↦ (A i j : ℝ))) : Set (J → ℝ)))
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) := by
  classical
  let C : ProperCone ℝ (J → ℝ) :=
    { toSubmodule := PointedCone.hull ℝ (Set.range (fun i j ↦ (A i j : ℝ)))
      isClosed' := hclosed }
  have houtside : -(fun j ↦ (u j : ℝ)) ∉ C := by
    intro hmem
    obtain ⟨x, hx⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ({x : ℝ // 0 ≤ x})).1 hmem
    have hreal : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
        ∀ j, ∑ i, x i * (A i j : ℝ) = ((-u j : ℤ) : ℝ) := by
      refine ⟨fun i ↦ (x i : ℝ), fun i ↦ (x i).property, fun j ↦ ?_⟩
      have hj := congrFun hx j
      simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul,
        smul_eq_mul, Pi.neg_apply, Int.cast_neg] using hj
    obtain ⟨D, hD, c, hc⟩ :=
      exists_nat_scaled_int_solution_of_nonneg_real A (fun j ↦ -u j) hreal
    exact hno ⟨D, hD, c, fun j ↦ by simpa only [mul_neg, neg_mul] using hc j⟩
  obtain ⟨f, hf, hfu⟩ := C.hyperplane_separation_point houtside
  have hpos : 0 < f (fun j ↦ (u j : ℝ)) := by
    simpa only [map_neg, neg_neg, neg_lt_zero] using hfu
  refine ⟨(f (fun j ↦ (u j : ℝ)))⁻¹ • f.toLinearMap, ?_, fun i ↦ ?_⟩
  · simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    exact inv_mul_cancel₀ hpos.ne'
  · change 0 ≤ (f (fun j ↦ (u j : ℝ)))⁻¹ * f (fun j ↦ (A i j : ℝ))
    exact mul_nonneg (inv_nonneg.mpr hpos.le)
      (hf _ (PointedCone.subset_hull (Set.mem_range_self i)))

/-- A finite integral cone either contains a positive integer multiple of the
negative normalizing vector, or admits a linear functional which is
nonnegative on the generators and takes value one on that vector. -/
theorem exists_normalized_nonneg_linear_of_no_nat_certificate
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) :=
  exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed A u
    (isClosed_pointedCone_hull_range _) hno

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule032
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.Farkas -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Catalyst -/
section FlattenModule033


namespace OAI

/-!
# Catalysts from additive completion certificates

Equality in the Grothendieck additive group means equality after adding a
common element of the original semiring. This gives catalytic inequalities
without assuming additive cancellation.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Algebra

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- A negative-unit certificate in the additive completion gives a catalytic
inequality in the original semiring, even when its addition is not cancellative. -/
theorem exists_catalyst_of_completion_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (m k : ℕ) (d X Y s : S) (hXY : X ≤ Y)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      GrothendieckAddGroup.of Y - GrothendieckAddGroup.of X +
        GrothendieckAddGroup.of (d * s) - k • GrothendieckAddGroup.of s) :
    ∃ D : S, D + (m : S) + d * s ≤ D + (k : S) * s := by
  let η : S →+ GrothendieckAddGroup S := GrothendieckAddGroup.of
  have hm : η (m : S) = m • η 1 := by
    rw [← nsmul_one m, map_nsmul]
  have hk : η ((k : S) * s) = k • η s := by
    rw [← nsmul_eq_mul, map_nsmul]
  have heq' : η ((m : S) + Y + d * s) = η (X + (k : S) * s) := by
    simp only [map_add, hm, hk]
    change -(m : ℤ) • η 1 = η Y - η X + η (d * s) - k • η s at heq
    simp only [neg_zsmul, natCast_zsmul] at heq
    calc
      m • η 1 + η Y + η (d * s) =
          m • η 1 + (η Y - η X + η (d * s) - k • η s) + η X + k • η s := by abel
      _ = m • η 1 + -(m • η 1) + η X + k • η s := by rw [← heq]
      _ = η X + k • η s := by abel
  obtain ⟨C, hC⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid S)).exists_of_eq heq'
  refine ⟨(C : S) + Y, ?_⟩
  calc
    ((C : S) + Y) + (m : S) + d * s = (C : S) + ((m : S) + Y + d * s) := by ac_rfl
    _ = (C : S) + (X + (k : S) * s) := hC
    _ ≤ (C : S) + (Y + (k : S) * s) :=
      hadd _ _ _ _ le_rfl (hadd _ _ _ _ hXY le_rfl)
    _ = ((C : S) + Y) + (k : S) * s := by ac_rfl

/-- A finite nonnegative integral combination of completion relations gives
one catalytic inequality. The catalyst absorbs the aggregate of the ordered
relations, and the resulting test element is the same combination of the
original test elements. -/
theorem exists_catalyst_of_completion_sum_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    {I : Type*} [Fintype I] (m k : ℕ) (d : S)
    (n : I → ℕ) (X Y Z : I → S) (hXY : ∀ i, X i ≤ Y i)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      ∑ i, n i • (GrothendieckAddGroup.of (Y i) - GrothendieckAddGroup.of (X i) +
        GrothendieckAddGroup.of (d * Z i) - k • GrothendieckAddGroup.of (Z i))) :
    ∃ D : S, D + (m : S) + d * (∑ i, n i • Z i) ≤
      D + (k : S) * (∑ i, n i • Z i) := by
  classical
  have hnsmul (a b : S) (hab : a ≤ b) (l : ℕ) : l • a ≤ l • b := by
    induction l with
    | zero => simp
    | succ l ih => simpa only [succ_nsmul] using hadd _ _ _ _ ih hab
  have hsum (t : Finset I) : ∑ i ∈ t, n i • X i ≤ ∑ i ∈ t, n i • Y i := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using
        hadd _ _ _ _ (hnsmul (X i) (Y i) (hXY i) (n i)) ih
  apply exists_catalyst_of_completion_eq hadd m k d
    (∑ i, n i • X i) (∑ i, n i • Y i) (∑ i, n i • Z i) (hsum Finset.univ)
  convert heq using 1
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    map_sum, map_nsmul, Finset.mul_sum, mul_smul_comm, ← smul_comm k]
  rw [Finset.smul_sum]

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule033
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Catalyst -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Coordinates -/
section FlattenModule034


namespace OAI

/-!
# Extending a finite coordinate functional

A linear functional on a finite coordinate set determines a state on the
whole index type by evaluating coordinate indicators. Its value on any
finitely supported integral vector depends only on those finite coordinates.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

/-- Extend a functional on a finite coordinate set by zero outside that set. -/
def finiteCoordinateState {S : Type*} (H : Finset S)
    (L : (H → ℝ) →ₗ[ℝ] ℝ) (x : S) : ℝ := by
  classical
  exact L (fun j : H ↦ if (j : S) = x then 1 else 0)

@[simp] theorem finiteCoordinateState_eq_zero_of_not_mem {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) {x : S} (hx : x ∉ H) :
    finiteCoordinateState H L x = 0 := by
  classical
  unfold finiteCoordinateState
  have hz : (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) = 0 := by
    funext j
    simp only [Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h ↦ hx (h ▸ j.property)
  rw [hz, map_zero]

/-- Evaluating a finitely supported integral vector against the extended
state agrees with restricting its coordinates and applying the functional. -/
theorem linearCombination_finiteCoordinateState {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) (v : S →₀ ℤ) :
    Finsupp.linearCombination ℤ (finiteCoordinateState H L) v =
      L (fun j : H ↦ (v j : ℝ)) := by
  classical
  induction v using Finsupp.induction with
  | zero =>
    simp only [map_zero, Finsupp.zero_apply, Int.cast_zero]
    exact (L.map_zero).symm
  | single_add x n v _ _ ih =>
    rw [map_add, Finsupp.linearCombination_single, ih]
    have hsingle :
        (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) =
          n • (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) := by
      funext j
      by_cases hj : (j : S) = x
      · simp [hj]
      · simp [hj]
    have hadd :
        (fun j : H ↦ ((Finsupp.single x n + v) j : ℝ)) =
          (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) +
            (fun j : H ↦ (v j : ℝ)) := by
      funext j
      simp
    rw [hadd, map_add, hsingle, map_zsmul]
    rfl

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule034
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Coordinates -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.StateObstruction -/
section FlattenModule035







namespace OAI

/-!+# Finite obstructions to normalized additive states

The state equations are homogeneous integer inequalities, except for the
normalization at the unit. Their finite certificates are interpreted in the
additive group completion, preserving catalysts in the original semiring.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- The homogeneous inequalities defining a normalized additive state. Both
signs of the additive relation are included. -/
inductive StateConstraint (S : Type*) [Preorder S] where
  | lower (x : S)
  | upper (x : S)
  | addPos (x y : S)
  | addNeg (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S)

/-- Integer coefficient vector of a homogeneous state constraint. -/
def stateConstraintVector (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) : S →₀ ℤ := by
  classical
  exact match c with
  | .lower x => Finsupp.single x 1
  | .upper x => Finsupp.single (1 : S) (R x : ℤ) - Finsupp.single x 1
  | .addPos x y => Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1
  | .addNeg x y => -(Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1)
  | .order x y _ => Finsupp.single y 1 - Finsupp.single x 1
  | .detector x => Finsupp.single (d * x) 1 - Finsupp.single x (k : ℤ)

/-- Evaluation of a finite integer coefficient vector on a real-valued function. -/
def statePairing (f : S → ℝ) : (S →₀ ℤ) →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ f

omit [CommSemiring S] [Preorder S] in
theorem statePairing_apply (f : S → ℝ) (v : S →₀ ℤ) :
    statePairing f v = ∑ x ∈ v.support, (v x : ℝ) * f x := by
  simp [statePairing, Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
@[simp] theorem statePairing_single (f : S → ℝ) (x : S) (n : ℤ) :
    statePairing f (Finsupp.single x n) = (n : ℝ) * f x := by
  simp [statePairing, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
theorem continuous_statePairing (v : S →₀ ℤ) :
    Continuous (fun f : S → ℝ ↦ statePairing f v) := by
  simp only [statePairing_apply]
  exact continuous_finsetSum _ fun x _ ↦ continuous_const.mul (continuous_apply x)

theorem normalizedStates_iff_stateConstraint (R : S → ℕ) (d : S) (k : ℕ)
    (f : S → ℝ) :
    f ∈ normalizedStates (fun x ↦ (R x : ℝ)) d k ↔
      f 1 = 1 ∧ ∀ c : StateConstraint S, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  constructor
  · intro hf
    refine ⟨hf.2.1, ?_⟩
    intro c
    cases c with
    | lower x => simpa [stateConstraintVector] using (hf.1 x).1
    | upper x =>
      simp only [stateConstraintVector, map_sub, statePairing_single, Int.cast_natCast,
        Int.cast_one, one_mul, hf.2.1, mul_one, sub_nonneg]
      exact (hf.1 x).2
    | addPos x y => simp [stateConstraintVector, hf.2.2.1]
    | addNeg x y => simp [stateConstraintVector, hf.2.2.1]
    | order x y h => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.1 x y h
    | detector x => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.2 x
  · rintro ⟨hn, hc⟩
    refine ⟨?_, hn, ?_, ?_, ?_⟩
    · intro x
      constructor
      · simpa [stateConstraintVector] using hc (.lower x)
      · simpa [stateConstraintVector, hn, sub_nonneg] using hc (.upper x)
    · intro x y
      have hp := hc (.addPos x y)
      have hm := hc (.addNeg x y)
      simp [stateConstraintVector] at hp hm
      linarith
    · intro x y hxy
      simpa [stateConstraintVector, sub_nonneg] using hc (.order x y hxy)
    · intro x
      simpa [stateConstraintVector, sub_nonneg] using hc (.detector x)

/-- The ordinary monotonicity difference in a state constraint. -/
def stateConstraintLower (c : StateConstraint S) : S :=
  match c with
  | .lower _ => 0
  | .upper x => x
  | .order x _ _ => x
  | _ => 0

def stateConstraintUpper (R : S → ℕ) (c : StateConstraint S) : S :=
  match c with
  | .lower x => x
  | .upper x => R x
  | .order _ y _ => y
  | _ => 0

/-- The multiplier of the distinguished detector difference. -/
def stateConstraintDetector (c : StateConstraint S) : S :=
  match c with
  | .detector x => x
  | _ => 0

theorem stateConstraintLower_le_upper (R : S → ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (c : StateConstraint S) :
    stateConstraintLower c ≤ stateConstraintUpper R c := by
  cases c with
  | lower x => exact hzero x
  | upper x => exact hbound x
  | order _ _ h => exact h
  | addPos _ _ => exact le_rfl
  | addNeg _ _ => exact le_rfl
  | detector _ => exact le_rfl

/-- Interpreting a constraint in the group completion separates its ordinary
order difference from its detector difference. -/
theorem stateConstraintVector_completion (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) :
    Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))
        (stateConstraintVector R d k c) =
      Algebra.GrothendieckAddGroup.of (stateConstraintUpper R c) -
        Algebra.GrothendieckAddGroup.of (stateConstraintLower c) +
      Algebra.GrothendieckAddGroup.of (d * stateConstraintDetector c) -
        k • Algebra.GrothendieckAddGroup.of (stateConstraintDetector c) := by
  classical
  have hcast (n : ℕ) : Algebra.GrothendieckAddGroup.of (n : S) =
      n • Algebra.GrothendieckAddGroup.of (1 : S) := by
    rw [← nsmul_one, map_nsmul]
  cases c <;>
    simp [stateConstraintVector, stateConstraintLower, stateConstraintUpper,
      stateConstraintDetector, hcast, Nat.cast_smul_eq_nsmul, map_add] <;> abel

/-- In the absence of a catalytic obstruction, no positive multiple of the
negative unit is a natural combination of state-constraint vectors. -/
theorem no_stateConstraint_certificate (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) :
    ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∑ i, n i • stateConstraintVector R d k (cs i) =
        -(m : ℤ) • Finsupp.single (1 : S) (1 : ℤ) := by
  classical
  rintro ⟨m, hm, n, hn⟩
  have heq := congrArg
    (Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))) hn
  simp only [map_sum, map_nsmul, map_smul, Finsupp.linearCombination_single,
    one_smul, stateConstraintVector_completion] at heq
  obtain ⟨D, hD⟩ := exists_catalyst_of_completion_sum_eq hadd m k d n
    (fun i ↦ stateConstraintLower (cs i)) (fun i ↦ stateConstraintUpper R (cs i))
    (fun i ↦ stateConstraintDetector (cs i))
    (fun i ↦ stateConstraintLower_le_upper R hzero hbound (cs i)) heq.symm
  exact hno D _ m hm hD

/-- Every finite family of constraints supported on `H` has a normalized
solution that vanishes outside `H`, provided no positive catalyst exists. -/
theorem finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) (H : Finset S) (hOne : (1 : S) ∈ H)
    (hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H) :
    ∃ f : S → ℝ, f 1 = 1 ∧
      (∀ i, 0 ≤ statePairing f (stateConstraintVector R d k (cs i))) ∧
      ∀ x ∉ H, f x = 0 := by
  classical
  let A : I → H → ℤ := fun i j ↦ stateConstraintVector R d k (cs i) j
  let u : H → ℤ := fun j ↦ (Finsupp.single (1 : S) (1 : ℤ)) j
  have hcert : ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∀ j, ∑ i, (n i : ℤ) * A i j = -(m : ℤ) * u j := by
    rintro ⟨m, hm, n, hn⟩
    apply no_stateConstraint_certificate R d k hzero hbound hadd hno cs
    refine ⟨m, hm, n, ?_⟩
    ext x
    by_cases hx : x ∈ H
    · have heq := hn ⟨x, hx⟩
      by_cases hx1 : (1 : S) = x <;>
        simpa [A, u, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, nsmul_eq_mul, zsmul_eq_mul, Finsupp.single_apply, hx1] using heq
    · have hz : ∀ i, stateConstraintVector R d k (cs i) x = 0 := by
        intro i
        apply Finsupp.notMem_support_iff.mp
        exact fun h ↦ hx (hH i h)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        hz, smul_zero, Finset.sum_const_zero]
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hx hOne
      simp [hx1]
  obtain ⟨L, hLu, hLA⟩ :=
    exists_normalized_nonneg_linear_of_no_nat_certificate A u hcert
  let f := finiteCoordinateState H L
  refine ⟨f, ?_, ?_, ?_⟩
  · have heq := linearCombination_finiteCoordinateState H L
      (Finsupp.single (1 : S) (1 : ℤ))
    simpa [f, u] using heq.trans hLu
  · intro i
    simpa only [statePairing, f, linearCombination_finiteCoordinateState, A] using hLA i
  · intro x hx
    exact finiteCoordinateState_eq_zero_of_not_mem H L hx

/-- A finite collection of state constraints can be solved while keeping all
coordinates in their rank intervals. -/
theorem bounded_finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    (F : Finset (StateConstraint S)) :
    ∃ f : S → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
      ∀ c ∈ F, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  let H : Finset S := insert 1 (F.biUnion fun c ↦ (stateConstraintVector R d k c).support)
  have hOne : (1 : S) ∈ H := Finset.mem_insert_self _ _
  let cs : F ⊕ (Bool × H) → StateConstraint S
    | .inl c => c
    | .inr (false, x) => .lower x
    | .inr (true, x) => .upper x
  have hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H := by
    intro i a ha
    cases i with
    | inl c =>
      exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨c, c.property, ha⟩)
    | inr i =>
      rcases i with ⟨tag, x⟩
      by_contra hnot
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hnot hOne
      have hax : a ≠ (x : S) := by
        rintro rfl
        exact hnot x.property
      have ha0 := Finsupp.mem_support_iff.mp ha
      cases tag <;>
        simp [cs, stateConstraintVector, ha1, hax] at ha0
  obtain ⟨f, hf1, hfc, hfzero⟩ :=
    finite_stateConstraint_solution R d k hzero hbound hadd hno cs H hOne hH
  refine ⟨f, ?_, hf1, ?_⟩
  · intro x
    by_cases hx : x ∈ H
    · have hlo := hfc (.inr (false, ⟨x, hx⟩))
      have hhi := hfc (.inr (true, ⟨x, hx⟩))
      constructor
      · simpa [cs, stateConstraintVector] using hlo
      · simpa [cs, stateConstraintVector, hf1, sub_nonneg] using hhi
    · rw [hfzero x hx]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
  · intro c hc
    exact hfc (.inl ⟨c, hc⟩)

/-- Absence of positive scalar-gain catalysts guarantees the existence of a
normalized additive monotone state satisfying the detector inequality. -/
theorem normalizedStates_nonempty_of_no_catalyst (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s) :
    (normalizedStates (fun x ↦ (R x : ℝ)) d k).Nonempty := by
  let B : Set (S → ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R x}
  let K : Set (S → ℝ) := B ∩ {f | f 1 = 1}
  let t : StateConstraint S → Set (S → ℝ) :=
    fun c ↦ {f | 0 ≤ statePairing f (stateConstraintVector R d k c)}
  have hBcompact : IsCompact B :=
    isCompact_pi_infinite (fun x ↦ isCompact_Icc (a := (0 : ℝ)) (b := (R x : ℝ)))
  have hKcompact : IsCompact K :=
    hBcompact.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have htclosed : ∀ c, IsClosed (t c) := fun c ↦
    isClosed_le continuous_const (continuous_statePairing (stateConstraintVector R d k c))
  have hfinite : ∀ F : Finset (StateConstraint S), (K ∩ ⋂ c ∈ F, t c).Nonempty := by
    intro F
    obtain ⟨f, hfb, hf1, hfc⟩ :=
      bounded_finite_stateConstraint_solution R d k hzero hbound hadd hno F
    refine ⟨f, ⟨hfb, hf1⟩, ?_⟩
    simp only [Set.mem_iInter]
    exact hfc
  obtain ⟨f, hfK, hft⟩ := hKcompact.inter_iInter_nonempty t htclosed hfinite
  refine ⟨f, (normalizedStates_iff_stateConstraint R d k f).mpr ?_⟩
  exact ⟨hfK.2, fun c ↦ Set.mem_iInter.mp hft c⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule035
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.StateObstruction -/

/- BEGIN upstream module FixedPointTheorems.cubical_sperner_prep -/
section FlattenModule036

/-!
# Cubical simplices and boundary incidence

The grid simplices of a labelled cube are classified by their boundary coordinates.
Coordinate-change counts order their vertices and determine the number of parent simplices,
providing the incidence identities used in the cubical Sperner argument.
-/


open Classical

structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I: Fin n → Fin (p+1) ), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube): Fintype SC.G := by {
  exact Pi.instFintype
}

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

def simplex (m:ℕ ) (I : Fin (m+1)→ SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

def complete_simplex (m:ℕ ) (I : Fin (m+1) → SC.G ) := simplex SC m I
    ∧ Set.range (fun (i:Fin (m+1))↦ SC.RL (I i)) = {j : ℕ | j ≤ m}

def is_face I J :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

def is_boundary_face I := ∃! J, @is_face SC n1 I J

def complete_boundary_face I := is_boundary_face SC I ∧ complete_simplex SC n1 I

def case_A (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = 0

def case_B (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = Fin.last SC.p

def case_C (I : Fin (n1 +1) → SC.G) :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q

lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by {
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  {
    apply Or.inl
    use j
    rwa [← q0]
  }
  by_cases qp : q = Fin.last SC.p
  {
    apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  }
  suffices h3 : case_C SC I by {
    simp only [h3, true_or, or_true]
  }
  use j, q
}

section simplex_properties

lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by {
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert! h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]
}

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by {
  apply Iff.intro
  {
    intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  }
  {
    intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)
  }
}

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by {
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2
}

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by {
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)
}

end simplex_properties

lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by {
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by {
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  }
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)
}

section simplex_child

def insert_index (j : Fin (SC.n+1)) (a: Fin (n1 +1 )) : Fin (SC.n+1) :=
{ val := if a.val < j.val then a.val else a.val+1,
  isLt := by {
    by_cases hlt : a.val < j.val
    {
      simp only [hlt, ↓reduceIte]
      exact Nat.lt_trans hlt j.2
    }
    {
      simp only [hlt, ↓reduceIte, add_lt_add_iff_right]
      rw [← hn1]
      exact a.2
    }
} }

def delete_vertex (j: Fin (SC.n+1)) (I : Fin (SC.n+1)→ SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by {
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  {
    simp only [hlt, ↓reduceIte]
    omega
  }
  {
    simp only [hlt, ↓reduceIte, ne_eq]
    omega
  }
}

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by {
  unfold insert_index
  by_cases hlt : a.1 < j.1
  {
    use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by {
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    }
    simp only [← h2, hlt]
    rfl
  }
  {
    have h2 : j.1 < a.1 := by {
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    }
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by {
      show a.1 - 1 + 1 = a.1
      omega
    }
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by {
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    }
    have h6 : a1f.1 = a1 := by {
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    }
    have h5 : ¬ (a1f < j.1) := by {
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    }
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]
  }
}

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by {
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  {
    by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  }
  {
    by_cases h4 : b.1 < j.1
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
  }
}

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by {
  apply StrictMono.injective
  apply insert_index_strict_mono
}

lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by {
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k
}

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by {
  apply And.intro
  {
    intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  }
  {
    intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    {
      apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      {
        simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      }
      apply insert_index_strict_mono
    }
    apply le_add_one_of_simplex SC J hs
  }
}

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by {
  apply And.intro
  {
    apply delete_vertex_simplex
    exact hs
  }
  {
    apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2
  }
}

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by {
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by {
    intro k
    exact h1 m k k.2
  }
  intro a
  induction' a with a ha
  {
    intro k h1
    omega
  }
  {
    have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by {
      intro hj
      apply ha
      omega
    }
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6
  }
}

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by {
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by {
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  }
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by {
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  }
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := by {
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  }
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]
}

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by {
  apply Iff.intro
  {
    intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by {
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by {
        intro k
        have h4 : I k ∈ Set.range I := by {
          exact Set.mem_range_self k
        }
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      }
      apply axiom_of_choice h3
    }
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by {
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    }
    have h3 : StrictMono f := by {
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    }
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  }
  {
    intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs
  }
}

end simplex_child

section cases_ABCD

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by {
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by {
    intro j2
    by_cases h1 : j2 = j
    {
      use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    }
    {
      have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by {
        apply almost_surjective_of_insert_index
        exact h1
      }
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
    }
  }
  obtain ⟨J, h2⟩ := axiomOfChoice h1
  use J
  apply And.intro
  {
    ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  }
  exact (h2 j).1 rfl
}

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by {
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by {
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  }
  apply And.intro
  {
    simp only [h2, ↓reduceIte]
    exact hij
  }
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]
}

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by {
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by {
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  }
  by_cases h8 : j1 = j
  {
    rw [h8, h7 j2]
    rw [←h8,h4]
  }
  by_cases h9 : j2 = j
  {
    rw [h9, h7 j1]
    rw [←h9,h4]
  }
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]
}

lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use 0
    exact h4
  }
  have h4 : J 0 ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  }
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by {
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  }
  intro j1 hj1 k1
  apply And.intro
  {
    rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    {
      simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    }
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  }
  {
    have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h4 : J j ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  }
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by {
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by {
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    }
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  }
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  {
    rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    {
      rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    }
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by {
      suffices h15 : j1 = n1 by {
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      }
      omega
    }
    have h14 : Fin.ofNat _ (j1+1) = j := by {
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    }
    rw [h13,h14]
    exact (h3 k1).1
  }
  {
    have h7 : J 0 = I 0 := by {
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    }
    rw [h7,←hj]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by {
    apply almost_surjective_of_insert_index
  }
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by {
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  }
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  {
    simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by {
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    }
    by_cases h8 : i2 = j.1
    {
      convert! h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by {
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      }
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    }
    by_cases h9 : i2 + 1 = j.1
    {
      rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert! h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    }
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    }
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    }
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by {
      apply insert_index_strict_mono
    }
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  }
  {
    have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by {
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      {
        rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      }
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    }
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    {
      rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
    {
      obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
  }
}

noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by {
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  {
    intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  }
  {
    intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  }
  {
    apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by {
      apply le_add_one_of_simplex _ _ hs
    }
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5
  }
}

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by {
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2
}

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨ coord_change_count SC (I 0) (I i), by {
      refine Nat.lt_succ_of_le ?_
      exact card_finset_fin_le {i_1 | I 0 i_1 ≠ I i i_1}
    } ⟩

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by {
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1
}

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by {
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs
}

lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by {
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    rw [Fin.ext_iff]
    change Finset.card {k : Fin SC.n | I 0 k ≠ I (Fin.last m) k} = SC.n ↔ _
    have hcard := Finset.card_eq_iff_eq_univ
      {k : Fin SC.n | I 0 k ≠ I (Fin.last m) k}
    simpa only [Fintype.card_fin, Finset.eq_univ_iff_forall,
      Finset.mem_filter, Finset.mem_univ, true_and] using hcard
  }
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  {
    intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    {
      rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    }
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  }
  {
    contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]
  }
}

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by {
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm
}

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by {
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  }
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  {
    simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by {
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    }
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by {
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    }
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by {
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    }
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by {
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by {
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      }
      apply insert_index_ne
    }
    have h10 : c2 + SC.n ≤ SC.n := by {
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    }
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  }
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by {
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  }
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by {
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  }
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne
}

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by {
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  }
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  {
    intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  }
  {
    intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2
  }
}

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  }
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  {
    rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  }
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]
}

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by {
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1
}

lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by {
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  }
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by {
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  }
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by {
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  }
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by {
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  }
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by {
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by {
      rw [← h11.2, ←h11.1]
    }
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by {
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    }
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  }
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by {
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert! h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  }
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by {
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  }
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by {
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  }
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by {
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by {
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    }
    have h22 : J3 j1 k3 ≠ I i1 k3 := by {
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    }
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by {
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    }
    have h7 : ins ∉ Set.range I := by {
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by {
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      }
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    }
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  }
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by {
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  }
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by {
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by {
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    }
    apply And.intro
    {
      apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    }
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  }
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  {
    have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  }
  apply subset_antisymm
  {
    intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by {
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    }
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by {
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by {
        rw [←h73.1]
        exact hk5.symm
      }
      exact h4.2.subset h21
    }
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by {
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    }
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  }
  {
    refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1
  }
}

lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by {
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by {
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  }
  have h6 : 2 ≤ sᶜ.card := by {
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  }
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7
}

lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by {
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  }
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by {
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by {
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by {
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    }
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    {
      rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    }
    rw [h2 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega
}

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  }
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p
}

lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by {
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  }
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by {
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by {
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by {
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    }
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by {
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  rw [←h6, ←h21 k1] at h5
  omega
}

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by {
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega
}

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl
}

lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by {
  have hnd : ¬ case_D SC I := by {
    contrapose! hABC
    exact hABC k1 q
  }
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  {
    intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  }
  {
    intro h1
    rw [←or_and_right] at h1
    exact h1.2
  }
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]
}

lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1
}

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1
}

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1
}

end cases_ABCD

lemma boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by {
  have hs : simplex SC n1 I := by {
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  }
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  assumption
  cases' h1 with h1 h1
  rw [@case_C_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
  rw [@case_D_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
}

lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)

lemma parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by {
  simp only [Set.mem_ofPred_eq]
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  left
  cases' h1 with h2 h2
  exact @case_A_parent_count SC n1 hn1 I hs h2
  exact @case_B_parent_count SC n1 hn1 I hs h2
  right
  cases' h1 with h2 h2
  exact @case_C_parent_count SC n1 hn1 I hs h2
  exact @case_D_parent_count SC n1 hn1 I hs h2
}

end FlattenModule036
/- END upstream module FixedPointTheorems.cubical_sperner_prep -/

/- BEGIN upstream module FixedPointTheorems.cubical_sperner -/
section FlattenModule037


/-!
# The cubical Sperner lemma

Boundary incidence counts give an odd number of completely labelled simplices.
The induction restricts a labelled cube to its boundary face; the resulting
existence theorem supplies the simplices used in the fixed-point argument.
-/


open Classical

section completeness

lemma complete_simplex_iff {SC} m I(hs : simplex SC m I) :
    complete_simplex SC m I ↔ ∀ c, c ≤ m → ∃ i, SC.RL (I i) = c := by {
  apply Iff.intro
  {
    intro h1 c hc
    rwa [← Set.mem_range, h1.2, Set.mem_ofPred_eq]
  }
  {
    intro c1
    apply And.intro hs
    refine Set.toFinset_inj.mp ?_
    refine (Finset.eq_iff_card_ge_of_superset ?_).mp ?_
    {
      simp only [Set.toFinset_range, Set.toFinset_subset, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      intro c hc
      simp only [Set.mem_range, c1 c hc]
    }
    let f1 := fun (j : ℕ ) ↦ SC.RL (I (Fin.ofNat _ j))
    apply Finset.card_le_card_of_surjOn f1
    intro j h1
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at h1
    obtain ⟨ i, hi⟩ := h1
    use i
    simp only [Set.coe_toFinset, Set.mem_ofPred_eq]
    apply And.intro (Fin.is_le i)
    unfold f1
    rw [← hi]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  }
}

lemma rl_inj_of_complete {SC} m I (hcs : complete_simplex SC m I):
    ∀ i1 i2, SC.RL (I i1) = SC.RL (I i2) → i1 = i2 := by {
  let f1 : Fin (m+1) → Fin (m+1) := fun j ↦ Fin.ofNat _ (SC.RL (I j))
  suffices h1 : Function.Injective f1 by {
    intro i1 i2 h2
    apply h1
    unfold f1
    rw [h2]
  }
  have h2 := hcs.2
  apply Function.Surjective.injective_of_finite
  rfl
  rw [complete_simplex_iff _ _ hcs.1] at hcs
  intro c
  obtain ⟨a, ha⟩ := hcs c (Fin.is_le c)
  use a
  unfold f1
  rw [ha]
  exact Fin.cast_val_eq_self c
}

lemma char_complete_face {SC n1 hn1} I J (hs : simplex SC SC.n J) :
    complete_simplex SC n1 I ∧ is_face SC I J
    ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J
    ∧ ∀ (c:ℕ ), c ≤ n1 → ∃ i2, i2 ≠ i ∧ SC.RL (J i2) = c := by {
  apply Iff.intro
  {
    rw [child_simplex_char]
    intro h1
    obtain ⟨i, hi1 ⟩ := h1.2
    use i
    apply And.intro hi1
    intro c hc
    have h2 := (complete_simplex_iff n1 I h1.1.1).mp h1.1 c hc
    obtain ⟨j, hj⟩ := h2
    rw [← hj, hi1]
    unfold delete_vertex
    use @insert_index SC n1 hn1 i j
    apply And.intro _ rfl
    apply insert_index_ne
    exact hn1
    exact hs
  }
  {
    intro h1
    obtain ⟨i, hi1 ⟩ := h1
    have hface : is_face SC I J := by {
      rw [child_simplex_char]
      use i
      exact hi1.1
      exact hs
    }
    apply And.intro _ hface
    rw [complete_simplex_iff n1 I hface.1]
    intro c hc
    obtain ⟨i2, hi2⟩ := hi1.2 c hc
    have h3 := @almost_surjective_of_insert_index SC n1 hn1 i i2 hi2.1
    obtain ⟨j, hj⟩ := h3
    use j
    rw [hi1.1, ← hi2.2, hj]
    rfl
  }
}

lemma complete_child_uniq {SC n1} {hn1 : n1 + 1 = SC.n} J (hcs : complete_simplex SC SC.n J) :
    ∃! (I : Fin (n1+1) → SC.G), complete_simplex SC n1 I ∧ is_face SC I J := by {
  have h4 : ∃ i, SC.RL (J i) = SC.n := by {
    rw [← Set.mem_range, hcs.2]
    simp only [Set.mem_ofPred_eq, le_refl]
  }
  obtain ⟨ i, hi⟩ := h4
  let I := @delete_vertex SC n1 hn1 i J
  have hs2 : simplex SC n1 I := by {
    apply delete_vertex_simplex
    exact hcs.1
  }
  use I
  have h1 : complete_simplex SC n1 I ∧ is_face SC I J := by
  {
    rw [@char_complete_face SC n1 hn1 _ _ hcs.1]
    use i
    apply And.intro rfl
    rw [complete_simplex_iff] at hcs
    {
      intro c hc
      have h3 : c ≤ SC.n := by omega
      obtain ⟨i2, hi2 ⟩ := hcs c h3
      use i2
      apply And.intro _ hi2
      intro h4
      rw [h4, hi, ← hn1] at hi2
      rw [← hi2] at hc
      revert hc
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_self]
    }
    {
      exact hcs.1
    }
  }
  simp only
  apply And.intro h1
  intro I2 h2
  rw [@char_complete_face SC n1 hn1 _ _ hcs.1] at h2
  obtain ⟨ i2, hi2 ⟩ := h2
  have h2 : SC.RL (J i2) = SC.n := by {
    let c2 := SC.RL (J i2)
    suffices h3 : ¬ (c2 ≤ n1) by {
      apply le_antisymm (SC.rl_proper (J i2)).1
      omega
    }
    intro h2
    obtain ⟨i3, hi3⟩ := hi2.2 c2 h2
    apply hi3.1
    apply rl_inj_of_complete SC.n J hcs
    exact hi3.2
  }
  suffices h3 : i2 = i by {
    rw [hi2.1, h3]
  }
  apply rl_inj_of_complete SC.n J hcs
  rw [h2]
  exact (Eq.symm hi)
}

lemma incomplete_childs {SC n1} {hn1 : n1 + 1 = SC.n} J (hs : simplex SC SC.n J)
    (hnc : ¬ complete_simplex SC SC.n J):
    Even (Finset.card { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}) := by {
  let S : Finset _:= { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}
  let c := S.card
  suffices h1 : c > 0 → c = 2 by {
    suffices h2 : Even c by {exact h2}
    by_cases h3 : c > 0
    rw [h1 h3]
    exact even_two
    use 0
    omega
  }
  intro cpos
  have h1 : Finset.Nonempty S := by {
    apply Finset.card_ne_zero.mp
    omega
  }
  obtain ⟨I1, h1 ⟩ := h1
  have hI1S := h1
  unfold S at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  obtain ⟨i1, hi1 ⟩ := (@char_complete_face SC n1 hn1 I1 J hs).mp h1
  apply Finset.card_eq_two.mpr
  have h2 : SC.RL (J i1) ≤ n1 := by {
    by_contra h3
    apply hnc
    rw [complete_simplex_iff _ _ hs]
    intro c hc
    by_cases h4 : c ≤ n1
    {
      obtain ⟨i2, hi2 ⟩ := hi1.2 c h4
      use i2
      exact hi2.2
    }
    {
      use i1
      have h6 : c = SC.n := le_antisymm hc (le_of_eq_of_le hn1.symm (not_le.mp h4))
      rw [h6]
      apply le_antisymm (SC.rl_proper (J i1)).1
      exact le_of_eq_of_le hn1.symm (not_le.mp h3)
    }
  }
  obtain ⟨i2, hi2⟩ := hi1.2 (SC.RL (J i1)) h2
  let I2 := @delete_vertex SC n1 hn1 i2 J
  have hI2S : I2 ∈ S := by {
    unfold S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [@char_complete_face SC n1 hn1 I2 J hs]
    use i2
    apply And.intro rfl
    intro c hc
    obtain ⟨i3, hi3⟩ := hi1.2 c hc
    by_cases h4 : i3 = i2
    {
      use i1
      rw [← hi3.2,h4, hi2.2]
      exact And.intro hi2.1.symm rfl
    }
    {
      use i3
      exact And.imp_left (fun a ↦ h4) hi3
    }
  }
  use I1, I2
  apply And.intro
  {
    intro h3
    apply hi2.1
    apply @delete_vertex_inj SC n1 hn1 J hs
    rw [← hi1.1, h3]
  }
  ext I3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Iff.intro
  {
    intro h3
    unfold S at h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h31 := h3
    rw [@char_complete_face SC n1 hn1 I3 J hs] at h3
    obtain ⟨ i3, hi3 ⟩ := h3
    by_contra h4
    simp only [not_or] at h4
    rw [hi1.1] at h4
    have h7 : ∀ i4, ¬ (I3 = @delete_vertex SC n1 hn1 i4 J) → i4 ≠ i3 := by {
      intro i4 h8 h9
      apply h8
      rw [hi3.1, h9]
    }
    have h5 := @almost_surjective_of_insert_index SC n1 hn1 i3
    obtain ⟨ k1, hk1 ⟩ := h5 i1 (h7 i1 h4.1)
    obtain ⟨ k2, hk2 ⟩ := h5 i2 (h7 i2 h4.2)
    apply hi2.1
    suffices h7 : k1 = k2 by {
      rw [hk1, hk2, h7]
    }
    apply rl_inj_of_complete n1 I3 h31.1
    rw [hi3.1]
    unfold delete_vertex
    rw [← hk1, ← hk2]
    exact hi2.2.symm
  }
  {
    intro h5
    cases h5
    rename_i h9
    rwa [h9]
    rename_i h9
    rwa [h9]
  }
}

lemma complete_boundary_face_last {SC n1} {hn1 : n1 + 1 = SC.n} (I : Fin (n1 + 1) → SC.G)
    (hcbf : complete_boundary_face SC I) :
    ∀ i, ∀ j, j.1 + 1 = SC.n →  (I i j).1 = SC.p := by {
  intro i j hj
  revert i
  have h3 := @boundary_is_A_or_B SC n1 hn1 I hcbf.1
  have h1 : j.1 = n1 := by omega
  have h4 : ∀ n2, n2 ≤ n1 → ∃ i, SC.RL (I i) = n2 := by {
    intro n2 hn2
    rw [← Set.mem_range, hcbf.2.2]
    simp only [Set.mem_ofPred_eq, hn2]
  }
  have h6 (j2 : Fin SC.n) : j2.1 ≤ n1 := by omega
  cases h3
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    exfalso
    obtain ⟨i, hi⟩ := h4 j2.1 (h6 j2)
    have h5 := ((SC.rl_proper (I i)).2 j2).1 (hj2 i)
    exact h5 hi
  }
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    have hj3 i : (I i j2).1 = SC.p := by {
      rw [hj2 i]
      exact Fin.val_last SC.p
    }
    suffices h3 : j = j2 by {
      intro i
      rw [h3, hj3 i]
    }
    have h3 := SC.rl_proper
    obtain ⟨i, hi⟩ := h4 n1 (Nat.le_refl n1)
    have h5 := ((SC.rl_proper (I i)).2 j2).2 (hj3 i)
    rw [hi] at h5
    ext
    rw [h1]
    exact Nat.le_antisymm h5 (h6 j2)
  }
}

end completeness

section handshake

variable {A B : Type*}
variable [Fintype A] [Fintype B]

lemma handshake_3 (r : A → B → Prop) (c : A → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    : Odd (Finset.card {a | c a}) ↔ Odd (∑ a, Finset.card {b | r a b}) := by {
  rw [Finset.odd_sum_iff_odd_card_odd]
  rw [iff_eq_eq]
  congr
  ext a
  exact h1 a
}

lemma handshake_2 (r : A → B → Prop)
    (c : A → Prop) (d : B → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    (h2 : ∀ b, d b ↔ Odd (Finset.card {a | r a b})) :
    Odd (Finset.card {a | c a}) → Odd (Finset.card {b | d b}) := by {
  intro h3
  have h5 : ∑ a, Finset.card {b | r a b} = ∑ b, Finset.card {a | r a b} := by {
    apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  }
  let r2 b a := r a b
  rw [handshake_3 r2 d h2, ←h5]
  rwa [←handshake_3 r c h1]
}

lemma handshake_1 (r : A → B → Prop)
    (c1 c2 c3: A → Prop) (d1 d2: B → Prop)
    (h1 : ∀ b, d1 b → ∃! a, c2 a ∧ r a b)
    (h2 : ∀ b, d2 b → ¬ d1 b → Even (Finset.card { a | c2 a ∧ r a b}))
    (h3 : ∀ a, c3 a → Finset.card { b | r a b} ∈ {c | c = 1 ∨ c = 2})
    (h5 : ∀ a, c1 a ↔ (∃! b, r a b) ∧ c2 a)
    (h6 : ∀ a, c2 a → c3 a) (h7 : ∀ b, ∀ a, r a b → d2 b)
    : Odd (Finset.card {a : A | c1 a}) → Odd (Finset.card {b : B | d1 b}) := by {
  let r2 a b := c2 a ∧ r a b
  apply handshake_2 r2
  {
    intro a
    rw [h5]
    by_cases p1 : c2 a
    unfold r2
    simp only [p1, and_true, true_and]
    rw [Fintype.existsUnique_iff_card_one]
    apply Iff.intro
    {
      intro p2
      use 0
      rwa [mul_zero, zero_add]
    }
    {
      intro p2
      have p3 := h3 a (h6 a p1)
      simp only [Set.mem_ofPred_eq] at p3
      cases p3
      rename_i p4
      exact p4
      rename_i p4
      rw [p4] at p2
      exfalso
      revert p2
      simp only [imp_false, Nat.not_odd_iff_even, even_two]
    }
    {
      unfold r2
      simp only [p1, and_false, false_and, Finset.filter_false, Finset.card_empty, Nat.not_odd_zero]
    }
  }
  {
    intro b
    by_cases p1 : d1 b
    {
      simp only [p1, true_iff]
      use 0
      rw [mul_zero, zero_add]
      rw [← Fintype.existsUnique_iff_card_one]
      exact h1 b p1
    }
    {
      simp only [p1, false_iff]
      intro p2
      have p5 : Finset.Nonempty {a | r2 a b} := by {
        have p3 : Odd (Finset.card { a | r2 a b}) := by {
          convert! p2
        }
        apply Finset.card_ne_zero.mp
        intro p4
        revert p3
        rw [p4]
        simp only [Nat.not_odd_zero, imp_self]
      }
      have p3 : d2 b := by {
        obtain ⟨a, p6⟩ := p5
        apply h7 b a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at p6
        exact p6.2
      }
      revert p2
      have p4 := h2 b p3 p1
      simp only [imp_false, Nat.not_odd_iff_even]
      convert! p4
    }
  }
}

end handshake

lemma odd_of_boundary_faces SC {n1} {hn1 : n1 + 1 = SC.n}:
    Odd (Finset.card { I : Fin (n1 + 1) → SC.G | complete_boundary_face SC I})
    → Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  apply handshake_1 (is_face SC)
  apply @complete_child_uniq SC n1 hn1
  apply @incomplete_childs SC n1 hn1
  apply @parent_count SC n1 hn1
  {
    intro I
    rfl
  }
  exact fun _ h1 ↦ h1.1
  exact fun _ _ h1 ↦ h1.2.1
}

section induction_step

variable (SC : SpernerCube)
variable {n1 : ℕ}

def child_map (v : Fin n1 → Fin (SC.p+1) ) : SC.G := fun i ↦
  match n1 with
  | 0 => Fin.last SC.p
  | Nat.succ _ => if i.1 + 1 = SC.n then Fin.last SC.p else v (Fin.ofNat _ i.1)

lemma child_map_last (v : Fin n1 → Fin (SC.p +1 ))
    : ∀ j, j.1 + 1 = SC.n → child_map SC v j = SC.p := by {
  intro j hj
  unfold child_map
  cases n1
  rfl
  simp only [hj, ↓reduceIte, Fin.val_last]
}

lemma child_map_applied [NeZero SC.n] {hn1 : n1 + 1 = SC.n} (v : Fin n1 → Fin (SC.p + 1))
    : ∀ (i : Fin n1), child_map SC v (Fin.ofNat _ i.1) = v i := by {
  intro i
  dsimp only [child_map]
  cases n1
  exact Fin.elim0 i
  rename_i n2
  simp only [Nat.succ_eq_add_one]
  have h5 : i.1 + 1 < SC.n := by omega
  have h2 : i.1 < SC.n := by omega
  have h3 := Fin.val_cast_of_lt h2
  rw [Fin.ofNat_eq_cast, h3]
  have h6 : i.1 + 1 ≠ SC.n := by omega
  simp only [h6, ↓reduceIte, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
}

lemma child_map_inj {hn1 : n1 + 1 = SC.n }: Function.Injective (@child_map SC n1) := by {
  intro v1 v2 h1
  ext i
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  rw [← child_map_applied SC v1]
  rw [← child_map_applied SC v2]
  rwa [h1]
  exact hn1
}

lemma child_map_surj_on {hn1 : n1 + 1 = SC.n} w
    (h1 : ∀ j, j.1 + 1 = SC.n → w j = SC.p)
    : ∃ v, @child_map SC n1 v = w := by {
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  let v2 : Fin n1 → Fin (SC.p +1) := fun i ↦ w (Fin.ofNat _ i.1)
  use v2
  apply funext
  intro i
  unfold child_map
  cases n1
  {
    simp only
    have h2 := h1 0
    simp only [Fin.val_zero, zero_add] at h2 hn1
    have h3 : i = 0 := by {
      have h4 := i.2
      simp only [← hn1] at h4
      ext
      simp only [Fin.val_zero]
      exact Nat.lt_one_iff.mp h4
    }
    rw [h3]
    exact Fin.eq_of_val_eq (id (Eq.symm (h2 hn1)))
  }
  {
    rename_i n2
    have h2 := h1 i
    by_cases h3 : i.1 +1 = SC.n
    {
      simp only [h3, ↓reduceIte]
      exact Eq.symm (Fin.eq_of_val_eq (h1 i h3))
    }
    simp only [h3, ↓reduceIte, Nat.succ_eq_add_one]
    unfold v2
    congr
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt]
    exact Fin.cast_val_eq_self i
    have h4 := i.2
    simp only [← hn1] at h3 h4
    omega
  }
}

def child_cube {hn1 : n1 + 1 = SC.n}: SpernerCube where
  n := n1
  p := SC.p
  RL := fun v ↦ SC.RL (child_map SC v)
  rl_proper := by {
    intro v
    have h0 : NeZero SC.n := by {
      rw [← hn1]
      exact instNeZeroNatHAdd_1
    }
    have h1 := child_map_last SC v
    have h2 := SC.rl_proper (child_map SC v)
    apply And.intro
    {
      have h3 := (h2.2 (Fin.ofNat _ n1)).2
      have h4 : n1 < SC.n := by omega
      simp only [Fin.ofNat_eq_cast] at h3
      rw [Fin.val_cast_of_lt h4] at h3
      apply h3
      apply child_map_last
      rw [Fin.val_cast_of_lt h4]
      exact hn1
    }
    intro i
    have h3 := h2.2 (Fin.ofNat _ i.1)
    rw [child_map_applied] at h3
    have h4 : (Fin.ofNat SC.n i.1).1 = i.1 := by {
      apply Fin.val_cast_of_lt
      omega
    }
    rwa [h4] at h3
    exact hn1
  }

end induction_step

lemma induction_start (SC : SpernerCube) (h0 : 0 = SC.n)
    : Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  use 0
  simp only [mul_zero, zero_add]
  rw [←Fintype.existsUnique_iff_card_one]
  let b : SC.G := fun _ ↦ 0
  let a : Fin (SC.n + 1) → SC.G := fun _ ↦ b
  use a
  simp only
  have h1 (x : Fin (SC.n+1)) : x = 0 := by {
    ext
    simp only [Fin.val_zero]
    rw [← Nat.lt_one_iff]
    apply Fin.val_lt_of_le x
    rw [←h0]
  }
  have hf (j : Fin SC.n) : False := by {
    apply Fin.elim0
    rwa [h0]
  }
  apply And.intro
  apply And.intro
  apply And.intro
  {
    intro x1 x2 _
    rw [h1 x1, h1 x2]
  }
  {
    intro i hi j
    exact False.elim ( hf j )
  }
  {
    ext i
    simp only [← h0]
    simp only [Set.mem_range, nonpos_iff_eq_zero, Set.ofPred_eq_eq_singleton, Set.mem_singleton_iff]
    have h3 : ∀ c, SC.RL (a c) = 0 := by {
      intro c
      have h2 := (SC.rl_proper (a c)).1
      simp only [← h0] at h2
      omega
    }
    apply Iff.intro
    {
      intro h2
      cases h2
      rename_i c hc
      rw [h3 c] at hc
      exact (Eq.symm hc)
    }
    {
      intro hi0
      use 0
      rw [hi0]
      exact h3 0
    }
  }
  {
    intro a2 h2
    ext i
    apply funext
    intro j
    exact False.elim ( hf j )
  }
}

theorem strong_cubical_sperner (k: ℕ ) : ∀ (SC : SpernerCube), k = SC.n →
    Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  induction' k with k hind
  {
    intro SC hk
    exact induction_start SC hk
  }
  {
    intro SC1 hk1
    apply @odd_of_boundary_faces SC1 k hk1
    let SC2 := @child_cube SC1 k hk1
    have hnz : NeZero SC1.n := by {
      rw [← hk1]
      exact instNeZeroNatHAdd_1
    }
    have h2 := hind SC2 rfl
    apply Eq.mpr _ h2
    apply congrArg
    let f1 : SC2.G → SC1.G := child_map SC1
    let f2 : (Fin (k+1)→ SC2.G) → (Fin (k+1)→ SC1.G) := fun a ↦ fun b ↦ f1 (a b)
    have hf1inj : Function.Injective f1 := by {
      apply child_map_inj SC1
      rw [← hk1]
      rfl
    }
    symm
    have hcomp I : complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 SC2.n I := by {
      unfold complete_boundary_face complete_simplex
      have h_last j k: j.1 + 1 = SC1.n → f2 I k j = SC1.p := by {
        apply child_map_last
      }
      have h_bf : simplex SC1 k (f2 I) ↔ is_boundary_face SC1 (f2 I) ∧ simplex SC1 k (f2 I):= by {
        simp only [iff_and_self]
        intro hs
        apply @case_B_boundary SC1 k hk1
        exact hs
        use (Fin.ofNat _ k)
        intro i
        ext
        apply h_last
        simp [← hk1]
      }
      rw [← and_assoc, ←h_bf]
      have h3 : SC2.n = k := rfl
      apply and_congr
      apply and_congr
      {
        apply Iff.intro
        {
          intro h4 i1 i2 h5
          exact h4 (congrArg f1 h5)
        }
        {
          intro h4 i1 i2 h5
          apply h4
          apply hf1inj h5
        }
      }
      {
        simp only [h3]
        apply forall₂_congr
        intro i hi1
        apply Iff.intro
        {
          intro h4 j
          have h6 k : (f2 I k (Fin.ofNat _ j.1)) = (I k j) := by {
            unfold f2
            apply child_map_applied
            rw [← hk1]
            rfl
          }
          change (I (Fin.ofNat (k + 1) i) j).val ≤
            (I (Fin.ofNat (k + 1) (i + 1)) j).val ∧
            (I (Fin.last k) j).val ≤ (I 0 j).val + 1
          rw [← h6, ← h6, ←h6, ← h6]
          exact h4 (Fin.ofNat _ j.1)
        }
        {
          intro h4 j
          by_cases h5 : j.1 + 1 = SC1.n
          {
            rw [h_last, h_last, h_last, h_last]
            simp only [le_refl, le_add_iff_nonneg_right, zero_le,
              and_self]
            repeat' exact h5
          }
          {
            have h7 : j.1 < SC2.n := by {
              rw [h3]
              have h6 := j.2
              simp only [← hk1] at h5 h6
              omega
            }
            have hn02 : NeZero SC2.n := by {
              exact NeZero.of_gt hi1
            }
            let j2 : Fin SC2.n := (Fin.ofNat _ j.1)
            have h8 : j = (Fin.ofNat _ j2.1) := by {
              unfold j2
              simp only [Fin.ofNat_eq_cast,]
              rw [Fin.val_cast_of_lt]
              exact Eq.symm (Fin.cast_val_eq_self j)
              exact h7
            }
            have h6 k : (f2 I k j) = (I k j2) := by {
              unfold f2
              rw [h8]
              apply child_map_applied
              exact hk1
            }
            rw [h6, h6, h6, h6]
            exact h4 j2
          }
        }
      }
      exact Eq.congr_right rfl
    }
    change ∀ I, complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 k I at hcomp
    change ({I : Fin (k + 1) → SC2.G | complete_simplex SC2 k I} : Finset _).card =
      ({I : Fin (k + 1) → SC1.G | complete_boundary_face SC1 I} : Finset _).card
    apply Finset.card_nbij f2
    {
      intro I hI
      have hI' : complete_simplex SC2 k I := by
        simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using hI
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        using (hcomp I).mpr hI'
    }
    {
      intro I1 h41 I2 h42 h5
      ext i
      apply hf1inj
      exact congrFun h5 i
    }
    {
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      intro J
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      intro h3
      have h4 : ∃ I, f2 I = J := by {
        suffices h6 : ∀ i, ∃ ii, f1 ii = J i by {
          obtain ⟨I, h5⟩  := axiomOfChoice h6
          use I
          ext i
          exact h5 i
        }
        intro i
        have h5 := @child_map_surj_on SC1 k hk1
        apply h5
        exact @complete_boundary_face_last SC1 k hk1 J h3 i
      }
      obtain ⟨I, h4⟩ := h4
      use I
      simp only [h4, and_true]
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        using (hcomp I).mp (h4 ▸ h3)
    }
  }

}

theorem weaker_cubical_sperner SC : ∃ I, complete_simplex SC SC.n I := by {
  have h1 := strong_cubical_sperner SC.n SC rfl
  obtain ⟨k1, hk1⟩ := h1
  have h2 : 0 < 2 * k1 + 1 := by omega
  rw [←hk1, Finset.card_pos] at h2
  obtain ⟨I, hI1⟩ := h2
  use I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI1
  exact hI1
}

end FlattenModule037
/- END upstream module FixedPointTheorems.cubical_sperner -/

/- BEGIN upstream module FixedPointTheorems.apply_cubical_sperner -/
section FlattenModule038


/-!
# Fixed points in the unit cube

Reduced labels encode coordinatewise displacement of a continuous cube map.
Cubical Sperner simplices on finer grids yield approximate fixed points, and
compactness of the cube supplies a genuine fixed point.
-/


open Classical

variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by {
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    }
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    }
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by {
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  }
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    suffices h3 : k1 ∈ s by {
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    }
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  }
  {
    intro h2
    have h3 : k1 ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    }
    exact Finset.min_le_of_eq h3 hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  {
    intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  }
  {
    intro h2
    apply (h1.2 k).2
    exact Or.inr h2
  }
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_ofPred_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    {
      intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    }
    {
      intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    }
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by {
    intro h4
    exact h3.2.symm.subset h4
  }
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  {
    apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  }
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
}

theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by {
    exact (continuous_apply k).comp continuous_subtype_val
  }
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by {
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  }
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by {
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by {
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      {
        intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      }
      exact fun _ ↦ dist_nonneg
    }
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  }
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)
}

theorem fixed_point_unit_cube_isFixedPt (f : C(@unit_cube n, @unit_cube n)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using! fixed_point_unit_cube f

end FlattenModule038
/- END upstream module FixedPointTheorems.apply_cubical_sperner -/

/- BEGIN upstream module FixedPointTheorems.convex_homeos -/
section FlattenModule039

/-!
# Homeomorphisms of compact convex sets

Compact convex sets are reduced to unit balls in their affine spans and then to
finite-dimensional cubes. These homeomorphisms transfer the cubical fixed-point
theorem to arbitrary nonempty compact convex domains.
-/


lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  have h1 := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni
  have h2 : Bornology.IsBounded s := IsCompact.isBounded hcmpct
  cases (h1 h2)
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  rw [h4] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}

theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 : Convex ℝ pL := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    {exact Ne.symm (zero_ne_one' ℝ)}
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ h4 h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}

lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [Set.mem_Icc, Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    rw [interior_Icc]; exact ⟨1/2, by norm_num, by norm_num⟩

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  have := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 := by {
    exact hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  }
  have h34 : (interior s3).Nonempty := by {
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv]
    rw [← AffineSubspace.comap_span]
    rw [affineSpan_coe_preimage_eq_top]
    rfl
  }
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by {
    intro w h1
    unfold s3 s2 at h1
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  }
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by {
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    refine (Set.mem_image g1 (g1 ⁻¹' s) v).mpr ?_
    have h11 : v ∈ affineSpan ℝ s := mem_affineSpan ℝ h1
    use ⟨v, h11⟩
    simp only [Set.mem_preimage]
    apply And.intro h1 rfl
  }
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by {
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  }
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  use k
  exact Nonempty.intro e5
}

end FlattenModule039
/- END upstream module FixedPointTheorems.convex_homeos -/

/- BEGIN upstream module FixedPointTheorems.brouwer -/
section FlattenModule040



/-!
# Brouwer's fixed-point theorem

The unit-cube fixed-point theorem is transported along a homeomorphism of a
nonempty compact convex set. The resulting theorem is also expressed using
`Function.IsFixedPt` and the set of fixed points.
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}

theorem brouwer_fixed_point_isFixedPt {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using! brouwer_fixed_point s hcvx hcmpct hne f

theorem brouwer_fixedPoints_nonempty {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    (Function.fixedPoints f).Nonempty := by
  exact brouwer_fixed_point_isFixedPt s hcvx hcmpct hne f

end FlattenModule040
/- END upstream module FixedPointTheorems.brouwer -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FixedPoint -/
section FlattenModule041


namespace OAI

/-! Fixed points of continuous maps on compact convex sets of real-valued functions. -/

namespace MatrixMultiplication.AuxiliarySeparation

open Set
open scoped BigOperators

private def weightSimplex (J : Type*) [Fintype J] : Set (J → ℝ) :=
  {w | (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1}

private theorem weightSimplex_convex (J : Type*) [Fintype J] :
    Convex ℝ (weightSimplex J) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    simpa using hab

private theorem weightSimplex_compact (J : Type*) [Fintype J] :
    IsCompact (weightSimplex J) := by
  have hc : IsClosed (weightSimplex J) := by
    change IsClosed ({w : J → ℝ | ∀ j, 0 ≤ w j} ∩ {w | ∑ j, w j = 1})
    have hn : IsClosed {w : J → ℝ | ∀ j, 0 ≤ w j} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const
        (continuous_apply j : Continuous (fun w : J → ℝ => w j))
    exact hn.inter
      (isClosed_eq (continuous_finsetSum _ fun _ _ => continuous_apply _) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro w hw
  constructor
  · exact hw.1
  · intro j
    calc
      w j ≤ ∑ k, w k := Finset.single_le_sum (fun k _ => hw.1 k) (Finset.mem_univ j)
      _ = 1 := hw.2

/-- A finite continuous system of barycentric weights gives an approximate fixed point.
The approximation is measured on any prescribed finite set of coordinates. -/
theorem exists_approximate_fixedPoint_of_weights
    {I J : Type*} [Fintype J] [Nonempty J]
    {K : Set (I → ℝ)} (hK : Convex ℝ K) (f : C(K, K))
    (a : J → K) (w : J → C(K, ℝ))
    (hw0 : ∀ j x, 0 ≤ w j x) (hw1 : ∀ x, ∑ j, w j x = 1)
    (s : Finset I) (ε : ℝ)
    (hclose : ∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| ≤ ε) :
    ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
  classical
  let D := weightSimplex J
  let b : D → K := fun v =>
    ⟨∑ j, v.val j • (a j).val,
      hK.sum_mem (fun j _ => v.property.1 j) v.property.2 (fun j _ => (a j).property)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).smul continuous_const
  let q : K → D := fun x => ⟨fun j => w j x, (fun j => hw0 j x), hw1 x⟩
  have hq : Continuous q := by
    exact (continuous_pi fun j => (w j).continuous).subtype_mk _
  let g : C(D, D) := ⟨fun v => q (f (b v)), hq.comp (f.continuous.comp hb)⟩
  have hDne : D.Nonempty := by
    let j₀ : J := Classical.choice inferInstance
    refine ⟨Pi.single j₀ 1, ?_, ?_⟩
    · intro j
      by_cases h : j = j₀ <;> simp [h]
    · simp
  obtain ⟨v, hv⟩ := brouwer_fixed_point D (weightSimplex_convex J)
    (weightSimplex_compact J) hDne g
  let x := b v
  have hwv (j : J) : w j (f x) = v.val j := congrArg (fun t : D => t.val j) hv
  refine ⟨x, fun i hi => ?_⟩
  have hx : x.val i - (f x).val i = ∑ j, v.val j * ((a j).val i - (f x).val i) := by
    change (∑ j, v.val j • (a j).val) i - (f x).val i = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, v.property.2, one_mul]
  rw [abs_sub_comm, hx]
  calc
    |∑ j, v.val j * ((a j).val i - (f x).val i)|
        ≤ ∑ j, |v.val j * ((a j).val i - (f x).val i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, v.val j * |(a j).val i - (f x).val i| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (v.property.1 j)]
    _ ≤ ∑ j, v.val j * ε := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : v.val j = 0
      · simp [hj]
      · exact mul_le_mul_of_nonneg_left
          (hclose (f x) j (by rwa [hwv]) i hi) (v.property.1 j)
    _ = ε := by rw [← Finset.sum_mul, v.property.2, one_mul]

theorem exists_finite_partition_weights {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : K → Set K := fun a => {x | ∀ i ∈ s, |a.val i - x.val i| < ε}
  have hUo : ∀ a, IsOpen (U a) := by
    intro a
    have hUa : U a = ⋂ i ∈ s, {x : K | |a.val i - x.val i| < ε} := by
      ext x
      simp [U]
    rw [hUa]
    apply isOpen_biInter_finset
    intro i hi
    exact isOpen_lt (continuous_const.sub ((continuous_apply i).comp continuous_subtype_val)).abs continuous_const
  have hUc : (univ : Set K) ⊆ ⋃ a, U a := by
    intro x hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    intro i hi
    simpa using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have htc : (univ : Set K) ⊆ ⋃ a : t, U a.val := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hat, hax⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, hax⟩
  obtain ⟨w, hw⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun a : t => U a.val) (fun a => hUo a.val) htc
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, (fun j => (e j).val), (fun j => w (e j)), ?_, ?_, ?_⟩
  · intro x j
    exact w.nonneg (e j) x
  · intro x
    change ∑ j, w (e j) x = 1
    calc
      ∑ j, w (e j) x = ∑ a : t, w a x := e.sum_comp (fun a => w a x)
      _ = 1 := by simpa only [finsum_eq_sum_of_fintype] using w.sum_eq_one (mem_univ x)
  · intro x j hj i hi
    exact hw (e j) (subset_closure hj) i hi


theorem exists_finite_partition_weights_nonempty {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  obtain ⟨n, a, w, hw0, hw1, hwa⟩ := exists_finite_partition_weights hK s hε
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    obtain ⟨x, hx⟩ := hne
    simpa using hw1 ⟨x, hx⟩
  exact ⟨n, hn, a, w, hw0, hw1, hwa⟩

theorem compact_approx_limit {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (_hne : K.Nonempty) (f : K → (I → ℝ)) (hf : Continuous f)
    (happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |f x i - x.val i| ≤ ε) :
    ∃ x : K, f x = x.val := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : (I × {ε : ℝ // 0 < ε}) → Set K :=
    fun p => {x | |f x p.1 - x.val p.1| ≤ p.2.val}
  have hclosed (p : I × {ε : ℝ // 0 < ε}) : IsClosed (C p) := by
    exact isClosed_le
      (((continuous_apply p.1).comp hf).sub
        ((continuous_apply p.1).comp continuous_subtype_val)).abs continuous_const
  have hfinite (s : Finset (I × {ε : ℝ // 0 < ε})) :
      (⋂ p ∈ s, C p).Nonempty := by
    let es : Finset ℝ := insert 1 (s.image fun p => p.2.val)
    have hes : es.Nonempty := ⟨1, by simp [es]⟩
    have he : 0 < es.min' hes := by
      rw [Finset.lt_min'_iff]
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · norm_num
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
        exact p.2.property
    obtain ⟨x, hx⟩ := happrox (s.image Prod.fst) (es.min' hes) he
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro p hp
    exact (hx p.1 (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).trans
      (Finset.min'_le es p.2.val (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨x, funext fun i => ?_⟩
  have hzero : |f x i - x.val i| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [C, Set.mem_ofPred_eq, zero_add] using
      (Set.mem_iInter.mp hx (i, ⟨ε, hε⟩))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))


/-- Schauder--Tychonoff for an arbitrary product of real lines. Compactness of the
set, rather than finite dimensionality of the ambient space, is the hypothesis. -/
theorem compact_convex_fixedPoint {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : C(K, K)) : ∃ x : K, f x = x := by
  have happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
    intro s ε hε
    obtain ⟨n, hn, a, w, hw0, hw1, hwa⟩ :=
      exists_finite_partition_weights_nonempty hKcompact hKne s hε
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact exists_approximate_fixedPoint_of_weights hKconvex f a w
      (fun j x => hw0 x j) hw1 s ε
      (fun x j hj i hi => (hwa x j hj i hi).le)
  obtain ⟨x, hx⟩ := compact_approx_limit hKcompact hKne
    (fun x => (f x).val) (continuous_subtype_val.comp f.continuous) happrox
  exact ⟨x, Subtype.ext hx⟩

/-- An unbundled form of the product-space fixed-point theorem. -/
theorem compact_convex_fixedPoint_of_continuous {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : K → K) (hf : Continuous f) : ∃ x : K, f x = x :=
  compact_convex_fixedPoint hKcompact hKconvex hKne ⟨f, hf⟩

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule041
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FixedPoint -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.MultiplicativeStates -/
section FlattenModule042


namespace OAI

/-! Multiplicative states obtained by normalizing translates of additive states. -/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S]

/-- Translate a state by multiplication, then normalize at the unit. -/
def normalizedTranslate (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z

theorem normalizedTranslate_continuousOn {K : Set (S → ℝ)} (z : S)
    (hz : ∀ f ∈ K, f z ≠ 0) :
    Continuous (fun f : K => normalizedTranslate z f.val) := by
  apply continuous_pi
  intro x
  exact ((continuous_apply (z * x)).comp continuous_subtype_val).div
    ((continuous_apply z).comp continuous_subtype_val) (fun f => hz f.val f.property)

def frozenConstraint (z : S) (c : ℝ) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = c * f x}

def frozenSlice (C : Set (S → ℝ)) (z : S) (c : ℝ) : Set (S → ℝ) :=
  C ∩ frozenConstraint z c

theorem frozenConstraint_isClosed (z : S) (c : ℝ) :
    IsClosed (frozenConstraint z c) := by
  unfold frozenConstraint
  simp only [ofPred_forall]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))

theorem frozenSlice_isClosed {C : Set (S → ℝ)} (hC : IsClosed C) (z : S) (c : ℝ) :
    IsClosed (frozenSlice C z c) :=
  hC.inter (frozenConstraint_isClosed z c)

theorem frozenSlice_isCompact {C : Set (S → ℝ)} (hC : IsCompact C) (z : S) (c : ℝ) :
    IsCompact (frozenSlice C z c) :=
  hC.inter_right (frozenConstraint_isClosed z c)

theorem frozenConstraint_convex (z : S) (c : ℝ) :
    Convex ℝ (frozenConstraint z c) := by
  intro f hf g hg a b _ _ _ x
  change a * f (z * x) + b * g (z * x) = c * (a * f x + b * g x)
  rw [hf x, hg x]
  ring

theorem frozenSlice_convex {C : Set (S → ℝ)} (hC : Convex ℝ C) (z : S) (c : ℝ) :
    Convex ℝ (frozenSlice C z c) :=
  hC.inter (frozenConstraint_convex z c)

theorem normalizedTranslate_mem_frozenConstraint {z w : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) :
    normalizedTranslate w f ∈ frozenConstraint z c := by
  intro x
  change f (w * (z * x)) / f w = c * (f (w * x) / f w)
  rw [show w * (z * x) = z * (w * x) by ac_rfl, hf (w * x)]
  ring

theorem frozenSlice_mapsTo_normalizedTranslate {C : Set (S → ℝ)} {z w : S} {c : ℝ}
    (hC : MapsTo (normalizedTranslate w) C C) :
    MapsTo (normalizedTranslate w) (frozenSlice C z c) (frozenSlice C z c) := by
  intro f hf
  exact ⟨hC hf.1, normalizedTranslate_mem_frozenConstraint hf.2⟩

theorem frozenConstraint_value {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) : f z = c := by
  simpa only [mul_one, hf1] using hf 1

theorem frozenConstraint_normalizedTranslate_eq {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) (hfz : f z ≠ 0) :
    normalizedTranslate z f = f := by
  funext x
  change f (z * x) / f z = f x
  rw [hf x, ← frozenConstraint_value hf hf1]
  exact mul_div_cancel_left₀ (f x) hfz

theorem normalizedTranslate_eq_mem_frozenConstraint {z : S} {f : S → ℝ}
    (hfz : f z ≠ 0) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) := by
  intro x
  have hx : f (z * x) / f z = f x := congrFun hf x
  exact (div_eq_iff hfz).mp hx |>.trans (mul_comm _ _)

theorem normalizedTranslate_eq_nonzero {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) : f z ≠ 0 := by
  intro hfz
  have hx := congrFun hf 1
  simp [normalizedTranslate, hfz, hf1] at hx

theorem normalizedTranslate_eq_mem_frozenConstraint_of_normalized {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) :=
  normalizedTranslate_eq_mem_frozenConstraint (normalizedTranslate_eq_nonzero hf1 hf) hf

theorem normalizedTranslate_eq_mem_frozenSlice {C : Set (S → ℝ)} {z : S} {f : S → ℝ}
    (hfC : f ∈ C) (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenSlice C z (f z) :=
  ⟨hfC, normalizedTranslate_eq_mem_frozenConstraint_of_normalized hf1 hf⟩

/-- Every finite collection of multiplication identities holds throughout a
nonempty compact convex subset that remains invariant under all translates. -/
theorem exists_finite_multiplicative_slice {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K)
    (t : Finset {z : S // z ≠ 0}) :
    ∃ C : Set (S → ℝ), C ⊆ K ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
      (∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) C C) ∧
      ∀ f ∈ C, ∀ z ∈ t, ∀ x, f (z.val * x) = f z.val * f x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨K, Subset.rfl, hKne, hKcompact, hKconvex, hKmap, by simp⟩
  | @insert z t hzt ih =>
      obtain ⟨C, hCK, hCne, hCcompact, hCconvex, hCmap, hCt⟩ := ih
      let P : C → C := fun f =>
        ⟨normalizedTranslate z.val f.val, hCmap z.val z.property f.property⟩
      have hP : Continuous P := by
        apply Continuous.subtype_mk
        exact normalizedTranslate_continuousOn z.val
          (fun f hf => hKnonzero f (hCK hf) z.val z.property)
      obtain ⟨g, hg⟩ := compact_convex_fixedPoint_of_continuous
        hCcompact hCconvex hCne P hP
      have hg' : normalizedTranslate z.val g.val = g.val := congrArg Subtype.val hg
      let c : ℝ := g.val z.val
      let D := frozenSlice C z.val c
      have hDC : D ⊆ C := fun _ hf => hf.1
      have hDK : D ⊆ K := hDC.trans hCK
      refine ⟨D, hDK, ?_, frozenSlice_isCompact hCcompact z.val c,
        frozenSlice_convex hCconvex z.val c, ?_, ?_⟩
      · exact ⟨g.val, normalizedTranslate_eq_mem_frozenSlice g.property
          (hKnorm g.val (hCK g.property)) hg'⟩
      · intro w hw
        exact frozenSlice_mapsTo_normalizedTranslate (hCmap w hw)
      · intro f hf w hw x
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · have hfc : f w.val = c := frozenConstraint_value hf.2 (hKnorm f (hDK hf))
          rw [hfc]
          exact hf.2 x
        · exact hCt f (hDC hf) w hwt x

/-- A compact convex normalized state space invariant under multiplication
translates contains a multiplicative state. Frozen eigenvalue slices preserve
convexity at each finite fixed-point step. -/
theorem exists_multiplicative_of_invariant_states {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1) (hKzero : ∀ f ∈ K, f 0 = 0)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K) :
    ∃ f ∈ K, ∀ x y, f (x * y) = f x * f y := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let F : {z : S // z ≠ 0} → Set K :=
    fun z => {f | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
  have hFclosed (z : {z : S // z ≠ 0}) : IsClosed (F z) := by
    change IsClosed {f : K | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_apply (z.val * x)).comp continuous_subtype_val)
        (((continuous_apply z.val).comp continuous_subtype_val).mul
          ((continuous_apply x).comp continuous_subtype_val))
  have hFfinite (t : Finset {z : S // z ≠ 0}) : (⋂ z ∈ t, F z).Nonempty := by
    obtain ⟨C, hCK, hCne, _, _, _, hCt⟩ := exists_finite_multiplicative_slice
      hKcompact hKconvex hKne hKnorm hKnonzero hKmap t
    obtain ⟨f, hf⟩ := hCne
    refine ⟨⟨f, hCK hf⟩, ?_⟩
    simp only [mem_iInter]
    intro z hz
    exact hCt f hf z hz
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty hFclosed hFfinite
  refine ⟨f.val, f.property, fun x y => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hKzero f.val f.property]
  · exact mem_iInter.mp hf ⟨x, hx⟩ y

/-- Appendix A.2 for a ranked restriction semiring: once the preliminary
normalized state set is nonempty, it contains a multiplicative state. -/
theorem normalizedStates_exists_multiplicative [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ f ∈ normalizedStates (fun x => (R x : ℝ)) d k,
      ∀ x y, f (x * y) = f x * f y := by
  apply exists_multiplicative_of_invariant_states
    (normalizedStates_isCompact _ d k) (normalizedStates_convex _ d k) hne
  · exact fun _ hf => hf.2.1
  · exact fun _ hf => state_zero hf
  · intro f hf z hz
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (state_one_le hf (hunit z hz)))
  · intro z hz f hf
    exact state_rescale hf z (hunit z hz) (hmulmono z) (hdom z)

/-- The multiplicative state as a normalized monotone semiring homomorphism,
with the original rank bounds and detector inequality preserved. -/
theorem exists_monotone_semiringHom_of_normalizedStates [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ R x) ∧ k ≤ χ d := by
  obtain ⟨f, hf, hfmul⟩ :=
    normalizedStates_exists_multiplicative R d k hunit hmulmono hdom hne
  let χ : S →+* ℝ :=
    { toFun := f
      map_zero' := state_zero hf
      map_one' := hf.2.1
      map_add' := hf.2.2.1
      map_mul' := hfmul }
  refine ⟨χ, ?_, hf.1, ?_⟩
  · intro x y hxy
    exact hf.2.2.2.1 x y hxy
  · simpa only [χ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_one, hf.2.1] using hf.2.2.2.2 1

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule042
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.MultiplicativeStates -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead -/
section FlattenModule043



namespace OAI

/-!
# Removing polynomial overhead from exponential inequalities

The interpolation argument in Section 4 bounds tensor powers with an extra
linear factor. Such a factor does not change their exponential growth rate.
The statements below include eventual inequalities and constant factors, so
the same argument also removes fixed counting losses in entropy limits.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- An eventual linear prefactor cannot increase an exponential growth rate. -/
theorem le_of_eventually_pow_le_linear_mul_pow {a b K C : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ ((j : ℝ) * K + C) * a ^ j) :
    b ≤ a := by
  by_contra hba
  have hab : a < b := lt_of_not_ge hba
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hr₀ : 0 ≤ a / b := div_nonneg ha hb.le
  have hr₁ : a / b < 1 := (div_lt_one hb).2 hab
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hr₀ hr₁).mul_const K
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).const_mul C
  have hlim : Tendsto (fun j : ℕ => ((j : ℝ) * K + C) * (a / b) ^ j)
      atTop (𝓝 0) := by
    convert hlinear.add hconstant using 1 <;> try simp
    funext j
    ring
  have hbound : ∀ᶠ j : ℕ in atTop,
      1 ≤ ((j : ℝ) * K + C) * (a / b) ^ j := by
    filter_upwards [h] with j hj
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hb j)).2 hj
    simpa only [div_self (pow_ne_zero j hb.ne'), mul_div_assoc, div_pow] using hdiv
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim hbound
  linarith

/-- Removing the linear interpolation overhead from inequalities for all powers. -/
theorem le_of_pow_le_linear_mul_pow {a b K : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ ((j : ℝ) * K + 1) * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_linear_mul_pow ha (Eventually.of_forall h)

/-- Fixed multiplicative losses disappear on taking exponential growth rates. -/
theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a := by
  apply le_of_eventually_pow_le_linear_mul_pow (K := 0) (C := C) ha
  simpa only [mul_zero, zero_add] using h

/-- An all-powers form of constant-factor removal. -/
theorem le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ C * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_const_mul_pow ha (Eventually.of_forall h)

/-- In particular, the fixed factor five in the type-counting bound is harmless. -/
theorem le_of_pow_le_five_mul_pow {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ 5 * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_const_mul_pow ha (Eventually.of_forall h)

/-- A fixed counting loss does not contribute to a normalized logarithmic
growth rate. The exponent may run through any sequence tending to infinity,
including the multiples of a common denominator used for rational types. -/
theorem exp_le_of_tendsto_log_div {u : ℕ → ℝ} {n : ℕ → ℕ} {b C L : ℝ}
    (hb : 0 < b) (hC : 0 < C) (hn : Tendsto n atTop atTop)
    (hu : ∀ᶠ k in atTop, 0 < u k)
    (hlim : Tendsto (fun k => Real.log (u k) / (n k : ℝ)) atTop (𝓝 L))
    (hbound : ∀ᶠ k in atTop, u k ≤ C * b ^ n k) :
    Real.exp L ≤ b := by
  have hconstant : Tendsto (fun k => Real.log C / (n k : ℝ) + Real.log b)
      atTop (𝓝 (Real.log b)) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).comp hn).add_const
      (Real.log b)
  have hnormalized : ∀ᶠ k in atTop,
      Real.log (u k) / (n k : ℝ) ≤ Real.log C / (n k : ℝ) + Real.log b := by
    filter_upwards [hu, hbound, hn.eventually (eventually_gt_atTop 0)] with k huk hk hnk
    have hnpos : (0 : ℝ) < n k := by exact_mod_cast hnk
    have hlog := Real.log_le_log huk hk
    rw [Real.log_mul hC.ne' (pow_ne_zero _ hb.ne'), Real.log_pow] at hlog
    calc
      Real.log (u k) / (n k : ℝ) ≤
          (Real.log C + (n k : ℝ) * Real.log b) / (n k : ℝ) :=
        (div_le_div_iff_of_pos_right hnpos).2 hlog
      _ = Real.log C / (n k : ℝ) + Real.log b := by
        field_simp
  have hL : L ≤ Real.log b := le_of_tendsto_of_tendsto hlim hconstant hnormalized
  simpa only [Real.exp_log hb] using Real.exp_le_exp.mpr hL

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule043
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.SpectralLimit -/
section FlattenModule044



namespace OAI

/-!
# Removing positive slack from the spectral inequality

The positive slack in the exponent can be sent to zero with the matrix size
fixed. A bound at all positive natural sizes then removes a fixed additive
error term.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter Topology

/-- Continuity removes the positive slack in the spectral exponent. -/
theorem spectral_bound_of_positive_slack {ν k D : ℝ} {d n : ℕ}
    (hν : 0 < ν) (hn : 1 ≤ n)
    (hbound : ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ (n : ℝ) * k + D) :
    (d : ℝ) ^ ν * (n : ℝ) ≤ (n : ℝ) * k + D := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    exact this.ne'
  have hδ : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdenom : Tendsto (fun m : ℕ => ν + 1 / ((m : ℝ) + 1))
      atTop (𝓝 ν) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := ν)).add hδ
  have hexponent : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1)))
      atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1)))
        atTop (𝓝 (ν / ν)) := by
      exact (tendsto_const_nhds (x := ν)).div hdenom hν.ne'
    rwa [div_self hν.ne'] at h
  have hpower : Tendsto
      (fun m : ℕ => (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + 1 / ((m : ℝ) + 1))))
      atTop (𝓝 ((d : ℝ) ^ ν * (n : ℝ))) := by
    simpa using tendsto_const_nhds.mul
      ((Real.continuousAt_const_rpow hn0).tendsto.comp hexponent)
  exact le_of_tendsto' hpower fun m => hbound _ (by positivity)

/-- A fixed additive error cannot enlarge a coefficient bounded at every
positive natural size. -/
theorem coefficient_le_of_nat_mul_bound {a k D : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → a * (n : ℝ) ≤ (n : ℝ) * k + D) :
    a ≤ k := by
  by_contra h
  have hgap : 0 < a - k := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (D / (a - k)) 0)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    omega
  have hlarge : D < (n : ℝ) * (a - k) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_left _ _) hn)
  have hsmall := hbound n hn1
  nlinarith

/-- Uniform spectral inequalities for all positive sizes and all positive
slacks force the desired coefficient bound. -/
theorem spectral_coefficient_le_of_all_nat {ν k D : ℝ} {d : ℕ}
    (hν : 0 < ν)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ (n : ℝ) * k + D) :
    (d : ℝ) ^ ν ≤ k := by
  apply coefficient_le_of_nat_mul_bound
  intro n hn
  exact spectral_bound_of_positive_slack hν hn (hbound n hn)

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule044
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.SpectralLimit -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition -/
section FlattenModule045

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

def composeRestrictionMatrix [Fintype X']
    (D : X'' → X' → K) (A : X' → X → K) : X'' → X → K :=
  fun x'' x => ∑ x', D x'' x' * A x' x

private theorem sum_three_mul [Fintype X] [Fintype Y] [Fintype Z]
    (a : X → K) (b : Y → K) (c : Z → K) (t : K) :
    (∑ x, a x) * (∑ y, b y) * (∑ z, c z) * t =
      ∑ x, ∑ y, ∑ z, a x * b y * c z * t := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]

private theorem sum_six_comm [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (f : X' → Y' → Z' → X → Y → Z → K) :
    (∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z, f x' y' z' x y z) =
      ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z', f x' y' z' x y z := by
  calc
    _ = ∑ p : X' × Y' × Z', ∑ q : X × Y × Z,
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : X × Y × Z, ∑ p : X' × Y' × Z',
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

private theorem sum_interleaved_triples {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X → Y → Z → U → V → W → K) :
    (∑ x, ∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, f x y z u v w := by
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
        ∑ y, ∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w) =
            ∑ u, ∑ z, ∑ v, ∑ w, f x y z u v w := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem restrict_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : X'' → X' → K) (E : Y'' → Y' → K) (F : Z'' → Z' → K)
    (T : Tensor K X Y Z) :
    restrict D E F (restrict A B C T) =
      restrict (composeRestrictionMatrix D A) (composeRestrictionMatrix E B)
        (composeRestrictionMatrix F C) T := by
  funext x'' y'' z''
  unfold restrict composeRestrictionMatrix
  calc
    _ = ∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z,
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := by
      simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z',
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := sum_six_comm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [sum_three_mul]
      apply Finset.sum_congr rfl
      intro x' hx'
      apply Finset.sum_congr rfl
      intro y' hy'
      apply Finset.sum_congr rfl
      intro z' hz'
      ring

theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (fun (x : X' × U') (u : X × U) => A x.1 u.1 * D x.2 u.2)
      (fun (y : Y' × V') (v : Y × V) => B y.1 v.1 * E y.2 v.2)
      (fun (z : Z' × W') (w : Z × W) => C z.1 w.1 * F z.2 w.2) (product T S) =
      product (restrict A B C T) (restrict D E F S) := by
  funext x' y' z'
  simp only [restrict, product, Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * D x'.2 u) * (B y'.1 y * E y'.2 v) *
          (C z'.1 z * F z'.2 w) * (T x y z * S u v w) :=
      sum_interleaved_triples _
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * B y'.1 y * C z'.1 z * T x y z) *
          (D x'.2 u * E y'.2 v * F z'.2 w * S u v w) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = _ := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem restrict_identity [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) :
    restrict (fun x' x => if x = x' then 1 else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T = T := by
  calc
    _ = pullback id id id T := (pullback_eq_restrict id id id T).symm
    _ = T := rfl

end Algebra

section ComplexTopology

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [Fintype X''] [Fintype Y''] [Fintype Z'']

theorem degeneratesTo_restrict (T : Tensor ℂ X Y Z)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    DegeneratesTo T (restrict A B C T) :=
  subset_closure ⟨A, B, C, rfl⟩

theorem DegeneratesTo.refl (T : Tensor ℂ X Y Z) : DegeneratesTo T T := by
  classical
  have h := degeneratesTo_restrict T
    (fun x' x => if x = x' then 1 else 0)
    (fun y' y => if y = y' then 1 else 0)
    (fun z' z => if z = z' then 1 else 0)
  simpa only [restrict_identity] using h

omit [Fintype X''] [Fintype Y''] [Fintype Z''] in
theorem mem_restrictionOrbit_restrict {T : Tensor ℂ X Y Z}
    {U : Tensor ℂ X' Y' Z'} (h : U ∈ restrictionOrbit T)
    (D : X'' → X' → ℂ) (E : Y'' → Y' → ℂ) (F : Z'' → Z' → ℂ) :
    restrict D E F U ∈ restrictionOrbit T := by
  rcases h with ⟨A, B, C, rfl⟩
  exact ⟨composeRestrictionMatrix D A, composeRestrictionMatrix E B,
    composeRestrictionMatrix F C, restrict_restrict A B C D E F T⟩

theorem DegeneratesTo.restrict {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (h : DegeneratesTo T U)
    (D : X'' → X' → ℂ) (E : Y'' → Y' → ℂ) (F : Z'' → Z' → ℂ) :
    DegeneratesTo T (Tensor.restrict D E F U) := by
  have hclosed : IsClosed {S : Tensor ℂ X' Y' Z' |
      DegeneratesTo T (Tensor.restrict D E F S)} :=
    isClosed_closure.preimage (continuous_restrict D E F)
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | DegeneratesTo T (Tensor.restrict D E F S)} := by
    intro S hS
    exact subset_closure (mem_restrictionOrbit_restrict hS D E F)
  exact closure_minimal hsubset hclosed h

theorem DegeneratesTo.trans {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    {V : Tensor ℂ X'' Y'' Z''} (hTU : DegeneratesTo T U)
    (hUV : DegeneratesTo U V) : DegeneratesTo T V := by
  have hsubset : restrictionOrbit U ⊆
      {S : Tensor ℂ X'' Y'' Z'' | DegeneratesTo T S} := by
    rintro S ⟨D, E, F, rfl⟩
    exact hTU.restrict D E F
  exact closure_minimal hsubset isClosed_closure hUV

theorem DegeneratesTo.of_restrict {T : Tensor ℂ X Y Z} {V : Tensor ℂ X'' Y'' Z''}
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ)
    (h : DegeneratesTo (Tensor.restrict A B C T) V) : DegeneratesTo T V :=
  (degeneratesTo_restrict T A B C).trans h

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule045
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSum -/
section FlattenModule046



namespace OAI

/-!
# Binary sums of finite coefficient tensors

The coordinate types of the summands may differ.  The identities below give
the explicit changes of coordinates needed for the tensor semiring, together
with the block-diagonal restriction maps.
-/

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {K X Y Z U V W A B C : Type*} [CommSemiring K]

/-- The binary direct sum, with each of its three block labels retained. -/
def sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

/-- The block-diagonal sum of two restriction matrices. -/
def sumRestriction {X' U' : Type*} (f : X' → X → K) (g : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => f x' x
  | .inr u', .inr u => g u' u
  | _, _ => 0

/-- Independent restrictions of both summands give a restriction of the sum. -/
theorem sumTensor_restrict
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X' → X → K) (g : Y' → Y → K) (h : Z' → Z → K)
    (f' : U' → U → K) (g' : V' → V → K) (h' : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (sumRestriction f f') (sumRestriction g g')
      (sumRestriction h h') (sumTensor T S) =
      sumTensor (Tensor.restrict f g h T) (Tensor.restrict f' g' h' S) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.restrict, sumRestriction, sumTensor, Fintype.sum_sum_type]

/-- Exchanging the two blocks is a coordinate permutation. -/
theorem sumTensor_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumComm X U) (Equiv.sumComm Y V)
      (Equiv.sumComm Z W) (sumTensor S T) = sumTensor T S := by
  funext x y z
  cases x <;> cases y <;> cases z <;> rfl

/-- Reassociating the three blocks is a coordinate permutation. -/
theorem sumTensor_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumAssoc X U A) (Equiv.sumAssoc Y V B)
      (Equiv.sumAssoc Z W C) (sumTensor T (sumTensor S R)) =
      sumTensor (sumTensor T S) R := by
  funext x y z
  rcases x with (x | x) | x <;>
    rcases y with (y | y) | y <;>
    rcases z with (z | z) | z <;> rfl

/-- An empty right summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_right [IsEmpty U] [IsEmpty V] [IsEmpty W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumEmpty X U).symm (Equiv.sumEmpty Y V).symm
      (Equiv.sumEmpty Z W).symm (sumTensor T S) = T := by
  rfl

/-- An empty left summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_left [IsEmpty X] [IsEmpty Y] [IsEmpty Z]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.emptySum X U).symm (Equiv.emptySum Y V).symm
      (Equiv.emptySum Z W).symm (sumTensor T S) = S := by
  rfl

/-- Tensor product distributes over the first binary sum by coordinate
permutation. -/
theorem sumTensor_product (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumProdDistrib X U A).symm
      (Equiv.sumProdDistrib Y V B).symm (Equiv.sumProdDistrib Z W C).symm
      (Tensor.product (sumTensor T S) R) =
      sumTensor (Tensor.product T R) (Tensor.product S R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

/-- Tensor product distributes over the second binary sum by coordinate
permutation. -/
theorem product_sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodSumDistrib X U A).symm
      (Equiv.prodSumDistrib Y V B).symm (Equiv.prodSumDistrib Z W C).symm
      (Tensor.product T (sumTensor S R)) =
      sumTensor (Tensor.product T S) (Tensor.product T R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

/-- Exchanging product factors is a coordinate permutation. -/
theorem tensorProduct_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.prodComm X U) (Equiv.prodComm Y V)
      (Equiv.prodComm Z W) (Tensor.product S T) = Tensor.product T S := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_comm]

/-- Reassociating product factors is a coordinate permutation. -/
theorem tensorProduct_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodAssoc X U A) (Equiv.prodAssoc Y V B)
      (Equiv.prodAssoc Z W C) (Tensor.product T (Tensor.product S R)) =
      Tensor.product (Tensor.product T S) R := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_assoc]

/-- Scalar multiplication by one is the right unit for tensor product. -/
theorem tensorProduct_one_right (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.prodPUnit X).symm (Equiv.prodPUnit Y).symm
      (Equiv.prodPUnit Z).symm
      (Tensor.product T (fun (_ _ _ : PUnit) => (1 : K))) = T := by
  funext x y z
  simp [Tensor.pullback, Tensor.product]

/-- Scalar multiplication by one is the left unit for tensor product. -/
theorem tensorProduct_one_left (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.punitProd X).symm (Equiv.punitProd Y).symm
      (Equiv.punitProd Z).symm
      (Tensor.product (fun (_ _ _ : PUnit) => (1 : K)) T) = T := by
  funext x y z
  simp [Tensor.pullback, Tensor.product]

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule046
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSum -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring -/
section FlattenModule047





namespace OAI

/-!
# Finite tensors modulo mutual restriction

Representatives have three natural-number dimensions and complex coefficients.
The order is actual linear restriction, and equality in the quotient is mutual
restriction. In particular, changing coordinates does not change the class.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.TensorSemiring

section Restriction

variable {X Y Z U V W P Q R : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]
variable [Fintype P] [Fintype Q] [Fintype R]

/-- `T` is obtained from `S` by three linear maps on its coordinate spaces. -/
def IsRestriction (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) : Prop :=
  ∃ (A : X → U → ℂ) (B : Y → V → ℂ) (C : Z → W → ℂ),
    T = Tensor.restrict A B C S

theorem IsRestriction.refl (T : Tensor ℂ X Y Z) : IsRestriction T T := by
  classical
  exact ⟨_, _, _, (Tensor.restrict_identity T).symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.trans {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W}
    {L : Tensor ℂ P Q R} (hTS : IsRestriction T S) (hSL : IsRestriction S L) :
    IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩
  rcases hSL with ⟨D, E, F, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix A D, Tensor.composeRestrictionMatrix B E,
    Tensor.composeRestrictionMatrix C F, Tensor.restrict_restrict D E F A B C L⟩

omit [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.pullback (T : Tensor ℂ X Y Z)
    (fx : U → X) (fy : V → Y) (fz : W → Z) :
    IsRestriction (Tensor.pullback fx fy fz T) T := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.of_reindex (T : Tensor ℂ X Y Z)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    IsRestriction T (Tensor.pullback ex ey ez T) := by
  have h := IsRestriction.pullback (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  rwa [heq] at h

theorem IsRestriction.reindex_iff
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W)
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype U'] [Fintype V'] [Fintype W']
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z)
    (eu : U' ≃ U) (ev : V' ≃ V) (ew : W' ≃ W) :
    IsRestriction (Tensor.pullback ex ey ez T) (Tensor.pullback eu ev ew S) ↔
      IsRestriction T S := by
  constructor
  · intro h
    exact (IsRestriction.of_reindex T ex ey ez).trans
      (h.trans (IsRestriction.pullback S eu ev ew))
  · intro h
    exact (IsRestriction.pullback T ex ey ez).trans
      (h.trans (IsRestriction.of_reindex S eu ev ew))

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.product {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W}
    {T' : Tensor ℂ P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor ℂ U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (Tensor.restrict_product A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.sum {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W}
    {T' : Tensor ℂ P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor ℂ U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (sumTensor_restrict A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.zero (S : Tensor ℂ U V W) :
    IsRestriction (0 : Tensor ℂ X Y Z) S := by
  refine ⟨0, 0, 0, ?_⟩
  funext x y z
  simp [Tensor.restrict]

theorem IsRestriction.rank_le {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W}
    (h : IsRestriction T S) : exactRank T ≤ exactRank S := by
  rcases h with ⟨A, B, C, rfl⟩
  exact exactRank_restrict_le S A B C

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.eq_zero_of_zero {T : Tensor ℂ X Y Z}
    (h : IsRestriction T (0 : Tensor ℂ U V W)) : T = 0 := by
  rcases h with ⟨A, B, C, h⟩
  funext x y z
  rw [h]
  simp [Tensor.restrict]

end Restriction

/-- A set-sized presentation of any finite complex coefficient tensor. -/
structure FiniteTensor where
  nx : ℕ
  ny : ℕ
  nz : ℕ
  coeff : Tensor ℂ (Fin nx) (Fin ny) (Fin nz)

namespace FiniteTensor

/-- Replace arbitrary finite coordinate sets by standard finite sets. -/
def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : FiniteTensor where
  nx := Fintype.card X
  ny := Fintype.card Y
  nz := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

instance : LE FiniteTensor := ⟨fun T S => IsRestriction T.coeff S.coeff⟩

instance : Preorder FiniteTensor where
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

theorem ofTensor_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    ofTensor T ≤ ofTensor S ↔ IsRestriction T S :=
  IsRestriction.reindex_iff T S _ _ _ _ _ _

def product (T S : FiniteTensor) : FiniteTensor :=
  ofTensor (Tensor.product T.coeff S.coeff)

def sum (T S : FiniteTensor) : FiniteTensor :=
  ofTensor (sumTensor T.coeff S.coeff)

theorem product_mono {T T' S S' : FiniteTensor} (hT : T ≤ T') (hS : S ≤ S') :
    product T S ≤ product T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.product hT hS)

theorem sum_mono {T T' S S' : FiniteTensor} (hT : T ≤ T') (hS : S ≤ S') :
    sum T S ≤ sum T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.sum hT hS)

end FiniteTensor

/-- Finite complex tensors, with two presentations identified exactly when
each is a linear restriction of the other. -/
abbrev TensorClass := Antisymmetrization FiniteTensor (· ≤ ·)

/-- The class of a finite tensor presentation. -/
def tensorClass (T : FiniteTensor) : TensorClass := toAntisymmetrization (· ≤ ·) T

@[simp] theorem tensorClass_eq_iff (T S : FiniteTensor) :
    tensorClass T = tensorClass S ↔ T ≤ S ∧ S ≤ T :=
  toAntisymmetrization_eq (· ≤ ·) T S

@[simp] theorem tensorClass_le_iff (T S : FiniteTensor) :
    tensorClass T ≤ tensorClass S ↔ T ≤ S := Iff.rfl

/-- The quotient class of a tensor on any three finite coordinate sets. -/
def classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : TensorClass := tensorClass (FiniteTensor.ofTensor T)

theorem classOf_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S := FiniteTensor.ofTensor_le_iff T S

theorem classOf_eq_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    classOf T = classOf S ↔ IsRestriction T S ∧ IsRestriction S T := by
  rw [le_antisymm_iff, classOf_le_iff, classOf_le_iff]

theorem classOf_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    classOf (Tensor.pullback ex ey ez T) = classOf T :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.pullback T ex ey ez,
    IsRestriction.of_reindex T ex ey ez⟩

theorem classOf_eq_of_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

@[simp] theorem classOf_coeff (T : FiniteTensor) : classOf T.coeff = tensorClass T := by
  apply (tensorClass_eq_iff _ _).mpr
  exact ⟨IsRestriction.pullback T.coeff _ _ _, IsRestriction.of_reindex T.coeff _ _ _⟩

instance : Mul TensorClass where
  mul := Quotient.map₂ FiniteTensor.product (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.product_mono hT.1 hS.1,
      FiniteTensor.product_mono hT.2 hS.2⟩)

instance : Add TensorClass where
  add := Quotient.map₂ FiniteTensor.sum (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.sum_mono hT.1 hS.1, FiniteTensor.sum_mono hT.2 hS.2⟩)

@[simp] theorem tensorClass_product (T S : FiniteTensor) :
    tensorClass T * tensorClass S = tensorClass (FiniteTensor.product T S) := rfl

@[simp] theorem tensorClass_sum (T S : FiniteTensor) :
    tensorClass T + tensorClass S = tensorClass (FiniteTensor.sum T S) := rfl

theorem classOf_product {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S := by
  symm
  exact classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)

theorem classOf_sum {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := by
  symm
  have h := classOf_reindex (sumTensor T S)
    (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
  change classOf (sumTensor (FiniteTensor.ofTensor T).coeff
    (FiniteTensor.ofTensor S).coeff) = _
  have heq : sumTensor (FiniteTensor.ofTensor T).coeff (FiniteTensor.ofTensor S).coeff =
      Tensor.pullback
        (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
        (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
        (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
        (sumTensor T S) := by
    funext x y z
    cases x <;> cases y <;> cases z <;> rfl
  rw [heq]
  exact h

instance : Zero TensorClass := ⟨classOf (0 : Tensor ℂ Empty Empty Empty)⟩
instance : One TensorClass := ⟨classOf (fun (_ _ _ : PUnit.{1}) => (1 : ℂ))⟩

theorem classOf_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    classOf (0 : Tensor ℂ X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

private theorem class_add_assoc (a b c : TensorClass) : (a + b) + c = a + (b + c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a + tensorClass b) + tensorClass c =
    tensorClass a + (tensorClass b + tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_assoc a.coeff b.coeff c.coeff)

private theorem class_add_comm (a b : TensorClass) : a + b = b + a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a + tensorClass b = tensorClass b + tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_comm a.coeff b.coeff)

private theorem class_add_zero (a : TensorClass) : a + 0 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a + 0 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff + classOf (0 : Tensor ℂ Empty Empty Empty) = classOf a.coeff
  rw [← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (sumTensor_empty_right a.coeff
    (0 : Tensor ℂ Empty Empty Empty))).symm

private theorem class_zero_add (a : TensorClass) : 0 + a = a :=
  (class_add_comm 0 a).trans (class_add_zero a)

private theorem class_mul_assoc (a b c : TensorClass) : (a * b) * c = a * (b * c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a * tensorClass b) * tensorClass c =
    tensorClass a * (tensorClass b * tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_assoc a.coeff b.coeff c.coeff)

private theorem class_mul_comm (a b : TensorClass) : a * b = b * a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a * tensorClass b = tensorClass b * tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_comm a.coeff b.coeff)

private theorem class_mul_one (a : TensorClass) : a * 1 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 1 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (fun (_ _ _ : PUnit.{1}) => (1 : ℂ)) = classOf a.coeff
  rw [← classOf_product]
  exact (classOf_eq_of_reindex _ _ _ (tensorProduct_one_right a.coeff)).symm

private theorem class_one_mul (a : TensorClass) : 1 * a = a :=
  (class_mul_comm 1 a).trans (class_mul_one a)

private theorem class_mul_zero (a : TensorClass) : a * 0 = 0 := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 0 = 0
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (0 : Tensor ℂ Empty Empty Empty) = 0
  rw [← classOf_product]
  have heq : Tensor.product a.coeff (0 : Tensor ℂ Empty Empty Empty) = 0 := by
    funext x y z
    simp [Tensor.product]
  rw [heq, classOf_zero]

private theorem class_zero_mul (a : TensorClass) : 0 * a = 0 :=
  (class_mul_comm 0 a).trans (class_mul_zero a)

private theorem class_left_distrib (a b c : TensorClass) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change tensorClass a * (tensorClass b + tensorClass c) =
    tensorClass a * tensorClass b + tensorClass a * tensorClass c
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product, ← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (product_sumTensor a.coeff b.coeff c.coeff)).symm

private theorem class_right_distrib (a b c : TensorClass) : (a + b) * c = a * c + b * c := by
  rw [class_mul_comm, class_left_distrib, class_mul_comm c a, class_mul_comm c b]

instance : CommSemiring TensorClass where
  add_assoc := class_add_assoc
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero := class_add_zero
  nsmul := nsmulRec
  mul_assoc := class_mul_assoc
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one := class_mul_one
  zero_mul := class_zero_mul
  mul_zero := class_mul_zero
  left_distrib := class_left_distrib
  right_distrib := class_right_distrib

theorem mul_mono {T T' S S' : TensorClass} (hT : T ≤ T') (hS : S ≤ S') :
    T * S ≤ T' * S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.product_mono hT hS

theorem add_mono {T T' S S' : TensorClass} (hT : T ≤ T') (hS : S ≤ S') :
    T + S ≤ T' + S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.sum_mono hT hS

/-- Every tensor class is nonnegative in the restriction order. -/
theorem zero_le (T : TensorClass) : 0 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change (0 : TensorClass) ≤ tensorClass T
  rw [← classOf_coeff T]
  exact (classOf_le_iff _ _).mpr (IsRestriction.zero T.coeff)

instance : OrderBot TensorClass where
  bot := 0
  bot_le := zero_le

instance : IsOrderedAddMonoid TensorClass where
  add_le_add_left _ _ h _c := add_mono h le_rfl

instance : IsOrderedMonoid TensorClass where
  mul_le_mul_left _ _ h _c := mul_mono h le_rfl

instance : IsOrderedRing TensorClass where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    exact mul_mono le_rfl hbc
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    exact mul_mono hbc le_rfl

/-- Exact rank descends to mutual-restriction classes. -/
def rank : TensorClass → ℕ := Quotient.lift (fun T : FiniteTensor => exactRank T.coeff)
  (by
    intro T S h
    exact le_antisymm (IsRestriction.rank_le h.1) (IsRestriction.rank_le h.2))

@[simp] theorem rank_tensorClass (T : FiniteTensor) :
    rank (tensorClass T) = exactRank T.coeff := rfl

@[simp] theorem rank_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : rank (classOf T) = exactRank T :=
  exactRank_reindex T _ _ _

theorem rank_mono {T S : TensorClass} (h : T ≤ S) : rank T ≤ rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  exact IsRestriction.rank_le h

theorem rank_mul_le (T S : TensorClass) : rank (T * S) ≤ rank T * rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change rank (tensorClass T * tensorClass S) ≤ rank (tensorClass T) * rank (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_product]
  simp only [rank_classOf]
  exact exactRank_product_le _ _

/-- Square matrix multiplication as an element of the tensor semiring. -/
def matrixClass (n : ℕ) : TensorClass := classOf (Tensor.matrixMultiplication n n n)

@[simp] theorem rank_matrixClass (n : ℕ) : rank (matrixClass n) = exactMatrixRank n :=
  rank_classOf _

private theorem classOf_matrixCoefficients_equiv {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (e : A ≃ B) :
    classOf (Tensor.matrixCoefficients (K := ℂ) A A A) =
      classOf (Tensor.matrixCoefficients (K := ℂ) B B B) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e)
    (Equiv.prodCongr e e)
  funext x y z
  simp [Tensor.pullback, Tensor.matrixCoefficients, e.injective.eq_iff]

theorem matrixClass_mul (m n : ℕ) : matrixClass (m * n) = matrixClass m * matrixClass n := by
  let e : Fin (m * n) ≃ Fin m × Fin n := Fintype.equivOfCardEq (by simp)
  have h := classOf_matrixCoefficients_equiv e
  change matrixClass (m * n) = classOf (Tensor.matrixCoefficients (K := ℂ)
    (Fin m × Fin n) (Fin m × Fin n) (Fin m × Fin n)) at h
  rw [h]
  change _ = classOf (Tensor.matrixCoefficients (K := ℂ) (Fin m) (Fin m) (Fin m)) *
    classOf (Tensor.matrixCoefficients (K := ℂ) (Fin n) (Fin n) (Fin n))
  rw [← classOf_product]
  apply classOf_eq_of_reindex (Equiv.prodProdProdComm _ _ _ _)
    (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
  funext x y z
  exact Tensor.matrixCoefficients_product x y z

@[simp] theorem matrixClass_one : matrixClass 1 = 1 := by
  let e : Fin 1 × Fin 1 ≃ PUnit.{1} := Fintype.equivOfCardEq (by simp)
  apply classOf_eq_of_reindex e e e
  funext x y z
  have hxy : x.2 = y.1 := Subsingleton.elim _ _
  have hyz : y.2 = z.1 := Subsingleton.elim _ _
  have hzx : z.2 = x.1 := Subsingleton.elim _ _
  simp [Tensor.pullback, Tensor.matrixMultiplication, hxy, hyz, hzx]

theorem matrixClass_pow (m j : ℕ) : matrixClass (m ^ j) = matrixClass m ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, matrixClass_mul, ih, pow_succ]

theorem classOf_eq_zero_iff {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : classOf T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr : IsRestriction T (0 : Tensor ℂ Empty Empty Empty) :=
      ((classOf_eq_iff _ _).mp h).1
    exact hr.eq_zero_of_zero
  · rintro rfl
    exact classOf_zero

instance : Nontrivial TensorClass := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have heq : (fun (_ _ _ : PUnit.{1}) => (1 : ℂ)) = 0 :=
    (classOf_eq_zero_iff _).mp h
  have := congrFun (congrFun (congrFun heq PUnit.unit) PUnit.unit) PUnit.unit
  exact one_ne_zero this

/-- A nonzero tensor has a nonzero coefficient, which restricts to scalar multiplication. -/
theorem one_le_classOf_of_ne_zero {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] {T : Tensor ℂ X Y Z} (hT : T ≠ 0) :
    1 ≤ classOf T := by
  classical
  have hex : ∃ x y z, T x y z ≠ 0 := by
    by_contra! h
    apply hT
    funext x y z
    exact h x y z
  obtain ⟨x, y, z, hxyz⟩ := hex
  apply (classOf_le_iff _ _).mpr
  refine ⟨(fun _ u => if u = x then (T x y z)⁻¹ else 0),
    (fun _ v => if v = y then 1 else 0),
    (fun _ w => if w = z then 1 else 0), ?_⟩
  funext a b c
  simp [Tensor.restrict, ite_mul, mul_ite, hxyz]

/-- Every nonzero class dominates the multiplicative unit. -/
theorem one_le_of_ne_zero {T : TensorClass} (hT : T ≠ 0) : 1 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change tensorClass T ≠ 0 at hT
  change 1 ≤ tensorClass T
  rw [← classOf_coeff T] at hT ⊢
  exact one_le_classOf_of_ne_zero (fun h => hT ((classOf_eq_zero_iff _).mpr h))

end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI

end FlattenModule047
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic -/
section FlattenModule048


namespace OAI

/-!
# Characters of finite complex tensors

The tensor operations in this file are the coefficient operations from
`MatrixMultiplication.Foundation.Tensor`. A character is an assumption on those
operations, not an assertion that a character exists. Restriction monotonicity
forces invariance under independent invertible changes of coordinates, so this
interface descends to the mutual-restriction classes of Section 3 of the paper.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- The scalar multiplication tensor, the multiplicative unit. -/
def unitTensor : Tensor ℂ PUnit PUnit PUnit := fun _ _ _ => 1

/-- The direct sum of `r` scalar multiplication tensors, in diagonal coordinates. -/
def scalarTensor (r : ℕ) : Tensor ℂ (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ i = k then 1 else 0

/-- A normalized, additive, multiplicative, restriction-monotone tensor valuation.

Index types vary over all finite types in `Type`. No character-existence result is
included among the fields or claimed by this definition.
-/
structure Character where
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] →
    Tensor ℂ X Y Z → ℝ
  nonneg : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z), 0 ≤ value T
  map_zero : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z],
    value (0 : Tensor ℂ X Y Z) = 0
  map_one : value unitTensor = 1
  map_directSum : ∀ {ι X Y Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor ℂ X Y Z),
    value (Tensor.directSum T) = ∑ i, value (T i)
  map_product : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (A : X' → X → ℂ)
    (B : Y' → Y → ℂ) (C : Z' → Z → ℂ),
    value (Tensor.restrict A B C T) ≤ value T

namespace Character

variable (χ : Character)
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Coordinate pullbacks are restrictions. -/
theorem value_pullback_le (T : Tensor ℂ X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  classical
  rw [Tensor.pullback_eq_restrict]
  exact χ.monotone T _ _ _

/-- Independent coordinate bijections preserve a character. -/
theorem value_reindex (T : Tensor ℂ X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  apply le_antisymm (χ.value_pullback_le T ex ey ez)
  have h := χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm
      (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- The character has the same value on mutually restricting tensors. -/
theorem value_eq_of_mutual_restriction (T : Tensor ℂ X Y Z) (S : Tensor ℂ X' Y' Z')
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ)
    (A' : X → X' → ℂ) (B' : Y → Y' → ℂ) (C' : Z → Z' → ℂ)
    (hS : S = Tensor.restrict A B C T) (hT : T = Tensor.restrict A' B' C' S) :
    χ.value T = χ.value S := by
  apply le_antisymm
  · calc
      χ.value T = χ.value (Tensor.restrict A' B' C' S) := congrArg χ.value hT
      _ ≤ χ.value S := χ.monotone S A' B' C'
  · calc
      χ.value S = χ.value (Tensor.restrict A B C T) := congrArg χ.value hS
      _ ≤ χ.value T := χ.monotone T A B C

/-- An integer scalar tensor has its expected character value. -/
@[simp] theorem value_scalarTensor (r : ℕ) : χ.value (scalarTensor r) = r := by
  let T : Fin r → Tensor ℂ PUnit PUnit PUnit := fun _ => unitTensor
  have heq : Tensor.pullback (Equiv.prodPUnit (Fin r)).symm
      (Equiv.prodPUnit (Fin r)).symm (Equiv.prodPUnit (Fin r)).symm
      (Tensor.directSum T) = scalarTensor r := by
    rfl
  rw [← heq, χ.value_reindex, χ.map_directSum]
  simp [T, χ.map_one]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Restricting a diagonal scalar tensor realizes a rank decomposition. -/
theorem restrict_scalarTensor (r : ℕ) (a : Fin r → X → ℂ)
    (b : Fin r → Y → ℂ) (c : Fin r → Z → ℂ) :
    Tensor.restrict (fun x i => a i x) (fun y i => b i y) (fun z i => c i z)
      (scalarTensor r) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
  classical
  funext x y z
  simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]

/-- Character values are bounded by every exact rank decomposition size. -/
theorem value_le_rank {T : Tensor ℂ X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.value T ≤ r := by
  rcases h with ⟨a, b, c, rfl⟩
  rw [← restrict_scalarTensor r a b c]
  exact (χ.monotone (scalarTensor r) _ _ _).trans_eq (χ.value_scalarTensor r)

/-- Every nonzero tensor restricts to the scalar multiplication tensor. -/
theorem one_le_value {T : Tensor ℂ X Y Z} (hT : T ≠ 0) : 1 ≤ χ.value T := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hT
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hy
  change T x y z ≠ 0 at hz
  let A : PUnit → X → ℂ := fun _ x' => if x' = x then (T x y z)⁻¹ else 0
  let B : PUnit → Y → ℂ := fun _ y' => if y' = y then 1 else 0
  let C : PUnit → Z → ℂ := fun _ z' => if z' = z then 1 else 0
  have heq : Tensor.restrict A B C T = unitTensor := by
    funext i j k
    simp [Tensor.restrict, A, B, C, unitTensor, ite_mul, mul_ite, hz]
  simpa only [heq, χ.map_one] using χ.monotone T A B C

/-- Normalization and restriction monotonicity make the character faithful. -/
@[simp] theorem value_eq_zero_iff (T : Tensor ℂ X Y Z) : χ.value T = 0 ↔ T = 0 := by
  constructor
  · intro h
    by_contra hT
    have hle := χ.one_le_value hT
    rw [h] at hle
    exact (not_le_of_gt zero_lt_one) hle
  · rintro rfl
    exact χ.map_zero

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule048
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Scalar -/
section FlattenModule049



namespace OAI

/-!
# Natural numbers and rank in the tensor semiring

The natural number `r` is the class of the diagonal scalar tensor with `r`
terms.  Consequently, comparison with `r` in the restriction order is exactly
the existence of a rank decomposition with `r` terms.
-/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- Splitting the diagonal index set splits its scalar tensor into two blocks. -/
theorem scalarTensor_add_reindex (m n : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      finSumFinEquiv finSumFinEquiv (scalarTensor (m + n)) =
      sumTensor (scalarTensor m) (scalarTensor n) := by
  funext x y z
  simp only [Tensor.pullback, scalarTensor,
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective.eq_iff]
  cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]

/-- A diagonal scalar tensor has its evident decomposition into simple terms. -/
theorem scalarTensor_rankAtMost (r : ℕ) : Tensor.RankAtMost (scalarTensor r) r := by
  classical
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0), (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- The diagonal flattening also gives the matching lower bound. -/
@[simp] theorem exactRank_scalarTensor (r : ℕ) : exactRank (scalarTensor r) = r := by
  apply le_antisymm (exactRank_le (scalarTensor_rankAtMost r))
  have h := (exactRank_spec (scalarTensor r)).card_le_of_identity id id id
    (by intro i j; simp [scalarTensor])
  simpa only [Fintype.card_fin] using h

namespace TensorSemiring

/-- Addition of the diagonal index sets is semiring addition. -/
theorem classOf_scalarTensor_add (m n : ℕ) :
    classOf (scalarTensor (m + n)) =
      classOf (scalarTensor m) + classOf (scalarTensor n) := by
  have h := classOf_eq_of_reindex _ _ _ (scalarTensor_add_reindex m n)
  exact h.symm.trans (classOf_sum _ _)

@[simp] theorem classOf_scalarTensor_zero :
    classOf (scalarTensor 0) = (0 : TensorClass) := by
  have h : scalarTensor 0 = 0 := by
    funext x
    exact Fin.elim0 x
  rw [h, classOf_zero]

@[simp] theorem classOf_scalarTensor_one :
    classOf (scalarTensor 1) = (1 : TensorClass) := by
  change classOf (scalarTensor 1) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : ℂ))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]

/-- Natural numbers in the quotient semiring have their intended tensor meaning. -/
@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf (scalarTensor r) = (r : TensorClass) := by
  induction r with
  | zero => exact classOf_scalarTensor_zero
  | succ r ih =>
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ,
        classOf_scalarTensor_one, ih] using
        classOf_scalarTensor_add r 1

/-- Exact rank decompositions are precisely restrictions of diagonal tensors. -/
theorem rankAtMost_iff_isRestriction_scalarTensor
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) :
    Tensor.RankAtMost T r ↔ IsRestriction T (scalarTensor r) := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨(fun x i => a i x), (fun y i => b i y), (fun z i => c i z), ?_⟩
    apply h.trans
    funext x y z
    simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  · rintro ⟨A, B, C, rfl⟩
    exact (scalarTensor_rankAtMost r).restrict A B C

/-- The restriction order below a natural number is exactly the usual rank bound. -/
theorem classOf_le_nat_iff_rankAtMost
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) :
    classOf T ≤ (r : TensorClass) ↔ Tensor.RankAtMost T r := by
  rw [← classOf_scalarTensor r, classOf_le_iff]
  exact (rankAtMost_iff_isRestriction_scalarTensor T r).symm

/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
@[simp] theorem rank_natCast (r : ℕ) : rank (r : TensorClass) = r := by
  rw [← classOf_scalarTensor r, rank_classOf, exactRank_scalarTensor]

/-- The rank is a natural-number upper bound in the restriction order. -/
theorem le_rank (T : TensorClass) : T ≤ (rank T : TensorClass) := by
  induction T using Quotient.inductionOn with
  | h T =>
    change tensorClass T ≤ (exactRank T.coeff : TensorClass)
    rw [← classOf_coeff T]
    exact (classOf_le_nat_iff_rankAtMost T.coeff (exactRank T.coeff)).mpr
      (exactRank_spec T.coeff)

/-- The tensor restriction order induces the usual order on natural numbers. -/
@[simp] theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : TensorClass) ≤ (n : TensorClass) ↔ m ≤ n := by
  constructor
  · intro h
    simpa only [rank_natCast] using rank_mono h
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add]
    simpa only [add_zero] using add_mono (le_refl (m : TensorClass)) (zero_le (k : TensorClass))

/-- A natural multiple of any nonzero tensor contains any prescribed tensor
by restriction. -/
theorem le_nat_mul_of_ne_zero (T S : TensorClass) (hS : S ≠ 0) :
    T ≤ (rank T : TensorClass) * S := by
  apply (le_rank T).trans
  simpa only [mul_one] using
    mul_mono (le_refl (rank T : TensorClass)) (one_le_of_ne_zero hS)

end TensorSemiring
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule049
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Scalar -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Obstruction -/
section FlattenModule050




namespace OAI

/-!
# The rank obstruction behind the preliminary spectral state

The finite catalyst is kept fixed while first tensor powers, then exponent
slack, then the number of copies are varied.  The hypotheses below isolate the
rank inequalities supplied by the catalytic comparison; they do not assert
the existence of a tensor spectrum or the separation argument producing that
comparison.
-/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- Tensor powers of a fixed exact matrix algorithm retain their exact rank
bound after identifying the product coordinates with one matrix dimension. -/
theorem exactMatrixRank_pow_le (u j : ℕ) :
    exactMatrixRank (u ^ j) ≤ exactMatrixRank u ^ j := by
  classical
  let e : Fin (u ^ j) ≃ (Fin j → Fin u) := Fintype.equivOfCardEq (by simp)
  let f : Fin (u ^ j) × Fin (u ^ j) → Fin j → Fin u × Fin u :=
    fun x i => (e x.1 i, e x.2 i)
  have h := ((exactMatrixRank_spec u).power j).pullback f f f
  have heq : Tensor.pullback f f f (Tensor.power (Tensor.matrixMultiplication u u u) j) =
      Tensor.matrixMultiplication (u ^ j) (u ^ j) (u ^ j) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, Tensor.matrixMultiplication, f,
      Fintype.prod_boole, forall_and, ← funext_iff, e.injective.eq_iff]
  rw [heq] at h
  exact exactRank_le h

/-- A floor approximation uses at most `n^j` copies of a fixed matrix
algorithm and loses at most one factor of its fixed matrix dimension. -/
theorem floor_rank_power_bounds {u n R : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n)
    {τ : ℝ} (hτ : 0 < τ) (hR : (R : ℝ) ≤ (u : ℝ) ^ τ) (j : ℕ) :
    let l := ⌊(j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ⌋₊
    (R : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
      (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l := by
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (show 1 < u by omega)
  have hu0 : (0 : ℝ) < u := zero_lt_one.trans hu1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  let x := (j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ
  let l := ⌊x⌋₊
  have hx : 0 ≤ x := div_nonneg
    (mul_nonneg (Nat.cast_nonneg j) (Real.logb_nonneg hu1 hn1)) hτ.le
  have hl : (l : ℝ) ≤ x := Nat.floor_le hx
  have hxl : x ≤ (l : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hlog : (u : ℝ) ^ Real.logb (u : ℝ) (n : ℝ) = n :=
    Real.rpow_logb hu0 (ne_of_gt hu1) hn0
  change (R : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
    (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l
  constructor
  · calc
      (R : ℝ) ^ l ≤ ((u : ℝ) ^ τ) ^ l :=
        pow_le_pow_left₀ (Nat.cast_nonneg R) hR l
      _ = (u : ℝ) ^ (τ * (l : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
      _ ≤ (u : ℝ) ^ (τ * x) :=
        Real.rpow_le_rpow_of_exponent_le hu1.le (mul_le_mul_of_nonneg_left hl hτ.le)
      _ = (n : ℝ) ^ j := by
        rw [show τ * x = Real.logb (u : ℝ) (n : ℝ) * (j : ℝ) by
          dsimp [x]; field_simp]
        rw [Real.rpow_mul hu0.le, hlog, Real.rpow_natCast]
  · calc
      (n : ℝ) ^ ((j : ℝ) / τ) = (u : ℝ) ^ x := by
        rw [← hlog, ← Real.rpow_mul hu0.le]
        congr 1
        dsimp [x]
        ring
      _ ≤ (u : ℝ) ^ ((l : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le hu1.le hxl
      _ = (u : ℝ) * (u : ℝ) ^ l := by
        rw [Real.rpow_add hu0, Real.rpow_natCast, Real.rpow_one, mul_comm]

/-- At fixed `n` and exponent slack, every admissible matrix rank budget
forces the exponential growth rate of the catalytic comparison.  The constant
`R` is fixed before the tensor-power parameter varies. -/
theorem catalytic_rank_bound_at_slack {d n K R : ℕ}
    (hd : 0 < d) (hn : 1 ≤ n)
    (hbound : ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ, exactMatrixRank g ≤ n ^ j →
      exactMatrixRank (d ^ j * g) ≤ R * K ^ j)
    {δ : ℝ} (hδ : 0 < δ) :
    (d : ℝ) ^ exactRankExponent *
      (n : ℝ) ^ (exactRankExponent / (exactRankExponent + δ)) ≤ K := by
  let ν := exactRankExponent
  let τ := ν + δ
  have hν : 0 ≤ ν := (by norm_num : (0 : ℝ) ≤ 2).trans exactRankExponent_lower
  have hτ : 0 < τ := add_pos_of_nonneg_of_pos hν hδ
  obtain ⟨u, hu, huR⟩ := exists_exactMatrixRank_lt_rpow
    (show exactRankExponent < τ from lt_add_of_pos_right _ hδ)
  apply le_of_eventually_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * R)
    (Nat.cast_nonneg K)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with j hj
  let l := ⌊(j : ℝ) * Real.logb (u : ℝ) (n : ℝ) / τ⌋₊
  let g := u ^ l
  have hg : 0 < g := pow_pos (by omega) l
  have hf := floor_rank_power_bounds hu hn hτ huR.le j
  change (exactMatrixRank u : ℝ) ^ l ≤ (n : ℝ) ^ j ∧
    (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * (u : ℝ) ^ l at hf
  have hbudget : exactMatrixRank g ≤ n ^ j := by
    have hpow : (exactMatrixRank g : ℝ) ≤ (exactMatrixRank u : ℝ) ^ l := by
      exact_mod_cast exactMatrixRank_pow_le u l
    have hb := hpow.trans hf.1
    exact_mod_cast hb
  have hrank := hbound j hj g hbudget
  have hsize : (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * g := by
    simpa only [g, Nat.cast_pow] using hf.2
  have hlow := exactMatrixRank_rpow_lower_of_pos (mul_pos (pow_pos hd j) hg)
  have hpow_n : ((n : ℝ) ^ (ν / τ)) ^ j =
      ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  calc
    ((d : ℝ) ^ ν * (n : ℝ) ^ (ν / τ)) ^ j =
        (((d ^ j : ℕ) : ℝ) ^ ν) * ((n : ℝ) ^ ((j : ℝ) / τ)) ^ ν := by
      rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), hpow_n, Nat.cast_pow]
    _ ≤ (((d ^ j : ℕ) : ℝ) ^ ν) * ((u : ℝ) * g) ^ ν := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsize hν)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (u : ℝ) ^ ν * (((d ^ j * g : ℕ) : ℝ) ^ ν) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg u) (Nat.cast_nonneg g),
        Real.mul_rpow (Nat.cast_nonneg (d ^ j)) (Nat.cast_nonneg g)]
      ring
    _ ≤ (u : ℝ) ^ ν * (exactMatrixRank (d ^ j * g) : ℝ) :=
      mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (Nat.cast_nonneg u) _)
    _ ≤ (u : ℝ) ^ ν * ((R : ℝ) * (K : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg u) _)
      exact_mod_cast hrank
    _ = ((u : ℝ) ^ ν * R) * (K : ℝ) ^ j := by ring

/-- The numerical rank consequence of a single fixed finite catalyst is
incompatible with `k < d^ν`.  The same `D` and `R` occur for every `n` and
every tensor power.  No uniform bound on the approximation block selected
after an exponent slack is assumed. -/
theorem catalytic_rank_obstruction {d k D R : ℕ} (hd : 0 < d)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ,
      exactMatrixRank g ≤ n ^ j →
      exactMatrixRank (d ^ j * g) ≤ R * (n * k + D) ^ j) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  apply spectral_coefficient_le_of_all_nat
    (hν := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) exactRankExponent_lower)
    (D := (D : ℝ))
  intro n hn δ hδ
  have h := catalytic_rank_bound_at_slack hd hn (hbound n hn) hδ
  simpa only [Nat.cast_add, Nat.cast_mul] using h

/-- Contradiction form for the finite-obstruction argument. -/
theorem not_catalytic_rank_bounds_of_lt {d k D R : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    ¬ (∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → ∀ g : ℕ,
      exactMatrixRank g ≤ n ^ j →
      exactMatrixRank (d ^ j * g) ≤ R * (n * k + D) ^ j) := by
  intro hbound
  exact (not_lt_of_ge (catalytic_rank_obstruction hd hbound)) hk

/-- Iteration and absorption of a fixed catalyst require no cancellation of
the tensor factor `s`.  Monotonicity is explicit so the lemma applies to the
restriction order on a tensor semiring, where additive cancellation fails. -/
theorem catalytic_power_comparison {S : Type*} [CommSemiring S] [Preorder S]
    (hadd : ∀ {a b c e : S}, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hmul : ∀ {a b c e : S}, a ≤ b → c ≤ e → a * c ≤ b * e)
    (hzero : ∀ a : S, 0 ≤ a)
    (D t s : S) (k C : ℕ)
    (hcat : D + t * s ≤ D + (k : S) * s)
    (hD : D ≤ (C : S) * s) (n j : ℕ) :
    (n : S) ^ j * t ^ j * s ≤ ((n * k + C : ℕ) : S) ^ j * s := by
  have hiter : ∀ m : ℕ,
      D + (m : S) * (t * s) ≤ D + (m : S) * ((k : S) * s) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        D + ((m + 1 : ℕ) : S) * (t * s) =
            (D + t * s) + (m : S) * (t * s) := by push_cast; ring
        _ ≤ (D + (k : S) * s) + (m : S) * (t * s) := hadd hcat le_rfl
        _ = (D + (m : S) * (t * s)) + (k : S) * s := by ring
        _ ≤ (D + (m : S) * ((k : S) * s)) + (k : S) * s := hadd ih le_rfl
        _ = D + ((m + 1 : ℕ) : S) * ((k : S) * s) := by push_cast; ring
  have habsorb : (n : S) * t * s ≤ ((n * k + C : ℕ) : S) * s := by
    calc
      (n : S) * t * s = 0 + (n : S) * (t * s) := by ring
      _ ≤ D + (n : S) * (t * s) := hadd (hzero D) le_rfl
      _ ≤ D + (n : S) * ((k : S) * s) := hiter n
      _ ≤ (C : S) * s + (n : S) * ((k : S) * s) := hadd hD le_rfl
      _ = ((n * k + C : ℕ) : S) * s := by push_cast; ring
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      (n : S) ^ (j + 1) * t ^ (j + 1) * s =
          ((n : S) ^ j * t ^ j) * ((n : S) * t * s) := by ring
      _ ≤ ((n : S) ^ j * t ^ j) * (((n * k + C : ℕ) : S) * s) :=
        hmul le_rfl habsorb
      _ = ((n * k + C : ℕ) : S) * ((n : S) ^ j * t ^ j * s) := by ring
      _ ≤ ((n * k + C : ℕ) : S) * (((n * k + C : ℕ) : S) ^ j * s) :=
        hmul le_rfl ih
      _ = ((n * k + C : ℕ) : S) ^ (j + 1) * s := by ring

/-- A rank-compatible ordered tensor semiring converts a single finite
catalytic inequality into the actual exact-rank obstruction.  The hypotheses
name the required tensor interpretation and scalar rank domination explicitly;
no additive rank formula or cancellation property is assumed. -/
theorem catalytic_semiring_obstruction {S : Type*} [CommSemiring S] [Preorder S]
    (hadd : ∀ {a b c e : S}, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hmul : ∀ {a b c e : S}, a ≤ b → c ≤ e → a * c ≤ b * e)
    (hzero : ∀ a : S, 0 ≤ a)
    (ρ : S → ℕ) (hρmono : Monotone ρ)
    (hρcopies : ∀ (m : ℕ) (s : S), ρ ((m : S) * s) ≤ m * ρ s)
    (M : ℕ → S)
    (hMmul : ∀ a b : ℕ, M (a * b) = M a * M b)
    (hMpow : ∀ a j : ℕ, M (a ^ j) = M a ^ j)
    (hρM : ∀ a : ℕ, ρ (M a) = exactMatrixRank a)
    (hbudget : ∀ n j g : ℕ, exactMatrixRank g ≤ n ^ j → M g ≤ (n : S) ^ j)
    (D s : S) (d k C : ℕ) (hd : 0 < d) (hs : 1 ≤ s)
    (hcat : D + M d * s ≤ D + (k : S) * s)
    (hD : D ≤ (C : S) * s) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  apply catalytic_rank_obstruction (D := C) (R := ρ s) hd
  intro n _hn j _hj g hg
  have hcompare : M (d ^ j * g) ≤ ((n * k + C : ℕ) : S) ^ j * s := by
    calc
      M (d ^ j * g) = M d ^ j * M g := by rw [hMmul, hMpow]
      _ ≤ M d ^ j * (n : S) ^ j := hmul le_rfl (hbudget n j g hg)
      _ = ((n : S) ^ j * M d ^ j) * 1 := by ring
      _ ≤ ((n : S) ^ j * M d ^ j) * s := hmul le_rfl hs
      _ ≤ ((n * k + C : ℕ) : S) ^ j * s :=
        catalytic_power_comparison hadd hmul hzero D (M d) s k C hcat hD n j
  calc
    exactMatrixRank (d ^ j * g) = ρ (M (d ^ j * g)) := (hρM _).symm
    _ ≤ ρ (((n * k + C : ℕ) : S) ^ j * s) := hρmono hcompare
    _ = ρ ((((n * k + C) ^ j : ℕ) : S) * s) := by rw [Nat.cast_pow]
    _ ≤ (n * k + C) ^ j * ρ s := hρcopies _ s
    _ = ρ s * (n * k + C) ^ j := Nat.mul_comm _ _

/-- In the semiring of actual finite complex tensors modulo mutual
restriction, a fixed catalyst cannot make `k` copies dominate multiplication
by `T_d` unless `k ≥ d^ν`.  The nonzero hypothesis is exactly what supplies
the scalar restriction `s ≥ 1`; the catalyst remains fixed throughout. -/
theorem tensor_catalytic_obstruction
    {D s : TensorSemiring.TensorClass} {d k : ℕ}
    (hd : 0 < d) (hs : s ≠ 0)
    (hcat : D + TensorSemiring.matrixClass d * s ≤ D + (k : TensorSemiring.TensorClass) * s) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  have hs1 : 1 ≤ s := TensorSemiring.one_le_of_ne_zero hs
  have hcopies : ∀ (m : ℕ) (x : TensorSemiring.TensorClass),
      TensorSemiring.rank ((m : TensorSemiring.TensorClass) * x) ≤
        m * TensorSemiring.rank x := by
    intro m x
    simpa only [TensorSemiring.rank_natCast] using
      TensorSemiring.rank_mul_le (m : TensorSemiring.TensorClass) x
  have hbudget : ∀ n j g : ℕ, exactMatrixRank g ≤ n ^ j →
      TensorSemiring.matrixClass g ≤ (n : TensorSemiring.TensorClass) ^ j := by
    intro n j g hg
    have hleft : TensorSemiring.matrixClass g ≤
        (exactMatrixRank g : TensorSemiring.TensorClass) := by
      simpa only [TensorSemiring.rank_matrixClass] using
        TensorSemiring.le_rank (TensorSemiring.matrixClass g)
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hg
    have hright : (exactMatrixRank g : TensorSemiring.TensorClass) ≤
        (n : TensorSemiring.TensorClass) ^ j := by
      rw [← Nat.cast_pow, hq, Nat.cast_add]
      simpa only [add_zero] using TensorSemiring.add_mono
        (le_refl (exactMatrixRank g : TensorSemiring.TensorClass))
        (TensorSemiring.zero_le (q : TensorSemiring.TensorClass))
    exact hleft.trans hright
  have hD : D ≤ (TensorSemiring.rank D : TensorSemiring.TensorClass) * s := by
    calc
      D ≤ (TensorSemiring.rank D : TensorSemiring.TensorClass) := TensorSemiring.le_rank D
      _ = (TensorSemiring.rank D : TensorSemiring.TensorClass) * 1 := (mul_one _).symm
      _ ≤ (TensorSemiring.rank D : TensorSemiring.TensorClass) * s :=
        TensorSemiring.mul_mono le_rfl hs1
  exact catalytic_semiring_obstruction
    TensorSemiring.add_mono TensorSemiring.mul_mono TensorSemiring.zero_le
    TensorSemiring.rank (fun _ _ h => TensorSemiring.rank_mono h) hcopies
    TensorSemiring.matrixClass TensorSemiring.matrixClass_mul TensorSemiring.matrixClass_pow
    TensorSemiring.rank_matrixClass hbudget D s d k (TensorSemiring.rank D) hd hs1 hcat hD

/-- The stronger comparison produced by a finite separation certificate
has the same consequence.  Its positive scalar summand is only needed
earlier to rule out `s = 0`; that nonzero fact is explicit here. -/
theorem tensor_catalytic_obstruction_of_scalar_gain
    {D s : TensorSemiring.TensorClass} {d k m : ℕ}
    (hd : 0 < d) (hs : s ≠ 0)
    (hcat : D + (m : TensorSemiring.TensorClass) + TensorSemiring.matrixClass d * s ≤
      D + (k : TensorSemiring.TensorClass) * s) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  apply tensor_catalytic_obstruction hd hs
  refine le_trans ?_ hcat
  simpa only [add_zero] using TensorSemiring.add_mono
    (TensorSemiring.add_mono (le_refl D)
      (TensorSemiring.zero_le (m : TensorSemiring.TensorClass)))
    (le_refl (TensorSemiring.matrixClass d * s))

/-- A finite tensor cannot absorb a positive scalar direct summand.  Iterating
such an absorption would place arbitrarily large scalar tensors below one
fixed finite-rank tensor.  This uses rank monotonicity, not rank additivity. -/
theorem not_tensor_add_positive_nat_le_self (D : TensorSemiring.TensorClass)
    {m : ℕ} (hm : 0 < m) : ¬ D + (m : TensorSemiring.TensorClass) ≤ D := by
  intro h
  have hiter : ∀ n : ℕ, D + ((n * m : ℕ) : TensorSemiring.TensorClass) ≤ D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        D + (((n + 1) * m : ℕ) : TensorSemiring.TensorClass) =
            (D + ((n * m : ℕ) : TensorSemiring.TensorClass)) + m := by push_cast; ring
        _ ≤ D + (m : TensorSemiring.TensorClass) := TensorSemiring.add_mono ih le_rfl
        _ ≤ D := h
  let n := TensorSemiring.rank D + 1
  have hscalar : ((n * m : ℕ) : TensorSemiring.TensorClass) ≤ D := by
    have hleft := TensorSemiring.add_mono (TensorSemiring.zero_le D)
      (le_refl ((n * m : ℕ) : TensorSemiring.TensorClass))
    have hsmall : ((n * m : ℕ) : TensorSemiring.TensorClass) ≤
        D + ((n * m : ℕ) : TensorSemiring.TensorClass) := by
      simpa only [zero_add] using hleft
    exact hsmall.trans (hiter n)
  have hrank : n * m ≤ TensorSemiring.rank D := by
    simpa only [TensorSemiring.rank_natCast] using TensorSemiring.rank_mono hscalar
  have hnm : n ≤ n * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt hm)
  have hlarge : TensorSemiring.rank D + 1 ≤ TensorSemiring.rank D := hnm.trans hrank
  omega

/-- The exact finite-obstruction comparison from Appendix A.1 forces
`k ≥ d^ν`.  Both tensors are fixed, `m` is a positive scalar gain, and the
ordinary tensor rank and restriction order are the actual ones. -/
theorem tensor_catalytic_obstruction_of_positive_scalar_gain
    {D s : TensorSemiring.TensorClass} {d k m : ℕ}
    (hd : 0 < d) (hm : 0 < m)
    (hcat : D + (m : TensorSemiring.TensorClass) + TensorSemiring.matrixClass d * s ≤
      D + (k : TensorSemiring.TensorClass) * s) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  apply tensor_catalytic_obstruction_of_scalar_gain hd (m := m) ?_ hcat
  intro hs
  subst s
  have hbad : D + (m : TensorSemiring.TensorClass) ≤ D := by
    simpa only [mul_zero, add_zero] using hcat
  exact not_tensor_add_positive_nat_le_self D hm hbad

/-- Contradiction interface for the finite inconsistency certificate in
the construction of an additive monotone state. -/
theorem no_tensor_catalytic_gain {d k : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    ¬ ∃ (D s : TensorSemiring.TensorClass) (m : ℕ), 0 < m ∧
      D + (m : TensorSemiring.TensorClass) + TensorSemiring.matrixClass d * s ≤
        D + (k : TensorSemiring.TensorClass) * s := by
  rintro ⟨D, s, m, hm, hcat⟩
  exact (not_lt_of_ge (tensor_catalytic_obstruction_of_positive_scalar_gain hd hm hcat)) hk

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule050
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Obstruction -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGroupTensor -/
section FlattenModule051


namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

def groupTensor : Tensor ℂ G G G := fun a b c => if a + b = c then 1 else 0

theorem groupTensor_fourier :
    groupTensor G = fun a b c => ∑ χ : AddChar G ℂ,
      Tensor.rankOne (fun a => χ a / (Fintype.card G : ℂ))
        (fun b => χ b) (fun c => χ (-c)) a b c := by
  funext a b c
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    groupTensor G a b c =
        (∑ χ : AddChar G ℂ, χ (a + b - c)) / (Fintype.card G : ℂ) := by
      rw [AddChar.sum_apply_eq_ite]
      by_cases h : a + b = c
      · simp [groupTensor, h, hcard]
      · simp [groupTensor, h, sub_ne_zero.mpr h]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [Tensor.rankOne, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

theorem groupTensor_rankAtMost : Tensor.RankAtMost (groupTensor G) (Fintype.card G) := by
  rw [groupTensor_fourier]
  simpa only [AddChar.card_eq] using
    Tensor.rankAtMost_sum_rankOne
      (fun χ : AddChar G ℂ => fun a => χ a / (Fintype.card G : ℂ))
      (fun χ : AddChar G ℂ => fun b => χ b)
      (fun χ : AddChar G ℂ => fun c => χ (-c))

end MatrixMultiplication.Foundation

end OAI

end FlattenModule051
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGroupTensor -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparation -/
section FlattenModule052







namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation.Separation

theorem grid_modular_collision (Q c t u v : ℤ)
    (hc : 0 ≤ c ∧ c < Q) (ht : 0 ≤ t ∧ t < Q)
    (hu : 0 ≤ u ∧ u < Q) (hv : 0 ≤ v ∧ v < Q)
    (hmod : Int.ModEq (4 * Q) c (t + u - v)) : c = t + u - v := by
  have hdvd : 4 * Q ∣ t + u - v - c := hmod.dvd
  have hz : t + u - v - c = 0 := by
    rcases le_total 0 (t + u - v - c) with h | h
    · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h (by omega) hdvd
    · have hn : -(t + u - v - c) = 0 :=
        Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) (Int.dvd_neg.mpr hdvd)
      omega
  omega

variable {ι : Type*} [Fintype ι]

def squaredNorm (t : ι → ℝ) : ℝ := ∑ i, (t i) ^ 2

def dot (t u : ι → ℝ) : ℝ := ∑ i, t i * u i

theorem squaredNorm_displacement (t u v : ι → ℝ) :
    squaredNorm (fun i => t i + u i - v i) =
      squaredNorm t + 2 * (dot t u - dot t v) +
        squaredNorm (fun i => u i - v i) := by
  calc
    squaredNorm (fun i => t i + u i - v i) =
        ∑ i, ((t i) ^ 2 + 2 * (t i * u i - t i * v i) +
          (u i - v i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [squaredNorm, dot, Finset.sum_add_distrib,
        mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

theorem sphere_slice_collision (t c u v : ι → ℝ)
    (hsphere : squaredNorm c = squaredNorm t)
    (hslice : dot t u = dot t v)
    (hcollision : ∀ i, c i = t i + u i - v i) : u = v ∧ c = t := by
  have hc : c = fun i => t i + u i - v i := funext hcollision
  have hzero : squaredNorm (fun i => u i - v i) = 0 := by
    have hid := squaredNorm_displacement t u v
    rw [← hc, hsphere, hslice] at hid
    linarith
  have huv : u = v := by
    funext i
    have hle : (u i - v i) ^ 2 ≤ squaredNorm (fun j => u j - v j) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j - v j)) (Finset.mem_univ i)
    rw [hzero] at hle
    nlinarith [sq_nonneg (u i - v i)]
  refine ⟨huv, ?_⟩
  funext i
  rw [hcollision, huv]
  ring

end MatrixMultiplication.Foundation.Separation

end OAI

end FlattenModule052
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparationCounting -/
section FlattenModule053



namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation.Separation

abbrev Grid (d Q : ℕ) := Fin d → Fin Q

def gridSquaredNorm {d Q : ℕ} (x : Grid d Q) : ℕ := ∑ i, (x i : ℕ) ^ 2

def gridDot {d Q : ℕ} (t u : Grid d Q) : ℕ := ∑ i, (t i : ℕ) * (u i : ℕ)

theorem gridSquaredNorm_le {d Q : ℕ} (x : Grid d Q) : gridSquaredNorm x ≤ d * Q ^ 2 := by
  calc
    gridSquaredNorm x ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.pow_le_pow_left (Nat.le_of_lt (x i).isLt) 2
    _ = d * Q ^ 2 := by simp

theorem gridDot_le {d Q : ℕ} (t u : Grid d Q) : gridDot t u ≤ d * Q ^ 2 := by
  calc
    gridDot t u ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [pow_two] using
        Nat.mul_le_mul (Nat.le_of_lt (t i).isLt) (Nat.le_of_lt (u i).isLt)
    _ = d * Q ^ 2 := by simp

def normColor {d Q : ℕ} (x : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridSquaredNorm x, Nat.lt_succ_of_le (gridSquaredNorm_le x)⟩

def dotColor {d Q : ℕ} (t u : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridDot t u, Nat.lt_succ_of_le (gridDot_le t u)⟩

theorem two_stage_pigeonhole {A : Type*} [Fintype A] [DecidableEq A]
    {M K m : ℕ} (hM : 0 < M) (f : A → Fin M) (g : A → A → Fin M)
    (hK : M * K ≤ Fintype.card A) (hm : M * m ≤ Fintype.card A) :
    ∃ tags : Finset A, tags.card = K ∧
      (∃ radius : Fin M, ∀ t ∈ tags, f t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset A, slice.card = m ∧
        ∃ level : Fin M, ∀ u ∈ slice, g t u = level := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨radius, hr⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f
    (by simpa only [Fintype.card_fin] using hK)
  obtain ⟨tags, htags, hcard⟩ := Finset.exists_subset_card_eq hr
  refine ⟨tags, hcard, ⟨radius, ?_⟩, ?_⟩
  · intro t ht
    exact (Finset.mem_filter.mp (htags ht)).2
  · intro t ht
    obtain ⟨level, hl⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (g t)
      (by simpa only [Fintype.card_fin] using hm)
    obtain ⟨slice, hslice, hsize⟩ := Finset.exists_subset_card_eq hl
    refine ⟨slice, hsize, level, ?_⟩
    intro u hu
    exact (Finset.mem_filter.mp (hslice hu)).2

theorem grid_tags_slices {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ tags : Finset (Grid d Q), tags.card = K ∧
      (∃ radius : Fin (d * Q ^ 2 + 1), ∀ t ∈ tags, normColor t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset (Grid d Q), slice.card = m ∧
        ∃ level : Fin (d * Q ^ 2 + 1), ∀ u ∈ slice, dotColor t u = level := by
  exact two_stage_pigeonhole (Nat.succ_pos _) normColor dotColor
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hK)
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hm)

end MatrixMultiplication.Foundation.Separation

end OAI

end FlattenModule053
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparationCounting -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexModularSeparation -/
section FlattenModule054





namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation.Separation

abbrev AuxiliaryGroup (d Q : ℕ) := Fin d → ZMod (4 * Q)

def gridToGroup {d Q : ℕ} (x : Grid d Q) : AuxiliaryGroup d Q :=
  fun i => (x i : ℕ)

def gridToReal {d Q : ℕ} (x : Grid d Q) : Fin d → ℝ :=
  fun i => (x i : ℕ)

theorem gridToReal_injective {d Q : ℕ} :
    Function.Injective (gridToReal : Grid d Q → Fin d → ℝ) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change ((x i : ℕ) : ℝ) = ((y i : ℕ) : ℝ) at hi
  exact_mod_cast hi

theorem squaredNorm_gridToReal {d Q : ℕ} (x : Grid d Q) :
    squaredNorm (gridToReal x) = (gridSquaredNorm x : ℝ) := by
  simp [squaredNorm, gridToReal, gridSquaredNorm, Nat.cast_sum]

theorem dot_gridToReal {d Q : ℕ} (x y : Grid d Q) :
    dot (gridToReal x) (gridToReal y) = (gridDot x y : ℝ) := by
  simp [dot, gridToReal, gridDot, Nat.cast_sum]

theorem grid_group_collision_lift {d Q : ℕ} (t c u v : Grid d Q)
    (h : gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c) :
    ∀ i, ((c i : ℕ) : ℤ) =
      ((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ) := by
  intro i
  have hcast : (((c i : ℕ) : ℤ) : ZMod (4 * Q)) =
      ((((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) :
        ZMod (4 * Q)) := by
    simpa [gridToGroup, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (congrFun h i).symm
  have hmod : Int.ModEq (4 * (Q : ℤ)) ((c i : ℕ) : ℤ)
      (((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (ZMod.intCast_eq_intCast_iff _ _ (4 * Q)).mp
        (by simpa only [Int.cast_add, Int.cast_sub] using hcast)
  have hbound (x : Fin Q) : 0 ≤ ((x : ℕ) : ℤ) ∧ ((x : ℕ) : ℤ) < (Q : ℤ) := by
    refine ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast x.isLt
  exact grid_modular_collision (Q : ℤ) _ _ _ _
    (hbound (c i)) (hbound (t i)) (hbound (u i)) (hbound (v i)) hmod

theorem grid_sphere_slice_collision {d Q : ℕ} (t c u v : Grid d Q)
    (hsphere : gridSquaredNorm c = gridSquaredNorm t)
    (hslice : gridDot t u = gridDot t v) :
    gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c ↔
      u = v ∧ c = t := by
  constructor
  · intro h
    have hnorm : squaredNorm (gridToReal c) = squaredNorm (gridToReal t) := by
      simp only [squaredNorm_gridToReal, hsphere]
    have hdot : dot (gridToReal t) (gridToReal u) =
        dot (gridToReal t) (gridToReal v) := by
      simp only [dot_gridToReal, hslice]
    have hlift := grid_group_collision_lift t c u v h
    have hreal : ∀ i, gridToReal c i =
        gridToReal t i + gridToReal u i - gridToReal v i := by
      intro i
      dsimp [gridToReal]
      exact_mod_cast hlift i
    obtain ⟨huv, hct⟩ := sphere_slice_collision
      (gridToReal t) (gridToReal c) (gridToReal u) (gridToReal v) hnorm hdot hreal
    exact ⟨gridToReal_injective huv, gridToReal_injective hct⟩
  · rintro ⟨rfl, rfl⟩
    simp [sub_eq_add_neg, add_left_comm]

theorem indexed_grid_collision {S U : Type*} {d Q : ℕ}
    (tag : S → Grid d Q) (point : S → U → Grid d Q)
    (htag : Function.Injective tag)
    (hpoint : ∀ s, Function.Injective (point s))
    (hsphere : ∀ s s', gridSquaredNorm (tag s') = gridSquaredNorm (tag s))
    (hslice : ∀ s i j, gridDot (tag s) (point s i) = gridDot (tag s) (point s j)) :
    ∀ s s' i j,
      gridToGroup (point s i) + (gridToGroup (tag s) - gridToGroup (point s j)) =
        gridToGroup (tag s') ↔ s = s' ∧ i = j := by
  intro s s' i j
  rw [grid_sphere_slice_collision (tag s) (tag s') (point s i) (point s j)
    (hsphere s s') (hslice s i j)]
  constructor
  · rintro ⟨hij, hss⟩
    exact ⟨(htag hss).symm, hpoint s hij⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem exists_modular_separation {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ (tag : Fin K → AuxiliaryGroup d Q)
      (point : Fin K → Fin m → AuxiliaryGroup d Q),
      ∀ s s' i j,
        point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j := by
  classical
  obtain ⟨tags, htags, ⟨radius, hradius⟩, hslices⟩ := grid_tags_slices hK hm
  choose slice hsliceCard level hlevel using
    (fun t : ↥tags => hslices t.val t.property)
  let tagEnum : Fin K ≃ ↥tags := (Finset.equivFinOfCardEq htags).symm
  let sliceEnum (t : ↥tags) : Fin m ≃ ↥(slice t) :=
    (Finset.equivFinOfCardEq (hsliceCard t)).symm
  let tagGrid (s : Fin K) : Grid d Q := (tagEnum s).val
  let pointGrid (s : Fin K) (i : Fin m) : Grid d Q :=
    (sliceEnum (tagEnum s) i).val
  have htag : Function.Injective tagGrid := by
    intro s s' h
    apply tagEnum.injective
    exact Subtype.ext h
  have hpoint : ∀ s, Function.Injective (pointGrid s) := by
    intro s i j h
    apply (sliceEnum (tagEnum s)).injective
    exact Subtype.ext h
  have hsphere : ∀ s s', gridSquaredNorm (tagGrid s') = gridSquaredNorm (tagGrid s) := by
    intro s s'
    have hc := (hradius (tagEnum s').val (tagEnum s').property).trans
      (hradius (tagEnum s).val (tagEnum s).property).symm
    exact congrArg Fin.val hc
  have hslice : ∀ s i j,
      gridDot (tagGrid s) (pointGrid s i) = gridDot (tagGrid s) (pointGrid s j) := by
    intro s i j
    have hc := (hlevel (tagEnum s) (sliceEnum (tagEnum s) i).val
      (sliceEnum (tagEnum s) i).property).trans
      (hlevel (tagEnum s) (sliceEnum (tagEnum s) j).val
        (sliceEnum (tagEnum s) j).property).symm
    exact congrArg Fin.val hc
  exact ⟨fun s => gridToGroup (tagGrid s), fun s i => gridToGroup (pointGrid s i),
    indexed_grid_collision tagGrid pointGrid htag hpoint hsphere hslice⟩

theorem card_auxiliaryGroup (d Q : ℕ) [NeZero (4 * Q)] :
    Fintype.card (AuxiliaryGroup d Q) = (4 * Q) ^ d := by
  simp [AuxiliaryGroup, ZMod.card]

end MatrixMultiplication.Foundation.Separation

end OAI

end FlattenModule054
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexModularSeparation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteSeparation -/
section FlattenModule055


namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

section Separation

variable {X Y Z S U G : Type*}
variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [DecidableEq S] [DecidableEq U]

def separatedTensor (lx : X → S) (T : Tensor ℂ X Y Z) :
    Tensor ℂ (X × U) (Y × U) (Z × S) :=
  fun x y z => if lx x.1 = z.2 ∧ x.2 = y.2 then T x.1 y.1 z.1 else 0

omit [Fintype G] in
theorem finite_separation_identity
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.pullback
      (fun x : X × U => (x.1, point (lx x.1) x.2))
      (fun y : Y × U => (y.1, tag (ly y.1) - point (ly y.1) y.2))
      (fun z : Z × S => (z.1, tag z.2))
      (Tensor.product T (groupTensor G)) = separatedTensor lx T := by
  funext x y z
  by_cases hzero : T x.1 y.1 z.1 = 0
  · simp [Tensor.pullback, Tensor.product, separatedTensor, hzero]
  · have hxy := hlabels x.1 y.1 z.1 hzero
    simp only [Tensor.pullback, Tensor.product, groupTensor, separatedTensor]
    simp only [← hxy, hcollision, mul_ite, mul_one, mul_zero]

theorem finite_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    separatedTensor (U := U) lx T ∈
      Tensor.restrictionOrbit (Tensor.product T (groupTensor G)) := by
  classical
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  refine ⟨(fun (x : X × U) (original : X × G) =>
      if original = (x.1, point (lx x.1) x.2) then 1 else 0),
    (fun (y : Y × U) (original : Y × G) =>
      if original = (y.1, tag (ly y.1) - point (ly y.1) y.2) then 1 else 0),
    (fun (z : Z × S) (original : Z × G) =>
      if original = (z.1, tag z.2) then 1 else 0), ?_⟩
  exact Tensor.pullback_eq_restrict _ _ _ _

theorem finite_separation_degeneratesTo
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.DegeneratesTo (Tensor.product T (groupTensor G))
      (separatedTensor (U := U) lx T) := by
  exact subset_closure
    (finite_separation_mem_restrictionOrbit T lx ly tag point hlabels hcollision)

theorem finite_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.RankAtMost (separatedTensor (U := U) lx T) (r * Fintype.card G) := by
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  exact (hT.product (groupTensor_rankAtMost G)).pullback _ _ _

theorem finite_separation_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G) {r : ℕ}
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.BorderRankAtMost (separatedTensor (U := U) lx T)
      (r * Fintype.card G) := by
  classical
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  rw [Tensor.pullback_eq_restrict]
  exact (hT.product (groupTensor_rankAtMost G).borderRankAtMost).restrict _ _ _

end Separation

section FiniteGrid

variable {X Y Z S : Type*} [Fintype S] [DecidableEq S]

theorem finite_grid_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m : ℕ} [NeZero (4 * Q)]
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin m) lx T ∈ Tensor.restrictionOrbit
      (Tensor.product T (groupTensor (Separation.AuxiliaryGroup d Q))) := by
  classical
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  exact finite_separation_mem_restrictionOrbit T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hlabels hc

theorem finite_grid_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m r : ℕ} (hQ : 0 < Q)
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (separatedTensor (U := Fin m) lx T) (r * (4 * Q) ^ d) := by
  classical
  let : NeZero (4 * Q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hQ)⟩
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  have hr := finite_separation_rankAtMost T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hT hlabels hc
  simpa only [Separation.card_auxiliaryGroup] using hr

theorem finite_grid_separation_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m r : ℕ} (hQ : 0 < Q)
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost (separatedTensor (U := Fin m) lx T)
      (r * (4 * Q) ^ d) := by
  classical
  let : NeZero (4 * Q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hQ)⟩
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  have hr := finite_separation_borderRankAtMost T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hT hlabels hc
  simpa only [Separation.card_auxiliaryGroup] using hr

end FiniteGrid
end MatrixMultiplication.Foundation

end OAI

end FlattenModule055
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteSeparation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing -/
section FlattenModule056

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Pairing

variable {K U : Type*} [CommSemiring K] [DecidableEq U]

def dotPairing (U : Type*) [DecidableEq U] : Tensor K U U Unit :=
  fun i j _ => if i = j then 1 else 0

@[simp] theorem dotPairing_matching (i : U) :
    dotPairing (K := K) U i i () = 1 := by
  simp [dotPairing]

theorem contract_dotPairing [Fintype U] (a b : U → K) :
    contract (dotPairing (K := K) U) a b () = ∑ i, a i * b i := by
  classical
  simp [contract, dotPairing, ite_mul]

end Pairing

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule056
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSeparatedTensorDecomposition -/
section FlattenModule057


namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section DependentSum

variable {K S : Type*} [CommSemiring K] [DecidableEq S]
variable {X Y Z : S → Type*}

def dependentDirectSum (T : ∀ s, Tensor K (X s) (Y s) (Z s)) :
    Tensor K (Σ s, X s) (Σ s, Y s) (Σ s, Z s) :=
  fun x y z =>
    if hxy : y.1 = x.1 then
      if hxz : z.1 = x.1 then T x.1 x.2 (hxy ▸ y.2) (hxz ▸ z.2)
      else 0
    else 0

@[simp] theorem dependentDirectSum_matching
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (s : S) (x : X s) (y : Y s) (z : Z s) :
    dependentDirectSum T ⟨s, x⟩ ⟨s, y⟩ ⟨s, z⟩ = T s x y z := by
  simp [dependentDirectSum]

theorem dependentDirectSum_zero_of_left_ne
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (x : Σ s, X s) (y : Σ s, Y s) (z : Σ s, Z s)
    (h : x.1 ≠ y.1) : dependentDirectSum T x y z = 0 := by
  simp [dependentDirectSum, Ne.symm h]

def directSumCoordinateEquiv {A : Type*} (e : ∀ s, X s ≃ A) :
    (Σ s, X s) ≃ S × A where
  toFun x := (x.1, e x.1 x.2)
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  left_inv := by
    rintro ⟨s, x⟩
    simp
  right_inv := by
    rintro ⟨s, x⟩
    simp

theorem dependentDirectSum_reindex {A B C : Type*}
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (ex : ∀ s, X s ≃ A) (ey : ∀ s, Y s ≃ B) (ez : ∀ s, Z s ≃ C) :
    pullback (directSumCoordinateEquiv ex).symm
      (directSumCoordinateEquiv ey).symm (directSumCoordinateEquiv ez).symm
      (dependentDirectSum T) =
      directSum (fun s => pullback (ex s).symm (ey s).symm (ez s).symm (T s)) := by
  funext x y z
  rcases x with ⟨s, x⟩
  rcases y with ⟨t, y⟩
  rcases z with ⟨v, z⟩
  by_cases ht : t = s
  · subst t
    by_cases hv : v = s
    · subst v
      simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum]
    · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
        hv, Ne.symm hv]
  · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
      ht, Ne.symm ht]

end DependentSum
end Tensor

section FiberDecomposition

variable {X Y Z S U : Type*} [DecidableEq S] [DecidableEq U]

def labelFiberTensor (lx : X → S) (ly : Y → S) (T : Tensor ℂ X Y Z) (s : S) :
    Tensor ℂ {x // lx x = s} {y // ly y = s} Z :=
  fun x y z => T x.1 y.1 z

def fiberCoordinateEquiv (lx : X → S) :
    (Σ s, {x // lx x = s} × U) ≃ X × U where
  toFun x := (x.2.1.1, x.2.2)
  invFun x := ⟨lx x.1, (⟨x.1, rfl⟩, x.2)⟩
  left_inv := by
    rintro ⟨s, ⟨⟨x, hx⟩, u⟩⟩
    cases hx
    rfl
  right_inv := by
    rintro ⟨x, u⟩
    rfl

def tagCoordinateEquiv : (Σ _ : S, Z × Unit) ≃ Z × S where
  toFun z := (z.2.1, z.1)
  invFun z := ⟨z.2, (z.1, ())⟩
  left_inv := by
    rintro ⟨s, z, u⟩
    cases u
    rfl
  right_inv := by
    rintro ⟨z, s⟩
    rfl

theorem separatedTensor_eq_fiber_directSum
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.pullback (fiberCoordinateEquiv (U := U) lx)
      (fiberCoordinateEquiv (U := U) ly) (tagCoordinateEquiv (Z := Z) (S := S))
      (separatedTensor lx T) =
      Tensor.dependentDirectSum (fun s =>
        Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U)) := by
  classical
  funext x y z
  rcases x with ⟨s, x, u⟩
  rcases y with ⟨t, y, v⟩
  rcases z with ⟨w, z, q⟩
  by_cases ht : t = s
  · subst t
    by_cases hw : w = s
    · subst w
      rw [Tensor.dependentDirectSum_matching]
      simp [Tensor.pullback, fiberCoordinateEquiv, tagCoordinateEquiv,
        separatedTensor, Tensor.product, labelFiberTensor, Tensor.dotPairing,
        x.property, mul_ite]
    · simp [Tensor.pullback, fiberCoordinateEquiv, tagCoordinateEquiv,
        separatedTensor, Tensor.dependentDirectSum, x.property, hw, Ne.symm hw]
  · have hzero : T x.1 y.1 z = 0 := by
      by_contra hzero
      have hxy := hlabels x.1 y.1 z hzero
      exact ht (y.property.symm.trans (hxy.symm.trans x.property))
    simp [Tensor.pullback, fiberCoordinateEquiv, tagCoordinateEquiv,
      separatedTensor, Tensor.dependentDirectSum, ht, hzero]

theorem fiber_directSum_eq_separatedTensor
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.pullback (fiberCoordinateEquiv (U := U) lx).symm
      (fiberCoordinateEquiv (U := U) ly).symm
      (tagCoordinateEquiv (Z := Z) (S := S)).symm
      (Tensor.dependentDirectSum (fun s =>
        Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) =
      separatedTensor lx T := by
  rw [← separatedTensor_eq_fiber_directSum T lx ly hlabels]
  funext x y z
  simp [Tensor.pullback]

theorem separatedTensor_fiber_directSum_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) r := by
  rw [← separatedTensor_eq_fiber_directSum T lx ly hlabels]
  exact h.pullback _ _ _

theorem separatedTensor_fiber_directSum_rankAtMost_iff
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (separatedTensor (U := U) lx T) r ↔
      Tensor.RankAtMost (Tensor.dependentDirectSum (fun s =>
        Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) r := by
  constructor
  · exact separatedTensor_fiber_directSum_rankAtMost T lx ly hlabels
  · intro h
    rw [← fiber_directSum_eq_separatedTensor T lx ly hlabels]
    exact h.pullback _ _ _

theorem separatedTensor_fiber_directSum_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (h : Tensor.BorderRankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.BorderRankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) r := by
  classical
  rw [← separatedTensor_eq_fiber_directSum T lx ly hlabels]
  rw [Tensor.pullback_eq_restrict]
  exact h.restrict _ _ _

theorem separatedTensor_uniform_directSum_rankAtMost {A B : Type*}
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (ex : ∀ s, {x // lx x = s} ≃ A) (ey : ∀ s, {y // ly y = s} ≃ B)
    {r : ℕ} (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.directSum (fun s => Tensor.pullback
      (Equiv.prodCongr (ex s) (Equiv.refl U)).symm
      (Equiv.prodCongr (ey s) (Equiv.refl U)).symm
      (Equiv.refl (Z × Unit)).symm
      (Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U)))) r := by
  have hf := separatedTensor_fiber_directSum_rankAtMost T lx ly hlabels h
  have hp := hf.pullback
    (Tensor.directSumCoordinateEquiv
      (fun s => Equiv.prodCongr (ex s) (Equiv.refl U))).symm
    (Tensor.directSumCoordinateEquiv
      (fun s => Equiv.prodCongr (ey s) (Equiv.refl U))).symm
    (Tensor.directSumCoordinateEquiv (fun _ : S => Equiv.refl (Z × Unit))).symm
  rw [Tensor.dependentDirectSum_reindex] at hp
  exact hp

theorem separatedTensor_localModels_identity {A B C : Type*}
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (fx : S → A → X) (fy : S → B → Y) (fz : S → C → Z)
    (hfx : ∀ s a, lx (fx s a) = s) (hfy : ∀ s b, ly (fy s b) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.pullback
      (fun x : S × (A × U) => (fx x.1 x.2.1, x.2.2))
      (fun y : S × (B × U) => (fy y.1 y.2.1, y.2.2))
      (fun z : S × (C × Unit) => (fz z.1 z.2.1, z.1))
      (separatedTensor lx T) =
      Tensor.directSum (fun s => Tensor.product
        (Tensor.pullback (fx s) (fy s) (fz s) T) (Tensor.dotPairing U)) := by
  funext x y z
  rcases x with ⟨s, a, u⟩
  rcases y with ⟨t, b, v⟩
  rcases z with ⟨w, c, q⟩
  by_cases ht : t = s
  · subst t
    by_cases hw : w = s
    · subst w
      simp [Tensor.pullback, separatedTensor, Tensor.directSum,
        Tensor.product, Tensor.dotPairing, hfx, mul_ite]
    · simp [Tensor.pullback, separatedTensor, Tensor.directSum,
        hfx, Ne.symm hw]
  · have hzero : T (fx s a) (fy t b) (fz w c) = 0 := by
      by_contra hzero
      have hxy := hlabels (fx s a) (fy t b) (fz w c) hzero
      exact ht ((hfy t b).symm.trans (hxy.symm.trans (hfx s a)))
    simp [Tensor.pullback, separatedTensor, Tensor.directSum,
      Ne.symm ht, hzero]

theorem separatedTensor_localModels_rankAtMost {A B C : Type*}
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (fx : S → A → X) (fy : S → B → Y) (fz : S → C → Z)
    (hfx : ∀ s a, lx (fx s a) = s) (hfy : ∀ s b, ly (fy s b) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    {r : ℕ} (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.directSum (fun s => Tensor.product
      (Tensor.pullback (fx s) (fy s) (fz s) T) (Tensor.dotPairing U))) r := by
  rw [← separatedTensor_localModels_identity T lx ly fx fy fz hfx hfy hlabels]
  exact h.pullback _ _ _

theorem separatedTensor_localModels_borderRankAtMost {A B C : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    [Fintype A] [Fintype B] [Fintype C]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (fx : S → A → X) (fy : S → B → Y) (fz : S → C → Z)
    (hfx : ∀ s a, lx (fx s a) = s) (hfy : ∀ s b, ly (fy s b) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    {r : ℕ} (h : Tensor.BorderRankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.BorderRankAtMost (Tensor.directSum (fun s => Tensor.product
      (Tensor.pullback (fx s) (fy s) (fz s) T) (Tensor.dotPairing U))) r := by
  classical
  rw [← separatedTensor_localModels_identity T lx ly fx fy fz hfx hfy hlabels]
  rw [Tensor.pullback_eq_restrict]
  exact h.restrict _ _ _

theorem separatedTensor_scalar_identity
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (sx : S → X) (sy : S → Y) (sz : S → Z)
    (hsx : ∀ s, lx (sx s) = s) (hsy : ∀ s, ly (sy s) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hscalar : ∀ s, T (sx s) (sy s) (sz s) = 1) :
    Tensor.pullback
      (fun x : S × U => (sx x.1, x.2))
      (fun y : S × U => (sy y.1, y.2))
      (fun z : S × Unit => (sz z.1, z.1)) (separatedTensor lx T) =
      Tensor.directSum (fun _ : S => Tensor.dotPairing U) := by
  have hmodels := separatedTensor_localModels_identity (U := U) T lx ly
    (fun s (_ : Unit) => sx s) (fun s (_ : Unit) => sy s) (fun s (_ : Unit) => sz s)
    (fun s _ => hsx s) (fun s _ => hsy s) hlabels
  have h := congrArg (Tensor.pullback
    (fun x : S × U => (x.1, ((), x.2)))
    (fun y : S × U => (y.1, ((), y.2)))
    (fun z : S × Unit => (z.1, ((), z.2)))) hmodels
  funext x y z
  have hpoint := congrFun (congrFun (congrFun h x) y) z
  simpa only [Tensor.pullback, Tensor.directSum, Tensor.product, hscalar, one_mul]
    using hpoint

theorem separatedTensor_scalar_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (sx : S → X) (sy : S → Y) (sz : S → Z)
    (hsx : ∀ s, lx (sx s) = s) (hsy : ∀ s, ly (sy s) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hscalar : ∀ s, T (sx s) (sy s) (sz s) = 1)
    {r : ℕ} (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : S => Tensor.dotPairing (K := ℂ) U)) r := by
  rw [← separatedTensor_scalar_identity T lx ly sx sy sz hsx hsy hlabels hscalar]
  exact h.pullback _ _ _

theorem separatedTensor_scalar_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (sx : S → X) (sy : S → Y) (sz : S → Z)
    (hsx : ∀ s, lx (sx s) = s) (hsy : ∀ s, ly (sy s) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hscalar : ∀ s, T (sx s) (sy s) (sz s) = 1)
    {r : ℕ} (h : Tensor.BorderRankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.BorderRankAtMost (Tensor.directSum (fun _ : S => Tensor.dotPairing U)) r := by
  classical
  rw [← separatedTensor_scalar_identity T lx ly sx sy sz hsx hsy hlabels hscalar]
  rw [Tensor.pullback_eq_restrict]
  exact h.restrict _ _ _

end FiberDecomposition
end MatrixMultiplication.Foundation

end OAI

end FlattenModule057
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSeparatedTensorDecomposition -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds -/
section FlattenModule058


namespace OAI

/-!
# Character values on powers and varying-dimension direct sums

These are consequences of the normalized restriction-monotone character
interface. Coordinate changes preserve values; permuting the three tensor
legs need not preserve an individual character.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character)

section Embeddings

variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']

/-- Extending finite coordinates by zero does not change a character value. -/
theorem value_extendByZero (T : Tensor ℂ X Y Z)
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz) :
    χ.value (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) = χ.value T := by
  classical
  apply le_antisymm (χ.monotone T _ _ _)
  have h := χ.value_pullback_le (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) fx fy fz
  have heq : Tensor.pullback fx fy fz (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) = T := by
    funext x y z
    simp [Tensor.pullback, Tensor.restrict, hx.eq_iff, hy.eq_iff, hz.eq_iff,
      ite_mul, mul_ite]
  simpa only [heq] using h

end Embeddings

section Powers

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Tensor powers turn a character value into an ordinary natural power. -/
@[simp] theorem value_power (T : Tensor ℂ X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  induction n with
  | zero =>
      have heq : Tensor.power T 0 = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) unitTensor := by
        funext x y z
        simp [Tensor.power, Tensor.pullback, unitTensor]
      rw [heq, χ.value_reindex, χ.map_one, pow_zero]
  | succ n ih =>
      have heq : Tensor.power T (n + 1) = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product T (Tensor.power T n)) := by
        funext x y z
        simp [Tensor.power, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, pow_succ, mul_comm]

/-- Full independent copies contribute their exact multiplicity. -/
theorem value_copies (T : Tensor ℂ X Y Z) (r : ℕ) :
    χ.value (Tensor.directSum (fun _ : Fin r => T)) = r * χ.value T := by
  rw [χ.map_directSum]
  simp

/-- The character cost of an exact number of full copies of a tensor power. -/
theorem value_power_copies (T : Tensor ℂ X Y Z) (r n : ℕ) :
    χ.value (Tensor.directSum (fun _ : Fin r => Tensor.power T n)) =
      r * χ.value T ^ n := by
  rw [χ.value_copies, χ.value_power]

end Powers

section DependentDirectSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X Y Z : ι → Type}
variable [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

/-- A branch extended to the common ambient sigma coordinate spaces. -/
def paddedBranch (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i)) (i : ι) :
    Tensor ℂ (Σ i, X i) (Σ i, Y i) (Σ i, Z i) :=
  Tensor.restrict
    (fun x a => if Sigma.mk i a = x then 1 else 0)
    (fun y b => if Sigma.mk i b = y then 1 else 0)
    (fun z c => if Sigma.mk i c = z then 1 else 0) (T i)

@[simp] theorem value_paddedBranch
    (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i)) (i : ι) :
    χ.value (paddedBranch T i) = χ.value (T i) := by
  simpa only [paddedBranch] using
    χ.value_extendByZero (T i) (Sigma.mk i) (Sigma.mk i) (Sigma.mk i)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

omit [Fintype ι] in
@[simp] theorem paddedBranch_matching
    (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i))
    (i : ι) (x : X i) (y : Y i) (z : Z i) :
    paddedBranch T i ⟨i, x⟩ ⟨i, y⟩ ⟨i, z⟩ = T i x y z := by
  simp [paddedBranch, Tensor.restrict, ite_mul, mul_ite]

omit [Fintype ι] in
theorem paddedBranch_zero_left
    (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hx : x.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ a : X i, Sigma.mk i a ≠ x :=
    fun a h => hx (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

omit [Fintype ι] in
theorem paddedBranch_zero_middle
    (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hy : y.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ b : Y i, Sigma.mk i b ≠ y :=
    fun b h => hy (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

omit [Fintype ι] in
theorem paddedBranch_zero_right
    (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hz : z.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ c : Z i, Sigma.mk i c ≠ z :=
    fun c h => hz (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

/-- Redundant outer labels give a zero extension of the varying-dimension sum. -/
theorem directSum_paddedBranch
    (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i)) :
    Tensor.directSum (paddedBranch T) = Tensor.restrict
      (fun (x' : ι × (Σ i, X i)) x => if (x.1, x) = x' then 1 else 0)
      (fun (y' : ι × (Σ i, Y i)) y => if (y.1, y) = y' then 1 else 0)
      (fun (z' : ι × (Σ i, Z i)) z => if (z.1, z) = z' then 1 else 0)
      (Tensor.dependentDirectSum T) := by
  funext x' y' z'
  rcases x' with ⟨i, ⟨ix, x⟩⟩
  rcases y' with ⟨j, ⟨iy, y⟩⟩
  rcases z' with ⟨k, ⟨iz, z⟩⟩
  have hgraph {A : Type} (f : A → ι) (a x : A) (i : ι) :
      (f a, a) = (i, x) ↔ a = x ∧ f x = i := by
    constructor
    · intro h
      have ha : a = x := congrArg Prod.snd h
      refine ⟨ha, ?_⟩
      rw [← ha]
      exact congrArg Prod.fst h
    · rintro ⟨rfl, h⟩
      simp [h]
  simp only [Tensor.restrict, hgraph, ite_and]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : ix = i
  · subst ix
    by_cases hj : iy = i
    · subst iy
      by_cases hk : iz = i
      · subst iz
        by_cases hij : i = j
        · subst j
          by_cases hik : i = k
          · subst k
            simp [Tensor.directSum, Tensor.dependentDirectSum]
          · simp [Tensor.directSum, hik]
        · simp [Tensor.directSum, hij]
      · simp [Tensor.directSum, Tensor.dependentDirectSum,
          paddedBranch_zero_right T i ⟨i, x⟩ ⟨i, y⟩ ⟨iz, z⟩ hk,
          hk]
    · simp [Tensor.directSum, Tensor.dependentDirectSum,
        paddedBranch_zero_middle T i ⟨i, x⟩ ⟨iy, y⟩ ⟨iz, z⟩ hj,
        hj]
  · simp [Tensor.directSum,
      paddedBranch_zero_left T i ⟨ix, x⟩ ⟨iy, y⟩ ⟨iz, z⟩ hi, hi]


/-- Additivity holds even when each summand has different coordinate types. -/
theorem value_dependentDirectSum
    (T : ∀ i, Tensor ℂ (X i) (Y i) (Z i)) :
    χ.value (Tensor.dependentDirectSum T) = ∑ i, χ.value (T i) := by
  have h := χ.value_extendByZero (Tensor.dependentDirectSum T)
    (fun x => (x.1, x)) (fun y => (y.1, y)) (fun z => (z.1, z))
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)
    (fun _ _ h => congrArg Prod.snd h)
  rw [← directSum_paddedBranch] at h
  rw [← h, χ.map_directSum]
  simp

end DependentDirectSum

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end FlattenModule058
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.BinaryCharacter -/
section FlattenModule059


namespace OAI

/-!
# Character additivity for binary tensor sums

The summands may have different finite coordinate types.  A binary sum is a
coordinate reindexing of the dependent direct sum over `Bool`.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

/-- A character is additive on binary direct sums with arbitrary finite
coordinate types. -/
theorem value_sumTensor (χ : Character)
    {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    χ.value (sumTensor T S) = χ.value T + χ.value S := by
  classical
  let family : (b : Bool) →
      Tensor ℂ (bif b then U else X) (bif b then V else Y) (bif b then W else Z)
    | false => T
    | true => S
  let : ∀ b : Bool, Fintype (bif b then U else X) :=
    fun | false => inferInstanceAs (Fintype X) | true => inferInstanceAs (Fintype U)
  let : ∀ b : Bool, Fintype (bif b then V else Y) :=
    fun | false => inferInstanceAs (Fintype Y) | true => inferInstanceAs (Fintype V)
  let : ∀ b : Bool, Fintype (bif b then W else Z) :=
    fun | false => inferInstanceAs (Fintype Z) | true => inferInstanceAs (Fintype W)
  have heq : Tensor.pullback (Equiv.sumEquivSigmaBool X U)
      (Equiv.sumEquivSigmaBool Y V) (Equiv.sumEquivSigmaBool Z W)
      (Tensor.dependentDirectSum family) = sumTensor T S := by
    funext x y z
    cases x <;> cases y <;> cases z <;>
      simp [Tensor.pullback, Tensor.dependentDirectSum, Equiv.sumEquivSigmaBool,
        family, sumTensor]
  rw [← heq, χ.value_reindex, χ.value_dependentDirectSum]
  simp [family, add_comm]

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end FlattenModule059
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.BinaryCharacter -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSumClass -/
section FlattenModule060


namespace OAI

/-!
# Finite direct sums in the tensor semiring

The tensor class of a block direct sum is the sum of its constituent classes.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.TensorSemiring

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

private theorem classOf_directSum_reindex {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (T : κ → Tensor ℂ X Y Z) (e : ι ≃ κ) :
    classOf (Tensor.directSum (fun i => T (e i))) = classOf (Tensor.directSum T) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e (Equiv.refl X))
    (Equiv.prodCongr e (Equiv.refl Y)) (Equiv.prodCongr e (Equiv.refl Z))
  funext x y z
  simp [Tensor.pullback, Tensor.directSum, e.injective.eq_iff]

private theorem classOf_directSum_option {ι : Type*} [Fintype ι] [di : DecidableEq ι]
    [dopt : DecidableEq (Option ι)]
    (T : Option ι → Tensor ℂ X Y Z) :
    classOf (Tensor.directSum T) =
      classOf (T none) + classOf (Tensor.directSum (fun i => T (some i))) := by
  rw [← classOf_sum]
  symm
  apply classOf_eq_of_reindex optionProdEquiv.symm
    optionProdEquiv.symm optionProdEquiv.symm
  funext x y z
  cases x with
  | inl x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]
  | inr x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]

/-- Passing to tensor classes converts every finite block direct sum to a sum. -/
theorem classOf_directSum {ι : Type*} [Fintype ι] [dec : DecidableEq ι]
    (T : ι → Tensor ℂ X Y Z) :
    classOf (Tensor.directSum T) = ∑ i, classOf (T i) := by
  have hdec : dec = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst dec
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ T : ι → Tensor ℂ X Y Z,
      classOf (Tensor.directSum T) = ∑ i, classOf (T i)) ?_ ?_ ?_ ι T
  · intro α β _ e ih S
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← classOf_directSum_reindex S e, ih]
    exact e.sum_comp (fun i => classOf (S i))
  · intro S
    have he : (∑ i, classOf (S i)) = 0 := Finset.sum_eq_zero (fun i _ => i.elim)
    rw [he]
    apply (classOf_eq_zero_iff _).mpr
    funext x
    exact x.1.elim
  · intro α _ ih S
    rw [classOf_directSum_option
      (di := fun a b => Classical.propDecidable (a = b))
      (dopt := fun a b => Classical.propDecidable (a = b)), ih, Fintype.sum_option]

end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI

end FlattenModule060
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSumClass -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Characters -/
section FlattenModule061




namespace OAI

/-!
# Concrete tensor characters and the tensor semiring

The coefficient-level character interface and monotone real-valued semiring
homomorphisms on mutual-restriction classes describe the same valuations.
The map `classOf` uses finite natural-number coordinate presentations, so
the construction applies to all finite coordinate types in the character
interface.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open TensorSemiring

namespace Character

/-- A character has a well-defined value on mutual-restriction classes. -/
def valueOnTensorClass (χ : Character) : TensorClass → ℝ :=
  Quotient.lift (fun T : FiniteTensor => χ.value T.coeff) (by
    intro T S h
    apply le_antisymm
    · rcases h.1 with ⟨A, B, C, heq⟩
      rw [heq]
      exact χ.monotone S.coeff A B C
    · rcases h.2 with ⟨A, B, C, heq⟩
      rw [heq]
      exact χ.monotone T.coeff A B C)

@[simp] theorem valueOnTensorClass_tensorClass (χ : Character) (T : FiniteTensor) :
    χ.valueOnTensorClass (tensorClass T) = χ.value T.coeff := rfl

/-- Passing to a finite natural-coordinate presentation preserves the value. -/
@[simp] theorem valueOnTensorClass_classOf (χ : Character)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : χ.valueOnTensorClass (classOf T) = χ.value T :=
  χ.value_reindex T _ _ _

/-- Restriction monotonicity descends to the quotient order. -/
theorem valueOnTensorClass_monotone (χ : Character) : Monotone χ.valueOnTensorClass := by
  intro T S h
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change IsRestriction T.coeff S.coeff at h
  rcases h with ⟨A, B, C, heq⟩
  change χ.value T.coeff ≤ χ.value S.coeff
  rw [heq]
  exact χ.monotone S.coeff A B C

@[simp] theorem valueOnTensorClass_zero (χ : Character) :
    χ.valueOnTensorClass 0 = 0 := by
  change χ.valueOnTensorClass (classOf (0 : Tensor ℂ Empty Empty Empty)) = 0
  rw [χ.valueOnTensorClass_classOf, χ.map_zero]

@[simp] theorem valueOnTensorClass_one (χ : Character) :
    χ.valueOnTensorClass 1 = 1 := by
  change χ.valueOnTensorClass (classOf unitTensor) = 1
  rw [χ.valueOnTensorClass_classOf, χ.map_one]

/-- Multiplicativity is unchanged on passing to tensor classes. -/
theorem valueOnTensorClass_mul (χ : Character) (T S : TensorClass) :
    χ.valueOnTensorClass (T * S) = χ.valueOnTensorClass T * χ.valueOnTensorClass S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change χ.valueOnTensorClass (tensorClass T * tensorClass S) =
    χ.valueOnTensorClass (tensorClass T) * χ.valueOnTensorClass (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_product]
  simp only [χ.valueOnTensorClass_classOf]
  exact χ.map_product T.coeff S.coeff

/-- Additivity is unchanged on passing to tensor classes. -/
theorem valueOnTensorClass_add (χ : Character) (T S : TensorClass) :
    χ.valueOnTensorClass (T + S) = χ.valueOnTensorClass T + χ.valueOnTensorClass S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change χ.valueOnTensorClass (tensorClass T + tensorClass S) =
    χ.valueOnTensorClass (tensorClass T) + χ.valueOnTensorClass (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_sum]
  simp only [χ.valueOnTensorClass_classOf]
  exact χ.value_sumTensor T.coeff S.coeff

/-- A coefficient-level character descends to a normalized semiring homomorphism. -/
def toTensorClassHom (χ : Character) : TensorClass →+* ℝ where
  toFun := χ.valueOnTensorClass
  map_zero' := χ.valueOnTensorClass_zero
  map_one' := χ.valueOnTensorClass_one
  map_add' := χ.valueOnTensorClass_add
  map_mul' := χ.valueOnTensorClass_mul

theorem toTensorClassHom_monotone (χ : Character) : Monotone χ.toTensorClassHom :=
  χ.valueOnTensorClass_monotone

@[simp] theorem toTensorClassHom_classOf (χ : Character)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : χ.toTensorClassHom (classOf T) = χ.value T :=
  χ.valueOnTensorClass_classOf T

/-- A monotone semiring homomorphism on tensor classes gives a character on all
finite coefficient tensors. Normalization follows from preservation of `0` and `1`. -/
def ofTensorClassHom (φ : TensorClass →+* ℝ) (hφ : Monotone φ) : Character where
  value := fun T => φ (classOf T)
  nonneg := by
    intro X Y Z hX hY hZ T
    simpa only [φ.map_zero] using hφ (TensorSemiring.zero_le (classOf T))
  map_zero := by
    intro X Y Z hX hY hZ
    rw [classOf_zero]
    exact φ.map_zero
  map_one := by
    change φ 1 = 1
    exact φ.map_one
  map_directSum := by
    intro ι X Y Z hι dι hX hY hZ T
    rw [classOf_directSum, map_sum]
  map_product := by
    intro X Y Z U V W hX hY hZ hU hV hW T S
    rw [classOf_product, map_mul]
  monotone := by
    intro X Y Z X' Y' Z' hX hY hZ hX' hY' hZ' T A B C
    apply hφ
    exact (classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩

@[simp] theorem ofTensorClassHom_value (φ : TensorClass →+* ℝ) (hφ : Monotone φ)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : (ofTensorClassHom φ hφ).value T = φ (classOf T) := rfl

/-- Equality of all coefficient-level values determines a character. -/
@[ext] theorem ext {χ ψ : Character}
    (h : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
      (T : Tensor ℂ X Y Z), χ.value T = ψ.value T) : χ = ψ := by
  cases χ
  cases ψ
  congr
  funext X Y Z hX hY hZ T
  exact h T

/-- Descending and then lifting recovers the original coefficient-level character. -/
@[simp] theorem ofTensorClassHom_toTensorClassHom (χ : Character) :
    ofTensorClassHom χ.toTensorClassHom χ.toTensorClassHom_monotone = χ := by
  apply ext
  intro X Y Z hX hY hZ T
  exact χ.toTensorClassHom_classOf T

/-- Lifting and then descending recovers the original semiring homomorphism. -/
@[simp] theorem toTensorClassHom_ofTensorClassHom
    (φ : TensorClass →+* ℝ) (hφ : Monotone φ) :
    (ofTensorClassHom φ hφ).toTensorClassHom = φ := by
  apply RingHom.ext
  intro T
  induction T using Quotient.inductionOn with | h T =>
  change φ (classOf T.coeff) = φ (tensorClass T)
  rw [classOf_coeff]

/-- Concrete characters are exactly monotone real-valued tensor semiring homomorphisms. -/
def tensorClassHomEquiv : Character ≃ {φ : TensorClass →+* ℝ // Monotone φ} where
  toFun χ := ⟨χ.toTensorClassHom, χ.toTensorClassHom_monotone⟩
  invFun φ := ofTensorClassHom φ.1 φ.2
  left_inv := ofTensorClassHom_toTensorClassHom
  right_inv φ := Subtype.ext (toTensorClassHom_ofTensorClassHom φ.1 φ.2)

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule061
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Characters -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Existence -/
section FlattenModule062




namespace OAI

/-!
# Detecting characters for complex matrix multiplication

This proves Lemma 3.1, including Appendix A. Finite inconsistency would
produce a positive scalar-gain catalyst, ruled out by the exact-rank exponent.
A compact normalized state space then yields a multiplicative state, which
transfers to the concrete coefficient-level character interface.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Lemma 3.1: normalized, additive, multiplicative, restriction-monotone
characters detect every integer strictly below the exact-rank growth value. -/
theorem exists_detecting_character {d k : ℕ} (hd : 2 ≤ d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    ∃ χ : Character, (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d) := by
  have hnonempty := normalizedStates_nonempty_of_no_catalyst
    TensorSemiring.rank (TensorSemiring.matrixClass d) k
    TensorSemiring.zero_le TensorSemiring.le_rank
    (fun _ _ _ _ h₁ h₂ => TensorSemiring.add_mono h₁ h₂)
    (fun D s m hm hcat => no_tensor_catalytic_gain (by omega) hk ⟨D, s, m, hm, hcat⟩)
  have hdom (z x : TensorSemiring.TensorClass) :
      z * x ≤ (TensorSemiring.rank x : TensorSemiring.TensorClass) * z := by
    calc
      z * x ≤ z * (TensorSemiring.rank x : TensorSemiring.TensorClass) :=
        TensorSemiring.mul_mono le_rfl (TensorSemiring.le_rank x)
      _ = (TensorSemiring.rank x : TensorSemiring.TensorClass) * z := mul_comm _ _
  obtain ⟨φ, hφ, _, hdetect⟩ := exists_monotone_semiringHom_of_normalizedStates
    TensorSemiring.rank (TensorSemiring.matrixClass d) (k : ℝ)
    (fun z hz => TensorSemiring.one_le_of_ne_zero hz)
    (fun _ _ _ h => TensorSemiring.mul_mono le_rfl h) hdom hnonempty
  exact ⟨Character.ofTensorClassHom φ hφ, hdetect⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule062
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Existence -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison -/
section FlattenModule063


namespace OAI

/-!
# Comparing power growth

The last scalar step of the auxiliary-separation argument compares a
fourth-power lower bound for the cube of the diagonal profile with its
dimension upper bound.  Powers of two suffice to compare the exponents, so
the argument needs no asymptotic estimates or approximation of constants.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- A uniform bound on all positive natural inputs forces the exponent on
the left to be no larger than the exponent on the right. -/
theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  have hC : 0 < C := by
    have h := hbound 1 (by omega)
    norm_num at h
    linarith
  by_contra hab
  have hab' : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (a - b) * Real.log 2 := mul_pos hab' hlog2
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.log C / ((a - b) * Real.log 2))
  have hk' : Real.log C < (k : ℝ) * ((a - b) * Real.log 2) :=
    (div_lt_iff₀ hp).mp hk
  have hn : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have h := Real.log_le_log (Real.rpow_pos_of_pos hn a)
    (hbound (2 ^ k) (Nat.one_le_iff_ne_zero.mpr (by positivity)))
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hn b).ne',
    Real.log_rpow hn a, Real.log_rpow hn b] at h
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  nlinarith

/-- The diagonal lower bound and the dimension upper bound force the scalar
exponent to be at most `3/4`. -/
theorem diagonal_exponent_le_three_quarters {D : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ D n)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 4 ≤ D n ^ 3)
    (hupper : ∀ n : ℕ, 1 ≤ n → D n ≤ (2 * (n : ℝ) - 1) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  have hexp : 0 ≤ 1 / t := le_of_lt (one_div_pos.mpr ht)
  have hpower : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (4 : ℝ) ≤
        (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbase : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
    have hu : D n ≤ (2 * (n : ℝ)) ^ (1 / t) :=
      (hupper n hn).trans (Real.rpow_le_rpow hbase (by linarith) hexp)
    calc
      (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by norm_num
      _ ≤ D n ^ 3 := hlower n hn
      _ ≤ ((2 * (n : ℝ)) ^ (1 / t)) ^ 3 :=
        pow_le_pow_left₀ (hnonneg n hn) hu 3
      _ = (2 * (n : ℝ)) ^ ((1 / t) * 3) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast (show 0 ≤ 2 * (n : ℝ) by positivity) (1 / t) 3).symm
      _ = (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) :=
        Real.mul_rpow (by norm_num) (by positivity)
  have hcompare : (4 : ℝ) ≤ (1 / t) * 3 :=
    rpow_exponent_le_of_nat_bound hpower
  have hmul := mul_le_mul_of_nonneg_right hcompare (le_of_lt ht)
  have hcancel : ((1 / t) * 3) * t = (3 : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  linarith

/-- The scalar comparison in the normalization used for the matrix
multiplication exponent. -/
theorem three_mul_diagonal_exponent_le_nine_quarters {D : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ D n)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 4 ≤ D n ^ 3)
    (hupper : ∀ n : ℕ, 1 ≤ n → D n ≤ (2 * (n : ℝ) - 1) ^ (1 / t)) :
    3 * t ≤ 9 / 4 := by
  have h := diagonal_exponent_le_three_quarters ht hnonneg hlower hupper
  linarith

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule063
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.CharacterRounding -/
section FlattenModule064




namespace OAI

/-!
# Integer rounding in the detecting-character argument

The character used at a matrix size may depend on that size. A uniform bound
on all those characters is enough: the loss of one in rounding their target
values cannot change a positive power exponent. The character-existence and
character-growth assumptions remain explicit in the final implications.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Rounding strictly down works at integers too: use `ceil x - 1`. -/
theorem exists_nat_sub_one_le_lt {x : ℝ} (hx : 0 < x) :
    ∃ k : ℕ, x - 1 ≤ (k : ℝ) ∧ (k : ℝ) < x := by
  have hc : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  refine ⟨⌈x⌉₊ - 1, ?_, ?_⟩
  · rw [Nat.cast_sub hc]
    norm_num only [Nat.cast_one]
    linarith [Nat.le_ceil x]
  · exact ((Nat.ceil_eq_iff (by omega : ⌈x⌉₊ ≠ 0)).1 rfl).1

/-- An additive loss of one does not affect a comparison to a nonnegative
power exponent. No sign assumption on the exponent on the left is needed. -/
theorem rpow_exponent_le_of_nat_sub_one_bound {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hbound : ∀ d : ℕ, 2 ≤ d → (d : ℝ) ^ ν - 1 ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  by_cases hd2 : 2 ≤ d
  · have h := hbound d hd2
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : 1 ≤ (d : ℝ) ^ τ := Real.one_le_rpow hdreal hτ
    linarith
  · have hd1 : d = 1 := by omega
    simp [hd1]

/-- The integer witnesses in the final rounding argument can vary with `d`. -/
theorem exponent_le_of_integer_rounding {ν τ : ℝ} (hτ : 0 ≤ τ)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply rpow_exponent_le_of_nat_sub_one_bound hτ
  intro d hd
  obtain ⟨k, hk, hk'⟩ := hround d hd
  exact hk.trans hk'

/-- A positive exponent on the left makes the target exponent nonnegative
automatically, so it is an alternative to that hypothesis above. -/
theorem exponent_le_of_integer_rounding_of_pos {ν τ : ℝ} (hν : 0 < ν)
    (hround : ∀ d : ℕ, 2 ≤ d →
      ∃ k : ℕ, (d : ℝ) ^ ν - 1 ≤ k ∧ (k : ℝ) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  have hτ : 0 ≤ τ := by
    by_contra hneg
    obtain ⟨k, hk, hk'⟩ := hround 2 le_rfl
    norm_num only [Nat.cast_ofNat] at hk hk'
    have hpτ : (2 : ℝ) ^ τ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (lt_of_not_ge hneg)
    have hklt : (k : ℝ) < 1 := hk'.trans_lt hpτ
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast hklt
      omega
    rw [hk0, Nat.cast_zero] at hk
    have hpν : 1 < (2 : ℝ) ^ ν := Real.one_lt_rpow (by norm_num) hν
    linarith
  exact exponent_le_of_integer_rounding hτ hround

/-- Explicitly conditional passage from detecting characters to the exponent
bound. The detecting character is allowed to depend on both `d` and `k`. -/
theorem exponent_le_of_detecting_characters {ν τ : ℝ} (hτ : 0 ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : Character, (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d))
    (bound : ∀ χ : Character, ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) ≤ (d : ℝ) ^ τ) :
    ν ≤ τ := by
  apply exponent_le_of_integer_rounding hτ
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨k, hk, hk'⟩ :=
    exists_nat_sub_one_le_lt (Real.rpow_pos_of_pos hdpos ν)
  obtain ⟨χ, hχ⟩ := detect d hd k hk'
  exact ⟨k, hk, hχ.trans (bound χ d hd)⟩

/-- The character growth bound can be supplied as a uniform bound on its
exponent sum, together with the matrix-value identity. -/
theorem exponent_le_of_detecting_character_exponents {ν τ : ℝ} (hτ : 0 ≤ τ)
    (exponentSum : Character → ℝ)
    (value : ∀ χ : Character, ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) = (d : ℝ) ^ exponentSum χ)
    (upper : ∀ χ : Character, exponentSum χ ≤ τ)
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ, (k : ℝ) < (d : ℝ) ^ ν →
      ∃ χ : Character, (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d)) :
    ν ≤ τ := by
  apply exponent_le_of_detecting_characters hτ detect
  intro χ d hd
  rw [value χ d hd]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ d by omega))
    (upper χ)

/-- The paper's final `ν ≤ 9/4` implication, with its two substantive character
inputs visible rather than incorporated into the definition of `ν`. -/
theorem exactRankExponent_le_nine_quarters_of_characters
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ,
      (k : ℝ) < (d : ℝ) ^ exactRankExponent →
      ∃ χ : Character, (k : ℝ) ≤ χ.value (Tensor.matrixMultiplication d d d))
    (bound : ∀ χ : Character, ∀ d : ℕ, 2 ≤ d →
      χ.value (Tensor.matrixMultiplication d d d) ≤ (d : ℝ) ^ (9 / 4 : ℝ)) :
    exactRankExponent ≤ 9 / 4 :=
  exponent_le_of_detecting_characters (by norm_num) detect bound

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule064
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.CharacterRounding -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PermutationProduct -/
section FlattenModule065







namespace OAI

/-!
# Products over the six permutations of three tensor legs

The symmetrized quantity in Section 5 uses every permutation of the three
tensor legs. Composing by a fixed permutation preserves this product. For
the exponent calculation, each original leg occurs twice in any fixed slot.
These are finite identities; they do not assume that an individual tensor
character is invariant under exchanging its legs.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- A permutation of the three tensor legs. -/
abbrev LegPermutation := Equiv.Perm (Fin 3)

namespace LegPermutation

/-- There are six orders of the three legs. -/
theorem card : Fintype.card LegPermutation = 6 := by
  norm_num [Fintype.card_perm, Nat.factorial]

/-- Right composition just reindexes a product over all six permutations. -/
theorem prod_mul_right {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π, f (π * σ)) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.mulRight σ) f

/-- Left composition also just reindexes the six factors. -/
theorem prod_mul_left {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π, f (σ * π)) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.mulLeft σ) f

/-- The same reindexing statement in explicit equivalence-composition notation. -/
theorem prod_trans_right {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π : LegPermutation, f (π.trans σ)) = ∏ π, f π := by
  exact prod_mul_left f σ

/-- A permutation-independent sum may likewise be reindexed on the right. -/
theorem sum_mul_right {A : Type*} [AddCommMonoid A]
    (f : LegPermutation → A) (σ : LegPermutation) :
    (∑ π, f (π * σ)) = ∑ π, f π := by
  exact Equiv.sum_comp (Equiv.mulRight σ) f

/-- Each original leg occurs twice in each fixed position. -/
theorem card_apply_fiber (i j : Fin 3) :
    Fintype.card {π : LegPermutation // π i = j} = 2 := by
  let _ : Fintype LegPermutation := fintypePerm
  fin_cases i <;> fin_cases j <;> decide

/-- The product of values attached to one slot contains each leg twice. -/
theorem prod_apply {M : Type*} [CommMonoid M] (f : Fin 3 → M) (i : Fin 3) :
    (∏ π : LegPermutation, f (π i)) = (∏ j, f j) ^ 2 := by
  rw [← Fintype.prod_fiberwise' (fun π : LegPermutation => π i) f]
  simp only [Finset.prod_const, Finset.card_univ, card_apply_fiber, Finset.prod_pow]

/-- The exponent attached to one slot contains each leg exponent twice. -/
theorem sum_apply {A : Type*} [AddCommMonoid A] (p : Fin 3 → A) (i : Fin 3) :
    (∑ π : LegPermutation, p (π i)) = 2 • ∑ j, p j := by
  rw [← Fintype.sum_fiberwise' (fun π : LegPermutation => π i) p]
  simp only [Finset.sum_const, Finset.card_univ, card_apply_fiber, Finset.sum_nsmul]

/-- Inverting the permutation preserves the symmetrized product. -/
theorem prod_symm {M : Type*} [CommMonoid M] (f : LegPermutation → M) :
    (∏ π : LegPermutation, f π.symm) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.inv LegPermutation) f

/-- Inverting the permutation preserves a sum over all six orders. -/
theorem sum_symm {A : Type*} [AddCommMonoid A] (f : LegPermutation → A) :
    (∑ π : LegPermutation, f π.symm) = ∑ π, f π := by
  exact Equiv.sum_comp (Equiv.inv LegPermutation) f

/-- The twice-per-leg count is independent of the permutation convention. -/
theorem sum_symm_apply {A : Type*} [AddCommMonoid A]
    (p : Fin 3 → A) (i : Fin 3) :
    (∑ π : LegPermutation, p (π.symm i)) = 2 • ∑ j, p j := by
  rw [sum_symm (fun π => p (π i)), sum_apply]

/-- The sum of the six singleton-leg exponents is six times their mean. -/
theorem sum_exponents (p : Fin 3 → ℝ) (i : Fin 3) (t : ℝ)
    (h : (∑ j, p j) = 3 * t) :
    (∑ π : LegPermutation, p (π i)) = 6 * t := by
  rw [sum_apply, h]
  simp only [nsmul_eq_mul]
  ring

/-- The product of the valuations of all six transforms of an object. -/
def orbitProduct {X M : Type*} [CommMonoid M]
    (transform : LegPermutation → X → X) (value : X → M) (x : X) : M :=
  ∏ π : LegPermutation, value (transform π x)

/-- A further leg transformation preserves the product whenever transforms compose. -/
theorem orbitProduct_transform {X M : Type*} [CommMonoid M]
    (transform : LegPermutation → X → X) (value : X → M)
    (compose : ∀ π σ x, transform π (transform σ x) = transform (π * σ) x)
    (σ : LegPermutation) (x : X) :
    orbitProduct transform value (transform σ x) = orbitProduct transform value x := by
  simp only [orbitProduct, compose]
  exact prod_mul_right (fun π => value (transform π x)) σ

end LegPermutation

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule065
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PermutationProduct -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization -/
section FlattenModule066

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

theorem RankAtMost.cyclic {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) : RankAtMost (Tensor.cyclic T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, c, a, ?_⟩
  funext y z x
  simp only [Tensor.cyclic, rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def directSumProductEquiv (ι κ X U : Type*) :
    ((ι × κ) × (X × U)) ≃ ((ι × X) × (κ × U)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (T : ι → Tensor K X Y Z) (S : κ → Tensor K U V W) :
    pullback (directSumProductEquiv ι κ X U)
      (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
      (product (directSum T) (directSum S)) =
      directSum (fun i : ι × κ => product (T i.1) (S i.2)) := by
  funext x y z
  change
    (if x.1.1 = y.1.1 ∧ x.1.1 = z.1.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 else 0) *
    (if x.1.2 = y.1.2 ∧ x.1.2 = z.1.2 then
      S x.1.2 x.2.2 y.2.2 z.2.2 else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 * S x.1.2 x.2.2 y.2.2 z.2.2 else 0
  have hguard : (x.1 = y.1 ∧ x.1 = z.1) ↔
      (x.1.1 = y.1.1 ∧ x.1.1 = z.1.1) ∧
      (x.1.2 = y.1.2 ∧ x.1.2 = z.1.2) := by
    constructor
    · intro h
      exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
        ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩⟩
    · intro h
      exact ⟨Prod.ext h.1.1 h.2.1, Prod.ext h.1.2 h.2.2⟩
  by_cases hi : x.1.1 = y.1.1 ∧ x.1.1 = z.1.1
  · by_cases hk : x.1.2 = y.1.2 ∧ x.1.2 = z.1.2
    · simp only [ite_eq_left hi, ite_eq_left hk, ite_eq_left (hguard.mpr ⟨hi, hk⟩)]
    · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hk (hguard.mp h).2
      simp only [ite_eq_left hi, ite_eq_right hk, ite_eq_right hfull, mul_zero]
  · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hi (hguard.mp h).1
    simp only [ite_eq_right hi, ite_eq_right hfull, zero_mul]

theorem RankAtMost.directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : ι → Tensor K X Y Z} {S : κ → Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost (directSum T) r) (hS : RankAtMost (directSum S) s) :
    RankAtMost (directSum (fun i : ι × κ => Tensor.product (T i.1) (S i.2))) (r * s) := by
  have h := (hT.product hS).pullback (directSumProductEquiv ι κ X U)
    (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
  rw [Tensor.directSum_product] at h
  exact h

theorem directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    pullback (fun x : ι × X' => (x.1, fx x.2))
      (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))
      (directSum T) = directSum (fun i => pullback fx fy fz (T i)) := rfl

theorem RankAtMost.directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (directSum (fun i => Tensor.pullback fx fy fz (T i))) r :=
  h.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

theorem cyclic_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [cyclic, directSum]
    · simp [cyclic, directSum, hik, Ne.symm hik]
  · by_cases hki : k = i
    · subst k
      simp [cyclic, directSum, hij]
    · simp [cyclic, directSum, hij, hki]

theorem RankAtMost.directSum_cyclic {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r) :
    RankAtMost (directSum (fun i => Tensor.cyclic (T i))) r := by
  rw [← Tensor.cyclic_directSum]
  exact h.cyclic

def directSumPowerEquiv (ι X : Type*) (n : ℕ) :
    ((Fin n → ι) × (Fin n → X)) ≃ (Fin n → ι × X) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem directSum_power {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum T) n) =
      directSum (fun f : Fin n → ι =>
        fun x y z => ∏ i, T (f i) (x i) (y i) (z i)) := by
  funext x y z
  change (∏ i, if x.1 i = y.1 i ∧ x.1 i = z.1 i then
      T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      ∏ i, T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff]

theorem directSum_const_power {ι : Type*} [DecidableEq ι]
    (T : Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum (fun _ : ι => T)) n) =
      directSum (fun _ : Fin n → ι => power T n) :=
  directSum_power (fun _ : ι => T) n

theorem RankAtMost.directSum_const_of_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {n R : ℕ}
    (h : RankAtMost (Tensor.power (directSum (fun _ : ι => T)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) R := by
  have h' := h.pullback (directSumPowerEquiv ι X n)
    (directSumPowerEquiv ι Y n) (directSumPowerEquiv ι Z n)
  rw [Tensor.directSum_const_power] at h'
  exact h'

theorem RankAtMost.directSum_const_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum (fun _ : ι => T)) r)
    (n : ℕ) : RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) (r ^ n) :=
  (h.power n).directSum_const_of_power

section Rectangular

variable {A B C : Type*}

def rectangularSquareX (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((A × B) × (B × C)) × (C × A)) where
  toFun x := (((x.1.1, x.2.2.1), (x.1.2.1, x.2.2.2)), (x.1.2.2, x.2.1))
  invFun x := ((x.1.1.1, x.1.2.1, x.2.1), (x.2.2, x.1.1.2, x.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareY (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((B × C) × (C × A)) × (A × B)) where
  toFun y := (((y.1.2.1, y.2.2.2), (y.1.2.2, y.2.1)), (y.1.1, y.2.2.1))
  invFun y := ((y.2.1, y.1.1.1, y.1.2.1), (y.1.2.2, y.2.2, y.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareZ (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((C × A) × (A × B)) × (B × C)) where
  toFun z := (((z.1.2.2, z.2.1), (z.1.1, z.2.2.1)), (z.1.2.1, z.2.2.2))
  invFun z := ((z.1.2.1, z.2.1, z.1.1.1), (z.1.1.2, z.1.2.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrixCoefficients_directSum_rank_of_power
    {ι : Type*} [DecidableEq ι] {n R : ℕ}
    (h : RankAtMost
      (power (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι =>
      matrixCoefficients (K := K) (Fin n → A) (Fin n → B) (Fin n → C))) R := by
  have h' := h.directSum_const_of_power.directSum_pullback
    (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
  have heq : pullback
      (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
      (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
      (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
      (power (matrixCoefficients (K := K) A B C) n) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) := by
    funext x y z
    exact matrixCoefficients_power n x y z
  simpa only [heq] using h'

theorem matrixCoefficients_cyclic_product_square :
    pullback (rectangularSquareX A B C) (rectangularSquareY A B C)
      (rectangularSquareZ A B C)
      (product (product (matrixCoefficients (K := K) A B C)
        (matrixCoefficients B C A)) (matrixCoefficients C A B)) =
      matrixCoefficients (A × B × C) (A × B × C) (A × B × C) := by
  funext x y z
  change
    ((if x.2.2.1 = y.1.2.1 ∧ y.2.2.2 = z.1.2.2 ∧ z.2.1 = x.1.1 then
        (1 : K) else 0) *
      (if x.2.2.2 = y.1.2.2 ∧ y.2.1 = z.1.1 ∧ z.2.2.1 = x.1.2.1 then
        1 else 0)) *
      (if x.2.1 = y.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ z.2.2.2 = x.1.2.2 then
        1 else 0) =
      if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [Prod.ext_iff]
  have hguard :
      (((x.2.2.1 = y.1.2.1 ∧ y.2.2.2 = z.1.2.2 ∧ z.2.1 = x.1.1) ∧
        (x.2.2.2 = y.1.2.2 ∧ y.2.1 = z.1.1 ∧ z.2.2.1 = x.1.2.1)) ∧
        (x.2.1 = y.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ z.2.2.2 = x.1.2.2)) ↔
      ((x.2.1 = y.1.1 ∧ x.2.2.1 = y.1.2.1 ∧ x.2.2.2 = y.1.2.2) ∧
        (y.2.1 = z.1.1 ∧ y.2.2.1 = z.1.2.1 ∧ y.2.2.2 = z.1.2.2) ∧
        z.2.1 = x.1.1 ∧ z.2.2.1 = x.1.2.1 ∧ z.2.2.2 = x.1.2.2) := by
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨⟨h₃.1, h₁.1, h₂.1⟩, ⟨h₂.2.1, h₃.2.1, h₁.2.1⟩,
        h₁.2.2, h₂.2.2, h₃.2.2⟩
    · intro h
      exact ⟨⟨⟨h.1.2.1, h.2.1.2.2, h.2.2.1⟩,
        ⟨h.1.2.2, h.2.1.1, h.2.2.2.1⟩⟩, ⟨h.1.1, h.2.1.2.1, h.2.2.2.2⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem cyclic_matrixCoefficients :
    cyclic (matrixCoefficients (K := K) A B C) = matrixCoefficients B C A := by
  funext x y z
  exact matrixCoefficients_cyclic x y z

theorem matrixCoefficients_symmetrized_rank {r : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K)
      (A × B × C) (A × B × C) (A × B × C)) (r ^ 3) := by
  have h' := ((h.product (matrixCoefficients_cyclic_rank h)).product
    (matrixCoefficients_cyclic_rank (matrixCoefficients_cyclic_rank h))).pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  rw [matrixCoefficients_cyclic_product_square] at h'
  simpa only [pow_succ, pow_zero, one_mul] using h'

theorem matrixCoefficients_directSum_symmetrized_rank
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : (ι × ι) × ι =>
      matrixCoefficients (K := K) (A × B × C) (A × B × C) (A × B × C))) (r ^ 3) := by
  have h₁ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
    simpa only [cyclic_matrixCoefficients] using h.directSum_cyclic
  have h₂ : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) C A B)) r := by
    simpa only [cyclic_matrixCoefficients] using h₁.directSum_cyclic
  have h₃ := ((h.directSum_product h₁).directSum_product h₂).directSum_pullback
    (rectangularSquareX A B C) (rectangularSquareY A B C) (rectangularSquareZ A B C)
  simpa only [matrixCoefficients_cyclic_product_square, pow_succ, pow_zero, one_mul] using h₃

theorem symmetrized_tag_card (ι : Type*) [Fintype ι] :
    Fintype.card ((ι × ι) × ι) = Fintype.card ι ^ 3 := by
  simp [Fintype.card_prod, pow_succ]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
theorem symmetrized_index_card [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (A × B × C) = Fintype.card A * Fintype.card B * Fintype.card C := by
  simp [Fintype.card_prod, mul_assoc]

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule066
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic -/
section FlattenModule067



namespace OAI

/-!
# The polynomial multiplication tensor

The coefficient tensor `convolution a b` represents multiplication of binary forms
of degrees `a - 1` and `b - 1`, or equivalently ordinary coefficient convolution.
The output leg has `a + b - 1` coordinates.  The definitions also make sense when
an input dimension is zero, while the nonzero and full-output-support statements
use the positive dimensions assumed in Section 5 of the paper.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- The tensor `C(a,b)` of Section 5, in monomial coefficient coordinates. -/
def convolution (a b : ℕ) : Tensor ℂ (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp] theorem convolution_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

@[simp] theorem convolution_ne_zero_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution a b i j k ≠ 0 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

@[simp] theorem convolution_eq_one_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution a b i j k = 1 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

@[simp] theorem convolution_eq_zero_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution a b i j k = 0 ↔ i.val + j.val ≠ k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

/-- Every pair of input monomials has a valid output coordinate. -/
def convolutionOutput {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a + b - 1) :=
  ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩

@[simp] theorem convolution_at_output {a b : ℕ} (i : Fin a) (j : Fin b) :
    convolution a b i j (convolutionOutput i j) = 1 := by
  simp [convolutionOutput]

/-- Every output monomial of the expected degree occurs in the product. -/
theorem convolution_output_supported {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (k : Fin (a + b - 1)) :
    ∃ (i : Fin a) (j : Fin b), convolution a b i j k = 1 := by
  by_cases hk : k.val < a
  · exact ⟨⟨k.val, hk⟩, ⟨0, hb⟩, by simp⟩
  · have hk' := k.isLt
    refine ⟨⟨a - 1, by omega⟩, ⟨k.val - (a - 1), by omega⟩, ?_⟩
    apply (convolution_eq_one_iff _ _ _).mpr
    dsimp
    omega

theorem convolution_nonzero {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    convolution a b ≠ 0 := by
  intro hz
  have hc := congrFun (congrFun (congrFun hz ⟨0, ha⟩) ⟨0, hb⟩)
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩)
  change convolution a b ⟨0, ha⟩ ⟨0, hb⟩
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩) = 0 at hc
  rw [convolution_at_output] at hc
  exact one_ne_zero hc

theorem convolution_nonzero_iff (a b : ℕ) :
    convolution a b ≠ 0 ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    constructor
    · by_contra ha
      have ha' : a = 0 := by omega
      subst a
      apply h
      funext i
      exact Fin.elim0 i
    · by_contra hb
      have hb' : b = 0 := by omega
      subst b
      apply h
      funext i j
      exact Fin.elim0 j
  · rintro ⟨ha, hb⟩
    exact convolution_nonzero ha hb

/-- Commuting the two inputs only casts the equal output dimensions. -/
theorem convolution_comm (a b : ℕ) (i : Fin a) (j : Fin b)
    (k : Fin (a + b - 1)) :
    convolution a b i j k =
      convolution b a j i (Fin.cast (by omega) k) := by
  simp only [convolution, Fin.val_cast, Nat.add_comm]

/-- The boundary tensor `C(1,b)` has the coefficient matrix of a dot product. -/
theorem convolution_one_left (b : ℕ) (i : Fin 1) (j : Fin b)
    (k : Fin (1 + b - 1)) :
    convolution 1 b i j k = if j.val = k.val then 1 else 0 := by
  simp [convolution]

/-- The other boundary tensor has the same coordinate identity. -/
theorem convolution_one_right (a : ℕ) (i : Fin a) (j : Fin 1)
    (k : Fin (a + 1 - 1)) :
    convolution a 1 i j k = if i.val = k.val then 1 else 0 := by
  simp [convolution]

/-- Relabel the output of `C(1,b)` by its actual dimension `b`. -/
def convolutionOneOutputEquiv (b : ℕ) : Fin b ≃ Fin (1 + b - 1) :=
  finCongr (by omega)

/-- Relabel the single input coordinate of `C(1,b)` by `Unit`. -/
def convolutionOneInputEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _i := Subsingleton.elim _ _

/-- `C(1,b)` is the dot-product tensor with the singleton on the first leg. -/
theorem convolution_one_left_dotPairing (b : ℕ) :
    Tensor.pullback convolutionOneInputEquiv (Equiv.refl (Fin b))
      (convolutionOneOutputEquiv b) (convolution 1 b) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin b))) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff]

/-- Relabel the output of `C(a,1)` by its actual dimension `a`. -/
def convolutionRightOneOutputEquiv (a : ℕ) : Fin a ≃ Fin (a + 1 - 1) :=
  finCongr (by omega)

/-- `C(a,1)` is the dot-product tensor with the singleton on the second leg. -/
theorem convolution_one_right_dotPairing (a : ℕ) :
    Tensor.pullback (Equiv.refl (Fin a)) convolutionOneInputEquiv
      (convolutionRightOneOutputEquiv a) (convolution a 1) =
      Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin a)) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionRightOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff, eq_comm]

/-- Contracting the coefficient tensor computes ordinary finite convolution. -/
theorem contract_convolution {a b : ℕ} (x : Fin a → ℂ) (y : Fin b → ℂ)
    (k : Fin (a + b - 1)) :
    Tensor.contract (convolution a b) x y k =
      ∑ i : Fin a, ∑ j : Fin b,
        if i.val + j.val = k.val then x i * y j else 0 := by
  simp [Tensor.contract, convolution, ite_mul]

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule067
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Symmetrization -/
section FlattenModule068




namespace OAI

/-!
# The symmetrized tensor-character product

The sixfold product is defined on arbitrary finite, possibly different, leg
spaces. Its symmetry follows by permuting the factors and requires no symmetry
of the character itself.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character)
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- The product of character values in the six orders of possibly different legs. -/
def sixfoldProduct (T : Tensor ℂ X Y Z) : ℝ :=
  χ.value T *
    χ.value (fun y z x => T x y z) *
    χ.value (fun z x y => T x y z) *
    χ.value (fun x z y => T x y z) *
    χ.value (fun z y x => T x y z) *
    χ.value (fun y x z => T x y z)

/-- Cycling the legs permutes the six factors. -/
theorem sixfoldProduct_cyclic (T : Tensor ℂ X Y Z) :
    χ.sixfoldProduct (fun y z x => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- Exchanging the first two legs permutes the six factors. -/
theorem sixfoldProduct_swap12 (T : Tensor ℂ X Y Z) :
    χ.sixfoldProduct (fun y x z => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- The leg exchange used by the middle convolution branch preserves the product. -/
theorem sixfoldProduct_swap23 (T : Tensor ℂ X Y Z) :
    χ.sixfoldProduct (fun x z y => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- Changing coordinates separately on the legs preserves the sixfold product. -/
theorem sixfoldProduct_reindex (T : Tensor ℂ X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.sixfoldProduct (Tensor.pullback ex ey ez T) = χ.sixfoldProduct T := by
  unfold sixfoldProduct
  rw [χ.value_reindex T ex ey ez]
  have h1 := χ.value_reindex (fun y z x => T x y z) ey ez ex
  have h2 := χ.value_reindex (fun z x y => T x y z) ez ex ey
  have h3 := χ.value_reindex (fun x z y => T x y z) ex ez ey
  have h4 := χ.value_reindex (fun z y x => T x y z) ez ey ex
  have h5 := χ.value_reindex (fun y x z => T x y z) ey ex ez
  change χ.value (fun y z x => T (ex x) (ey y) (ez z)) =
    χ.value (fun y z x => T x y z) at h1
  change χ.value (fun z x y => T (ex x) (ey y) (ez z)) =
    χ.value (fun z x y => T x y z) at h2
  change χ.value (fun x z y => T (ex x) (ey y) (ez z)) =
    χ.value (fun x z y => T x y z) at h3
  change χ.value (fun z y x => T (ex x) (ey y) (ez z)) =
    χ.value (fun z y x => T x y z) at h4
  change χ.value (fun y x z => T (ex x) (ey y) (ez z)) =
    χ.value (fun y x z => T x y z) at h5
  simp only [Tensor.pullback]
  rw [h1, h2, h3, h4, h5]

/-- Commuting convolution inputs preserves the sixfold character product. -/
theorem sixfoldProduct_convolution_comm (a b : ℕ) :
    χ.sixfoldProduct (convolution a b) = χ.sixfoldProduct (convolution b a) := by
  let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
  have heq : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
      (convolution b a) = fun j i k => convolution a b i j k := by
    funext j i k
    exact (convolution_comm a b i j k).symm
  have h := χ.sixfoldProduct_reindex (convolution b a)
    (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
  rw [heq, χ.sixfoldProduct_swap12] at h
  exact h

/-- The Section 5 symmetrized value with mean singleton-leg exponent `t`. -/
def symmetrizedProfile (t : ℝ) (T : Tensor ℂ X Y Z) : ℝ :=
  χ.sixfoldProduct T ^ (1 / (6 * t))

theorem symmetrizedProfile_cyclic (t : ℝ) (T : Tensor ℂ X Y Z) :
    χ.symmetrizedProfile t (fun y z x => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_cyclic T)

theorem symmetrizedProfile_swap12 (t : ℝ) (T : Tensor ℂ X Y Z) :
    χ.symmetrizedProfile t (fun y x z => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_swap12 T)

theorem symmetrizedProfile_swap23 (t : ℝ) (T : Tensor ℂ X Y Z) :
    χ.symmetrizedProfile t (fun x z y => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_swap23 T)

theorem symmetrizedProfile_reindex (t : ℝ) (T : Tensor ℂ X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.symmetrizedProfile t (Tensor.pullback ex ey ez T) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_reindex T ex ey ez)

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule068
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Symmetrization -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Rank -/
section FlattenModule069


namespace OAI

/-!
# Polynomial convolution by evaluation and interpolation

Evaluating the two input polynomials at `a + b - 1` distinct complex points,
then interpolating their product, expresses the convolution tensor as a sum
of `a + b - 1` rank-one tensors. This is the polynomial multiplication rank
upper bound used in Section 5.
-/

open scoped BigOperators
open Polynomial

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Recover each monomial coefficient from evaluations at distinct nodes. -/
lemma monomial_coeff_eq_sum_interpolation {n m : ℕ} (hm : m < n)
    (v : Fin n → ℂ) (hv : Function.Injective v) (k : ℕ) :
    (if m = k then (1 : ℂ) else 0) =
      ∑ r : Fin n, v r ^ m * (Lagrange.basis Finset.univ v r).coeff k := by
  have hdeg : (X ^ m : ℂ[X]).degree < (Finset.univ : Finset (Fin n)).card := by
    simpa using hm
  have hpoly := Lagrange.eq_interpolate (f := (X ^ m : ℂ[X])) hv.injOn hdeg
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff k) hpoly
  simpa only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow, eq_comm] using hcoeff

/-- Evaluation at distinct nodes and Lagrange interpolation give an explicit
rank-one decomposition of polynomial convolution. -/
theorem convolution_eq_sum_rankOne {a b : ℕ}
    (v : Fin (a + b - 1) → ℂ) (hv : Function.Injective v) :
    convolution a b = fun i j k => ∑ r : Fin (a + b - 1),
      Tensor.rankOne (fun i : Fin a => v r ^ i.val)
        (fun j : Fin b => v r ^ j.val)
        (fun k : Fin (a + b - 1) => (Lagrange.basis Finset.univ v r).coeff k.val)
        i j k := by
  funext i j k
  have hij : i.val + j.val < a + b - 1 := (convolutionOutput i j).isLt
  simpa only [convolution_apply, Tensor.rankOne, pow_add] using
    monomial_coeff_eq_sum_interpolation hij v hv k.val

/-- The convolution tensor `C(a,b)` has rank at most `a + b - 1` over `ℂ`. -/
theorem convolution_rankAtMost (a b : ℕ) :
    Tensor.RankAtMost (convolution a b) (a + b - 1) := by
  let v : Fin (a + b - 1) → ℂ := fun r => r.val
  have hv : Function.Injective v := by
    intro i j h
    apply Fin.ext
    change (i.val : ℂ) = j.val at h
    exact_mod_cast h
  rw [convolution_eq_sum_rankOne v hv]
  simpa using Tensor.rankAtMost_sum_rankOne
    (fun r (i : Fin a) => v r ^ i.val)
    (fun r (j : Fin b) => v r ^ j.val)
    (fun r (k : Fin (a + b - 1)) => (Lagrange.basis Finset.univ v r).coeff k.val)

/-- The interpolation algorithm also bounds border rank. -/
theorem convolution_borderRankAtMost (a b : ℕ) :
    Tensor.BorderRankAtMost (convolution a b) (a + b - 1) :=
  (convolution_rankAtMost a b).borderRankAtMost

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule069
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Rank -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.MultiplicativePower -/
section FlattenModule070



namespace OAI

/-!
# Monotone multiplicative functions on the positive natural numbers

The scalar classification used in Section 3.1: positivity, multiplicativity,
and monotonicity force a function on positive natural numbers to be a real
power. No property of the function at zero is required.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Multiplicativity and positivity determine the value at one. -/
theorem positiveMultiplicative_one
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) :
    f 1 = 1 := by
  have hm := hmul 1 1 (by omega) (by omega)
  have hp := hpos 1 (by omega)
  norm_num at hm
  nlinarith

/-- A positive multiplicative function preserves natural powers. -/
theorem positiveMultiplicative_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : f (n ^ k) = f n ^ k := by
  induction k with
  | zero => simpa using positiveMultiplicative_one hpos hmul
  | succ k ih =>
      rw [pow_succ, hmul (n ^ k) n (pow_pos hn k) hn, ih, pow_succ]

/-- Monotonicity transfers comparisons of natural powers to the values. -/
theorem positiveMultiplicative_pow_le_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) : f m ^ j ≤ f n ^ k := by
  rw [← positiveMultiplicative_pow hpos hmul hm,
    ← positiveMultiplicative_pow hpos hmul hn]
  exact hmono (pow_pos hm j) (pow_pos hn k) h

/-- The same comparison after taking logarithms. -/
theorem positiveMultiplicative_log_pow_le
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) :
    (j : ℝ) * Real.log (f m) ≤ (k : ℝ) * Real.log (f n) := by
  have hv := positiveMultiplicative_pow_le_pow hpos hmul hmono hm hn h
  simpa only [Real.log_pow] using
    Real.log_le_log (pow_pos (hpos m hm) j) hv

/-- Bounds from neighboring powers of two have a fixed logarithmic error,
independent of the exponent `k`. -/
theorem positiveMultiplicative_log_error_bounds
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k : ℝ) * (Real.log (f n) * Real.log 2 -
      Real.log (n : ℝ) * Real.log (f 2)) ≤ Real.log (f 2) * Real.log 2 ∧
    (k : ℝ) * (Real.log (n : ℝ) * Real.log (f 2) -
      Real.log (f n) * Real.log 2) ≤ Real.log (f 2) * Real.log 2 := by
  have hf2 : 0 ≤ Real.log (f 2) := by
    apply Real.log_nonneg
    have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rwa [positiveMultiplicative_one hpos hmul] at hm
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨m, hlow, hupp⟩ :=
    exists_nat_pow_near (show 1 ≤ n ^ k from Nat.one_le_iff_ne_zero.mpr (by positivity))
      (show 1 < (2 : ℕ) by omega)
  have hflow := positiveMultiplicative_log_pow_le hpos hmul hmono
    (show 0 < (2 : ℕ) by omega) hn hlow
  have hfupp := positiveMultiplicative_log_pow_le hpos hmul hmono hn
    (show 0 < (2 : ℕ) by omega) hupp.le
  have hlow' : (2 : ℝ) ^ m ≤ (n : ℝ) ^ k := by exact_mod_cast hlow
  have hupp' : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hupp.le
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) m) hlow'
  have hnupp := Real.log_le_log (pow_pos hnp k) hupp'
  simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at hflow hfupp hnlow hnupp
  have h₁ := mul_le_mul_of_nonneg_right hfupp hlog2
  have h₂ := mul_le_mul_of_nonneg_right hnlow hf2
  have h₃ := mul_le_mul_of_nonneg_right hnupp hf2
  have h₄ := mul_le_mul_of_nonneg_right hflow hlog2
  constructor <;> nlinarith

/-- If every natural multiple of both differences has a common upper bound,
the two real numbers coincide. -/
theorem eq_of_nat_mul_sub_bounded {x y C : ℝ}
    (hxy : ∀ k : ℕ, (k : ℝ) * (x - y) ≤ C)
    (hyx : ∀ k : ℕ, (k : ℝ) * (y - x) ≤ C) : x = y := by
  apply le_antisymm
  · by_contra h
    have hd : 0 < x - y := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (x - y))
    have hk' : C < (k : ℝ) * (x - y) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hxy k)) hk'
  · by_contra h
    have hd : 0 < y - x := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (y - x))
    have hk' : C < (k : ℝ) * (y - x) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hyx k)) hk'

/-- The logarithmic exponent is the same at every positive natural number. -/
theorem positiveMultiplicative_log_eq
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    Real.log (f n) = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by
  have heq : Real.log (f n) * Real.log 2 =
      Real.log (n : ℝ) * Real.log (f 2) :=
    eq_of_nat_mul_sub_bounded
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).1)
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).2)
  calc
    Real.log (f n) = (Real.log (n : ℝ) * Real.log (f 2)) / Real.log 2 :=
      (eq_div_iff (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne').2 heq
    _ = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by ring

/-- The explicit exponent in the classification of positive monotone
multiplicative functions on the positive natural numbers. -/
theorem positiveMultiplicative_eq_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnp, ← positiveMultiplicative_log_eq hpos hmul hmono hn,
    Real.exp_log (hpos n hn)]

/-- Every positive monotone multiplicative function on the positive natural
numbers is a nonnegative real power, as used in Section 3.1. -/
theorem positiveMultiplicative_is_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0)) :
    ∃ p : ℝ, 0 ≤ p ∧ ∀ n : ℕ, 0 < n → f n = (n : ℝ) ^ p := by
  refine ⟨Real.log (f 2) / Real.log 2, ?_, fun n hn =>
    positiveMultiplicative_eq_rpow hpos hmul hmono hn⟩
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply Real.log_nonneg
  have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
  rwa [positiveMultiplicative_one hpos hmul] at hm

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule070
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.MultiplicativePower -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexPairingMatrixTensor -/
section FlattenModule071


namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K : Type*} [CommSemiring K]

def dotPairingMatrixX (U : Type*) : (Unit × U) ≃ U where
  toFun x := x.2
  invFun x := ((), x)
  left_inv := by rintro ⟨⟨⟩, x⟩; rfl
  right_inv x := rfl

def dotPairingMatrixY (U : Type*) : (U × Unit) ≃ U where
  toFun y := y.1
  invFun y := (y, ())
  left_inv := by rintro ⟨y, ⟨⟩⟩; rfl
  right_inv y := rfl

def dotPairingMatrixZ : (Unit × Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := ((), ())
  left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv := by rintro ⟨⟩; rfl

theorem dotPairing_matrixCoefficients (U : Type*) [DecidableEq U] :
    pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
      (dotPairing (K := K) U) = matrixCoefficients Unit U Unit := by
  funext x y z
  change (if x.2 = y.1 then (1 : K) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) ↔ x.2 = y.1 :=
    ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  by_cases hxy : x.2 = y.1
  · calc
      (if x.2 = y.1 then (1 : K) else 0) = 1 := ite_eq_left hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (ite_eq_left (hguard.mpr hxy)).symm
  · have hfull : ¬ (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
      fun h => hxy (hguard.mp h)
    calc
      (if x.2 = y.1 then (1 : K) else 0) = 0 := ite_eq_right hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (ite_eq_right hfull).symm

theorem matrixCoefficients_rank_of_dotPairing {U : Type*} [DecidableEq U] {r : ℕ}
    (h : RankAtMost (dotPairing (K := K) U) r) :
    RankAtMost (matrixCoefficients (K := K) Unit U Unit) r := by
  have h' := h.pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
  rw [dotPairing_matrixCoefficients] at h'
  exact h'

theorem matrixCoefficients_borderRank_of_dotPairing
    {U : Type*} [Fintype U] [DecidableEq U] {r : ℕ}
    (h : BorderRankAtMost (dotPairing (K := ℂ) U) r) :
    BorderRankAtMost (matrixCoefficients (K := ℂ) Unit U Unit) r := by
  classical
  rw [← dotPairing_matrixCoefficients, pullback_eq_restrict]
  exact h.restrict _ _ _

def pairingTriple (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K ((B × A) × Unit) ((B × Unit) × C) ((Unit × A) × C) :=
  product (product (dotPairing B) (cyclic (dotPairing A)))
    (cyclic (cyclic (dotPairing C)))

def pairingTripleMatrixX (A B : Type*) : (A × B) ≃ ((B × A) × Unit) where
  toFun x := ((x.2, x.1), ())
  invFun x := (x.1.2, x.1.1)
  left_inv x := rfl
  right_inv := by rintro ⟨⟨b, a⟩, ⟨⟩⟩; rfl

def pairingTripleMatrixY (B C : Type*) : (B × C) ≃ ((B × Unit) × C) where
  toFun y := ((y.1, ()), y.2)
  invFun y := (y.1.1, y.2)
  left_inv y := rfl
  right_inv := by rintro ⟨⟨b, ⟨⟩⟩, c⟩; rfl

def pairingTripleMatrixZ (C A : Type*) : (C × A) ≃ ((Unit × A) × C) where
  toFun z := (((), z.2), z.1)
  invFun z := (z.2, z.1.2)
  left_inv z := rfl
  right_inv := by rintro ⟨⟨⟨⟩, a⟩, c⟩; rfl

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem pairingTriple_matrixCoefficients :
    pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
      (pairingTripleMatrixZ C A) (pairingTriple (K := K) A B C) =
      matrixCoefficients A B C := by
  funext x y z
  change ((if x.2 = y.1 then (1 : K) else 0) *
    (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : ((x.2 = y.1 ∧ z.2 = x.1) ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem matrixCoefficients_rank_of_pairingTriple {r : ℕ}
    (h : RankAtMost (pairingTriple (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) A B C) r := by
  have h' := h.pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  rw [pairingTriple_matrixCoefficients] at h'
  exact h'

theorem matrixCoefficients_borderRank_of_pairingTriple
    [Fintype A] [Fintype B] [Fintype C] {r : ℕ}
    (h : BorderRankAtMost (pairingTriple (K := ℂ) A B C) r) :
    BorderRankAtMost (matrixCoefficients (K := ℂ) A B C) r := by
  classical
  rw [← pairingTriple_matrixCoefficients, pullback_eq_restrict]
  exact h.restrict _ _ _

theorem matrixCoefficients_directSum_rank_of_pairingTriple
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => pairingTriple (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r := by
  have h' := h.directSum_pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  simpa only [pairingTriple_matrixCoefficients] using h'

theorem matrixCoefficients_directSum_borderRank_of_pairingTriple
    [Fintype A] [Fintype B] [Fintype C]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (h : BorderRankAtMost (directSum (fun _ : ι => pairingTriple (K := ℂ) A B C)) r) :
    BorderRankAtMost (directSum (fun _ : ι => matrixCoefficients (K := ℂ) A B C)) r := by
  classical
  have heq := directSum_pullback (fun _ : ι => pairingTriple (K := ℂ) A B C)
    (pairingTripleMatrixX A B) (pairingTripleMatrixY B C) (pairingTripleMatrixZ C A)
  simp only [pairingTriple_matrixCoefficients] at heq
  rw [← heq, pullback_eq_restrict]
  exact h.restrict _ _ _

end Tensor
end MatrixMultiplication.Foundation

end OAI

end FlattenModule071
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexPairingMatrixTensor -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot -/
section FlattenModule072



namespace OAI

/-!
# Dot-product exponents of tensor characters

The power laws here follow from restriction monotonicity and tensor products.
They are not additional assumptions on a character. The three exponents refer
to the leg on which the corresponding dot product has dimension one.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character)

theorem value_pos {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} (hT : T ≠ 0) : 0 < χ.value T :=
  lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)

/-- Precomposing a character with a cyclic permutation gives a character. -/
def cyclicCharacter : Character where
  value T := χ.value (Tensor.cyclic T)
  nonneg T := χ.nonneg (Tensor.cyclic T)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    rw [Tensor.cyclic_directSum, χ.map_directSum]
  map_product T S := χ.map_product (Tensor.cyclic T) (Tensor.cyclic S)
  monotone T A B C := by
    have heq : Tensor.cyclic (Tensor.restrict A B C T) =
        Tensor.restrict B C A (Tensor.cyclic T) := by
      funext y z x
      simp only [Tensor.cyclic, Tensor.restrict]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    exact χ.monotone (Tensor.cyclic T) B C A

@[simp] theorem cyclicCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℂ X Y Z) :
    χ.cyclicCharacter.value T = χ.value (Tensor.cyclic T) := rfl

private theorem dotPairing_ne_zero {m : ℕ} (hm : 0 < m) :
    Tensor.dotPairing (K := ℂ) (Fin m) ≠ 0 := by
  intro h
  have hv := congrFun (congrFun (congrFun h ⟨0, hm⟩) ⟨0, hm⟩) ()
  simp [Tensor.dotPairing] at hv

private theorem dotPairing_rank (m : ℕ) :
    Tensor.RankAtMost (Tensor.dotPairing (K := ℂ) (Fin m)) m := by
  let a : Fin m → Fin m → ℂ := fun i j => if i = j then 1 else 0
  have heq : Tensor.dotPairing (K := ℂ) (Fin m) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (a i) (fun _ : Unit => 1) x y z := by
    funext x y z
    simp [Tensor.dotPairing, Tensor.rankOne, a, mul_ite, eq_comm]
  rw [heq]
  simpa using Tensor.rankAtMost_sum_rankOne a a (fun (_ : Fin m) (_ : Unit) => (1 : ℂ))

theorem value_dotPairing_pos {m : ℕ} (hm : 0 < m) :
    0 < χ.value (Tensor.dotPairing (K := ℂ) (Fin m)) :=
  χ.value_pos (dotPairing_ne_zero hm)

theorem value_dotPairing_le (m : ℕ) :
    χ.value (Tensor.dotPairing (K := ℂ) (Fin m)) ≤ m :=
  χ.value_le_rank (dotPairing_rank m)

theorem value_dotPairing_mono {m n : ℕ} (hmn : m ≤ n) :
    χ.value (Tensor.dotPairing (K := ℂ) (Fin m)) ≤
      χ.value (Tensor.dotPairing (K := ℂ) (Fin n)) := by
  have heq : Tensor.pullback (Fin.castLE hmn) (Fin.castLE hmn) id
      (Tensor.dotPairing (K := ℂ) (Fin n)) = Tensor.dotPairing (K := ℂ) (Fin m) := by
    funext x y z
    simp [Tensor.pullback, Tensor.dotPairing]
  rw [← heq]
  exact χ.value_pullback_le _ _ _ _

theorem value_dotPairing_mul (m n : ℕ) :
    χ.value (Tensor.dotPairing (K := ℂ) (Fin (m * n))) =
      χ.value (Tensor.dotPairing (K := ℂ) (Fin m)) *
        χ.value (Tensor.dotPairing (K := ℂ) (Fin n)) := by
  have heq : Tensor.pullback finProdFinEquiv.symm finProdFinEquiv.symm
      (Equiv.prodUnique Unit Unit).symm
      (Tensor.product (Tensor.dotPairing (K := ℂ) (Fin m))
        (Tensor.dotPairing (K := ℂ) (Fin n))) =
      Tensor.dotPairing (K := ℂ) (Fin (m * n)) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing,
      ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  rw [← heq, χ.value_reindex, χ.map_product]

/-- The exponent on dot products whose third leg has dimension one. -/
def pZ : ℝ :=
  Real.log (χ.value (Tensor.dotPairing (K := ℂ) (Fin 2))) / Real.log 2

/-- The exponent on dot products whose second leg has dimension one. -/
def pY : ℝ := χ.cyclicCharacter.pZ

/-- The exponent on dot products whose first leg has dimension one. -/
def pX : ℝ := χ.cyclicCharacter.cyclicCharacter.pZ

theorem pZ_nonneg : 0 ≤ χ.pZ := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  exact Real.log_nonneg (χ.one_le_value (dotPairing_ne_zero (by norm_num)))

theorem pZ_le_one : χ.pZ ≤ 1 := by
  apply (div_le_one (Real.log_pos (by norm_num))).2
  exact Real.log_le_log (χ.value_dotPairing_pos (by norm_num)) (χ.value_dotPairing_le 2)

theorem pY_nonneg : 0 ≤ χ.pY := χ.cyclicCharacter.pZ_nonneg
theorem pY_le_one : χ.pY ≤ 1 := χ.cyclicCharacter.pZ_le_one
theorem pX_nonneg : 0 ≤ χ.pX := χ.cyclicCharacter.cyclicCharacter.pZ_nonneg
theorem pX_le_one : χ.pX ≤ 1 := χ.cyclicCharacter.cyclicCharacter.pZ_le_one

theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (K := ℂ) (Fin m)) = (m : ℝ) ^ χ.pZ := by
  apply positiveMultiplicative_eq_rpow
    (f := fun m => χ.value (Tensor.dotPairing (K := ℂ) (Fin m)))
    (fun n hn => χ.value_dotPairing_pos hn)
    (fun m n _ _ => χ.value_dotPairing_mul m n)
    (fun _ _ _ _ hmn => χ.value_dotPairing_mono hmn) hm

theorem value_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m))) =
      (m : ℝ) ^ χ.pY :=
  χ.cyclicCharacter.value_dotPairing hm

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm

/-- Exact factorization through the three oriented dot products. -/
theorem value_matrixCoefficients {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    χ.value (Tensor.matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)) =
      (b : ℝ) ^ χ.pZ * (a : ℝ) ^ χ.pY * (c : ℝ) ^ χ.pX := by
  rw [← Tensor.pairingTriple_matrixCoefficients, χ.value_reindex]
  simp only [Tensor.pairingTriple, χ.map_product, χ.value_dotPairing hb,
    χ.value_cyclic_dotPairing ha, χ.value_cyclic_cyclic_dotPairing hc]

/-- The character of square matrix multiplication has exponent `pX + pY + pZ`. -/
theorem value_matrixCoefficients_square {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matrixCoefficients (K := ℂ) (Fin m) (Fin m) (Fin m)) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  rw [χ.value_matrixCoefficients hm hm hm]
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [Real.rpow_add hm', Real.rpow_add hm']
  ring

/-- The same power law in the matrix-tensor notation used for exact rank. -/
theorem value_matrixMultiplication {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.matrixMultiplication m m m) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  simpa only [Tensor.matrixMultiplication_eq_matrixCoefficients] using
    χ.value_matrixCoefficients_square hm

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end FlattenModule072
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SixfoldProductBounds -/
section FlattenModule073



namespace OAI

/-!
# Algebra and bounds for the sixfold character product

The product over all six leg orders is multiplicative and nonnegative. A
nonzero tensor has product at least one, and every rank decomposition bounds
the product by the sixth power of its size.
-/

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character)
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

/-- Taking the product over all six leg orders preserves tensor multiplication. -/
theorem sixfoldProduct_product (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    χ.sixfoldProduct (Tensor.product T S) = χ.sixfoldProduct T * χ.sixfoldProduct S := by
  unfold sixfoldProduct
  change χ.value (Tensor.product T S) *
      χ.value (Tensor.product (fun y z x => T x y z) (fun v w u => S u v w)) *
      χ.value (Tensor.product (fun z x y => T x y z) (fun w u v => S u v w)) *
      χ.value (Tensor.product (fun x z y => T x y z) (fun u w v => S u v w)) *
      χ.value (Tensor.product (fun z y x => T x y z) (fun w v u => S u v w)) *
      χ.value (Tensor.product (fun y x z => T x y z) (fun v u w => S u v w)) = _
  simp only [χ.map_product]
  ring

/-- All six factors of the symmetrized product are nonnegative. -/
theorem sixfoldProduct_nonneg (T : Tensor ℂ X Y Z) : 0 ≤ χ.sixfoldProduct T := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (χ.nonneg T) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)) (χ.nonneg _)

/-- Every nonzero tensor has symmetrized character product at least one. -/
theorem one_le_sixfoldProduct {T : Tensor ℂ X Y Z} (hT : T ≠ 0) :
    1 ≤ χ.sixfoldProduct T := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hT
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hy
  change T x y z ≠ 0 at hz
  have h0 := χ.one_le_value hT
  have h1 : 1 ≤ χ.value (fun y z x => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S y z x) h))
  have h2 : 1 ≤ χ.value (fun z x y => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S z x y) h))
  have h3 : 1 ≤ χ.value (fun x z y => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S x z y) h))
  have h4 : 1 ≤ χ.value (fun z y x => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S z y x) h))
  have h5 : 1 ≤ χ.value (fun y x z => T x y z) := χ.one_le_value (by
    intro h
    exact hz (congrArg (fun S => S y x z) h))
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2) h3) h4) h5

/-- In particular, the sixfold product of a nonzero tensor is positive. -/
theorem sixfoldProduct_pos {T : Tensor ℂ X Y Z} (hT : T ≠ 0) :
    0 < χ.sixfoldProduct T :=
  zero_lt_one.trans_le (χ.one_le_sixfoldProduct hT)

private theorem rankAtMost_swap12 {K X Y Z : Type*} [CommSemiring K]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    Tensor.RankAtMost (fun y x z => T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, a, c, ?_⟩
  funext y x z
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [Tensor.rankOne]
  ring

/-- A rank decomposition bounds each of the six character factors. -/
theorem sixfoldProduct_le_rank {T : Tensor ℂ X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) : χ.sixfoldProduct T ≤ (r : ℝ) ^ 6 := by
  have h0 := χ.value_le_rank h
  have h1 := χ.value_le_rank h.cyclic
  have h2 := χ.value_le_rank h.cyclic.cyclic
  have h5 := χ.value_le_rank (rankAtMost_swap12 h)
  have h3 := χ.value_le_rank (rankAtMost_swap12 h).cyclic
  have h4 := χ.value_le_rank (rankAtMost_swap12 h).cyclic.cyclic
  unfold sixfoldProduct
  calc
    _ ≤ (r : ℝ) * r * r * r * r * r := by
      gcongr <;> first
        | exact χ.nonneg _
        | exact h0
        | exact h1
        | exact h2
        | exact h3
        | exact h4
    _ = _ := by ring

end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule073
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SixfoldProductBounds -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.NormalizedProfile -/
section FlattenModule074


namespace OAI

/-!
# Positivity and rank bounds for the normalized profile

The normalization exponent is positive when the mean singleton-leg exponent
is positive. Under this hypothesis, passing to the profile preserves order,
and a rank bound `r` becomes the bound `r ^ (1 / t)`.
-/

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character)
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

theorem symmetrizedProfile_nonneg (t : ℝ) (T : Tensor ℂ X Y Z) :
    0 ≤ χ.symmetrizedProfile t T :=
  Real.rpow_nonneg (χ.sixfoldProduct_nonneg T) _

theorem symmetrizedProfile_pos (t : ℝ) {T : Tensor ℂ X Y Z} (hT : T ≠ 0) :
    0 < χ.symmetrizedProfile t T :=
  Real.rpow_pos_of_pos (χ.sixfoldProduct_pos hT) _

theorem one_le_symmetrizedProfile {t : ℝ} (ht : 0 < t)
    {T : Tensor ℂ X Y Z} (hT : T ≠ 0) : 1 ≤ χ.symmetrizedProfile t T := by
  exact Real.one_le_rpow (χ.one_le_sixfoldProduct hT) (by positivity)

/-- Tensor products become products of normalized profile values. -/
theorem symmetrizedProfile_product (t : ℝ) (T : Tensor ℂ X Y Z)
    (S : Tensor ℂ U V W) :
    χ.symmetrizedProfile t (Tensor.product T S) =
      χ.symmetrizedProfile t T * χ.symmetrizedProfile t S := by
  simp only [symmetrizedProfile, χ.sixfoldProduct_product]
  exact Real.mul_rpow (χ.sixfoldProduct_nonneg T) (χ.sixfoldProduct_nonneg S)

/-- Positive normalization preserves the order of the underlying sixfold products. -/
theorem symmetrizedProfile_le_iff {t : ℝ} (ht : 0 < t)
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W) :
    χ.symmetrizedProfile t T ≤ χ.symmetrizedProfile t S ↔
      χ.sixfoldProduct T ≤ χ.sixfoldProduct S := by
  exact Real.rpow_le_rpow_iff (χ.sixfoldProduct_nonneg T)
    (χ.sixfoldProduct_nonneg S) (by positivity)

/-- The symmetrized profile has the rank bound used in Section 5. -/
theorem symmetrizedProfile_le_rank {t : ℝ} (ht : 0 < t)
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.symmetrizedProfile t T ≤ (r : ℝ) ^ (1 / t) := by
  calc
    χ.symmetrizedProfile t T ≤ ((r : ℝ) ^ 6) ^ (1 / (6 * t)) :=
      Real.rpow_le_rpow (χ.sixfoldProduct_nonneg T) (χ.sixfoldProduct_le_rank h)
        (by positivity)
    _ = (r : ℝ) ^ (1 / t) := by
      rw [← Real.rpow_natCast (r : ℝ) 6, ← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
      norm_num

/-- A factor `c ^ (6*t)` in the sixfold product becomes `c` in the profile. -/
theorem mul_symmetrizedProfile_le_of_le {t c : ℝ} (ht : 0 < t) (hc : 0 ≤ c)
    (T : Tensor ℂ X Y Z) (S : Tensor ℂ U V W)
    (h : c ^ (6 * t) * χ.sixfoldProduct T ≤ χ.sixfoldProduct S) :
    c * χ.symmetrizedProfile t T ≤ χ.symmetrizedProfile t S := by
  have hp := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg hc _) (χ.sixfoldProduct_nonneg T)) h
    (show 0 ≤ 1 / (6 * t) by positivity)
  rw [Real.mul_rpow (Real.rpow_nonneg hc _) (χ.sixfoldProduct_nonneg T),
    one_div, Real.rpow_rpow_inv hc (ne_of_gt (mul_pos (by norm_num) ht))] at hp
  simpa only [symmetrizedProfile, one_div] using hp

end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule074
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.NormalizedProfile -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Symmetry -/
section FlattenModule075




namespace OAI

/-!
# Character identities for polynomial convolution

The boundary convolution tensors are dot products. In the sixfold character
product, each possible singleton leg appears exactly twice. Consequently the
normalization by the average dot-product exponent gives the boundary values
of the polynomial profile from Section 5.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character)

/-- A symmetric dot product occurs twice in each of its three leg positions. -/
theorem sixfoldProduct_dotPairing (n : ℕ) :
    χ.sixfoldProduct (Tensor.dotPairing (K := ℂ) (Fin n)) =
      (χ.value (Tensor.dotPairing (K := ℂ) (Fin n)) *
        χ.value (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin n))) *
        χ.value (Tensor.cyclic (Tensor.cyclic
          (Tensor.dotPairing (K := ℂ) (Fin n))))) ^ 2 := by
  let D := Tensor.dotPairing (K := ℂ) (Fin n)
  have h3 : (fun (i : Fin n) (_ : Unit) (j : Fin n) => D i j ()) =
      Tensor.cyclic D := by
    funext i u j
    simp [D, Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have h4 : (fun (_ : Unit) (j i : Fin n) => D i j ()) =
      Tensor.cyclic (Tensor.cyclic D) := by
    funext u j i
    simp [D, Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have h5 : (fun (j i : Fin n) (_ : Unit) => D i j ()) = D := by
    funext j i u
    simp [D, Tensor.dotPairing, eq_comm]
  change χ.sixfoldProduct D = _
  unfold sixfoldProduct
  change χ.value D * χ.value (Tensor.cyclic D) *
      χ.value (Tensor.cyclic (Tensor.cyclic D)) *
      χ.value (fun (i : Fin n) (_ : Unit) (j : Fin n) => D i j ()) *
      χ.value (fun (_ : Unit) (j i : Fin n) => D i j ()) *
      χ.value (fun (j i : Fin n) (_ : Unit) => D i j ()) = _
  rw [h3, h4, h5]
  ring

/-- The boundary `C(1,b)` has the sixfold product of a dot product. -/
theorem sixfoldProduct_convolution_one_left (b : ℕ) :
    χ.sixfoldProduct (convolution 1 b) =
      χ.sixfoldProduct (Tensor.dotPairing (K := ℂ) (Fin b)) := by
  have h := χ.sixfoldProduct_reindex (convolution 1 b)
    convolutionOneInputEquiv (Equiv.refl (Fin b)) (convolutionOneOutputEquiv b)
  rw [convolution_one_left_dotPairing] at h
  calc
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.cyclic
        (Tensor.dotPairing (K := ℂ) (Fin b)))) := h.symm
    _ = χ.sixfoldProduct (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin b))) :=
      χ.sixfoldProduct_cyclic _
    _ = _ := χ.sixfoldProduct_cyclic _

/-- The boundary `C(a,1)` has the same dot-product product. -/
theorem sixfoldProduct_convolution_one_right (a : ℕ) :
    χ.sixfoldProduct (convolution a 1) =
      χ.sixfoldProduct (Tensor.dotPairing (K := ℂ) (Fin a)) := by
  rw [χ.sixfoldProduct_convolution_comm, χ.sixfoldProduct_convolution_one_left]

/-- The mean of the character's three singleton-leg exponents. -/
def meanExponent : ℝ := (χ.pX + χ.pY + χ.pZ) / 3

theorem meanExponent_nonneg : 0 ≤ χ.meanExponent := by
  exact div_nonneg (add_nonneg (add_nonneg χ.pX_nonneg χ.pY_nonneg) χ.pZ_nonneg)
    (by norm_num)

theorem meanExponent_le_one : χ.meanExponent ≤ 1 := by
  unfold meanExponent
  have hx := χ.pX_le_one
  have hy := χ.pY_le_one
  have hz := χ.pZ_le_one
  linarith

/-- The three exponents occur twice in the sixfold boundary product. -/
theorem sixfoldProduct_dotPairing_eq_rpow {n : ℕ} (hn : 0 < n) :
    χ.sixfoldProduct (Tensor.dotPairing (K := ℂ) (Fin n)) =
      (n : ℝ) ^ (6 * χ.meanExponent) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [χ.sixfoldProduct_dotPairing, χ.value_dotPairing hn,
    χ.value_cyclic_dotPairing hn, χ.value_cyclic_cyclic_dotPairing hn,
    ← Real.rpow_add hn', ← Real.rpow_add hn']
  calc
    ((n : ℝ) ^ (χ.pZ + χ.pY + χ.pX)) ^ 2 =
        (n : ℝ) ^ ((χ.pZ + χ.pY + χ.pX) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast hn'.le _ 2).symm
    _ = _ := by congr 1; unfold meanExponent; ring

/-- The positive-size boundary product has its exact normalized power. -/
theorem sixfoldProduct_convolution_one_left_eq_rpow {b : ℕ} (hb : 0 < b) :
    χ.sixfoldProduct (convolution 1 b) = (b : ℝ) ^ (6 * χ.meanExponent) := by
  rw [χ.sixfoldProduct_convolution_one_left, χ.sixfoldProduct_dotPairing_eq_rpow hb]

/-- The polynomial profile `P(a,b)` normalized by the actual mean exponent. -/
def convolutionProfile (a b : ℕ) : ℝ :=
  χ.symmetrizedProfile χ.meanExponent (convolution a b)

/-- Swapping the two polynomial inputs preserves the normalized profile. -/
theorem convolutionProfile_comm (a b : ℕ) :
    χ.convolutionProfile a b = χ.convolutionProfile b a := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * χ.meanExponent)))
    (χ.sixfoldProduct_convolution_comm a b)

theorem convolutionProfile_nonneg (a b : ℕ) : 0 ≤ χ.convolutionProfile a b :=
  χ.symmetrizedProfile_nonneg _ _

/-- Nonzero polynomial multiplication gives a positive normalized profile. -/
theorem convolutionProfile_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.convolutionProfile a b :=
  χ.symmetrizedProfile_pos _ (convolution_nonzero ha hb)

/-- The evaluation/interpolation algorithm bounds the normalized profile. -/
theorem convolutionProfile_le {a b : ℕ} (ht : 0 < χ.meanExponent) :
    χ.convolutionProfile a b ≤ (a + b - 1 : ℕ) ^ (1 / χ.meanExponent) :=
  χ.symmetrizedProfile_le_rank ht (convolution_rankAtMost a b)

/-- The normalization gives the exact initial value `P(1,b) = b`. -/
theorem convolutionProfile_one_left {b : ℕ} (ht : 0 < χ.meanExponent) (hb : 0 < b) :
    χ.convolutionProfile 1 b = b := by
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  unfold convolutionProfile symmetrizedProfile
  rw [χ.sixfoldProduct_convolution_one_left_eq_rpow hb, ← Real.rpow_mul hb'.le]
  rw [show (6 * χ.meanExponent) * (1 / (6 * χ.meanExponent)) = 1 by
    field_simp [ne_of_gt ht]]
  exact Real.rpow_one _

/-- Input symmetry gives the other exact initial value `P(a,1) = a`. -/
theorem convolutionProfile_one_right {a : ℕ} (ht : 0 < χ.meanExponent) (ha : 0 < a) :
    χ.convolutionProfile a 1 = a := by
  rw [χ.convolutionProfile_comm, χ.convolutionProfile_one_left ht ha]

/-- Interpolation bounds an individual character on polynomial convolution. -/
theorem value_convolution_le (a b : ℕ) :
    χ.value (convolution a b) ≤ (a + b - 1 : ℕ) :=
  χ.value_le_rank (convolution_rankAtMost a b)

/-- Positive input sizes give a positive individual character value. -/
theorem value_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.value (convolution a b) :=
  zero_lt_one.trans_le (χ.one_le_value (convolution_nonzero ha hb))

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule075
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Symmetry -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Permutation -/
section FlattenModule076


namespace OAI

/-!
# The six permuted tensor characters

Precomposing a character with a leg permutation gives another character. The
six resulting values multiply to the symmetrized product, and each singleton
leg exponent occurs twice among their first-leg exponents.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character)

/-- The reflected character exchanges the second and third tensor legs. -/
def swap23Character : Character where
  value T := χ.value (fun x z y => T x y z)
  nonneg T := χ.nonneg (fun x z y => T x y z)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    have heq : (fun x z y => Tensor.directSum T x y z) =
        Tensor.directSum (fun i x z y => T i x y z) := by
      funext x z y
      simp only [Tensor.directSum, and_comm]
    change χ.value (fun x z y => Tensor.directSum T x y z) = _
    rw [heq, χ.map_directSum]
  map_product T S := χ.map_product (fun x z y => T x y z) (fun x z y => S x y z)
  monotone T A B C := by
    have heq : (fun x z y => Tensor.restrict A B C T x y z) =
        Tensor.restrict A C B (fun x z y => T x y z) := by
      funext x z y
      simp only [Tensor.restrict]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change χ.value (fun x z y => Tensor.restrict A B C T x y z) ≤ _
    rw [heq]
    exact χ.monotone (fun x z y => T x y z) A C B

@[simp] theorem swap23Character_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℂ X Y Z) :
    χ.swap23Character.value T = χ.value (fun x z y => T x y z) := rfl

/-- The three cyclic orders followed by their reflected orders. -/
def permutedCharacter (i : Fin 6) : Character :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.swap23Character.cyclicCharacter,
    χ.swap23Character.cyclicCharacter.cyclicCharacter] i

/-- The six permuted characters give exactly the sixfold product on any legs. -/
theorem prod_permutedCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℂ X Y Z) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value T) = χ.sixfoldProduct T := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change χ.value T * (χ.value (fun y z x => T x y z) *
      (χ.value (fun z x y => T x y z) * (χ.value (fun x z y => T x y z) *
      (χ.value (fun y x z => T x y z) * χ.value (fun z y x => T x y z))))) = _
  unfold sixfoldProduct
  ring

@[simp] theorem cyclicCharacter_pX : χ.cyclicCharacter.pX = χ.pZ := by
  rfl

@[simp] theorem cyclicCharacter_pY : χ.cyclicCharacter.pY = χ.pX := rfl

@[simp] theorem cyclicCharacter_pZ : χ.cyclicCharacter.pZ = χ.pY := rfl

@[simp] theorem swap23Character_pX : χ.swap23Character.pX = χ.pX := by
  unfold pX pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pY : χ.swap23Character.pY = χ.pZ := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pZ : χ.swap23Character.pZ = χ.pY := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

/-- Each singleton-leg exponent occurs twice among the first-leg exponents. -/
theorem sum_permutedCharacter_pX :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 2 * (χ.pX + χ.pY + χ.pZ) := by
  simp [permutedCharacter, Fin.sum_univ_succ]
  ring

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end FlattenModule076
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Permutation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy -/
section FlattenModule077







namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

def entropyTerm (p : ℝ) : ℝ := -p * Real.log p

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, entropyTerm (p a)

theorem finiteEntropy_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) : finiteEntropy (fun a => p (e a)) = finiteEntropy p :=
  e.sum_comp (fun b => entropyTerm (p b))

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

theorem finiteEntropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : A → B → ℝ) (hq : ∀ a, ∑ b, q a b = 1) :
    finiteEntropy (fun ab : A × B => p ab.1 * q ab.1 ab.2) =
      finiteEntropy p + ∑ a, p a * finiteEntropy (q a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B := by
  classical
  exact
    { mass := fun b => ∑ a, if f a = b then p.mass a else 0
      nonneg := fun b => Finset.sum_nonneg fun a _ => by
        split_ifs
        · exact p.nonneg a
        · exact le_rfl
      total := by
        rw [Finset.sum_comm]
        simpa using p.total }

@[simp] theorem map_mass [DecidableEq B] (p : FiniteLaw A) (f : A → B) (b : B) :
    (p.map f).mass b = ∑ a, if f a = b then p.mass a else 0 := by
  classical
  dsimp only [map]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, ite_false]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

theorem map_entropy_of_injective (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) : finiteEntropy (p.map f).mass = finiteEntropy p.mass := by
  classical
  have hterm (b : B) : entropyTerm ((p.map f).mass b) =
      ∑ a, if f a = b then entropyTerm (p.mass a) else 0 := by
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_mass_apply p f hf]
      simp [hf.eq_iff]
    · simp [map_mass, not_exists.mp hb]
  unfold finiteEntropy
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

def joint (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw (A × B) where
  mass ab := p.mass ab.1 * (q ab.1).mass ab.2
  nonneg ab := mul_nonneg (p.nonneg ab.1) ((q ab.1).nonneg ab.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, (q _).total, p.total]

theorem joint_entropy (p : FiniteLaw A) (q : A → FiniteLaw B) :
    finiteEntropy (p.joint q).mass =
      finiteEntropy p.mass + ∑ a, p.mass a * finiteEntropy (q a).mass :=
  finiteEntropy_chain p.mass (fun a => (q a).mass) (fun a => (q a).total)

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

def conditional (p : FiniteLaw A) (f : A → B) (b : B) : FiniteLaw A := by
  classical
  exact if hzero : (p.map f).mass b = 0 then p else
    { mass := fun a => (if f a = b then p.mass a else 0) / (p.map f).mass b
      nonneg := fun a => div_nonneg
        (by split_ifs; exact p.nonneg a; exact le_rfl) ((p.map f).nonneg b)
      total := by
        rw [← Finset.sum_div, ← map_mass p f b, div_self hzero] }

theorem map_mass_mul_conditional [DecidableEq B]
    (p : FiniteLaw A) (f : A → B) (b : B) (a : A) :
    (p.map f).mass b * (p.conditional f b).mass a =
      if f a = b then p.mass a else 0 := by
  classical
  by_cases hzero : (p.map f).mass b = 0
  · have ha : f a = b → p.mass a = 0 := by
      intro hab
      have hle := p.mass_le_map_mass f a
      rw [hab, hzero] at hle
      exact le_antisymm hle (p.nonneg a)
    rw [hzero, zero_mul]
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ha hab]
    · rw [ite_eq_right hab]
  · simp only [conditional, hzero, ↓reduceDIte]
    by_cases hab : f a = b
    · simpa only [hab, ite_true] using (mul_div_cancel₀ (p.mass a) hzero)
    · simp only [hab, ite_false, zero_div, mul_zero]

theorem entropy_eq_map_add_conditional (p : FiniteLaw A) (f : A → B) :
    finiteEntropy p.mass = finiteEntropy (p.map f).mass +
      ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
  classical
  let graph : A → B × A := fun a => (f a, a)
  have hinj : Function.Injective graph := fun _ _ h => congrArg Prod.snd h
  have hmass : ((p.map f).joint (p.conditional f)).mass = (p.map graph).mass := by
    funext ba
    rcases ba with ⟨b, a⟩
    change (p.map f).mass b * (p.conditional f b).mass a = (p.map graph).mass (b, a)
    rw [map_mass_mul_conditional, map_mass, Finset.sum_eq_single a]
    · simp only [graph, Prod.mk.injEq, and_true]
    · intro x _ hxa
      simp only [graph, Prod.mk.injEq, hxa, and_false, ite_false]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    finiteEntropy p.mass = finiteEntropy (p.map graph).mass :=
      (p.map_entropy_of_injective graph hinj).symm
    _ = finiteEntropy ((p.map f).joint (p.conditional f)).mass := by rw [hmass]
    _ = _ := (p.map f).joint_entropy (p.conditional f)

end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule077
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity -/
section FlattenModule078



namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem entropyTerm_eq_negMulLog (p : ℝ) : entropyTerm p = Real.negMulLog p := rfl

@[simp] theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm]

theorem mul_entropyTerm_inv (x : ℝ) : x * entropyTerm x⁻¹ = Real.log x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [entropyTerm, Real.log_inv]
    calc
      _ = (x * x⁻¹) * Real.log x := by ring
      _ = Real.log x := by rw [mul_inv_cancel₀ hx, one_mul]

theorem finiteEntropy_uniform {A : Type*} [Fintype A] :
    finiteEntropy (fun _a : A => (Fintype.card A : ℝ)⁻¹) =
      Real.log (Fintype.card A) := by
  simp only [finiteEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_entropyTerm_inv (Fintype.card A)

theorem finiteEntropy_deterministic {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) : finiteEntropy (fun b => if b = a then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  change entropyTerm (if b = a then 1 else 0) = 0
  split_ifs <;> simp

@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

theorem concaveOn_entropyTerm : ConcaveOn ℝ (Set.Ici 0) entropyTerm :=
  Real.concaveOn_negMulLog

@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) := by
  unfold finiteEntropy
  exact continuous_finsetSum _ fun value _ =>
    continuous_entropyTerm.comp (continuous_apply value)

theorem tendsto_entropyTerm {I : Type*} {l : Filter I} {p : I → ℝ} {q : ℝ}
    (h : Tendsto p l (𝓝 q)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 (entropyTerm q)) :=
  continuous_entropyTerm.continuousAt.tendsto.comp h

theorem tendsto_entropyTerm_zero {I : Type*} {l : Filter I} {p : I → ℝ}
    (h : Tendsto p l (𝓝 0)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 0) := by
  simpa only [entropyTerm_zero] using tendsto_entropyTerm h

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

theorem finiteEntropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hp₁ : ∀ a, p a ≤ 1) : 0 ≤ finiteEntropy p := by
  exact Finset.sum_nonneg fun a _ => entropyTerm_nonneg (hp₀ a) (hp₁ a)

theorem finiteEntropy_mix_le {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * finiteEntropy p + b * finiteEntropy q ≤
      finiteEntropy (fun i => a * p i + b * q i) := by
  calc
    a * finiteEntropy p + b * finiteEntropy q =
        ∑ i, (a * entropyTerm (p i) + b * entropyTerm (q i)) := by
      simp only [finiteEntropy, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ finiteEntropy (fun i => a * p i + b * q i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact concaveOn_entropyTerm.2 (hp i) (hq i) ha hb hab

theorem finiteEntropy_le_log_card {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (htotal : ∑ a, p a = 1) :
    finiteEntropy p ≤ Real.log (Fintype.card A) := by
  classical
  have hcard : 0 < Fintype.card A := by
    by_contra h
    have : IsEmpty A := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    simp at htotal
  have hn : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr hcard
  have hw : ∑ _a : A, (Fintype.card A : ℝ)⁻¹ = 1 := by
    simp [Finset.sum_const, nsmul_eq_mul, hn.ne']
  have hJ := concaveOn_entropyTerm.le_map_sum
    (t := (Finset.univ : Finset A))
    (w := fun _a : A => (Fintype.card A : ℝ)⁻¹) (p := p)
    (fun _a _ha => (inv_pos.mpr hn).le) hw (fun a _ha => hp a)
  have hJ' : (Fintype.card A : ℝ)⁻¹ * finiteEntropy p ≤
      entropyTerm (Fintype.card A : ℝ)⁻¹ := by
    simpa only [smul_eq_mul, ← Finset.mul_sum, htotal, mul_one, finiteEntropy] using hJ
  calc
    finiteEntropy p = (Fintype.card A : ℝ) *
        ((Fintype.card A : ℝ)⁻¹ * finiteEntropy p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    _ ≤ (Fintype.card A : ℝ) * entropyTerm (Fintype.card A : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hJ' hn.le
    _ = Real.log (Fintype.card A) := mul_entropyTerm_inv (Fintype.card A)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  mass _a := (Fintype.card A : ℝ)⁻¹
  nonneg _a := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card A : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A)).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

@[simp] theorem uniform_mass [Nonempty A] (a : A) :
    (uniform A).mass a = (Fintype.card A : ℝ)⁻¹ := rfl

@[simp] theorem uniform_entropy [Nonempty A] :
    finiteEntropy (uniform A).mass = Real.log (Fintype.card A) :=
  finiteEntropy_uniform

def pure (a : A) : FiniteLaw A := by
  classical
  exact
    { mass := fun b => if b = a then 1 else 0
      nonneg := fun b => by split_ifs <;> norm_num
      total := by simp }

@[simp] theorem pure_entropy (a : A) : finiteEntropy (pure a).mass = 0 := by
  classical
  exact finiteEntropy_deterministic a

theorem mass_le_one (p : FiniteLaw A) (a : A) : p.mass a ≤ 1 := by
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _hb => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.total

theorem entropy_nonneg (p : FiniteLaw A) : 0 ≤ finiteEntropy p.mass :=
  finiteEntropy_nonneg p.mass p.nonneg p.mass_le_one

theorem entropy_le_log_card (p : FiniteLaw A) :
    finiteEntropy p.mass ≤ Real.log (Fintype.card A) :=
  finiteEntropy_le_log_card p.mass p.nonneg p.total

theorem map_entropy_le {B : Type*} [Fintype B] (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass := by
  calc
    finiteEntropy (p.map f).mass ≤ finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun b _ =>
        mul_nonneg ((p.map f).nonneg b) ((p.conditional f b).entropy_nonneg))
    _ = finiteEntropy p.mass := (p.entropy_eq_map_add_conditional f).symm

theorem entropy_tendsto {I : Type*} {l : Filter I}
    {p : I → FiniteLaw A} {q : FiniteLaw A}
    (h : ∀ a, Tendsto (fun i => (p i).mass a) l (𝓝 (q.mass a))) :
    Tendsto (fun i => finiteEntropy (p i).mass) l (𝓝 (finiteEntropy q.mass)) :=
  tendsto_finiteEntropy_of_tendsto h

end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule078
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Laws -/
section FlattenModule079




namespace OAI

/-!
# Probability laws for the polynomial tensor inequalities

The determinant filtration uses an arbitrary binary law, while the three-sector
filtration uses the uniform law on three branches.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- The common binary probability law used for every permuted character. -/
def binaryLaw (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : FiniteLaw (Fin 2) where
  mass i := if i = 0 then q else 1 - q
  nonneg i := by
    fin_cases i
    · simpa using hq₀
    · simpa using sub_nonneg.mpr hq₁
  total := by simp [Fin.sum_univ_two]

@[simp] theorem binaryLaw_zero (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 0 = q := by simp [binaryLaw]

@[simp] theorem binaryLaw_one (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (binaryLaw q hq₀ hq₁).mass 1 = 1 - q := by simp [binaryLaw]

/-- The finite-law entropy agrees exactly with the binary entropy convention. -/
theorem binaryLaw_entropy (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    finiteEntropy (binaryLaw q hq₀ hq₁).mass = Real.binEntropy q := by
  simp [finiteEntropy, Fin.sum_univ_two, entropyTerm, Real.binEntropy, Real.log_inv]
  ring

theorem binaryLaw_product (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (f : Fin 2 → ℝ) :
    (∏ i, f i ^ (binaryLaw q hq₀ hq₁).mass i) = f 0 ^ q * f 1 ^ (1 - q) := by
  simp [Fin.prod_univ_two]

/-- The three-sector entropy factor is `3 ^ p`. -/
theorem uniformThree_entropy_factor (p : ℝ) :
    Real.exp (p * finiteEntropy (FiniteLaw.uniform (Fin 3)).mass) = (3 : ℝ) ^ p := by
  rw [FiniteLaw.uniform_entropy]
  norm_num only [Fintype.card_fin]
  rw [Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

theorem uniformThree_product (f : Fin 3 → ℝ) :
    (∏ i, f i ^ (FiniteLaw.uniform (Fin 3)).mass i) =
      f 0 ^ (1 / 3 : ℝ) * f 1 ^ (1 / 3 : ℝ) * f 2 ^ (1 / 3 : ℝ) := by
  simp [Fin.prod_univ_three, FiniteLaw.uniform_mass, mul_assoc]

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule079
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Laws -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Kernel -/
section FlattenModule080


namespace OAI

/-!
# The determinant kernel of diagonal substitution

A form `A(u,v)s + B(u,v)w` of bidegree `(e,1)` is represented on the affine chart
`u = 1` by the polynomial pair `(A(1,X), B(1,X))`. Diagonal substitution becomes
`(A,B) ↦ A + X * B`, and multiplication by `uw - vs` becomes
`p ↦ (-X * p, p)`.

The identities here hold over every commutative ring. They include the fixed
quotient/kernel coordinates and the monomial identities underlying the
simultaneous triangularization in Section 5.1 of *Matrix Multiplication via
Auxiliary Separation and Polynomial Multiplication*.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantKernel

open Polynomial

variable {R : Type*} [CommRing R]

/-- Affine representatives of forms linear in the second pair of variables. -/
abbrev FormPair (R : Type*) [CommRing R] := R[X] × R[X]

/-- Substitute the first variable pair into the second variable pair. -/
def diagonal : FormPair R →ₗ[R] R[X] where
  toFun p := p.1 + X * p.2
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, mul_add]; ring
  map_smul' c p := by simp [smul_eq_C_mul]; ring

/-- Multiplication by `D = uw - vs` after putting `u = 1`. -/
def determinant : R[X] →ₗ[R] FormPair R where
  toFun p := (-X * p, p)
  map_add' p q := by apply Prod.ext <;> simp [mul_add]
  map_smul' c p := by
    apply Prod.ext <;> simp [smul_eq_C_mul]
    ring

@[simp] theorem diagonal_apply (p : FormPair R) : diagonal p = p.1 + X * p.2 := rfl

@[simp] theorem determinant_apply (p : R[X]) : determinant p = (-X * p, p) := rfl

@[simp] theorem diagonal_determinant (p : R[X]) : diagonal (determinant p) = 0 := by
  simp [diagonal, determinant]

/-- The determinant factor can be recovered from the second component. -/
theorem determinant_injective : Function.Injective (determinant (R := R)) := by
  intro p q h
  exact congrArg Prod.snd h

/-- Vanishing after diagonal substitution is exactly divisibility by `uw - vs`. -/
theorem diagonal_eq_zero_iff (p : FormPair R) :
    diagonal p = 0 ↔ p = determinant p.2 := by
  constructor
  · intro h
    apply Prod.ext
    · change p.1 = -X * p.2
      have h' : p.1 + X * p.2 = 0 := h
      linear_combination h'
    · rfl
  · intro h
    rw [h]
    exact diagonal_determinant _

/-- The kernel parametrization does not require any field or domain hypothesis. -/
theorem mem_kernel_iff (p : FormPair R) :
    p ∈ LinearMap.ker diagonal ↔ ∃ q, determinant q = p := by
  rw [LinearMap.mem_ker, diagonal_eq_zero_iff]
  constructor
  · intro h
    exact ⟨p.2, h.symm⟩
  · rintro ⟨q, rfl⟩
    rfl

theorem kernel_eq_range : LinearMap.ker (diagonal (R := R)) = LinearMap.range determinant := by
  ext p
  exact mem_kernel_iff p

/-- A fixed linear complement to the determinant kernel on unrestricted polynomials. -/
def split : (R[X] × R[X]) ≃ₗ[R] FormPair R where
  toFun p := (p.1 - X * p.2, p.2)
  invFun p := (p.1 + X * p.2, p.2)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp
  map_add' p q := by
    apply Prod.ext <;> simp
    ring
  map_smul' c p := by
    apply Prod.ext <;> simp [smul_eq_C_mul]
    ring

@[simp] theorem split_apply (p : R[X] × R[X]) : split p = (p.1 - X * p.2, p.2) := rfl

@[simp] theorem split_symm_apply (p : FormPair R) : split.symm p = (diagonal p, p.2) := rfl

@[simp] theorem diagonal_split (p : R[X] × R[X]) : diagonal (split p) = p.1 := by
  simp [split, diagonal]

@[simp] theorem split_zero_left (q : R[X]) : split (0, q) = determinant q := by
  simp [split, determinant]

theorem diagonal_surjective : Function.Surjective (diagonal (R := R)) := by
  intro p
  exact ⟨(p, 0), by simp⟩

/-- The kernel is canonically isomorphic to one polynomial copy. -/
def kernelEquiv : R[X] ≃ₗ[R] LinearMap.ker (diagonal (R := R)) where
  toFun p := ⟨determinant p, by simp⟩
  invFun p := p.1.2
  left_inv p := rfl
  right_inv p := by
    apply Subtype.ext
    exact ((diagonal_eq_zero_iff p.1).mp p.2).symm
  map_add' p q := by apply Subtype.ext; exact map_add determinant p q
  map_smul' c p := by apply Subtype.ext; exact map_smul determinant c p

/-- Multiply both coefficients by a first-input polynomial. -/
def multiply (f : R[X]) : FormPair R →ₗ[R] FormPair R where
  toFun p := (f * p.1, f * p.2)
  map_add' p q := by apply Prod.ext <;> simp [mul_add]
  map_smul' c p := by apply Prod.ext <;> simp [smul_eq_C_mul] <;> ring

@[simp] theorem multiply_apply (f : R[X]) (p : FormPair R) :
    multiply f p = (f * p.1, f * p.2) := rfl

/-- The quotient action is ordinary polynomial multiplication. -/
theorem diagonal_multiply (f : R[X]) (p : FormPair R) :
    diagonal (multiply f p) = f * diagonal p := by
  simp [diagonal, multiply]
  ring

/-- The kernel action is ordinary polynomial multiplication with the same first input. -/
theorem multiply_determinant (f p : R[X]) :
    multiply f (determinant p) = determinant (f * p) := by
  apply Prod.ext <;> simp [multiply, determinant]
  ring

/-- Every first-input slice preserves the determinant kernel. -/
theorem multiply_mem_kernel (f : R[X]) {p : FormPair R}
    (hp : p ∈ LinearMap.ker diagonal) : multiply f p ∈ LinearMap.ker diagonal := by
  rw [LinearMap.mem_ker, diagonal_multiply, LinearMap.mem_ker.mp hp, mul_zero]

/-- Quotient and kernel coordinates transform simultaneously, with an unchanged first input. -/
theorem split_multiply (f : R[X]) (p : R[X] × R[X]) :
    multiply f (split p) = split (f * p.1, f * p.2) := by
  apply Prod.ext <;> simp [multiply, split]
  ring

/-- The ordinary quotient monomial `u^(e-j) v^j s`, with `j ≤ e`. -/
def quotientMonomial (j : ℕ) : FormPair R := (X ^ j, 0)

/-- The last quotient monomial `v^e w`. -/
def quotientTop (e : ℕ) : FormPair R := (0, X ^ e)

/-- The kernel monomial `(uw-vs) u^(e-1-j) v^j`, with `j < e`. -/
def kernelMonomial (j : ℕ) : FormPair R := determinant (X ^ j)

@[simp] theorem diagonal_quotientMonomial (j : ℕ) :
    diagonal (quotientMonomial (R := R) j) = X ^ j := by
  simp [diagonal, quotientMonomial]

@[simp] theorem diagonal_quotientTop (e : ℕ) :
    diagonal (quotientTop (R := R) e) = X ^ (e + 1) := by
  simp [diagonal, quotientTop, pow_succ, mul_comm]

@[simp] theorem diagonal_kernelMonomial (j : ℕ) :
    diagonal (kernelMonomial (R := R) j) = 0 := by
  simp [kernelMonomial]

@[simp] theorem multiply_quotientMonomial (i j : ℕ) :
    multiply (X ^ i) (quotientMonomial (R := R) j) = quotientMonomial (i + j) := by
  apply Prod.ext <;> simp [multiply, quotientMonomial, pow_add]

@[simp] theorem multiply_kernelMonomial (i j : ℕ) :
    multiply (X ^ i) (kernelMonomial (R := R) j) = kernelMonomial (i + j) := by
  rw [kernelMonomial, multiply_determinant, ← pow_add, kernelMonomial]

/-- The sole cross term in a nonfinal first-input slice has coefficient one. -/
theorem multiply_quotientTop_cross (i e : ℕ) :
    multiply (X ^ i) (quotientTop (R := R) e) =
      quotientMonomial (i + e + 1) + kernelMonomial (i + e) := by
  apply Prod.ext <;> simp [multiply, quotientTop, quotientMonomial, kernelMonomial, determinant,
    pow_add, pow_succ]
  ring

/-- For the final first-input monomial the last quotient vector remains the last vector. -/
theorem multiply_quotientTop_last (d e : ℕ) :
    multiply (X ^ d) (quotientTop (R := R) e) = quotientTop (d + e) := by
  apply Prod.ext <;> simp [multiply, quotientTop, pow_add]

/-- The actual quotient vectors used at degree `e`: there are `e + 2` of them. -/
def quotientVector (e : ℕ) (j : Fin (e + 2)) : FormPair R :=
  if (j : ℕ) < e + 1 then quotientMonomial j else quotientTop e

/-- The actual kernel vectors used at degree `e`: there are `e` of them. -/
def kernelVector (_e : ℕ) (j : Fin _e) : FormPair R := kernelMonomial j

@[simp] theorem diagonal_quotientVector (e : ℕ) (j : Fin (e + 2)) :
    diagonal (quotientVector (R := R) e j) = X ^ (j : ℕ) := by
  unfold quotientVector
  split_ifs with h
  · exact diagonal_quotientMonomial j
  · have hj : (j : ℕ) = e + 1 := by omega
    simpa [hj] using diagonal_quotientTop (R := R) e

@[simp] theorem diagonal_kernelVector (e : ℕ) (j : Fin e) :
    diagonal (kernelVector (R := R) e j) = 0 := by
  exact diagonal_kernelMonomial j

/-- Ordinary quotient columns have no kernel correction in the adapted output basis. -/
theorem multiply_quotientVector_ordinary (d e i j : ℕ)
    (hi : i ≤ d) (hj : j ≤ e) :
    multiply (X ^ i) (quotientVector (R := R) e ⟨j, by omega⟩) =
      quotientVector (d + e) ⟨i + j, by omega⟩ := by
  simp only [quotientVector, show j < e + 1 by omega,
    show i + j < d + e + 1 by omega, ↓reduceIte]
  exact multiply_quotientMonomial i j

/-- Nonfinal slices have exactly the quotient-top cross term described in Section 5.1. -/
theorem multiply_quotientVector_top_cross (d e i : ℕ) (hi : i < d) :
    multiply (X ^ i) (quotientVector (R := R) e ⟨e + 1, by omega⟩) =
      quotientVector (d + e) ⟨e + 1 + i, by omega⟩ +
        kernelVector (d + e) ⟨e + i, by omega⟩ := by
  simp only [quotientVector, lt_self_iff_false, ↓reduceIte,
    show e + 1 + i < d + e + 1 by omega, kernelVector]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    multiply_quotientTop_cross (R := R) i e

/-- The final slice has no cross term. -/
theorem multiply_quotientVector_top_last (d e : ℕ) :
    multiply (X ^ d) (quotientVector (R := R) e ⟨e + 1, by omega⟩) =
      quotientVector (d + e) ⟨d + e + 1, by omega⟩ := by
  simp only [quotientVector, lt_self_iff_false, ↓reduceIte]
  exact multiply_quotientTop_last d e

/-- All kernel columns have the convolution indices of the smaller branch. -/
theorem multiply_kernelVector (d e i j : ℕ) (hi : i ≤ d) (hj : j < e) :
    multiply (X ^ i) (kernelVector (R := R) e ⟨j, hj⟩) =
      kernelVector (d + e) ⟨i + j, by omega⟩ := by
  exact multiply_kernelMonomial i j


/-- Distinct bounded powers of `X` are independent even when the coefficient ring
has zero divisors. -/
theorem monomials_linearIndependent (n : ℕ) :
    LinearIndependent R (fun i : Fin n => (X : R[X]) ^ (i : ℕ)) := by
  have h := (Polynomial.degreeLT.basis R n).linearIndependent.map'
    (Polynomial.degreeLT R n).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  simpa only [Function.comp_def, Submodule.subtype_apply, Polynomial.degreeLT.basis_val] using h

/-- The quotient vectors followed by the kernel vectors are linearly independent.
This establishes nonsingularity of the simultaneous change of coordinates,
without any genericity assumption on the first input. -/
theorem adaptedVectors_linearIndependent (e : ℕ) :
    LinearIndependent R (Sum.elim (quotientVector (R := R) e) (kernelVector e)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : ∑ i : Fin (e + 2), c (Sum.inl i) • (X : R[X]) ^ (i : ℕ) = 0 := by
    have h := congrArg (diagonal (R := R)) hc
    simpa only [Fintype.sum_sum_type, map_add, map_sum, map_smul,
      Sum.elim_inl, Sum.elim_inr, diagonal_quotientVector, diagonal_kernelVector,
      smul_zero, Finset.sum_const_zero, add_zero, map_zero] using h
  have cq : ∀ i : Fin (e + 2), c (Sum.inl i) = 0 :=
    (Fintype.linearIndependent_iff.mp (monomials_linearIndependent (R := R) (e + 2))) _ hq
  have hk : ∑ i : Fin e, c (Sum.inr i) • (X : R[X]) ^ (i : ℕ) = 0 := by
    have h := congrArg Prod.snd hc
    simpa only [Fintype.sum_sum_type, Prod.snd_add, Prod.snd_sum, Prod.snd_smul,
      Sum.elim_inl, Sum.elim_inr, cq, zero_smul, Finset.sum_const_zero, zero_add,
      kernelVector, kernelMonomial, determinant_apply, Prod.snd_zero, Prod.smul_mk] using h
  have ck : ∀ i : Fin e, c (Sum.inr i) = 0 :=
    (Fintype.linearIndependent_iff.mp (monomials_linearIndependent (R := R) e)) _ hk
  exact Sum.rec cq ck

end MatrixMultiplication.AuxiliarySeparation.DeterminantKernel

end

end OAI

end FlattenModule080
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Kernel -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Basis -/
section FlattenModule081


namespace OAI

/-!
# The finite adapted basis for the determinant filtration

The quotient vectors and determinant-kernel vectors of Section 5.1 form a basis
of the actual space of bidegree `(e,1)` forms. The proof works over every field,
including in the boundary case `e = 0` where the kernel has dimension zero.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantBasis

open Polynomial

variable {R : Type*} [CommRing R]

/-- Affine coefficient pairs of forms of bidegree `(e,1)`. -/
abbrev BoundedPair (R : Type*) [CommRing R] (e : ℕ) :=
  degreeLT R (e + 1) × degreeLT R (e + 1)

/-- Forget the degree bounds in the affine representation of binary forms. -/
def forget (e : ℕ) : BoundedPair R e →ₗ[R] DeterminantKernel.FormPair R where
  toFun p := ((p.1 : R[X]), (p.2 : R[X]))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem forget_injective (e : ℕ) : Function.Injective (forget (R := R) e) := by
  intro p q h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- A quotient vector with both coefficient polynomials of degree at most `e`. -/
def quotientVector (e : ℕ) (j : Fin (e + 2)) : BoundedPair R e :=
  if h : (j : ℕ) < e + 1 then
    (⟨X ^ (j : ℕ), mem_degreeLT.mpr ((degree_X_pow_le _).trans_lt (by exact_mod_cast h))⟩, 0)
  else
    (0, ⟨X ^ e, mem_degreeLT.mpr ((degree_X_pow_le _).trans_lt (by exact_mod_cast Nat.lt_succ_self e))⟩)

/-- A bounded kernel vector, obtained by multiplication by `uw-vs`. -/
def kernelVector (e : ℕ) (j : Fin e) : BoundedPair R e :=
  (⟨-(X ^ ((j : ℕ) + 1)), mem_degreeLT.mpr <| by
      rw [degree_neg]
      exact (degree_X_pow_le _).trans_lt (by exact_mod_cast (show (j : ℕ) + 1 < e + 1 by omega))⟩,
   ⟨X ^ (j : ℕ), mem_degreeLT.mpr <|
      (degree_X_pow_le _).trans_lt (by exact_mod_cast (show (j : ℕ) < e + 1 by omega))⟩)

/-- The quotient vectors first, followed by the determinant-kernel vectors. -/
def vector (e : ℕ) : (Fin (e + 2) ⊕ Fin e) → BoundedPair R e :=
  Sum.elim (quotientVector e) (kernelVector e)

@[simp] theorem forget_quotientVector (e : ℕ) (j : Fin (e + 2)) :
    forget e (quotientVector (R := R) e j) = DeterminantKernel.quotientVector e j := by
  unfold quotientVector DeterminantKernel.quotientVector
  split_ifs <;> rfl

@[simp] theorem forget_kernelVector (e : ℕ) (j : Fin e) :
    forget e (kernelVector (R := R) e j) = DeterminantKernel.kernelVector e j := by
  apply Prod.ext
  · change -(X ^ ((j : ℕ) + 1)) = -X * X ^ (j : ℕ)
    rw [pow_succ, mul_comm, neg_mul]
  · rfl

@[simp] theorem forget_vector (e : ℕ) (j : Fin (e + 2) ⊕ Fin e) :
    forget e (vector (R := R) e j) =
      Sum.elim (DeterminantKernel.quotientVector e) (DeterminantKernel.kernelVector e) j := by
  cases j <;> simp [vector]

/-- Linear independence holds over a general commutative coefficient ring. -/
theorem vector_linearIndependent (e : ℕ) : LinearIndependent R (vector (R := R) e) := by
  apply LinearIndependent.of_comp (forget e)
  simpa only [Function.comp_def, forget_vector] using
    DeterminantKernel.adaptedVectors_linearIndependent (R := R) e

/-- The dimension of the original space of forms is twice `e+1`. -/
theorem finrank_boundedPair (K : Type*) [Field K] (e : ℕ) :
    Module.finrank K (BoundedPair K e) = 2 * (e + 1) := by
  have h : Module.finrank K (degreeLT K (e + 1)) = e + 1 := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis K (e + 1))
  rw [Module.finrank_prod, h]
  omega

/-- The fixed simultaneous change of basis used in the determinant degeneration. -/
def basis (K : Type*) [Field K] (e : ℕ) :
    Module.Basis (Fin (e + 2) ⊕ Fin e) K (BoundedPair K e) :=
  basisOfLinearIndependentOfCardEqFinrank' (vector e) (vector_linearIndependent e) (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_boundedPair]
    omega)

@[simp] theorem basis_apply (K : Type*) [Field K] (e : ℕ)
    (j : Fin (e + 2) ⊕ Fin e) : basis K e j = vector e j := by
  rw [basis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- Forgetting degree bounds identifies the finite basis with the explicit
polynomial-pair formulas. -/
@[simp] theorem forget_basis (K : Type*) [Field K] (e : ℕ)
    (j : Fin (e + 2) ⊕ Fin e) :
    forget e (basis K e j) =
      Sum.elim (DeterminantKernel.quotientVector e) (DeterminantKernel.kernelVector e) j := by
  rw [basis_apply, forget_vector]

end MatrixMultiplication.AuxiliarySeparation.DeterminantBasis

end

end OAI

end FlattenModule081
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Basis -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation -/
section FlattenModule082





namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {F X Y Z : Type*} [Field F]

theorem coeff_eq_sum_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    (p : Polynomial F) (d : ℕ) (hdegree : p.degree < Fintype.card ι) :
    p.coeff d = ∑ i, p.eval (nodes i) *
      (Lagrange.basis Finset.univ nodes i).coeff d := by
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset ι)) := hnodes.injOn
  have hinterp := Lagrange.eq_interpolate hinj (by simpa using hdegree)
    (f := p)
  calc
    p.coeff d = (Lagrange.interpolate Finset.univ nodes
        (fun i => p.eval (nodes i))).coeff d := congrArg (fun q => q.coeff d) hinterp
    _ = _ := by
      simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul]

theorem RankAtMost.coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ} (hP : RankAtMost P r)
    (d : ℕ) (hdegree : ∀ x y z, (P x y z).degree < Fintype.card ι) :
    RankAtMost (fun x y z => (P x y z).coeff d) (Fintype.card ι * r) := by
  rcases hP with ⟨a, b, c, rfl⟩
  let w : ι → F := fun i => (Lagrange.basis Finset.univ nodes i).coeff d
  let aa : (ι × Fin r) → X → F := fun i x => w i.1 * (a i.2 x).eval (nodes i.1)
  let bb : (ι × Fin r) → Y → F := fun i y => (b i.2 y).eval (nodes i.1)
  let cc : (ι × Fin r) → Z → F := fun i z => (c i.2 z).eval (nodes i.1)
  have heq : (fun x y z => (∑ j, rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    rw [coeff_eq_sum_eval nodes hnodes _ d (hdegree x y z)]
    simp only [Fintype.sum_prod_type, rankOne, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [aa, bb, cc, w]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

structure PolynomialApproximation (T : Tensor F X Y Z) (r d D : ℕ) where
  polynomial : Tensor (Polynomial F) X Y Z
  rank_bound : RankAtMost polynomial r
  vanishes : ∀ x y z k, k < d → (polynomial x y z).coeff k = 0
  leading : ∀ x y z, (polynomial x y z).coeff d = T x y z
  degree_bound : ∀ x y z, (polynomial x y z).degree ≤ D

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

def normalized (A : PolynomialApproximation T r d D) :
    Tensor (Polynomial F) X Y Z :=
  fun x y z => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem polynomial_eq (A : PolynomialApproximation T r d D) (x : X) (y : Y) (z : Z) :
    A.polynomial x y z = Polynomial.X ^ d * A.normalized x y z :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem normalized_constant (A : PolynomialApproximation T r d D)
    (x : X) (y : Y) (z : Z) : (A.normalized x y z).coeff 0 = T x y z := by
  have h := A.leading x y z
  rw [A.polynomial_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h

theorem power_polynomial_eq (A : PolynomialApproximation T r d D) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
    Tensor.power A.polynomial n x y z =
      Polynomial.X ^ (d * n) * Tensor.power A.normalized n x y z := by
  simp [Tensor.power, A.polynomial_eq, Finset.prod_mul_distrib, ← pow_mul]

def power (A : PolynomialApproximation T r d D) (n : ℕ) :
    PolynomialApproximation (Tensor.power T n) (r ^ n) (d * n) (D * n) where
  polynomial := Tensor.power A.polynomial n
  rank_bound := A.rank_bound.power n
  vanishes := by
    intro x y z k hk
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false]
  leading := by
    intro x y z
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      Tensor.power, Polynomial.coeff_zero_prod, A.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    calc
      (Tensor.power A.polynomial n x y z).natDegree ≤
          ∑ i, (A.polynomial (x i) (y i) (z i)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact Polynomial.natDegree_le_of_degree_le (A.degree_bound (x i) (y i) (z i))
      _ = D * n := by simp [Nat.mul_comm]

theorem rank_power [CharZero F] (A : PolynomialApproximation T r d D) (n : ℕ) :
    RankAtMost (Tensor.power T n) ((D * n + 1) * r ^ n) := by
  let nodes : Fin (D * n + 1) → F := fun i => (i.val : F)
  have hinj : Function.Injective nodes := by
    intro i j h
    apply Fin.ext
    exact Nat.cast_injective h
  have hdegree (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
      ((A.power n).polynomial x y z).degree < Fintype.card (Fin (D * n + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt ((A.power n).degree_bound x y z)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (D * n)))
  have h := (A.power n).rank_bound.coeff nodes hinj (d * n) hdegree
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq, Fintype.card_fin] at h
  exact h

theorem rank_normalized_eval (A : PolynomialApproximation T r d D)
    (t : F) (ht : t ≠ 0) :
    RankAtMost (fun x y z => (A.normalized x y z).eval t) r := by
  have h := (A.rank_bound.map (Polynomial.evalRingHom t)).scale ((t ^ d)⁻¹)
  change RankAtMost (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) r at h
  have heq : (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) =
      fun x y z => (A.normalized x y z).eval t := by
    funext x y z
    rw [A.polynomial_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d ht), one_mul]
  rw [heq] at h
  exact h

theorem borderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    {S : Tensor ℂ X Y Z} (A : PolynomialApproximation S r d D) :
    BorderRankAtMost S r := by
  let f : ℂ → Tensor ℂ X Y Z := fun t x y z => (A.normalized x y z).eval t
  have hf : Continuous f := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    apply continuous_pi
    intro z
    exact (A.normalized x y z).continuous
  have hclosed : IsClosed {t : ℂ | BorderRankAtMost (f t) r} :=
    isClosed_closure.preimage hf
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ {t : ℂ | BorderRankAtMost (f t) r} := by
    intro t ht
    exact (A.rank_normalized_eval t (by simpa using ht)).borderRankAtMost
  have hz := closure_minimal hsubset hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  have heq : f 0 = S := by
    funext x y z
    simp only [f, ← Polynomial.coeff_zero_eq_eval_zero, A.normalized_constant]
  change BorderRankAtMost (f 0) r at hz
  rw [heq] at hz
  exact hz

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule082
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition -/
section FlattenModule083




namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ScalarRestriction

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]
variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_scalar_mul (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) (s : K) :
    restrict A B C (fun x y z => s * P x y z) =
      fun x' y' z' => s * restrict A B C P x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem cyclic_restrict (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) :
    cyclic (restrict A B C P) = restrict B C A (cyclic P) := by
  funext y' z' x'
  simp only [cyclic, restrict]
  calc
    (∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * P x y z) =
        ∑ y, ∑ x, ∑ z, A x' x * B y' y * C z' z * P x y z :=
      Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ x, A x' x * B y' y * C z' z * P x y z := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro x hx
      ring

end ScalarRestriction

section PolynomialCoefficients

variable {F : Type*} [Field F]

theorem coeff_mul_expand_eq_constant (M p : Polynomial F) (a : F)
    (hp : p.coeff 0 = a) (k j : ℕ) (hj : j ≤ k) :
    (M * Polynomial.expand F (k + 1) p).coeff j =
      (M * Polynomial.C a).coeff j := by
  have hdiv : Polynomial.X ∣ p - Polynomial.C a :=
    Polynomial.X_dvd_iff.mpr (by simp only [Polynomial.coeff_sub,
      Polynomial.coeff_C_zero, hp, sub_self])
  rcases hdiv with ⟨q, hq⟩
  have hpq : p = Polynomial.C a + Polynomial.X * q := by
    rw [← hq]
    ring
  have hexpand : Polynomial.expand F (k + 1) p =
      Polynomial.C a + Polynomial.X ^ (k + 1) *
        Polynomial.expand F (k + 1) q := by
    rw [hpq, map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X]
  have hmul : M * Polynomial.expand F (k + 1) p =
      M * Polynomial.C a + Polynomial.X ^ (k + 1) *
        (M * Polynomial.expand F (k + 1) q) := by
    rw [hexpand]
    ring
  rw [hmul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    ite_eq_right (by omega), add_zero]

end PolynomialCoefficients

section PolynomialLocalMaps

variable {F X Y Z X' Y' Z' : Type*} [Field F]
variable [Fintype X] [Fintype Y] [Fintype Z]

structure PolynomialRestrictionDegeneration
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly Lz : ℕ) where
  leftMap : X' → X → Polynomial F
  middleMap : Y' → Y → Polynomial F
  rightMap : Z' → Z → Polynomial F
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  right_degree : ∀ z' z, (rightMap z' z).degree ≤ Lz
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff k = U x' y' z'

namespace PolynomialRestrictionDegeneration

variable {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'}
variable {k Lx Ly Lz r d D : ℕ}

def cyclic (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    PolynomialRestrictionDegeneration (Tensor.cyclic T) (Tensor.cyclic U) k Ly Lz Lx where
  leftMap := L.middleMap
  middleMap := L.rightMap
  rightMap := L.leftMap
  left_degree := L.middle_degree
  middle_degree := L.right_degree
  right_degree := L.left_degree
  vanishes := by
    intro y' z' x' j hj
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff j = 0
    rw [← cyclic_restrict]
    exact L.vanishes x' y' z' j hj
  leading := by
    intro y' z' x'
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff k =
        Tensor.cyclic U y' z' x'
    rw [← cyclic_restrict]
    exact L.leading x' y' z'

def basePolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap (fun x y z => Polynomial.C (T x y z))

def compositionPolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z))

def normalizedComposition (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.normalized x y z))

theorem compositionPolynomial_eq
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    L.compositionPolynomial W x' y' z' =
      Polynomial.X ^ (d * (k + 1)) * L.normalizedComposition W x' y' z' := by
  have hpoint : (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) =
      fun x y z => Polynomial.X ^ (d * (k + 1)) *
        Polynomial.expand F (k + 1) (W.normalized x y z) := by
    funext x y z
    rw [W.polynomial_eq, map_mul, map_pow, Polynomial.expand_X]
    simp only [← pow_mul, Nat.mul_comm]
  unfold compositionPolynomial normalizedComposition
  rw [hpoint, restrict_scalar_mul]

theorem normalizedComposition_coeff
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (j : ℕ) (hj : j ≤ k)
    (x' : X') (y' : Y') (z' : Z') :
    (L.normalizedComposition W x' y' z').coeff j =
      (L.basePolynomial x' y' z').coeff j := by
  simp only [normalizedComposition, basePolynomial, restrict, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  exact coeff_mul_expand_eq_constant
    (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z)
    (W.normalized x y z) (T x y z) (W.normalized_constant x y z) k j hj

theorem compositionPolynomial_rank
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    RankAtMost (L.compositionPolynomial W) r :=
  (W.rank_bound.map (Polynomial.expand F (k + 1)).toRingHom).restrict
    L.leftMap L.middleMap L.rightMap

theorem compositionPolynomial_degree
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    (L.compositionPolynomial W x' y' z').degree ≤ D * (k + 1) + Lx + Ly + Lz := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold compositionPolynomial restrict
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have hA := Polynomial.natDegree_le_of_degree_le (L.left_degree x' x)
  have hB := Polynomial.natDegree_le_of_degree_le (L.middle_degree y' y)
  have hC := Polynomial.natDegree_le_of_degree_le (L.right_degree z' z)
  have hP : (Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) := by
    rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right (k + 1)
      (Polynomial.natDegree_le_of_degree_le (W.degree_bound x y z))
  have hprod := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le hA hB) hC) hP
  change (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z *
    Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) + Lx + Ly + Lz
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprod

def compose (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    PolynomialApproximation U r (d * (k + 1) + k) (D * (k + 1) + Lx + Ly + Lz) where
  polynomial := L.compositionPolynomial W
  rank_bound := L.compositionPolynomial_rank W
  vanishes := by
    intro x' y' z' j hj
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    split_ifs with hdj
    · have hjk : j - d * (k + 1) < k := by omega
      rw [L.normalizedComposition_coeff W _ (Nat.le_of_lt hjk)]
      exact L.vanishes x' y' z' _ hjk
    · rfl
  leading := by
    intro x' y' z'
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
    rw [L.normalizedComposition_coeff W k le_rfl]
    exact L.leading x' y' z'
  degree_bound := L.compositionPolynomial_degree W

@[simp] theorem compose_polynomial
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    (L.compose W).polynomial = restrict L.leftMap L.middleMap L.rightMap
      (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) := rfl

end PolynomialRestrictionDegeneration

end PolynomialLocalMaps

end Tensor
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule083
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Filtration -/
section FlattenModule084




namespace OAI

/-!
# The finite determinant filtration of polynomial multiplication

The first leg is kept fixed throughout. The second and third legs use the
explicit quotient/kernel vectors of `DeterminantKernel`. The coefficient
identity `adaptedTensor_reconstruct` verifies the actual multiplication on
every basis input; it does not assume a simultaneous triangularization.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation Polynomial

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

abbrev Index (e : ℕ) := Sum (Fin (e + 2)) (Fin e)

/-- The ordered quotient/kernel vectors in the actual polynomial pair space. -/
def vector (e : ℕ) : Index e → DeterminantKernel.FormPair ℂ :=
  Sum.elim (DeterminantKernel.quotientVector e) (DeterminantKernel.kernelVector e)

/-- All multiplication coefficients in the explicit adapted bases.
Here `a=d+1`, `b=e+1`, and no first-leg change of coordinates occurs. -/
def adaptedTensor (d e : ℕ) : Tensor ℂ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

/-- The associated graded tensor, whose two branches still share the first leg. -/
def gradedTensor (d e : ℕ) : Tensor ℂ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | _, .inl _, .inr _ => 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

private theorem sum_coordinate {n r : ℕ} (hr : r < n)
    (v : Fin n → DeterminantKernel.FormPair ℂ) :
    (∑ k : Fin n, (if r = k.val then (1 : ℂ) else 0) • v k) = v ⟨r, hr⟩ := by
  have h (k : Fin n) : r = k.val ↔ k = ⟨r, hr⟩ := by
    constructor
    · intro hk
      apply Fin.ext
      exact hk.symm
    · intro hk
      exact congrArg Fin.val hk.symm
  simp_rw [h]
  simp

/-- Exact coordinate reconstruction of every first-leg slice, in common bases. -/
theorem adaptedTensor_reconstruct (d e : ℕ) (i : Fin (d + 1)) (j : Index e) :
    (∑ k : Index (d + e), adaptedTensor d e i j k • vector (d + e) k) =
      DeterminantKernel.multiply (X ^ i.val) (vector e j) := by
  have hi : i.val ≤ d := by omega
  rcases j with j | j
  · by_cases hj : j.val ≤ e
    · have hn : j.val ≠ e + 1 := by omega
      simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
        Sum.elim_inr, hn, false_and, ↓reduceIte, zero_smul, Finset.sum_const_zero,
        add_zero]
      rw [sum_coordinate (by omega)]
      exact (DeterminantKernel.multiply_quotientVector_ordinary d e i.val j.val hi hj).symm
    · have hj' : j.val = e + 1 := by omega
      have hjfin : j = ⟨e + 1, by omega⟩ := Fin.ext hj'
      rw [hjfin]
      by_cases hi' : i.val < d
      · simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
          Sum.elim_inr, hi', true_and]
        rw [sum_coordinate (by omega), sum_coordinate (by omega)]
        have h := DeterminantKernel.multiply_quotientVector_top_cross
          (R := ℂ) d e i.val hi'
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
      · have hi'' : i.val = d := by omega
        simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
          Sum.elim_inr, hi', and_false, false_and, ↓reduceIte, zero_smul,
          Finset.sum_const_zero, add_zero]
        rw [sum_coordinate (by omega)]
        have h := DeterminantKernel.multiply_quotientVector_top_last (R := ℂ) d e
        simpa only [hi'', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
  · simp only [Fintype.sum_sum_type, adaptedTensor, vector, Sum.elim_inl,
      Sum.elim_inr, zero_smul, Finset.sum_const_zero, zero_add]
    rw [sum_coordinate (by omega)]
    exact (DeterminantKernel.multiply_kernelVector d e i.val j.val hi j.isLt).symm

/-- The reconstruction uniquely determines every tensor coefficient. -/
theorem adaptedTensor_unique (d e : ℕ)
    (T : Tensor ℂ (Fin (d + 1)) (Index e) (Index (d + e)))
    (hT : ∀ i j, (∑ k, T i j k • vector (d + e) k) =
      DeterminantKernel.multiply (X ^ i.val) (vector e j)) :
    T = adaptedTensor d e := by
  funext i j k
  have h := (DeterminantKernel.adaptedVectors_linearIndependent (R := ℂ) (d + e))
  have hs : ∑ z, (T i j z - adaptedTensor d e i j z) • vector (d + e) z = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hT, adaptedTensor_reconstruct, sub_self]
  exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp h) _ hs k)

/-- The quotient branch is exactly `C(a,b+1)`. -/
theorem gradedTensor_quotient (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 2)) (k : Fin (d + e + 2)) :
    gradedTensor d e i (.inl j) (.inl k) =
      convolution (d + 1) (e + 2) i j (Fin.cast (by omega) k) := by
  simp only [gradedTensor, convolution, Fin.val_cast]

/-- The kernel branch is exactly `C(a,b-1)`. -/
theorem gradedTensor_kernel (d e : ℕ) (i : Fin (d + 1))
    (j : Fin e) (k : Fin (d + e)) :
    gradedTensor d e i (.inr j) (.inr k) =
      convolution (d + 1) e i j (Fin.cast (by omega) k) := by
  simp only [gradedTensor, convolution, Fin.val_cast]

@[simp] theorem adaptedTensor_kernel_to_quotient (d e : ℕ)
    (i : Fin (d + 1)) (j : Fin e) (k : Fin (d + e + 2)) :
    adaptedTensor d e i (.inr j) (.inl k) = 0 := rfl

/-- Polynomial diagonal maps; scaling the quotient input by `X` clears
the negative input-kernel weight without changing the leading tensor. -/
def inputScale (e : ℕ) : Index e → ℂ[X]
  | .inl _ => X
  | .inr _ => 1

def outputScale (e : ℕ) : Index e → ℂ[X]
  | .inl _ => 1
  | .inr _ => X

def diagonalMap {I : Type*} [DecidableEq I] (s : I → ℂ[X]) : I → I → ℂ[X] :=
  fun i j => if i = j then s i else 0

private theorem restrict_diagonal {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (a : I → ℂ[X]) (b : J → ℂ[X]) (c : K → ℂ[X])
    (T : Tensor ℂ[X] I J K) (i : I) (j : J) (k : K) :
    Tensor.restrict (diagonalMap a) (diagonalMap b) (diagonalMap c) T i j k =
      a i * b j * c k * T i j k := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

/-- A checked polynomial degeneration to the two matched convolution branches. -/
def degeneration (d e : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (adaptedTensor d e)
      (gradedTensor d e) 1 0 1 1 where
  leftMap := diagonalMap (fun _ => 1)
  middleMap := diagonalMap (inputScale e)
  rightMap := diagonalMap (outputScale (d + e))
  left_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs <;> simp
  middle_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs
    · cases i <;> simp [inputScale]
    · simp
  right_degree := by
    intro i j
    simp only [diagonalMap]
    split_ifs
    · cases i <;> simp [outputScale]
    · simp
  vanishes := by
    intro i j k n hn
    have hn' : n = 0 := by omega
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [hn', ← pow_two]
  leading := by
    intro i j k
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, gradedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [← pow_two]

/-! The actual coordinate change from the original two-copy convolution. -/

abbrev OriginalIndex (e : ℕ) := Sum (Fin (e + 1)) (Fin (e + 1))

/-- The original monomial bases in the `s` and `w` components. -/
def originalBasis (e : ℕ) :
    Module.Basis (OriginalIndex e) ℂ (DeterminantBasis.BoundedPair ℂ e) :=
  (Polynomial.degreeLT.basis ℂ (e + 1)).prod (Polynomial.degreeLT.basis ℂ (e + 1))

private theorem degree_shift_lt (d e : ℕ) (i : Fin (d + 1))
    (p : Polynomial.degreeLT ℂ (e + 1)) :
    ((X : ℂ[X]) ^ i.val * (p : ℂ[X])).degree < (d + e + 1 : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · have hp := Polynomial.mem_degreeLT.mp p.2
    rw [Polynomial.degree_lt_iff_coeff_zero] at hp
    exact hp (n - i.val) (by have hi := i.isLt; omega)
  · rfl

/-- Multiplication by a fixed first-input monomial between the bounded spaces. -/
def boundedShift (d e : ℕ) (i : Fin (d + 1)) :
    Polynomial.degreeLT ℂ (e + 1) →ₗ[ℂ] Polynomial.degreeLT ℂ (d + e + 1) where
  toFun p := ⟨X ^ i.val * (p : ℂ[X]), Polynomial.mem_degreeLT.mpr (degree_shift_lt d e i p)⟩
  map_add' p q := by apply Subtype.ext; simp [mul_add]
  map_smul' c p := by apply Subtype.ext; simp [Polynomial.smul_eq_C_mul]; ring

/-- The same first monomial multiplies both components. -/
def boundedMultiply (d e : ℕ) (i : Fin (d + 1)) :
    DeterminantBasis.BoundedPair ℂ e →ₗ[ℂ] DeterminantBasis.BoundedPair ℂ (d + e) :=
  (boundedShift d e i).prodMap (boundedShift d e i)

@[simp] theorem forget_boundedMultiply (d e : ℕ) (i : Fin (d + 1))
    (p : DeterminantBasis.BoundedPair ℂ e) :
    DeterminantBasis.forget (d + e) (boundedMultiply d e i p) =
      DeterminantKernel.multiply (X ^ i.val) (DeterminantBasis.forget e p) := rfl

/-- Polynomial multiplication in its original monomial coordinates. -/
def sourceTensor (d e : ℕ) :
    Tensor ℂ (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)) :=
  fun i j k => (originalBasis (d + e)).repr
    (boundedMultiply d e i (originalBasis e j)) k

@[simp] theorem sourceTensor_inl_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor d e i (.inl j) (.inl k) =
      convolution (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inr_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor d e i (.inr j) (.inr k) =
      convolution (d + 1) (e + 1) i j (Fin.cast (by omega) k) := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift,
    ← pow_add, convolution, eq_comm]

@[simp] theorem sourceTensor_inl_inr (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor d e i (.inl j) (.inr k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]

@[simp] theorem sourceTensor_inr_inl (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 1)) (k : Fin (d + e + 1)) :
    sourceTensor d e i (.inr j) (.inl k) = 0 := by
  simp [sourceTensor, originalBasis, boundedMultiply, boundedShift]

/-- Record the polynomial coordinate and the choice of `s` or `w` separately. -/
def originalCoordinate (e : ℕ) : OriginalIndex e → Fin (e + 1) × Bool
  | .inl j => (j, false)
  | .inr j => (j, true)

/-- The source is exactly polynomial convolution tensored with a two-coordinate
dot product whose singleton is on the unchanged first leg. -/
theorem sourceTensor_product (d e : ℕ) :
    sourceTensor d e =
      Tensor.pullback (fun i : Fin (d + 1) => (i, ())) (originalCoordinate e)
        (fun k => (Fin.cast (by omega) (originalCoordinate (d + e) k).1,
          (originalCoordinate (d + e) k).2))
        (Tensor.product (convolution (d + 1) (e + 1))
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) Bool)))) := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [Tensor.pullback, Tensor.product, Tensor.cyclic, Tensor.dotPairing,
      originalCoordinate]

/-- The input matrix has adapted vectors as columns in the original basis. -/
def inputChange (e : ℕ) (j : Index e) (old : OriginalIndex e) : ℂ :=
  (originalBasis e).repr (DeterminantBasis.basis ℂ e j) old

/-- The output-dual matrix uses the inverse basis change, as required for tensors. -/
def outputDualChange (e : ℕ) (k : Index e) (old : OriginalIndex e) : ℂ :=
  (DeterminantBasis.basis ℂ e).repr (originalBasis e old) k

/-- The first input is unchanged, including throughout the basis change. -/
def fixedFirst (d : ℕ) (i j : Fin (d + 1)) : ℂ := if i = j then 1 else 0

private theorem restrict_fixedFirst (d e : ℕ)
    (B : Index e → OriginalIndex e → ℂ)
    (C : Index (d + e) → OriginalIndex (d + e) → ℂ)
    (T : Tensor ℂ (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)))
    (i : Fin (d + 1)) (j : Index e) (k : Index (d + e)) :
    Tensor.restrict (fixedFirst d) B C T i j k =
      ∑ y, ∑ z, B j y * C k z * T i y z := by
  simp [Tensor.restrict, fixedFirst, ite_mul]

theorem boundedMultiply_adapted_coordinates (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    (DeterminantBasis.basis ℂ (d + e)).repr
      (boundedMultiply d e i (DeterminantBasis.basis ℂ e j)) k =
      adaptedTensor d e i j k := by
  have h := adaptedTensor_unique d e
    (fun i j k => (DeterminantBasis.basis ℂ (d + e)).repr
      (boundedMultiply d e i (DeterminantBasis.basis ℂ e j)) k) ?_
  · exact congrFun (congrFun (congrFun h i) j) k
  · intro i j
    have hsum := congrArg (DeterminantBasis.forget (R := ℂ) (d + e))
      ((DeterminantBasis.basis ℂ (d + e)).sum_repr
        (boundedMultiply d e i (DeterminantBasis.basis ℂ e j)))
    simpa only [map_sum, map_smul, DeterminantBasis.forget_basis,
      forget_boundedMultiply, vector] using hsum

/-- A concrete restriction, with the identity first map, changes the original
two-copy convolution into the simultaneously triangular coefficient tensor. -/
theorem sourceTensor_coordinate_change (d e : ℕ) :
    Tensor.restrict (fixedFirst d) (inputChange e) (outputDualChange (d + e))
      (sourceTensor d e) = adaptedTensor d e := by
  funext i j k
  rw [restrict_fixedFirst]
  simp only [inputChange, outputDualChange, sourceTensor]
  calc
    (∑ y, ∑ z,
        (originalBasis e).repr (DeterminantBasis.basis ℂ e j) y *
          (DeterminantBasis.basis ℂ (d + e)).repr (originalBasis (d + e) z) k *
          (originalBasis (d + e)).repr (boundedMultiply d e i (originalBasis e y)) z) =
        ∑ y, (originalBasis e).repr (DeterminantBasis.basis ℂ e j) y *
          (DeterminantBasis.basis ℂ (d + e)).repr
            (boundedMultiply d e i (originalBasis e y)) k := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      exact (DeterminantBasis.basis ℂ (d + e)).sum_repr_mul_repr
        (originalBasis (d + e)) _ k
    _ = (DeterminantBasis.basis ℂ (d + e)).repr
          (boundedMultiply d e i (DeterminantBasis.basis ℂ e j)) k := by
      have hsum := congrArg (fun p => (DeterminantBasis.basis ℂ (d + e)).repr
          (boundedMultiply d e i p) k)
        ((originalBasis e).sum_repr (DeterminantBasis.basis ℂ e j))
      simpa only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
        smul_eq_mul] using hsum
    _ = adaptedTensor d e i j k := boundedMultiply_adapted_coordinates d e i j k

end MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

end

end OAI

end FlattenModule084
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Filtration -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Interpolation -/
section FlattenModule085

namespace OAI

/-!
# Exact interpolation away from zero

The coefficient-extraction theorem already proved for matrix multiplication is
used here with the nonzero nodes `1, ..., D + 1`.  In particular a polynomial
degeneration can be recovered by a finite sum of its ordinary restrictions at
nonzero parameters, with the leading power divided out at each parameter.
-/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- An explicit set of `D + 1` nonzero complex interpolation parameters. -/
def interpolationNode (D : ℕ) (i : Fin (D + 1)) : ℂ := (i.val + 1 : ℕ)

theorem interpolationNode_injective (D : ℕ) :
    Function.Injective (interpolationNode D) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_right_cancel (Nat.cast_injective hij)

theorem interpolationNode_ne_zero (D : ℕ) (i : Fin (D + 1)) :
    interpolationNode D i ≠ 0 := by
  change ((i.val + 1 : ℕ) : ℂ) ≠ 0
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val)

/-- The constant-coefficient functional expressed in the Lagrange basis. -/
def constantInterpolationWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (i : ι) : ℂ :=
  (Lagrange.basis Finset.univ nodes i).coeff 0

/-- Exact constant recovery; this specializes the existing coefficient theorem. -/
theorem constant_eq_sum_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hinj : Function.Injective nodes) (p : Polynomial ℂ)
    (hdegree : p.degree < Fintype.card ι) :
    p.coeff 0 = ∑ i, constantInterpolationWeight nodes i * p.eval (nodes i) := by
  simpa only [constantInterpolationWeight, mul_comm] using
    Tensor.coeff_eq_sum_eval nodes hinj p 0 hdegree

/-- A degree-`D` polynomial is recovered at zero using only nonzero parameters. -/
theorem constant_eq_sum_nonzero_eval (D : ℕ) (p : Polynomial ℂ)
    (hdegree : p.degree ≤ D) :
    p.coeff 0 = ∑ i, constantInterpolationWeight (interpolationNode D) i *
      p.eval (interpolationNode D i) := by
  apply constant_eq_sum_eval _ (interpolationNode_injective D)
  simp only [Fintype.card_fin]
  exact lt_of_le_of_lt hdegree (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))

/-- Removing a leading power before interpolation only requires evaluations at
nonzero nodes.  The degree bound is on the normalized polynomial. -/
theorem leading_eq_sum_normalized_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hinj : Function.Injective nodes)
    (hnonzero : ∀ i, nodes i ≠ 0) (p q : Polynomial ℂ) (d : ℕ)
    (hp : p = Polynomial.X ^ d * q) (hdegree : q.degree < Fintype.card ι) :
    p.coeff d = ∑ i, constantInterpolationWeight nodes i *
      (nodes i ^ d)⁻¹ * p.eval (nodes i) := by
  have hcoeff : p.coeff d = q.coeff 0 := by
    rw [hp, Polynomial.coeff_X_pow_mul']
    simp
  rw [hcoeff, constant_eq_sum_eval nodes hinj q hdegree]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  have hpow : nodes i ^ d ≠ 0 := pow_ne_zero d (hnonzero i)
  calc
    constantInterpolationWeight nodes i * q.eval (nodes i) =
        constantInterpolationWeight nodes i *
          ((nodes i ^ d)⁻¹ * (nodes i ^ d)) * q.eval (nodes i) := by
            rw [inv_mul_cancel₀ hpow, mul_one]
    _ = _ := by ring

/-- A leading coefficient is a finite linear combination of normalized
evaluations, assuming all lower coefficients vanish. -/
theorem leading_eq_sum_nonzero_eval (D d : ℕ) (p : Polynomial ℂ)
    (hvanish : ∀ j < d, p.coeff j = 0) (hdegree : p.degree ≤ D) :
    p.coeff d = ∑ i, constantInterpolationWeight (interpolationNode D) i *
      (interpolationNode D i ^ d)⁻¹ * p.eval (interpolationNode D i) := by
  obtain ⟨q, hp⟩ := Polynomial.X_pow_dvd_iff.mpr hvanish
  apply leading_eq_sum_normalized_eval _ (interpolationNode_injective D)
    (interpolationNode_ne_zero D) p q d hp
  have hqdegree : q.degree ≤ p.degree := by
    rw [hp, mul_comm]
    exact Polynomial.degree_le_mul_left q (pow_ne_zero d Polynomial.X_ne_zero)
  simp only [Fintype.card_fin]
  exact lt_of_le_of_lt (le_trans hqdegree hdegree)
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))

section PolynomialRestriction

variable {X Y Z X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
variable {k Lx Ly Lz : ℕ}

/-- Evaluating the polynomial restriction evaluates its three local maps. -/
theorem restrictionDegeneration_eval
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (t : ℂ) (x' : X') (y' : Y') (z' : Z') :
    (L.basePolynomial x' y' z').eval t =
      Tensor.restrict (fun a x => (L.leftMap a x).eval t)
        (fun b y => (L.middleMap b y).eval t)
        (fun c z => (L.rightMap c z).eval t) T x' y' z' := by
  simp only [Tensor.PolynomialRestrictionDegeneration.basePolynomial, Tensor.restrict,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]

/-- The degree of a polynomial restriction is bounded by the sum of the
degrees of its three local maps. -/
theorem restrictionDegeneration_degree
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (x' : X') (y' : Y') (z' : Z') :
    (L.basePolynomial x' y' z').degree ≤ (Lx + Ly + Lz : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold Tensor.PolynomialRestrictionDegeneration.basePolynomial Tensor.restrict
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have hA := Polynomial.natDegree_le_of_degree_le (L.left_degree x' x)
  have hB := Polynomial.natDegree_le_of_degree_le (L.middle_degree y' y)
  have hC := Polynomial.natDegree_le_of_degree_le (L.right_degree z' z)
  have hconstant : (Polynomial.C (T x y z)).natDegree ≤ 0 := by simp
  simpa using Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le hA hB) hC) hconstant

/-- The existing polynomial-approximation API applies to a polynomial
restriction as soon as the source tensor has a rank bound. -/
def restrictionDegeneration_approximation
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) :
    Tensor.PolynomialApproximation U r k (Lx + Ly + Lz) where
  polynomial := L.basePolynomial
  rank_bound := (hT.map Polynomial.C).restrict L.leftMap L.middleMap L.rightMap
  vanishes := L.vanishes
  leading := L.leading
  degree_bound := restrictionDegeneration_degree L

/-- Interpolation after tensor powering has a linear degree overhead, rather
than raising the single-copy interpolation overhead to the tensor power. -/
theorem restrictionDegeneration_power_rankAtMost
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power U n) (((Lx + Ly + Lz) * n + 1) * r ^ n) :=
  (restrictionDegeneration_approximation L hT).rank_power n

/-- A polynomial degeneration yields an exact finite sum of ordinary
restrictions at nonzero parameters.  There are `Lx + Ly + Lz + 1` terms. -/
theorem restrictionDegeneration_recovery
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (x' : X') (y' : Y') (z' : Z') :
    U x' y' z' = ∑ i,
      constantInterpolationWeight (interpolationNode (Lx + Ly + Lz)) i *
      (interpolationNode (Lx + Ly + Lz) i ^ k)⁻¹ *
      Tensor.restrict
        (fun a x => (L.leftMap a x).eval (interpolationNode (Lx + Ly + Lz) i))
        (fun b y => (L.middleMap b y).eval (interpolationNode (Lx + Ly + Lz) i))
        (fun c z => (L.rightMap c z).eval (interpolationNode (Lx + Ly + Lz) i))
        T x' y' z' := by
  rw [← L.leading x' y' z']
  change (L.basePolynomial x' y' z').coeff k = _
  rw [leading_eq_sum_nonzero_eval (Lx + Ly + Lz) k
    (L.basePolynomial x' y' z') (L.vanishes x' y' z')
    (restrictionDegeneration_degree L x' y' z')]
  simp_rw [restrictionDegeneration_eval]

/-- Finite interpolation converts a polynomial degeneration into an exact
rank bound with its explicit number of evaluation parameters. -/
theorem restrictionDegeneration_rankAtMost
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    {r : ℕ} (hT : Tensor.RankAtMost T r) :
    Tensor.RankAtMost U ((Lx + Ly + Lz + 1) * r) := by
  have hbase := (hT.map Polynomial.C).restrict L.leftMap L.middleMap L.rightMap
  change Tensor.RankAtMost L.basePolynomial r at hbase
  have hdegree (x' : X') (y' : Y') (z' : Z') :
      (L.basePolynomial x' y' z').degree <
        Fintype.card (Fin (Lx + Ly + Lz + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (restrictionDegeneration_degree L x' y' z')
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (Lx + Ly + Lz)))
  have h := hbase.coeff (interpolationNode (Lx + Ly + Lz))
    (interpolationNode_injective _) k hdegree
  have hleading : (fun x' y' z' => (L.basePolynomial x' y' z').coeff k) = U := by
    funext x' y' z'
    exact L.leading x' y' z'
  simpa only [hleading, Fintype.card_fin] using h

end PolynomialRestriction

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule085
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Interpolation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Degeneration -/
section FlattenModule086



namespace OAI

/-!
# Characters decrease under polynomial degeneration

Finite interpolation expresses a polynomial's leading coefficient as a sum
of evaluations.  Applying it after tensor powering gives only a linear
overhead, which disappears in the exponential growth rate.  No continuity
assumption on the character is used.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

variable (χ : Character)
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Scalar multiplication is a restriction, including when the scalar is zero. -/
theorem value_scale_le (c : ℂ) (T : Tensor ℂ X Y Z) :
    χ.value (fun x y z => c * T x y z) ≤ χ.value T := by
  classical
  have heq : Tensor.restrict
      (fun x' x => if x = x' then c else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T =
      fun x y z => c * T x y z := by
    funext x y z
    simp [Tensor.restrict, ite_mul, mul_ite]
  simpa only [heq] using χ.monotone T
    (fun x' x => if x = x' then c else 0)
    (fun y' y => if y = y' then 1 else 0)
    (fun z' z => if z = z' then 1 else 0)

/-- Nonzero scalar multiplication preserves a character. -/
theorem value_scale (c : ℂ) (hc : c ≠ 0) (T : Tensor ℂ X Y Z) :
    χ.value (fun x y z => c * T x y z) = χ.value T := by
  apply le_antisymm (χ.value_scale_le c T)
  have h := χ.value_scale_le c⁻¹ (fun x y z => c * T x y z)
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h

/-- Adding tensors is a restriction of their independent direct sum. -/
theorem value_sum_le {ι : Type} [Fintype ι] (T : ι → Tensor ℂ X Y Z) :
    χ.value (fun x y z => ∑ i, T i x y z) ≤ ∑ i, χ.value (T i) := by
  classical
  have heq : Tensor.restrict
      (fun x (p : ι × X) => if p.2 = x then 1 else 0)
      (fun y (p : ι × Y) => if p.2 = y then 1 else 0)
      (fun z (p : ι × Z) => if p.2 = z then 1 else 0)
      (Tensor.directSum T) = fun x y z => ∑ i, T i x y z := by
    funext x y z
    simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
      ite_mul, mul_ite, ite_and]
  rw [← χ.map_directSum T, ← heq]
  exact χ.monotone (Tensor.directSum T) _ _ _

/-- Exact interpolation bounds any polynomial coefficient by the sum of the
character values of finitely many evaluation tensors. -/
theorem value_coefficient_le (P : Tensor (Polynomial ℂ) X Y Z) (d D : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D) :
    χ.value (fun x y z => (P x y z).coeff d) ≤
      ∑ i : Fin (D + 1), χ.value (fun x y z => (P x y z).eval (interpolationNode D i)) := by
  classical
  let w : Fin (D + 1) → ℂ := fun i =>
    (Lagrange.basis Finset.univ (interpolationNode D) i).coeff d
  have heq : (fun x y z => (P x y z).coeff d) =
      fun x y z => ∑ i : Fin (D + 1), w i * (P x y z).eval (interpolationNode D i) := by
    funext x y z
    have hlt : (P x y z).degree < Fintype.card (Fin (D + 1)) := by
      simp only [Fintype.card_fin]
      exact lt_of_le_of_lt (hdegree x y z)
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
    simpa only [w, mul_comm] using Tensor.coeff_eq_sum_eval
      (interpolationNode D) (interpolationNode_injective D) (P x y z) d hlt
  rw [heq]
  apply (χ.value_sum_le _).trans
  exact Finset.sum_le_sum fun i _ => χ.value_scale_le (w i) _

/-- A uniform bound on nonzero evaluations bounds the leading tensor.  The
proof uses tensor powers and removes their linear interpolation overhead. -/
theorem value_le_of_polynomialApproximation
    {U : Tensor ℂ X Y Z} {r d D : ℕ}
    (A : Tensor.PolynomialApproximation U r d D) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ t : ℂ, t ≠ 0 →
      χ.value (fun x y z => (A.polynomial x y z).eval t) ≤ b) :
    χ.value U ≤ b := by
  apply le_of_pow_le_linear_mul_pow (K := (D : ℝ)) hb
  intro n
  have hcoefficient := χ.value_coefficient_le (A.power n).polynomial
    (d * n) (D * n) (A.power n).degree_bound
  have hleading : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power U n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [hleading, χ.value_power] at hcoefficient
  apply hcoefficient.trans
  calc
    (∑ i : Fin (D * n + 1), χ.value
        (fun x y z => ((A.power n).polynomial x y z).eval
          (interpolationNode (D * n) i))) ≤
        ∑ _i : Fin (D * n + 1), b ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have heval : (fun x y z => ((A.power n).polynomial x y z).eval
          (interpolationNode (D * n) i)) =
          Tensor.power (fun x y z => (A.polynomial x y z).eval
            (interpolationNode (D * n) i)) n := by
        funext x y z
        simp only [Tensor.PolynomialApproximation.power, Tensor.power,
          Polynomial.eval_prod]
      rw [heval, χ.value_power]
      exact pow_le_pow_left₀ (χ.nonneg _)
        (hbound _ (interpolationNode_ne_zero _ _)) n
    _ = ((n : ℝ) * (D : ℝ) + 1) * b ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring

omit [Fintype Z] in
private theorem exists_rankAtMost (T : Tensor ℂ X Y Z) :
    ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y → X → ℂ := fun p x => if p.1 = x then 1 else 0
  let b : X × Y → Y → ℂ := fun p y => if p.2 = y then 1 else 0
  let c : X × Y → Z → ℂ := fun p z => T p.1 p.2 z
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [Tensor.rankOne, a, b, c, Fintype.sum_prod_type, ite_mul, mul_ite]
  exact ⟨Fintype.card (X × Y), heq ▸ Tensor.rankAtMost_sum_rankOne a b c⟩

/-- The character axioms imply monotonicity under polynomial degeneration.
Continuity of the character is neither assumed nor used. -/
theorem value_polynomialRestrictionDegeneration_le
    {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    χ.value U ≤ χ.value T := by
  obtain ⟨r, hr⟩ := exists_rankAtMost T
  apply χ.value_le_of_polynomialApproximation
    (restrictionDegeneration_approximation L hr) (χ.nonneg T)
  intro t ht
  have heval : (fun x y z =>
      ((restrictionDegeneration_approximation L hr).polynomial x y z).eval t) =
      Tensor.restrict (fun x' x => (L.leftMap x' x).eval t)
        (fun y' y => (L.middleMap y' y).eval t)
        (fun z' z => (L.rightMap z' z).eval t) T := by
    funext x y z
    exact restrictionDegeneration_eval L t x y z
  rw [heval]
  exact χ.monotone T _ _ _

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule086
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Degeneration -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SupportExtension -/
section FlattenModule087

namespace OAI

/-!
# Recovering tensors from their supported coordinate subspaces

If a tensor has support inside three injectively embedded coordinate sets, it
is exactly the extension by zero of its pullback to those sets. Characters
therefore have the same value on the ambient tensor and this smaller tensor.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation
open scoped Classical

variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

omit [Fintype X'] [Fintype Y'] [Fintype Z'] in
/-- Support in embedded coordinate sets reconstructs the tensor by zero extension. -/
theorem tensor_eq_extendByZero_pullback (T : Tensor ℂ X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    T = Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0)
      (Tensor.pullback fx fy fz T) := by
  classical
  funext x' y' z'
  by_cases hx' : x' ∈ Set.range fx
  · obtain ⟨x, rfl⟩ := hx'
    by_cases hy' : y' ∈ Set.range fy
    · obtain ⟨y, rfl⟩ := hy'
      by_cases hz' : z' ∈ Set.range fz
      · obtain ⟨z, rfl⟩ := hz'
        simp [Tensor.restrict, Tensor.pullback, hx.eq_iff, hy.eq_iff, hz.eq_iff,
          ite_mul, mul_ite]
      · have hzero : T (fx x) (fy y) z' = 0 := by
          by_contra h
          exact hz' (hs _ _ _ h).2.2
        have hnone : ∀ z, fz z ≠ z' := fun z h => hz' ⟨z, h⟩
        simp [Tensor.restrict, hzero, hnone]
    · have hzero : T (fx x) y' z' = 0 := by
        by_contra h
        exact hy' (hs _ _ _ h).2.1
      have hnone : ∀ y, fy y ≠ y' := fun y h => hy' ⟨y, h⟩
      simp [Tensor.restrict, hzero, hnone]
  · have hzero : T x' y' z' = 0 := by
      by_contra h
      exact hx' (hs _ _ _ h).1
    have hnone : ∀ x, fx x ≠ x' := fun x h => hx' ⟨x, h⟩
    simp [Tensor.restrict, hzero, hnone]

namespace Character

/-- A character ignores ambient coordinates outside a tensor's support. -/
theorem value_eq_pullback_of_support (χ : Character) (T : Tensor ℂ X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    χ.value T = χ.value (Tensor.pullback fx fy fz T) := by
  calc
    χ.value T = χ.value (Tensor.restrict
        (fun x' x => if fx x = x' then 1 else 0)
        (fun y' y => if fy y = y' then 1 else 0)
        (fun z' z => if fz z = z' then 1 else 0)
        (Tensor.pullback fx fy fz T)) :=
      congrArg χ.value (tensor_eq_extendByZero_pullback T fx fy fz hx hy hz hs)
    _ = _ := χ.value_extendByZero _ fx fy fz hx hy hz

end Character
end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule087
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SupportExtension -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexFactorialLogBounds -/
section FlattenModule088




namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

noncomputable def factorialLogRemainder (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n)

theorem factorialLogRemainder_eq (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n) := rfl

@[simp] theorem factorialLogRemainder_zero : factorialLogRemainder 0 = 0 := by
  simp [factorialLogRemainder]

theorem factorialLogRemainder_stirling (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Stirling.log_stirlingSeq_formula (n + 1)
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
    unfold factorialLogRemainder
    linarith

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hstirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
        atTop (𝓝 0) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hconstant : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hstirling.add ((hconstant.add hlog).const_mul (1 / 2 : ℝ))
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [factorialLogRemainder_stirling,
    Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ))
      atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hmul : Tendsto (fun t : ℕ => t * c) atTop atTop :=
    tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc)
  have hscaled : Tendsto
      (fun t : ℕ => factorialLogRemainder (t * c) / (t * c : ℕ) * (c : ℝ))
      atTop (𝓝 0) := by
    simpa using (tendsto_factorialLogRemainder_div.comp hmul).mul_const (c : ℝ)
  apply hscaled.congr
  intro t
  by_cases ht : t = 0
  · simp [ht]
  rw [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr ht]

theorem factorialLogRemainder_succ (n : ℕ) :
    factorialLogRemainder (n + 1) = factorialLogRemainder n + 1 -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  unfold factorialLogRemainder
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

private theorem nat_mul_log_increment_le_one (n : ℕ) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have heq : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp [hpos.ne']
    ring
  rwa [heq] at hmul

private theorem one_le_succ_mul_log_increment (n : ℕ) (hn : 0 < n) :
    1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hsucc.le
  have heq : ((n : ℝ) + 1) * (1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹) = 1 := by
    rw [inv_div]
    field_simp [hsucc.ne']
    ring
  rwa [heq] at hmul

theorem factorialLogRemainder_nonneg (n : ℕ) : 0 ≤ factorialLogRemainder n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlog := nat_mul_log_increment_le_one n
    rw [factorialLogRemainder_succ]
    linarith

theorem factorialLogRemainder_le_one_add_log_pos (n : ℕ) :
    factorialLogRemainder (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) := by
  induction n with
  | zero => norm_num [factorialLogRemainder]
  | succ n ih =>
    have hlog := one_le_succ_mul_log_increment (n + 1) (Nat.succ_pos n)
    have hstep := factorialLogRemainder_succ (n + 1)
    push_cast at ih hlog hstep ⊢
    nlinarith

theorem factorialLogRemainder_le_one_add_log (n : ℕ) :
    factorialLogRemainder n ≤ 1 + Real.log (n + 1 : ℕ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    refine (factorialLogRemainder_le_one_add_log_pos n).trans ?_
    apply add_le_add_right
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.le_succ (n + 1)

theorem abs_factorialLogRemainder_le (n : ℕ) :
    |factorialLogRemainder n| ≤ 1 + Real.log (n + 1 : ℕ) := by
  rw [abs_of_nonneg (factorialLogRemainder_nonneg n)]
  exact factorialLogRemainder_le_one_add_log n

end MatrixMultiplication.Foundation

end OAI

end FlattenModule088
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexFactorialLogBounds -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl -/
section FlattenModule089











namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation
namespace FiniteControl

open scoped BigOperators

theorem every_path_safe {State : Type*} (Safe : ℕ → State → Prop)
    (Allows : ℕ → State → State → Prop) (n : ℕ) (path : ℕ → State)
    (initial : Safe 0 (path 0))
    (closed : ∀ t < n, ∀ s s', Safe t s → Allows t s s' → Safe (t + 1) s')
    (steps : ∀ t < n, Allows t (path t) (path (t + 1))) :
    ∀ t ≤ n, Safe t (path t) := by
  intro t
  induction t with
  | zero => intro _; exact initial
  | succ t ih =>
      intro ht
      have htn : t < n := Nat.lt_of_succ_le ht
      exact closed t htn (path t) (path (t + 1))
        (ih (Nat.le_of_lt htn)) (steps t htn)

theorem exists_population_preserving_equiv {I J Node : Type*}
    [Fintype I] [Fintype J] [DecidableEq Node]
    (f : I → Node) (g : J → Node)
    (counts : ∀ node, Fintype.card {i // f i = node} =
      Fintype.card {j // g j = node}) :
    ∃ e : I ≃ J, ∀ i, g (e i) = f i := by
  classical
  let ef : ∀ node, {i // f i = node} ≃ {j // g j = node} :=
    fun node => Fintype.equivOfCardEq (counts node)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  exact (ef (f i) ⟨i, rfl⟩).property

theorem population_product_eq {I J Node M : Type*}
    [Fintype I] [Fintype J] [DecidableEq Node] [CommMonoid M]
    (f : I → Node) (g : J → Node)
    (counts : ∀ node, Fintype.card {i // f i = node} =
      Fintype.card {j // g j = node}) (cost : Node → M) :
    (∏ i, cost (f i)) = ∏ j, cost (g j) := by
  obtain ⟨e, he⟩ := exists_population_preserving_equiv f g counts
  calc
    (∏ i, cost (f i)) = ∏ i, cost (g (e i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [he i]
    _ = ∏ j, cost (g j) := e.prod_comp (fun j => cost (g j))

theorem exists_common_bank_multiple {Node : Type*} [Fintype Node]
    (denominator blockSize : Node → ℕ)
    (denominator_pos : ∀ node, 0 < denominator node)
    (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧
      ∀ node, denominator node * blockSize node ∣ bank := by
  classical
  refine ⟨∏ node, denominator node * blockSize node, ?_, ?_⟩
  · exact Finset.prod_pos fun node _ =>
      Nat.mul_pos (denominator_pos node) (blockSize_pos node)
  · intro node
    exact Finset.dvd_prod_of_mem (fun node => denominator node * blockSize node)
      (Finset.mem_univ node)

theorem exists_exact_rational_tiling {Node : Type*} [Fintype Node]
    (weight : Node → ℚ) (nonnegative : ∀ node, 0 ≤ weight node)
    (blockSize : Node → ℕ) (blockSize_pos : ∀ node, 0 < blockSize node) :
    ∃ bank : ℕ, 0 < bank ∧ ∀ node, ∃ copies : ℕ,
      (bank : ℚ) * weight node = (copies * blockSize node : ℕ) := by
  obtain ⟨bank, bank_pos, divisible⟩ := exists_common_bank_multiple
    (fun node => (weight node).den) blockSize
    (fun node => (weight node).den_pos) blockSize_pos
  refine ⟨bank, bank_pos, ?_⟩
  intro node
  obtain ⟨multiple, hmultiple⟩ := divisible node
  refine ⟨multiple * (weight node).num.toNat, ?_⟩
  have hnum : ((weight node).num.toNat : ℚ) = ((weight node).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (nonnegative node))
  have hden : ((weight node).den : ℚ) ≠ 0 := by
    exact_mod_cast (weight node).den_ne_zero
  calc
    (bank : ℚ) * weight node =
        (bank : ℚ) * (((weight node).num : ℚ) / ((weight node).den : ℚ)) := by
      rw [(weight node).num_div_den]
    _ = ((multiple * (weight node).num.toNat) * blockSize node : ℕ) := by
      rw [hmultiple]
      push_cast
      rw [hnum]
      field_simp [hden]

theorem target_relation_of_windows (a b c : ℤ) (x y z d : ℝ)
    (hd : 0 < d) (tight : x + y + z = 0)
    (hx : |x - (a : ℝ) * d| ≤ d / 10)
    (hy : |y - (b : ℝ) * d| ≤ d / 10)
    (hz : |z + 2 * (c : ℝ) * d| ≤ d / 10) :
    a + b = c + c := by
  obtain ⟨hx₀, hx₁⟩ := abs_le.mp hx
  obtain ⟨hy₀, hy₁⟩ := abs_le.mp hy
  obtain ⟨hz₀, hz₁⟩ := abs_le.mp hz
  let k : ℤ := a + b - 2 * c
  have hkcast : (k : ℝ) = (a : ℝ) + (b : ℝ) - 2 * (c : ℝ) := by
    simp [k]
  have hlow : -(1 : ℝ) < (k : ℝ) := by
    by_contra hn
    have hn' : (k : ℝ) ≤ -1 := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hd)
    rw [hkcast] at hm
    nlinarith
  have hhigh : (k : ℝ) < 1 := by
    by_contra hn
    have hn' : 1 ≤ (k : ℝ) := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt hd)
    rw [hkcast] at hm
    nlinarith
  have hsmall : |(k : ℝ)| < 1 := abs_lt.mpr ⟨hlow, hhigh⟩
  have hsmallInt : |k| < 1 := by exact_mod_cast hsmall
  have hk : k = 0 := Int.abs_lt_one_iff.mp hsmallInt
  dsimp [k] at hk
  linarith

theorem synchronized_targets_of_windows (targets : Set ℤ)
    (free : ThreeAPFree targets) (a b c : ℤ)
    (ha : a ∈ targets) (hb : b ∈ targets) (hc : c ∈ targets)
    (x y z d : ℝ) (hd : 0 < d) (tight : x + y + z = 0)
    (hx : |x - (a : ℝ) * d| ≤ d / 10)
    (hy : |y - (b : ℝ) * d| ≤ d / 10)
    (hz : |z + 2 * (c : ℝ) * d| ≤ d / 10) :
    a = b ∧ a = c := by
  have hrelation := target_relation_of_windows a b c x y z d hd tight hx hy hz
  have hac : a = c := free ha hc hb hrelation
  exact ⟨by linarith, hac⟩

end FiniteControl
end MatrixMultiplication.Foundation

end OAI

end FlattenModule089
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexRationalTypes -/
section FlattenModule090





namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

structure RationalLaw (A : Type*) [Fintype A] where
  mass : A → ℚ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def toFiniteLaw (p : RationalLaw A) : FiniteLaw A where
  mass a := p.mass a
  nonneg a := by exact_mod_cast p.nonneg a
  total := by exact_mod_cast p.total

@[simp] theorem toFiniteLaw_mass (p : RationalLaw A) (a : A) :
    p.toFiniteLaw.mass a = (p.mass a : ℝ) := rfl

theorem exists_exact_counts (p : RationalLaw A) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : A → ℕ,
      (∑ a, counts a) = D ∧
      ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
  classical
  obtain ⟨D, hD, hcopies⟩ := FiniteControl.exists_exact_rational_tiling
    p.mass p.nonneg (fun _ => 1) (fun _ => Nat.zero_lt_one)
  choose counts hcounts using hcopies
  have hc : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
    intro a
    simpa using (hcounts a).symm
  refine ⟨D, hD, counts, ?_, hc⟩
  have hsum : (∑ a, (counts a : ℚ)) = (D : ℚ) := by
    simp_rw [hc]
    rw [← Finset.mul_sum, p.total, mul_one]
  exact_mod_cast hsum

theorem scale_exact_counts (p : RationalLaw A) (D : ℕ) (counts : A → ℕ)
    (hsum : (∑ a, counts a) = D)
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (k : ℕ) :
    (∑ a, k * counts a) = k * D ∧
      ∀ a, ((k * counts a : ℕ) : ℚ) = ((k * D : ℕ) : ℚ) * p.mass a := by
  constructor
  · rw [← Finset.mul_sum, hsum]
  · intro a
    simp only [Nat.cast_mul]
    rw [hcounts a]
    ring

theorem exact_counts_zero_iff (p : RationalLaw A) {D : ℕ} (hD : 0 < D)
    {counts : A → ℕ}
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (a : A) :
    counts a = 0 ↔ p.mass a = 0 := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  constructor
  · intro hzero
    have hz : (D : ℚ) * p.mass a = 0 := by
      rw [← hcounts a, hzero, Nat.cast_zero]
    exact (mul_eq_zero.mp hz).resolve_left hDq
  · intro hzero
    have hz : (counts a : ℚ) = 0 := by rw [hcounts a, hzero, mul_zero]
    exact_mod_cast hz

theorem exact_counts_real_mass (p : RationalLaw A) {D : ℕ} (hD : 0 < D)
    {counts : A → ℕ}
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (a : A) :
    (counts a : ℝ) / (D : ℝ) = p.toFiniteLaw.mass a := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  apply (div_eq_iff hDr).2
  have hc : (counts a : ℝ) = (D : ℝ) * (p.mass a : ℝ) := by
    exact_mod_cast hcounts a
  simpa only [toFiniteLaw_mass, mul_comm] using hc

theorem exists_type_representation (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      ∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a := by
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := p.exists_exact_counts
  refine ⟨counts, by simpa only [hsum] using hD, ?_⟩
  intro a
  rw [hsum]
  exact p.exact_counts_real_mass hD hcounts a

end RationalLaw

private theorem exists_nonnegative_rat_below (x : ℝ) (hx : 0 ≤ x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℚ, 0 ≤ r ∧ (r : ℝ) ≤ x ∧ (r = 0 ↔ x = 0) ∧
      |(r : ℝ) - x| < δ := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, le_rfl, by simp, by simp, by simpa using hδ⟩
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hlo : max 0 (x - δ) < x := max_lt hxpos (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hlo
  have hrpos : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hrlo
  have hrposq : (0 : ℚ) < r := by exact_mod_cast hrpos
  refine ⟨r, hrposq.le, hrhi.le,
    iff_of_false (ne_of_gt hrposq) hx0, ?_⟩
  have hrlo' : x - δ < r := lt_of_le_of_lt (le_max_right _ _) hrlo
  rw [abs_of_nonpos (sub_nonpos.mpr hrhi.le)]
  linarith

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem exists_rational_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : RationalLaw A,
      (∀ a, q.mass a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(q.mass a : ℝ) - p.mass a| < ε := by
  classical
  have hpivot : ∃ a, 0 < p.mass a := by
    by_contra h
    have hnonpos : ∀ a, p.mass a ≤ 0 :=
      fun a => le_of_not_gt (fun ha => h ⟨a, ha⟩)
    have hsum : (∑ a, p.mass a) ≤ 0 :=
      Finset.sum_nonpos (fun a _ => hnonpos a)
    rw [p.total] at hsum
    norm_num at hsum
  obtain ⟨a₀, ha₀⟩ := hpivot
  let δ : ℝ := ε / ((Fintype.card A : ℝ) + 1)
  have hcard : 0 ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (Fintype.card A : ℝ) + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * ((Fintype.card A : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hden)
  have hcardδ : 0 ≤ (Fintype.card A : ℝ) * δ := mul_nonneg hcard hδ.le
  have hδle : δ ≤ ε := by nlinarith
  choose r hrnonneg hrle hrzero hrclose using
    fun a => exists_nonnegative_rat_below (p.mass a) (p.nonneg a) δ hδ
  have hsum : (∑ a, (r a : ℝ)) ≤ 1 := by
    calc
      (∑ a, (r a : ℝ)) ≤ ∑ a, p.mass a :=
        Finset.sum_le_sum (fun a _ => hrle a)
      _ = 1 := p.total
  have hrest : 0 ≤ 1 - ∑ a, (r a : ℝ) := sub_nonneg.mpr hsum
  have hrestq : (0 : ℚ) ≤ 1 - ∑ a, r a := by exact_mod_cast hrest
  have hrest_le : 1 - ∑ a, (r a : ℝ) ≤ (Fintype.card A : ℝ) * δ := by
    calc
      1 - ∑ a, (r a : ℝ) = ∑ a, (p.mass a - (r a : ℝ)) := by
        rw [Finset.sum_sub_distrib, p.total]
      _ ≤ ∑ _a : A, δ := by
        apply Finset.sum_le_sum
        intro a _
        have h := (abs_lt.mp (hrclose a)).1
        linarith
      _ = (Fintype.card A : ℝ) * δ := by simp
  let q : RationalLaw A :=
    { mass := fun a => r a + if a = a₀ then 1 - ∑ b, r b else 0
      nonneg := by
        intro a
        apply add_nonneg (hrnonneg a)
        split_ifs
        · exact hrestq
        · exact le_rfl
      total := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring }
  refine ⟨q, ?_, ?_⟩
  · intro a
    by_cases ha : a = a₀
    · subst a
      have hrpos : 0 < r a₀ :=
        lt_of_le_of_ne (hrnonneg a₀) (Ne.symm (fun hz => (ne_of_gt ha₀) ((hrzero a₀).mp hz)))
      have hqpos : 0 < q.mass a₀ := by
        dsimp [q]
        simp only [ite_true]
        linarith
      exact iff_of_false (ne_of_gt hqpos) (ne_of_gt ha₀)
    · simpa only [q, ite_eq_right ha, add_zero] using hrzero a
  · intro a
    by_cases ha : a = a₀
    · have hqcast : (q.mass a : ℝ) =
          (r a : ℝ) + (1 - ∑ b, (r b : ℝ)) := by
        simp [q, ha]
      rw [hqcast]
      have habs : |(r a : ℝ) + (1 - ∑ b, (r b : ℝ)) - p.mass a| ≤
          |(r a : ℝ) - p.mass a| + (1 - ∑ b, (r b : ℝ)) := by
        calc
          _ = |((r a : ℝ) - p.mass a) + (1 - ∑ b, (r b : ℝ))| := by
            congr 1
            ring
          _ ≤ |(r a : ℝ) - p.mass a| + |1 - ∑ b, (r b : ℝ)| := abs_add_le _ _
          _ = _ := by rw [abs_of_nonneg hrest]
      have hclose := hrclose a
      nlinarith
    · simpa only [q, ite_eq_right ha, add_zero] using
        lt_of_lt_of_le (hrclose a) hδle

theorem exists_exact_type_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : A → ℕ,
      (∑ a, counts a) = D ∧
      (∀ a, counts a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(counts a : ℝ) / (D : ℝ) - p.mass a| < ε := by
  obtain ⟨q, hsupport, hclose⟩ := p.exists_rational_approximation ε hε
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := q.exists_exact_counts
  refine ⟨D, hD, counts, hsum, ?_, ?_⟩
  · intro a
    exact (q.exact_counts_zero_iff hD hcounts a).trans (hsupport a)
  · intro a
    rw [q.exact_counts_real_mass hD hcounts a, RationalLaw.toFiniteLaw_mass]
    exact hclose a

end FiniteLaw

end MatrixMultiplication.Foundation

end OAI

end FlattenModule090
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexRationalTypes -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting -/
section FlattenModule091




namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

def wordPopulation (w : I → A) (a : A) : ℕ := Fintype.card {i // w i = a}

omit [DecidableEq I] in
theorem wordPopulation_sum (w : I → A) :
    ∑ a, wordPopulation w a = Fintype.card I := by
  simpa [wordPopulation] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)

omit [Fintype A] [DecidableEq I] in
theorem wordPopulation_reindex (w : I → A) (e : J ≃ I) (a : A) :
    wordPopulation (w ∘ e) a = wordPopulation w a :=
  Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

abbrev ExactWords (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, wordPopulation w a = counts a}

theorem wordPopulation_sigma_fst (counts : A → ℕ) (a : A) :
    wordPopulation (fun i : Σ b, Fin (counts b) => i.1) a = counts a := by
  let e : {i : Σ b, Fin (counts b) // i.1 = a} ≃ Fin (counts a) :=
    { toFun := fun i => i.property ▸ i.val.2
      invFun := fun i => ⟨⟨a, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨b, i⟩, h⟩
        cases h
        rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem exactWords_nonempty (counts : A → ℕ) : Nonempty (ExactWords counts) := by
  classical
  let e : Fin (∑ a, counts a) ≃ (Σ a, Fin (counts a)) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, ?_⟩⟩
  intro a
  rw [wordPopulation_reindex, wordPopulation_sigma_fst]

omit [Fintype A] [DecidableEq I] in
theorem samePopulation_iff_permutation (w v : I → A) :
    (∀ a, wordPopulation v a = wordPopulation w a) ↔
      ∃ e : Equiv.Perm I, w ∘ e = v := by
  classical
  constructor
  · intro h
    let es : ∀ a, {i // v i = a} ≃ {i // w i = a} :=
      fun a => Fintype.equivOfCardEq (h a)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨e, rfl⟩ a
    exact wordPopulation_reindex w e a

theorem samePopulation_card_mul (w : I → A) :
    Fintype.card {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} *
      (∏ a, (wordPopulation w a).factorial) = (Fintype.card I).factorial := by
  classical
  let G := DomMulAct (Equiv.Perm I)
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  let eOrbit : {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} ≃
      MulAction.orbit G w :=
    Equiv.subtypeEquivRight fun v => by
      rw [samePopulation_iff_permutation, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨DomMulAct.mk e, he⟩
      · rintro ⟨g, hg⟩
        exact ⟨DomMulAct.mk.symm g, hg⟩
  let eStab : MulAction.stabilizer G w ≃
      {e : Equiv.Perm I // w ∘ e = w} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have hstab : Fintype.card (MulAction.stabilizer G w) =
      ∏ a, (wordPopulation w a).factorial := by
    rw [Fintype.card_congr eStab]
    exact DomMulAct.stabilizer_card w
  have hgroup : Fintype.card G = (Fintype.card I).factorial :=
    (Fintype.card_congr DomMulAct.mk.symm).trans Fintype.card_perm
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [← Fintype.card_congr eOrbit, hstab, hgroup] at h
  exact h

theorem exactWords_card (counts : A → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by
  classical
  obtain ⟨w⟩ := exactWords_nonempty counts
  let e : ExactWords counts ≃
      {v : Fin (∑ a, counts a) → A // ∀ a,
        wordPopulation v a = wordPopulation w.val a} :=
    Equiv.subtypeEquivRight fun v => by simp only [w.property]
  have h := samePopulation_card_mul w.val
  rw [← Fintype.card_congr e] at h
  simp only [w.property, Fintype.card_fin] at h
  exact Nat.eq_div_of_mul_eq_left
    (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]
  exact Nat.multinomial_pos Finset.univ counts

theorem exactWords_card_le (counts : A → ℕ) :
    Fintype.card (ExactWords counts) ≤ (Fintype.card A) ^ (∑ a, counts a) := by
  classical
  calc
    Fintype.card (ExactWords counts) ≤
        Fintype.card (Fin (∑ a, counts a) → A) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

end MatrixMultiplication.Foundation

end OAI

end FlattenModule091
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy -/
section FlattenModule092









namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (s := Finset.univ) (f := fun a => (Nat.factorial (counts a) : ℝ))
      (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem log_multinomial_eq_entropy_add_remainder (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  rw [log_multinomial_eq_main_add_remainder, finiteEntropy_nat_normalize counts hD,
    mul_sub, mul_div_cancel₀ _ hD']

theorem log_multinomial_sub_entropy_eq_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  by_cases hD : 0 < ∑ a, counts a
  · rw [log_multinomial_eq_entropy_add_remainder counts hD]
    ring
  · have hzero : (∑ a, counts a) = 0 := Nat.eq_zero_of_not_pos hD
    have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, Nat.multinomial]

theorem abs_log_multinomial_sub_entropy_le (counts : A → ℕ) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  rw [log_multinomial_sub_entropy_eq_remainder]
  have hsum_nonneg : 0 ≤ ∑ a, factorialLogRemainder (counts a) :=
    Finset.sum_nonneg (fun a _ => factorialLogRemainder_nonneg (counts a))
  have heach (a : A) : factorialLogRemainder (counts a) ≤
      1 + Real.log ((∑ b, counts b) + 1 : ℕ) := by
    refine (factorialLogRemainder_le_one_add_log (counts a)).trans ?_
    apply add_le_add_right
    apply Real.log_le_log
    · positivity
    · have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      exact_mod_cast Nat.add_le_add_right hle 1
  calc
    |factorialLogRemainder (∑ a, counts a) - ∑ a, factorialLogRemainder (counts a)| ≤
        |factorialLogRemainder (∑ a, counts a)| +
          |∑ a, factorialLogRemainder (counts a)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (factorialLogRemainder (∑ a, counts a))
          (-(∑ a, factorialLogRemainder (counts a)))
    _ = factorialLogRemainder (∑ a, counts a) +
        ∑ a, factorialLogRemainder (counts a) := by
      rw [abs_of_nonneg (factorialLogRemainder_nonneg _), abs_of_nonneg hsum_nonneg]
    _ ≤ (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) +
        ∑ _a : A, (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) :=
      add_le_add (factorialLogRemainder_le_one_add_log _)
        (Finset.sum_le_sum (fun a _ => heach a))
    _ = ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem abs_log_multinomial_div_sub_entropy_le (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  calc
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| =
        |(Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))) /
              (∑ a, counts a : ℕ)| := by
      rw [sub_div, mul_div_cancel_left₀ _ hD'.ne']
    _ = |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| /
              (∑ a, counts a : ℕ) := by
      rw [abs_div, abs_of_pos hD']
    _ ≤ ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (abs_log_multinomial_sub_entropy_le counts) hD'.le

private theorem tendsto_one_add_log_succ_div :
    Tendsto (fun n : ℕ => (1 + Real.log (n + 1 : ℕ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hshift := Real.tendsto_log_nat_add_one_sub_log.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => (1 : ℝ) / n +
        ((Real.log ((n : ℝ) + 1) - Real.log n) / n + Real.log n / n))
      atTop (𝓝 0) := by
    simpa using hconstant.add (hshift.add hlog)
  apply hsum.congr
  intro n
  push_cast
  ring

theorem tendsto_log_multinomial_div_sub_entropy {I : Type*} {l : Filter I}
    (counts : I → A → ℕ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
          (∑ a, counts i a : ℕ) -
        finiteEntropy (fun a => (counts i a : ℝ) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
  have hbound : Tendsto
      (fun i => ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts i a) + 1 : ℕ)) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
    simpa using (tendsto_one_add_log_succ_div.comp htotal).const_mul
      ((Fintype.card A : ℝ) + 1)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [htotal.eventually (eventually_gt_atTop (0 : ℕ))] with i hi
  simpa only [Real.norm_eq_abs] using
    abs_log_multinomial_div_sub_entropy_le (counts i) hi

theorem tendsto_log_multinomial_of_empirical_tendsto {I : Type*} {l : Filter I}
    (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  have herror := tendsto_log_multinomial_div_sub_entropy counts htotal
  have hentropy := tendsto_finiteEntropy_of_tendsto hmass
  simpa only [zero_add, sub_add_cancel] using herror.add hentropy

private theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      (x * Real.log x) * y + x * (y * Real.log y) := by
  calc
    (x * y) * Real.log (x * y) = -entropyTerm (x * y) := by
      simp [entropyTerm]
    _ = -(y * entropyTerm x + x * entropyTerm y) := by
      rw [entropyTerm_mul]
    _ = (x * Real.log x) * y + x * (y * Real.log y) := by
      unfold entropyTerm
      ring

theorem log_multinomial_mul_eq (counts : A → ℕ) (t : ℕ) :
    Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) =
      (t : ℝ) *
          ((∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
            ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (t * ∑ a, counts a) -
        ∑ a, factorialLogRemainder (t * counts a) := by
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a :=
    (Finset.mul_sum Finset.univ counts t).symm
  have hlogs :
      (∑ a, ((t : ℝ) * counts a) * Real.log ((t : ℝ) * counts a)) =
        ((t : ℝ) * Real.log t) * (∑ a, counts a : ℕ) +
          (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ) := by
    simp only [mul_log_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Nat.cast_sum]
  rw [log_multinomial_eq_main_add_remainder, hsum]
  simp only [Nat.cast_mul]
  rw [mul_log_mul, hlogs]
  ring

theorem tendsto_log_multinomial_mul (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  have hsum :
      Tendsto (fun t : ℕ => ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun a _ => tendsto_factorialLogRemainder_mul_div (counts a))
  have herror : Tendsto
      (fun t : ℕ =>
        (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
          ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
            (∑ a, counts a : ℕ)) atTop (𝓝 0) := by
    simpa using ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub
      hsum).div_const (∑ a, counts a : ℕ)
  have hlimit : Tendsto
      (fun t : ℕ =>
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
          (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
            ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
              (∑ a, counts a : ℕ))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hlimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  rw [log_multinomial_mul_eq, finiteEntropy_nat_normalize counts hD,
    ← Finset.sum_div]
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  field_simp [ht', hD']
  ring

theorem tendsto_log_multinomial_repetitions {I : Type*} {l : Filter I}
    (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (repetitions : I → ℕ) (hrep : Tendsto repetitions l atTop) :
    Tendsto
      (fun i =>
        Real.log (Nat.multinomial Finset.univ
          (fun a => repetitions i * counts a) : ℝ) /
            ((repetitions i : ℝ) * (∑ a, counts a : ℕ)))
      l (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  exact (tendsto_log_multinomial_mul counts hD).comp hrep

theorem tendsto_log_exactWords_card_mul [DecidableEq A] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [exactWords_card] using tendsto_log_multinomial_mul counts hD

theorem abs_log_exactWords_card_sub_entropy_le [DecidableEq A] (counts : A → ℕ) :
    |Real.log (Fintype.card (ExactWords counts) : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  simpa only [exactWords_card] using abs_log_multinomial_sub_entropy_le counts

theorem log_card_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) ≤
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hcard := Fintype.card_le_of_injective label hinj
  have hlog : Real.log (Fintype.card O : ℝ) ≤
      Real.log (Fintype.card (ExactWords counts) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr Fintype.card_pos) (by exact_mod_cast hcard)
  have herror := (abs_le.mp (abs_log_exactWords_card_sub_entropy_le counts)).2
  linarith

theorem log_card_div_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) / (∑ a, counts a : ℕ) ≤
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  have h := div_le_div_of_nonneg_right
    (log_card_le_entropy_of_injective_exactWords counts label hinj) hD'.le
  rw [add_div, mul_div_cancel_left₀ _ hD'.ne', mul_div_assoc] at h
  exact h

theorem tendsto_log_exactWords_card_of_empirical_tendsto [DecidableEq A]
    {I : Type*} {l : Filter I} (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Fintype.card (ExactWords (counts i)) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  simpa only [exactWords_card] using
    tendsto_log_multinomial_of_empirical_tendsto counts p htotal hmass

namespace RationalLaw

theorem exists_exactWords_entropy_limit [DecidableEq A] (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      (∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a) ∧
      Tendsto
        (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) := by
  obtain ⟨counts, hD, hmass⟩ := p.exists_type_representation
  refine ⟨counts, hD, hmass, ?_⟩
  have hfun : (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      p.toFiniteLaw.mass := funext hmass
  rw [← hfun]
  exact tendsto_log_exactWords_card_mul counts hD

end RationalLaw

end MatrixMultiplication.Foundation

end OAI

end FlattenModule092
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexSeparationAsymptotics -/
section FlattenModule093











namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Separation

open Filter

private theorem scale_exists (K : ℕ) : ∃ n : ℕ, K ≤ 2 ^ (n ^ 2) := by
  refine ⟨K + 1, ?_⟩
  have hK : K < 2 ^ K := Nat.lt_pow_self (by decide : 1 < 2)
  exact hK.le.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

noncomputable def gridScale (K : ℕ) : ℕ := Nat.find (scale_exists K)

theorem population_le_scale (K : ℕ) : K ≤ 2 ^ ((gridScale K) ^ 2) :=
  Nat.find_spec (scale_exists K)

theorem previous_scale_lt_population {K : ℕ} (hn : 0 < gridScale K) :
    2 ^ ((gridScale K - 1) ^ 2) < K := by
  exact lt_of_not_ge (Nat.find_min (scale_exists K) (Nat.sub_lt hn (by decide)))

theorem scale_pos {K : ℕ} (hK : 1 < K) : 0 < gridScale K := by
  have h := population_le_scale K
  by_contra hn
  have hz : gridScale K = 0 := Nat.eq_zero_of_not_pos hn
  simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at h
  exact (not_le_of_gt hK) h

theorem scale_gt_of_population_gt {K n : ℕ} (hK : 2 ^ (n ^ 2) < K) :
    n < gridScale K := by
  by_contra hn
  have hscale : gridScale K ≤ n := Nat.le_of_not_gt hn
  have hp : 2 ^ ((gridScale K) ^ 2) ≤ 2 ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hscale 2)
  exact (not_le_of_gt hK) ((population_le_scale K).trans hp)

theorem gridScale_monotone : Monotone gridScale := by
  intro K L hKL
  exact Nat.find_min' (scale_exists K) (hKL.trans (population_le_scale L))

def gridDimension (K : ℕ) : ℕ := gridScale K + 4

def gridWidth (K : ℕ) : ℕ := 2 ^ (gridScale K + 2)

def gridGroupOrder (K : ℕ) : ℕ := (4 * gridWidth K) ^ gridDimension K

theorem gridDimension_pos (K : ℕ) : 0 < gridDimension K := by
  simp [gridDimension]

theorem gridWidth_ge_two (K : ℕ) : 2 ≤ gridWidth K := by
  simpa only [gridWidth, pow_one] using
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ gridScale K + 2))

private theorem dimension_le_power (n : ℕ) : n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 2 ^ (n + 2 + 1) = 2 ^ (n + 2) * 2 := pow_succ _ _
    have he : n + 1 + 2 = n + 2 + 1 := by omega
    rw [he, hp]
    omega

theorem grid_population_bound (K : ℕ) :
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
      gridWidth K ^ gridDimension K := by
  let n := gridScale K
  have hd : n + 4 ≤ 2 ^ (n + 2) := dimension_le_power n
  have hq : 0 < 2 ^ (n + 2) := by positivity
  have hcolorpos : 0 < (n + 4) * (2 ^ (n + 2)) ^ 2 := by positivity
  have hcolor : (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤ 2 ^ (3 * n + 7) := by
    calc
      (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤
          2 * ((n + 4) * (2 ^ (n + 2)) ^ 2) := by nlinarith
      _ ≤ 2 * (2 ^ (n + 2) * (2 ^ (n + 2)) ^ 2) := by gcongr
      _ = 2 ^ (3 * n + 7) := by
        rw [← pow_mul, ← pow_add, ← pow_succ']
        congr 1
        omega
  calc
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
        2 ^ (3 * n + 7) * 2 ^ (n ^ 2) :=
      Nat.mul_le_mul hcolor (population_le_scale K)
    _ = 2 ^ (3 * n + 7 + n ^ 2) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((n + 2) * (n + 4)) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ = gridWidth K ^ gridDimension K := by
      simp only [gridWidth, gridDimension, n, pow_mul]

theorem gridGroupOrder_eq (K : ℕ) :
    gridGroupOrder K = 2 ^ ((gridScale K + 4) ^ 2) := by
  unfold gridGroupOrder gridWidth gridDimension
  have hb : 4 * 2 ^ (gridScale K + 2) = 2 ^ (gridScale K + 4) := by
    calc
      4 * 2 ^ (gridScale K + 2) = 2 ^ 2 * 2 ^ (gridScale K + 2) := by norm_num
      _ = 2 ^ (2 + (gridScale K + 2)) := (pow_add _ _ _).symm
      _ = 2 ^ (gridScale K + 4) := by congr 1; omega
  rw [hb, ← pow_mul, pow_two]

theorem gridGroupOrder_pos (K : ℕ) : 0 < gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  positivity

theorem population_le_gridGroupOrder (K : ℕ) : K ≤ gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  exact (population_le_scale K).trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_left (Nat.le_add_right (gridScale K) 4) 2))

theorem gridGroupOrder_monotone : Monotone gridGroupOrder := by
  intro K L hKL
  rw [gridGroupOrder_eq, gridGroupOrder_eq]
  exact Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (gridScale_monotone hKL) 4) 2)

theorem asymptotic_grid_tags_slices (K : ℕ) :
    ∃ tags : Finset (Grid (gridDimension K) (gridWidth K)), tags.card = K ∧
      (∃ radius : Fin (gridDimension K * gridWidth K ^ 2 + 1),
        ∀ t ∈ tags, normColor t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset (Grid (gridDimension K) (gridWidth K)),
        slice.card = K ∧ ∃ level : Fin (gridDimension K * gridWidth K ^ 2 + 1),
          ∀ u ∈ slice, dotColor t u = level :=
  grid_tags_slices (grid_population_bound K) (grid_population_bound K)

theorem log_gridGroupOrder (K : ℕ) :
    Real.log (gridGroupOrder K : ℝ) = ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := by
  rw [gridGroupOrder_eq, Nat.cast_pow, Real.log_pow]
  norm_cast

theorem log_population_le_log_gridGroupOrder {K : ℕ} (hK : 0 < K) :
    Real.log (K : ℝ) ≤ Real.log (gridGroupOrder K : ℝ) := by
  exact Real.log_le_log (by exact_mod_cast hK)
    (by exact_mod_cast population_le_gridGroupOrder K)

theorem previous_scale_log_lt {K : ℕ} (hK : 1 < K) :
    ((gridScale K : ℝ) - 1) ^ 2 * Real.log 2 < Real.log (K : ℝ) := by
  have hn : 1 ≤ gridScale K := scale_pos hK
  have hp : (0 : ℝ) < (2 : ℝ) ^ ((gridScale K - 1) ^ 2) := by positivity
  have hc : (2 : ℝ) ^ ((gridScale K - 1) ^ 2) < (K : ℝ) := by
    exact_mod_cast previous_scale_lt_population (scale_pos hK)
  have h := Real.log_lt_log hp hc
  simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_sub hn, Nat.cast_one] using h

theorem log_gridGroupOrder_le_of_scale {K : ℕ} {ε : ℝ}
    (hK : 1 < K) (hε : 0 ≤ ε)
    (hscale : 10 * (gridScale K : ℝ) + 15 ≤
      ε * ((gridScale K : ℝ) - 1) ^ 2) :
    Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly : ((gridScale K : ℝ) + 4) ^ 2 ≤
      (1 + ε) * ((gridScale K : ℝ) - 1) ^ 2 := by nlinarith
  calc
    Real.log (gridGroupOrder K : ℝ) =
        ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := log_gridGroupOrder K
    _ ≤ ((1 + ε) * ((gridScale K : ℝ) - 1) ^ 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hpoly hlog2.le
    _ = (1 + ε) * (((gridScale K : ℝ) - 1) ^ 2 * Real.log 2) := by ring
    _ ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_le_mul_of_nonneg_left (previous_scale_log_lt hK).le (by positivity)

private theorem scale_error_bound {n ε : ℝ} (hn : 2 ≤ n) (hε : 0 ≤ ε)
    (hlarge : 72 ≤ ε * n) : 10 * n + 15 ≤ ε * (n - 1) ^ 2 := by
  have hsq : n ^ 2 ≤ 4 * (n - 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hε
  have hlarge' := mul_le_mul_of_nonneg_right hlarge (by linarith : 0 ≤ n)
  nlinarith

theorem eventually_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (max 2 (72 / ε))
  refine eventually_atTop.2 ⟨2 ^ (m ^ 2) + 1, ?_⟩
  intro K hK
  have hKm : 2 ^ (m ^ 2) < K := by omega
  have hn := scale_gt_of_population_gt hKm
  have hnR : (m : ℝ) < (gridScale K : ℝ) := by exact_mod_cast hn
  have hm2 : 2 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmε : 72 / ε < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hnε : 72 ≤ ε * (gridScale K : ℝ) := by
    have hdiv : 72 / ε < (gridScale K : ℝ) := hmε.trans hnR
    have hmul := (div_lt_iff₀ hε).1 hdiv
    nlinarith
  have hKone : 1 < K := by
    have hp : 1 ≤ 2 ^ (m ^ 2) := Nat.one_le_pow _ _ (by decide)
    omega
  exact log_gridGroupOrder_le_of_scale hKone hε.le
    (scale_error_bound (by linarith) hε.le hnε)

theorem uniform_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) + C := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (eventually_log_gridGroupOrder_le hε)
  refine ⟨Real.log (gridGroupOrder K₀ : ℝ), Real.log_natCast_nonneg _, ?_⟩
  intro K
  by_cases hK : K₀ ≤ K
  · exact (hK₀ K hK).trans (le_add_of_nonneg_right (Real.log_natCast_nonneg _))
  · have horder : gridGroupOrder K ≤ gridGroupOrder K₀ :=
      gridGroupOrder_monotone (Nat.le_of_lt (Nat.lt_of_not_ge hK))
    have hpos : (0 : ℝ) < (gridGroupOrder K : ℝ) := by
      rw [gridGroupOrder_eq, Nat.cast_pow]
      positivity
    have hcast : (gridGroupOrder K : ℝ) ≤ (gridGroupOrder K₀ : ℝ) := by
      exact_mod_cast horder
    have hlog := Real.log_le_log hpos hcast
    have hnonneg : 0 ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_nonneg (by linarith) (Real.log_natCast_nonneg K)
    linarith

theorem tendsto_log_gridGroupOrder_div_log_population :
    Tendsto (fun K : ℕ => Real.log (gridGroupOrder K : ℝ) / Real.log (K : ℝ))
      atTop (nhds 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    refine eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hKone : 1 < K := by omega
    have hlog : 0 < Real.log (K : ℝ) :=
      Real.log_pos (by exact_mod_cast hKone)
    have hle := log_population_le_log_gridGroupOrder (by omega : 0 < K)
    exact ha.trans_le ((le_div_iff₀ hlog).2 (by simpa using hle))
  · intro b hb
    have he : 0 < (b - 1) / 2 := by linarith
    filter_upwards [eventually_log_gridGroupOrder_le he,
      (eventually_atTop.2 ⟨2, fun K (hK : 2 ≤ K) => hK⟩)] with K hcost hK
    have hlog : 0 < Real.log (K : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < K by omega))
    have hratio : Real.log (gridGroupOrder K : ℝ) / Real.log (K : ℝ) ≤
        1 + (b - 1) / 2 := (div_le_iff₀ hlog).2 hcost
    linarith

theorem tendsto_log_gridGroupOrder_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ N, 0 < K N) (hH : 0 ≤ H)
    (hpop : Tendsto (fun N => Real.log (K N : ℝ) / (N : ℝ)) atTop (nhds H)) :
    Tendsto (fun N => Real.log (gridGroupOrder (K N) : ℝ) / (N : ℝ))
      atTop (nhds H) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [(tendsto_order.1 hpop).1 a ha,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N haN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact haN.trans_le (div_le_div_of_nonneg_right
      (log_population_le_log_gridGroupOrder (hK N)) hNpos.le)
  · intro b hb
    let ε := (b - H) / (2 * (H + 1))
    have hdenom : 0 < 2 * (H + 1) := by linarith
    have hε : 0 < ε := div_pos (by linarith) hdenom
    obtain ⟨C, hC, hbound⟩ := uniform_log_gridGroupOrder_le hε
    have hεeq : ε * (2 * (H + 1)) = b - H := div_mul_cancel₀ _ hdenom.ne'
    have hlimitlt : (1 + ε) * H < b := by nlinarith
    have hconstant : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hupper : Tendsto
        (fun N : ℕ => (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ))
        atTop (nhds ((1 + ε) * H)) := by
      simpa using (hpop.const_mul (1 + ε)).add hconstant
    filter_upwards [(tendsto_order.1 hupper).2 b hlimitlt,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N hbN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hle := div_le_div_of_nonneg_right (hbound (K N)) hNpos.le
    have heq : ((1 + ε) * Real.log (K N : ℝ) + C) / (N : ℝ) =
        (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ) := by ring
    rw [heq] at hle
    exact hle.trans_lt hbN

theorem log_nat_prod {I : Type*} (s : Finset I) (a : I → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Real.log ((∏ i ∈ s, a i : ℕ) : ℝ) = ∑ i ∈ s, Real.log (a i : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (s := s) (f := fun i => (a i : ℝ)) fun i hi =>
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha i hi))

theorem tendsto_log_nat_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, K i N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  have hsum := tendsto_finsetSum s hpop
  apply hsum.congr
  intro N
  rw [log_nat_prod s (fun i => K i N) (fun i hi => hK i hi N)]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem tendsto_log_gridGroupOrder_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, gridGroupOrder (K i N) : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  exact tendsto_log_nat_prod_div_nat s (fun i hi N => gridGroupOrder_pos (K i N))
    (fun i hi => tendsto_log_gridGroupOrder_div_nat (hK i hi) (hH i hi) (hpop i hi))

theorem tendsto_log_nat_weighted_prod_div_nat {I : Type*} (s : Finset I) (w : I → ℕ)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, (K i N) ^ w i : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, (w i : ℝ) * H i)) := by
  apply tendsto_log_nat_prod_div_nat s
  · intro i hi N
    exact pow_pos (hK i hi N) _
  · intro i hi
    simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using
      (hpop i hi).const_mul (w i : ℝ)

theorem tendsto_log_gridGroupOrder_weighted_prod_div_nat {I : Type*}
    (s : Finset I) (w : I → ℕ) {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto
      (fun N => Real.log ((∏ i ∈ s, gridGroupOrder (K i N) ^ w i : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, (w i : ℝ) * H i)) := by
  exact tendsto_log_nat_weighted_prod_div_nat s w
    (fun i hi N => gridGroupOrder_pos (K i N))
    (fun i hi => tendsto_log_gridGroupOrder_div_nat (hK i hi) (hH i hi) (hpop i hi))

end MatrixMultiplication.Foundation.Separation

end

end OAI

end FlattenModule093
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexSeparationAsymptotics -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexAuxiliarySeparation -/
section FlattenModule094


namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

instance auxiliarySeparation_modulus_neZero (K : ℕ) :
    NeZero (4 * Separation.gridWidth K) :=
  ⟨Nat.mul_ne_zero (by decide)
    (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two K)))⟩

section AuxiliarySeparation

variable {X Y Z S : Type*} [Fintype S] [DecidableEq S]

theorem auxiliary_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin (Fintype.card S)) lx T ∈ Tensor.restrictionOrbit
      (Tensor.product T (groupTensor (Separation.AuxiliaryGroup
        (Separation.gridDimension (Fintype.card S))
        (Separation.gridWidth (Fintype.card S))))) := by
  exact finite_grid_separation_mem_restrictionOrbit T lx ly
    (Separation.grid_population_bound (Fintype.card S))
    (Separation.grid_population_bound (Fintype.card S)) hlabels

theorem auxiliary_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (separatedTensor (U := Fin (Fintype.card S)) lx T)
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact finite_grid_separation_rankAtMost T lx ly
    (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two (Fintype.card S)))
    (Separation.grid_population_bound (Fintype.card S))
    (Separation.grid_population_bound (Fintype.card S)) hT hlabels

theorem auxiliary_separation_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost (separatedTensor (U := Fin (Fintype.card S)) lx T)
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact finite_grid_separation_borderRankAtMost T lx ly
    (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two (Fintype.card S)))
    (Separation.grid_population_bound (Fintype.card S))
    (Separation.grid_population_bound (Fintype.card S)) hT hlabels

theorem auxiliary_separation_directSum_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s)
        (Tensor.dotPairing (Fin (Fintype.card S)))))
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact separatedTensor_fiber_directSum_rankAtMost T lx ly hlabels
    (auxiliary_separation_rankAtMost T lx ly hT hlabels)

theorem auxiliary_separation_directSum_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s)
        (Tensor.dotPairing (Fin (Fintype.card S)))))
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact separatedTensor_fiber_directSum_borderRankAtMost T lx ly hlabels
    (auxiliary_separation_borderRankAtMost T lx ly hT hlabels)

end AuxiliarySeparation

theorem auxiliary_separation_logarithmic_cost :
    Filter.Tendsto
      (fun K : ℕ => Real.log (Separation.gridGroupOrder K : ℝ) / Real.log (K : ℝ))
      Filter.atTop (nhds 1) :=
  Separation.tendsto_log_gridGroupOrder_div_log_population

end MatrixMultiplication.Foundation

end OAI

end FlattenModule094
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexAuxiliarySeparation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy -/
section FlattenModule095

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

noncomputable section

namespace FiniteLaw

theorem map_mass_mul_conditional_map {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (f : A → B) (g : A → C) (b : B) (c : C) :
    (p.map f).mass b * ((p.conditional f b).map g).mass c =
      (p.map (fun a => (f a, g a))).mass (b, c) := by
  classical
  rw [map_mass (p.conditional f b) g c, Finset.mul_sum,
    map_mass p (fun a => (f a, g a)) (b, c)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hgc : g a = c
  · rw [ite_eq_left hgc, map_mass_mul_conditional]
    simp only [Prod.mk.injEq, hgc, and_true]
  · rw [ite_eq_right hgc, mul_zero]
    have hpair : (f a, g a) ≠ (b, c) :=
      fun he => hgc (congrArg Prod.snd he)
    rw [ite_eq_right hpair]

end FiniteLaw

def LabelRecord (Label : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => LabelRecord Label n × Label n

instance labelRecordFintype (Label : ℕ → Type u) [∀ n, Fintype (Label n)] :
    (n : ℕ) → Fintype (LabelRecord Label n)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | n + 1 => by
      letI := labelRecordFintype Label n
      change Fintype (LabelRecord Label n × Label n)
      infer_instance

def labelRecordOf {A : Type v} {Label : ℕ → Type u}
    (labels : ∀ n, A → Label n) : (n : ℕ) → A → LabelRecord Label n
  | 0, _ => PUnit.unit
  | n + 1, a => (labelRecordOf labels n a, labels n a)

structure FiniteLabelHierarchy (Label : ℕ → Type u) [∀ n, Fintype (Label n)]
    (depth : ℕ) where
  conditional : ∀ n, n < depth → LabelRecord Label n → FiniteLaw (Label n)

namespace FiniteLabelHierarchy

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)] {depth : ℕ}

def prefixLaw (h : FiniteLabelHierarchy Label depth) :
    (n : ℕ) → n ≤ depth → FiniteLaw (LabelRecord Label n)
  | 0, _ =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := by
          classical
          refine Finset.sum_eq_single_of_mem (PUnit.unit : LabelRecord Label 0)
            (Finset.mem_univ _) ?_
          intro r _ hr
          cases r
          exact (hr rfl).elim }
  | n + 1, hn =>
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn))

@[simp] theorem prefixLaw_zero_mass (h : FiniteLabelHierarchy Label depth)
    (hn : 0 ≤ depth) (r : LabelRecord Label 0) :
    (h.prefixLaw 0 hn).mass r = 1 := rfl

@[simp] theorem prefixLaw_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    h.prefixLaw (n + 1) hn =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn)) := rfl

@[simp] theorem prefixLaw_succ_mass (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) (r : LabelRecord Label n) (s : Label n) :
    (h.prefixLaw (n + 1) hn).mass (r, s) =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).mass r *
        (h.conditional n (Nat.lt_of_succ_le hn) r).mass s := rfl

def refinementEntropy (h : FiniteLabelHierarchy Label depth) (n : ℕ) : ℝ :=
  if hn : n < depth then
    ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
      finiteEntropy (h.conditional n hn r).mass
  else 0

theorem refinementEntropy_eq (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n < depth) :
    h.refinementEntropy n =
      ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
        finiteEntropy (h.conditional n hn r).mass := by
  simp only [refinementEntropy, dite_eq_left hn]

@[simp] theorem refinementEntropy_eq_zero_of_le
    (h : FiniteLabelHierarchy Label depth) {n : ℕ} (hn : depth ≤ n) :
    h.refinementEntropy n = 0 := by
  simp only [refinementEntropy, dite_eq_right (Nat.not_lt.mpr hn)]

theorem zero_prefix_contribution (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n < depth) (r : LabelRecord Label n)
    (hr : (h.prefixLaw n (Nat.le_of_lt hn)).mass r = 0) :
    (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
      finiteEntropy (h.conditional n hn r).mass = 0 := by
  rw [hr, zero_mul]

theorem prefixLaw_entropy_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    finiteEntropy (h.prefixLaw (n + 1) hn).mass =
      finiteEntropy (h.prefixLaw n (Nat.le_of_succ_le hn)).mass +
        h.refinementEntropy n := by
  rw [refinementEntropy_eq h n (Nat.lt_of_succ_le hn)]
  exact FiniteLaw.joint_entropy (h.prefixLaw n (Nat.le_of_succ_le hn))
    (h.conditional n (Nat.lt_of_succ_le hn))

theorem prefixLaw_entropy (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n ≤ depth) :
    finiteEntropy (h.prefixLaw n hn).mass =
      ∑ j ∈ Finset.range n, h.refinementEntropy j := by
  induction n with
  | zero =>
      simp [prefixLaw, finiteEntropy, entropyTerm, LabelRecord]
  | succ n ih =>
      rw [prefixLaw_entropy_succ h n hn,
        ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]

def recordLaw (h : FiniteLabelHierarchy Label depth) :
    FiniteLaw (LabelRecord Label depth) := h.prefixLaw depth le_rfl

theorem recordLaw_entropy (h : FiniteLabelHierarchy Label depth) :
    finiteEntropy h.recordLaw.mass =
      ∑ j ∈ Finset.range depth, h.refinementEntropy j :=
  h.prefixLaw_entropy depth le_rfl

theorem refinementEntropy_sum_of_injective_record
    {A : Type v} [Fintype A] (h : FiniteLabelHierarchy Label depth)
    (p : FiniteLaw A) (record : A → LabelRecord Label depth)
    (hinjective : Function.Injective record)
    (hmass : h.recordLaw.mass = (p.map record).mass) :
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) = finiteEntropy p.mass := by
  calc
    (∑ j ∈ Finset.range depth, h.refinementEntropy j) =
        finiteEntropy h.recordLaw.mass := h.recordLaw_entropy.symm
    _ = finiteEntropy (p.map record).mass := congrArg finiteEntropy hmass
    _ = finiteEntropy p.mass := p.map_entropy_of_injective record hinjective

def ofLawLabels {A : Type v} [Fintype A] (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ) : FiniteLabelHierarchy Label depth where
  conditional n _ r := (p.conditional (labelRecordOf labels n) r).map (labels n)

theorem ofLawLabels_prefixLaw_mass {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n ≤ depth) :
    ((ofLawLabels p labels depth).prefixLaw n hn).mass =
      (p.map (labelRecordOf labels n)).mass := by
  classical
  induction n with
  | zero =>
      funext r
      rw [prefixLaw_zero_mass, FiniteLaw.map_mass]
      refine p.total.symm.trans ?_
      apply Finset.sum_congr rfl
      intro a _
      rw [ite_eq_left (show labelRecordOf labels 0 a = r by cases r; rfl)]
  | succ n ih =>
      funext rs
      rcases rs with ⟨r, s⟩
      rw [prefixLaw_succ_mass]
      change ((ofLawLabels p labels depth).prefixLaw n
          (Nat.le_of_succ_le hn)).mass r *
        ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass s =
          (p.map (labelRecordOf labels (n + 1))).mass (r, s)
      rw [ih (Nat.le_of_succ_le hn)]
      exact p.map_mass_mul_conditional_map
        (labelRecordOf labels n) (labels n) r s

theorem ofLawLabels_refinementEntropy_eq {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n < depth) :
    (ofLawLabels p labels depth).refinementEntropy n =
      ∑ r : LabelRecord Label n, (p.map (labelRecordOf labels n)).mass r *
        finiteEntropy ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass := by
  rw [refinementEntropy_eq _ n hn,
    ofLawLabels_prefixLaw_mass p labels depth n (Nat.le_of_lt hn)]
  rfl

theorem ofLawLabels_refinementEntropy_sum {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ j ∈ Finset.range depth,
      (ofLawLabels p labels depth).refinementEntropy j) = finiteEntropy p.mass := by
  apply (ofLawLabels p labels depth).refinementEntropy_sum_of_injective_record
    p (labelRecordOf labels depth) hinjective
  exact ofLawLabels_prefixLaw_mass p labels depth depth le_rfl

theorem entropy_eq_sum_conditional_labels {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    finiteEntropy p.mass =
      ∑ j ∈ Finset.range depth, ∑ r : LabelRecord Label j,
        (p.map (labelRecordOf labels j)).mass r *
          finiteEntropy ((p.conditional (labelRecordOf labels j) r).map (labels j)).mass := by
  rw [← ofLawLabels_refinementEntropy_sum p labels depth hinjective]
  apply Finset.sum_congr rfl
  intro j hj
  exact ofLawLabels_refinementEntropy_eq p labels depth j (Finset.mem_range.mp hj)

end FiniteLabelHierarchy

end
end MatrixMultiplication.Foundation

end OAI

end FlattenModule095
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalTypeCounting -/
section FlattenModule096

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

abbrev PopulationWords (I : Type*) [Fintype I] (counts : A → ℕ) :=
  {w : I → A // ∀ a, wordPopulation w a = counts a}

noncomputable def populationWordsEquiv (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) : PopulationWords I counts ≃ ExactWords counts := by
  let e : I ≃ Fin (∑ a, counts a) := Fintype.equivFinOfCardEq h
  exact
    { toFun := fun w =>
        ⟨w.val ∘ e.symm, fun a => (wordPopulation_reindex w.val e.symm a).trans (w.property a)⟩
      invFun := fun w =>
        ⟨w.val ∘ e, fun a => (wordPopulation_reindex w.val e a).trans (w.property a)⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp }

theorem populationWords_card (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) :
    Fintype.card (PopulationWords I counts) = Nat.multinomial Finset.univ counts := by
  rw [Fintype.card_congr (populationWordsEquiv counts h), exactWords_card]

abbrev ConditionalWords (w : I → A) (counts : A → B → ℕ) :=
  {r : I → B // ∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b}

def fiberWordEquiv (w : I → A) : (I → B) ≃ (∀ a, {i // w i = a} → B) where
  toFun r _ i := r i.val
  invFun r i := r (w i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv := by
    intro r
    funext a i
    rcases i with ⟨i, hi⟩
    cases hi
    rfl

omit [Fintype A] [Fintype B] [DecidableEq I] in
theorem wordPopulation_fiber (w : I → A) (r : I → B) (a : A) (b : B) :
    wordPopulation (fun i : {i // w i = a} => r i.val) b =
      Fintype.card {i // w i = a ∧ r i = b} :=
  Fintype.card_congr
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => w i = a) (fun i => r i = b))

def conditionalWordsEquiv (w : I → A) (counts : A → B → ℕ) :
    ConditionalWords w counts ≃ ∀ a, PopulationWords {i // w i = a} (counts a) := by
  let e : ConditionalWords w counts ≃
      {r : ∀ a, {i // w i = a} → B // ∀ a b, wordPopulation (r a) b = counts a b} :=
    Equiv.subtypeEquiv (fiberWordEquiv w) fun r => by
      change (∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b) ↔
        ∀ a b, wordPopulation (fun i : {i // w i = a} => r i.val) b = counts a b
      simp only [wordPopulation_fiber]
  exact e.trans (Equiv.subtypePiEquivPi
    (β := fun a : A => {i // w i = a} → B)
    (p := fun a r => ∀ b, wordPopulation r b = counts a b))

theorem conditionalWords_card (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Fintype.card (ConditionalWords w counts) =
      ∏ a, Nat.multinomial Finset.univ (counts a) := by
  rw [Fintype.card_congr (conditionalWordsEquiv w counts), Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => populationWords_card (counts a) (h a)

theorem conditionalWords_card_pos (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    0 < Fintype.card (ConditionalWords w counts) := by
  rw [conditionalWords_card w counts h]
  exact Finset.prod_pos fun a _ => Nat.multinomial_pos Finset.univ (counts a)

theorem conditionalWords_nonempty (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Nonempty (ConditionalWords w counts) :=
  Fintype.card_pos_iff.mp (conditionalWords_card_pos w counts h)

theorem conditionalWords_nonempty_iff (w : I → A) (counts : A → B → ℕ) :
    Nonempty (ConditionalWords w counts) ↔
      ∀ a, wordPopulation w a = ∑ b, counts a b := by
  constructor
  · rintro ⟨r⟩ a
    calc
      wordPopulation w a =
          ∑ b, wordPopulation (fun i : {i // w i = a} => r.val i.val) b :=
        (wordPopulation_sum _).symm
      _ = ∑ b, counts a b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [wordPopulation_fiber, r.property]
  · exact conditionalWords_nonempty w counts

omit [DecidableEq A] [DecidableEq B] in
theorem multinomial_prod_counts (counts : A × B → ℕ) :
    Nat.multinomial Finset.univ counts =
      Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
        ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b)) := by
  apply Nat.mul_left_cancel (Nat.prod_factorial_pos Finset.univ counts)
  rw [Nat.multinomial_spec]
  symm
  calc
    (∏ ab, (counts ab).factorial) *
        (Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) =
        ((∏ a, ∏ b, (counts (a, b)).factorial) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Fintype.prod_prod_type]
      ac_rfl
    _ = (∏ a, ((∏ b, (counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun b => counts (a, b)))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ a, (∑ b, counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact Nat.multinomial_spec Finset.univ (fun b => counts (a, b))
    _ = (∑ a, ∑ b, counts (a, b)).factorial :=
      Nat.multinomial_spec Finset.univ (fun a => ∑ b, counts (a, b))
    _ = (∑ ab, counts ab).factorial := by rw [Fintype.sum_prod_type]

theorem exactWords_card_prod_counts (counts : A × B → ℕ) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (fun a => ∑ b, counts (a, b))) *
        ∏ a, Fintype.card (ExactWords (fun b => counts (a, b))) := by
  simpa only [exactWords_card] using multinomial_prod_counts counts

theorem exactWords_card_eq_coarse_mul_conditional (counts : A × B → ℕ)
    (w : ExactWords (fun a => ∑ b, counts (a, b))) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (fun a => ∑ b, counts (a, b))) *
        Fintype.card (ConditionalWords w.val (fun a b => counts (a, b))) := by
  rw [conditionalWords_card w.val (fun a b => counts (a, b)) w.property]
  simpa only [exactWords_card] using multinomial_prod_counts counts

end MatrixMultiplication.Foundation

end OAI

end FlattenModule096
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalTypeCounting -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexHierarchyTypeCounting -/
section FlattenModule097


namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

def pushforwardCounts {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (b : B) : ℕ := by
  classical
  exact ∑ a, if label a = b then counts a else 0

theorem pushforwardCounts_sum {A B : Type*} [Fintype A] [Fintype B]
    (counts : A → ℕ) (label : A → B) :
    (∑ b, pushforwardCounts counts label b) = ∑ a, counts a := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  simp

theorem pushforwardCounts_apply {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (hinjective : Function.Injective label)
    (a : A) : pushforwardCounts counts label (label a) = counts a := by
  classical
  simp [pushforwardCounts, hinjective.eq_iff]

theorem pushforwardCounts_sum_pair {A B C : Type*}
    [Fintype A] [Fintype C] (counts : A → ℕ)
    (coarse : A → B) (fine : A → C) (b : B) :
    (∑ c, pushforwardCounts counts (fun a => (coarse a, fine a)) (b, c)) =
      pushforwardCounts counts coarse b := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : coarse a = b
  · simp [Prod.mk.injEq, hab]
  · simp [Prod.mk.injEq, hab]

theorem pushforwardCounts_factorial_prod_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    (∏ b, (pushforwardCounts counts label b).factorial) =
      ∏ a, (counts a).factorial := by
  classical
  have hfactor (b : B) : (pushforwardCounts counts label b).factorial =
      ∏ a, if label a = b then (counts a).factorial else 1 := by
    by_cases hb : ∃ a, label a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [pushforwardCounts_apply counts label hinjective]
      simp [hinjective.eq_iff]
    · simp [pushforwardCounts, not_exists.mp hb]
  simp_rw [hfactor]
  rw [Finset.prod_comm]
  simp

theorem multinomial_pushforwardCounts_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    Nat.multinomial Finset.univ (pushforwardCounts counts label) =
      Nat.multinomial Finset.univ counts := by
  simp only [Nat.multinomial, pushforwardCounts_sum,
    pushforwardCounts_factorial_prod_of_injective counts label hinjective]

namespace LabelHierarchyCounts

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)]

def refinementCount (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ) : ℕ :=
  ∏ r : LabelRecord Label n,
    Nat.multinomial Finset.univ (fun s : Label n => counts (n + 1) (r, s))

theorem multinomial_succ (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ)
    (compatible : ∀ r, counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts (n + 1)) =
      Nat.multinomial Finset.univ (counts n) * refinementCount counts n := by
  classical
  have hrows : (fun r => ∑ s : Label n, counts (n + 1) (r, s)) = counts n :=
    funext fun r => (compatible r).symm
  exact (multinomial_prod_counts
    (A := LabelRecord Label n) (B := Label n) (counts (n + 1))).trans
      (congrArg (fun rows : LabelRecord Label n → ℕ =>
        Nat.multinomial Finset.univ rows * refinementCount counts n) hrows)

theorem pool_multinomial_eq_one_of_zero
    (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ)
    (compatible : ∀ r, counts n r = ∑ s : Label n, counts (n + 1) (r, s))
    (r : LabelRecord Label n) (hzero : counts n r = 0) :
    Nat.multinomial Finset.univ (fun s : Label n => counts (n + 1) (r, s)) = 1 := by
  have hchild (s : Label n) : counts (n + 1) (r, s) = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      counts (n + 1) (r, s) ≤ ∑ t : Label n, counts (n + 1) (r, t) :=
        Finset.single_le_sum (f := fun t : Label n => counts (n + 1) (r, t))
          (fun t _ => Nat.zero_le _) (Finset.mem_univ s)
      _ = 0 := (compatible r).symm.trans hzero
  simp [Nat.multinomial, hchild]

theorem multinomial_eq_refinementCount_product
    (counts : ∀ n, LabelRecord Label n → ℕ) (depth : ℕ)
    (compatible : ∀ n < depth, ∀ r,
      counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts depth) =
      ∏ n ∈ Finset.range depth, refinementCount counts n := by
  classical
  induction depth with
  | zero =>
      exact Nat.multinomial_singleton (PUnit.unit : LabelRecord Label 0) (counts 0)
  | succ depth ih =>
      rw [multinomial_succ counts depth (compatible depth (Nat.lt_succ_self depth))]
      rw [ih (fun n hn => compatible n (Nat.lt_trans hn (Nat.lt_succ_self depth))),
        Finset.prod_range_succ]

def sourcePrefixCounts {A : Type v} [Fintype A] (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) : LabelRecord Label n → ℕ :=
  pushforwardCounts counts (labelRecordOf labels n)

theorem sourcePrefixCounts_compatible {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) :
    sourcePrefixCounts counts labels n r =
      ∑ s : Label n, sourcePrefixCounts counts labels (n + 1) (r, s) :=
  (pushforwardCounts_sum_pair counts (labelRecordOf labels n) (labels n) r).symm

theorem source_refinementCount_product {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Nat.multinomial Finset.univ counts := by
  calc
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
        Nat.multinomial Finset.univ (sourcePrefixCounts counts labels depth) :=
      (multinomial_eq_refinementCount_product (sourcePrefixCounts counts labels) depth
        (fun n _ r => sourcePrefixCounts_compatible counts labels n r)).symm
    _ = Nat.multinomial Finset.univ counts :=
      multinomial_pushforwardCounts_of_injective counts
        (labelRecordOf labels depth) hinjective

theorem source_refinementCount_product_eq_exactWords_card
    {A : Type v} [Fintype A] [DecidableEq A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Fintype.card (ExactWords counts) := by
  rw [source_refinementCount_product counts labels depth hinjective, exactWords_card]

end LabelHierarchyCounts
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule097
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexHierarchyTypeCounting -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexLocalMaps -/
section FlattenModule098


namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation
namespace LocalMaps

open scoped BigOperators

variable {K X Y Z A B C A' B' C' : Type*}
variable [CommSemiring K] [Fintype A] [Fintype B] [Fintype C]

def fiberMatrix [DecidableEq X] (M : X → A' → A → K) :
    (X × A') → (X × A) → K :=
  fun output input => if output.1 = input.1 then M output.1 output.2 input.2 else 0

def fiberTransform (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A') (Y × B') (Z × C') :=
  fun x y z => ∑ a, ∑ b, ∑ c,
    MX x.1 x.2 a * MY y.1 y.2 b * MZ z.1 z.2 c *
      T (x.1, a) (y.1, b) (z.1, c)

def originalScale (coefficient : X → Y → Z → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A) (Y × B) (Z × C) :=
  fun x y z => coefficient x.1 y.1 z.1 * T x y z

theorem fiberTransform_originalScale (MX : X → A' → A → K)
    (MY : Y → B' → B → K) (MZ : Z → C' → C → K)
    (coefficient : X → Y → Z → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ (originalScale coefficient T) =
      originalScale coefficient (fiberTransform MX MY MZ T) := by
  funext x y z
  simp only [fiberTransform, originalScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ac_rfl

theorem fiberTransform_substitution
    (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C))
    (U : Tensor K (X × A') (Y × B') (Z × C'))
    (identity : fiberTransform MX MY MZ T = U)
    (coefficient : X → Y → Z → K) :
    fiberTransform MX MY MZ (originalScale coefficient T) =
      originalScale coefficient U := by
  rw [fiberTransform_originalScale, identity]

theorem fiberTransform_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ T =
      Tensor.restrict (fiberMatrix MX) (fiberMatrix MY) (fiberMatrix MZ) T := by
  funext x y z
  simp [fiberTransform, Tensor.restrict, fiberMatrix, Fintype.sum_prod_type,
    ite_mul, mul_ite]

noncomputable def originalMask (P : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A) (Y × B) (Z × C) := by
  classical
  exact fun x y z => if P x.1 y.1 z.1 then T x y z else 0

theorem fiberTransform_originalMask (MX : X → A' → A → K)
    (MY : Y → B' → B → K) (MZ : Z → C' → C → K)
    (P : X → Y → Z → Prop) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ (originalMask P T) =
      originalMask P (fiberTransform MX MY MZ T) := by
  classical
  funext x y z
  by_cases h : P x.1 y.1 z.1 <;> simp [fiberTransform, originalMask, h]

def SupportedOn (P : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) : Prop :=
  ∀ x y z, ¬ P x.1 y.1 z.1 → T x y z = 0

theorem fiberTransform_supportedOn (MX : X → A' → A → K)
    (MY : Y → B' → B → K) (MZ : Z → C' → C → K)
    (P : X → Y → Z → Prop) (T : Tensor K (X × A) (Y × B) (Z × C))
    (hT : SupportedOn P T) : SupportedOn P (fiberTransform MX MY MZ T) := by
  intro x y z h
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  simp [hT (x.1, a) (y.1, b) (z.1, c) h]

omit [Fintype A] [Fintype B] [Fintype C] in
theorem originalMask_eq_self (P : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) (hT : SupportedOn P T) :
    originalMask P T = T := by
  classical
  funext x y z
  by_cases h : P x.1 y.1 z.1
  · simp [originalMask, h]
  · simp [originalMask, h, hT x y z h]

noncomputable def localSelector (P : X → Prop) : (X × A) → (X × A) → K := by
  classical
  exact fun output input =>
    if output = input then (if P output.1 then 1 else 0) else 0

theorem factoredMask_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    originalMask (fun x y z => PX x ∧ PY y ∧ PZ z) T =
      Tensor.restrict (localSelector PX) (localSelector PY) (localSelector PZ) T := by
  classical
  funext x y z
  by_cases hx : PX x.1 <;> by_cases hy : PY y.1 <;> by_cases hz : PZ z.1 <;>
    simp [originalMask, Tensor.restrict, localSelector, ite_mul, mul_ite, hx, hy, hz]

variable {Label : Type*}

def Synchronized (lx : X → Label) (ly : Y → Label) (lz : Z → Label) :
    X → Y → Z → Prop :=
  fun x y z => lx x = ly y ∧ lx x = lz z

def InBranch (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (label : Label) : X → Y → Z → Prop :=
  fun x y z => lx x = label ∧ ly y = label ∧ lz z = label

omit [Fintype A] [Fintype B] [Fintype C] in
theorem factoredMask_synchronized
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (support : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C))
    (hT : SupportedOn support T)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      Synchronized lx ly lz x y z) :
    SupportedOn (Synchronized lx ly lz)
      (originalMask (fun x y z => PX x ∧ PY y ∧ PZ z) T) := by
  classical
  intro x y z hn
  by_cases hs : support x.1 y.1 z.1
  · by_cases hw : PX x.1 ∧ PY y.1 ∧ PZ z.1
    · exact (hn (compatible x.1 y.1 z.1 hs hw.1 hw.2.1 hw.2.2)).elim
    · simp [originalMask, hw]
  · simp [originalMask, hT x y z hs]

theorem controlled_eq_sum_branches [Fintype Label]
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (MX : Label → X → A' → A → K) (MY : Label → Y → B' → B → K)
    (MZ : Label → Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform (fun x => MX (lx x) x) (fun y => MY (ly y) y)
        (fun z => MZ (lz z) z) (originalMask (Synchronized lx ly lz) T) =
      fun x y z => ∑ label,
        fiberTransform (MX label) (MY label) (MZ label)
          (originalMask (InBranch lx ly lz label) T) x y z := by
  classical
  funext x y z
  by_cases h : Synchronized lx ly lz x.1 y.1 z.1
  · have hy : ly y.1 = lx x.1 := h.1.symm
    have hz : lz z.1 = lx x.1 := h.2.symm
    rw [Finset.sum_eq_single (lx x.1)]
    · simp [fiberTransform, originalMask, InBranch, h, hy, hz]
    · intro label _ hlabel
      have hn : lx x.1 ≠ label := Ne.symm hlabel
      simp [fiberTransform, originalMask, InBranch, hn]
    · simp
  · have hn (label : Label) : ¬ InBranch lx ly lz label x.1 y.1 z.1 := by
      intro hb
      exact h ⟨hb.1.trans hb.2.1.symm, hb.1.trans hb.2.2.symm⟩
    simp [fiberTransform, originalMask, h, hn]

theorem controlled_eq_sum_branches_of_supported [Fintype Label]
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (MX : Label → X → A' → A → K) (MY : Label → Y → B' → B → K)
    (MZ : Label → Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C))
    (hT : SupportedOn (Synchronized lx ly lz) T) :
    fiberTransform (fun x => MX (lx x) x) (fun y => MY (ly y) y)
        (fun z => MZ (lz z) z) T =
      fun x y z => ∑ label,
        fiberTransform (MX label) (MY label) (MZ label)
          (originalMask (InBranch lx ly lz label) T) x y z := by
  have h := controlled_eq_sum_branches lx ly lz MX MY MZ T
  rw [originalMask_eq_self _ _ hT] at h
  exact h

end LocalMaps
end MatrixMultiplication.Foundation

end OAI

end FlattenModule098
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexLocalMaps -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSharedAuxiliaryBank -/
section FlattenModule099


namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation.LabelHierarchySeparation

variable {K I : Type*} [CommSemiring K] [Fintype I]
variable {X Y Z : I → Type*}

def bankTensor (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    Tensor K (∀ i, X i) (∀ i, Y i) (∀ i, Z i) :=
  fun x y z => ∏ i, T i (x i) (y i) (z i)

theorem bankTensor_rankAtMost (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (r : I → ℕ) (h : ∀ i, Tensor.RankAtMost (T i) (r i)) :
    Tensor.RankAtMost (bankTensor T) (∏ i, r i) := by
  classical
  choose a b c hc using h
  let aa : (∀ i, Fin (r i)) → (∀ i, X i) → K :=
    fun f x => ∏ i, a i (f i) (x i)
  let bb : (∀ i, Fin (r i)) → (∀ i, Y i) → K :=
    fun f y => ∏ i, b i (f i) (y i)
  let cc : (∀ i, Fin (r i)) → (∀ i, Z i) → K :=
    fun f z => ∏ i, c i (f i) (z i)
  have heq : bankTensor T =
      fun x y z => ∑ f, Tensor.rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [bankTensor, hc, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [Tensor.rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi, Fintype.card_fin] using
    Tensor.rankAtMost_sum_rankOne aa bb cc

theorem bankTensor_reindex {J : Type*} [Fintype J]
    {X' Y' Z' : J → Type*} (e : I ≃ J)
    (ex : ∀ i, X i ≃ X' (e i)) (ey : ∀ i, Y i ≃ Y' (e i))
    (ez : ∀ i, Z i ≃ Z' (e i))
    (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (S : ∀ j, Tensor K (X' j) (Y' j) (Z' j))
    (compatible : ∀ i x y z, S (e i) (ex i x) (ey i y) (ez i z) = T i x y z) :
    Tensor.pullback (e.piCongr ex) (e.piCongr ey) (e.piCongr ez)
      (bankTensor S) = bankTensor T := by
  funext x y z
  change (∏ j, S j ((e.piCongr ex) x j) ((e.piCongr ey) y j)
    ((e.piCongr ez) z j)) = ∏ i, T i (x i) (y i) (z i)
  rw [← e.prod_comp (fun j => S j ((e.piCongr ex) x j)
    ((e.piCongr ey) y j) ((e.piCongr ez) z j))]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [Equiv.piCongr_apply_apply] using compatible i (x i) (y i) (z i)

theorem bankTensor_reindex_rankAtMost {J : Type*} [Fintype J]
    {X' Y' Z' : J → Type*} (e : I ≃ J)
    (ex : ∀ i, X i ≃ X' (e i)) (ey : ∀ i, Y i ≃ Y' (e i))
    (ez : ∀ i, Z i ≃ Z' (e i))
    (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (S : ∀ j, Tensor K (X' j) (Y' j) (Z' j))
    (compatible : ∀ i x y z, S (e i) (ex i x) (ey i y) (ez i z) = T i x y z)
    {r : ℕ} (hS : Tensor.RankAtMost (bankTensor S) r) :
    Tensor.RankAtMost (bankTensor T) r := by
  rw [← bankTensor_reindex e ex ey ez T S compatible]
  exact hS.pullback _ _ _

end MatrixMultiplication.Foundation.LabelHierarchySeparation

end OAI

end FlattenModule099
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSharedAuxiliaryBank -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexLabelHierarchySeparation -/
section FlattenModule100





namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace LabelHierarchySeparation

section Bank

variable {K I : Type*} [CommSemiring K] [Fintype I]
variable {X Y Z : I → Type*}

variable {Node : Type*} [Fintype Node]

def populationCoordinateEquiv {J : Type*} (D : Node → Type*)
    (pool : I → Node) (reference : J → Node) (e : I ≃ J)
    (same : ∀ i, reference (e i) = pool i) :
    (∀ i, D (pool i)) ≃ (∀ j, D (reference j)) :=
  e.piCongr (fun i => Equiv.cast (congrArg D (same i).symm))

omit [CommSemiring K] [Fintype Node] in
theorem tensor_transport {AX AY AZ : Node → Type*}
    (T : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    {node node' : Node} (h : node = node') (x : AX node) (y : AY node) (z : AZ node) :
    T node' (Equiv.cast (congrArg AX h) x) (Equiv.cast (congrArg AY h) y)
      (Equiv.cast (congrArg AZ h) z) = T node x y z := by
  cases h
  rfl

omit [Fintype Node] in
theorem bankTensor_population_reindex {J : Type*} [Fintype J]
    {AX AY AZ : Node → Type*}
    (T : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    (pool : I → Node) (reference : J → Node) (e : I ≃ J)
    (same : ∀ i, reference (e i) = pool i) :
    Tensor.pullback (populationCoordinateEquiv AX pool reference e same)
      (populationCoordinateEquiv AY pool reference e same)
      (populationCoordinateEquiv AZ pool reference e same)
      (bankTensor (fun j => T (reference j))) = bankTensor (fun i => T (pool i)) := by
  unfold populationCoordinateEquiv
  apply bankTensor_reindex e
  intro i x y z
  exact tensor_transport T (same i).symm x y z

omit [Fintype Node] in
theorem bankTensor_population_rankAtMost {J : Type*} [Fintype J]
    {AX AY AZ : Node → Type*}
    (T : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    (pool : I → Node) (reference : J → Node) (e : I ≃ J)
    (same : ∀ i, reference (e i) = pool i)
    {r : ℕ} (hT : Tensor.RankAtMost (bankTensor (fun j => T (reference j))) r) :
    Tensor.RankAtMost (bankTensor (fun i => T (pool i))) r := by
  rw [← bankTensor_population_reindex T pool reference e same]
  exact hT.pullback _ _ _

abbrev BankOccurrences (population : Node → ℕ) :=
  (node : Node) × Fin (population node)

theorem canonical_bank_product {M : Type*} [CommMonoid M]
    (population : Node → ℕ) (cost : Node → M) :
    (∏ i : BankOccurrences population, cost i.1) =
      ∏ node, cost node ^ population node := by
  simp [BankOccurrences, Fintype.prod_sigma]

theorem canonical_pairing_card [DecidableEq Node] (population dimension : Node → ℕ) :
    Fintype.card (∀ i : BankOccurrences population, Fin (dimension i.1)) =
      ∏ node, dimension node ^ population node := by
  classical
  simp only [Fintype.card_pi, Fintype.card_fin, canonical_bank_product]

theorem canonical_bank_rankAtMost
    {AX AY AZ : Node → Type*}
    (E : ∀ node, Tensor K (AX node) (AY node) (AZ node))
    (population rank : Node → ℕ)
    (hE : ∀ node, Tensor.RankAtMost (E node) (rank node)) :
    Tensor.RankAtMost
      (bankTensor (fun i : BankOccurrences population => E i.1))
      (∏ node, rank node ^ population node) := by
  simpa only [canonical_bank_product] using
    bankTensor_rankAtMost
      (fun i : BankOccurrences population => E i.1)
      (fun i => rank i.1) (fun i => hE i.1)

theorem occurrence_product {M : Type*} [CommMonoid M] [DecidableEq Node]
    (pool : I → Node) (cost : Node → M) :
    (∏ i, cost (pool i)) =
      ∏ node, cost node ^ Fintype.card {i // pool i = node} := by
  rw [← Fintype.prod_fiberwise' pool cost]
  simp

theorem exact_population_product {M : Type*} [CommMonoid M] [DecidableEq Node]
    (pool : I → Node) (population : Node → ℕ)
    (exactPopulation : ∀ node,
      Fintype.card {i // pool i = node} = population node) (cost : Node → M) :
    (∏ i, cost (pool i)) = ∏ node, cost node ^ population node := by
  rw [occurrence_product]
  simp only [exactPopulation]

omit [Fintype Node] in
theorem exact_population_bank_equiv [DecidableEq Node]
    (pool : I → Node) (population : Node → ℕ)
    (exactPopulation : ∀ node,
      Fintype.card {i // pool i = node} = population node) :
    ∃ e : I ≃ BankOccurrences population, ∀ i, (e i).1 = pool i := by
  classical
  let ef : ∀ node, {i // pool i = node} ≃ Fin (population node) :=
    fun node => Fintype.equivOfCardEq (by simp [exactPopulation node])
  refine ⟨(Equiv.sigmaFiberEquiv pool).symm.trans
    (Equiv.sigmaCongrRight ef), ?_⟩
  intro i
  rfl

end Bank

section PrefixSeparation

variable {X Y Z Prefix Label Pairing G : Type*}
variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [DecidableEq Label] [DecidableEq Pairing]

omit [Fintype G] in
theorem prefix_separation_identity
    (T : Tensor ℂ X Y Z)
    (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (tag : Prefix → Label → G) (point : Prefix → Label → Pairing → G)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (collision : ∀ p s s' i j,
      point p s i + (tag p s - point p s j) = tag p s' ↔
        s = s' ∧ i = j) :
    Tensor.pullback
      (fun x : X × Pairing => (x.1, point (px x.1) (lx x.1) x.2))
      (fun y : Y × Pairing =>
        (y.1, tag (py y.1) (ly y.1) - point (py y.1) (ly y.1) y.2))
      (fun z : Z × Label => (z.1, tag (pz z.1) z.2))
      (Tensor.product T (groupTensor G)) = separatedTensor lx T := by
  funext x y z
  by_cases hzero : T x.1 y.1 z.1 = 0
  · simp [Tensor.pullback, Tensor.product, separatedTensor, hzero]
  · obtain ⟨hxy, hxz⟩ := prefixes x.1 y.1 z.1 hzero
    have hl := labels x.1 y.1 z.1 hzero
    simp only [Tensor.pullback, Tensor.product, groupTensor, separatedTensor]
    simp only [← hxy, ← hxz, ← hl, collision, mul_ite, mul_one, mul_zero]

theorem prefix_separation_rankAtMost
    (T : Tensor ℂ X Y Z)
    (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (tag : Prefix → Label → G) (point : Prefix → Label → Pairing → G)
    {r : ℕ} (hT : Tensor.RankAtMost T r)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (collision : ∀ p s s' i j,
      point p s i + (tag p s - point p s j) = tag p s' ↔
        s = s' ∧ i = j) :
    Tensor.RankAtMost (separatedTensor (U := Pairing) lx T)
      (r * Fintype.card G) := by
  rw [← prefix_separation_identity T px py pz lx ly tag point
    prefixes labels collision]
  exact (hT.product (groupTensor_rankAtMost G)).pullback _ _ _

@[simp] theorem separated_coefficient
    (T : Tensor ℂ X Y Z) (lx : X → Label)
    (x : X) (y : Y) (z : Z) (u : Pairing) :
    separatedTensor lx T (x, u) (y, u) (z, lx x) = T x y z := by
  simp [separatedTensor]

theorem deterministic_separation_identity
    [Subsingleton Label] [Subsingleton Pairing] [Nonempty Pairing]
    (T : Tensor ℂ X Y Z) (lx : X → Label) :
    separatedTensor (U := Pairing) lx T =
      Tensor.pullback Prod.fst Prod.fst Prod.fst T := by
  funext x y z
  simp [separatedTensor, Tensor.pullback, Subsingleton.elim (lx x.1) z.2,
    Subsingleton.elim x.2 y.2]

theorem separated_prefix_synchronized
    (T : Tensor ℂ X Y Z)
    (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (x : X × Pairing) (y : Y × Pairing) (z : Z × Label)
    (h : separatedTensor lx T x y z ≠ 0) :
    (px x.1, lx x.1) = (py y.1, ly y.1) ∧
      (px x.1, lx x.1) = (pz z.1, z.2) := by
  have hguard : lx x.1 = z.2 ∧ x.2 = y.2 := by
    by_contra hn
    exact h (by simp [separatedTensor, hn])
  have hT : T x.1 y.1 z.1 ≠ 0 := by
    simpa [separatedTensor, hguard] using h
  obtain ⟨hxy, hxz⟩ := prefixes x.1 y.1 z.1 hT
  exact ⟨Prod.ext hxy (labels x.1 y.1 z.1 hT), Prod.ext hxz hguard.1⟩

end PrefixSeparation

section ExactPools

variable {X Y Z Prefix Label : Type*} [DecidableEq Label]

noncomputable def poolEnumeration (pool : Prefix → Finset Label) (k : ℕ)
    (counts : ∀ p, (pool p).card = k) : ∀ p, ↥(pool p) ≃ Fin k :=
  fun p => Finset.equivFinOfCardEq (counts p)

def poolCode (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (prior : X → Prefix) (label : X → Label)
    (allowed : ∀ x, label x ∈ pool (prior x)) : X → Fin k :=
  fun x => enumerate (prior x) ⟨label x, allowed x⟩

omit [DecidableEq Label] in
@[simp] theorem poolCode_decode (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (prior : X → Prefix) (label : X → Label)
    (allowed : ∀ x, label x ∈ pool (prior x)) (x : X) :
    ((enumerate (prior x)).symm (poolCode pool enumerate prior label allowed x)).val =
      label x := by
  simp [poolCode]

omit [DecidableEq Label] in
theorem poolCode_agree (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (px : X → Prefix) (py : Y → Prefix) (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (x : X) (y : Y) (hp : px x = py y) (hl : lx x = ly y) :
    poolCode pool enumerate px lx ax x = poolCode pool enumerate py ly ay y := by
  have congr_code : ∀ (p q : Prefix) (a : ↥(pool p)) (b : ↥(pool q)),
      p = q → a.val = b.val → enumerate p a = enumerate q b := by
    intro p q a b hp hl
    cases hp
    exact congrArg (enumerate p) (Subtype.ext hl)
  exact congr_code _ _ ⟨lx x, ax x⟩ ⟨ly y, ay y⟩ hp hl

noncomputable def poolAuxiliaryCost (k : ℕ) : ℕ :=
  if k = 1 then 1 else Separation.gridGroupOrder k

abbrev PoolAuxiliaryGroup (k : ℕ) :=
  Separation.AuxiliaryGroup (Separation.gridDimension k) (Separation.gridWidth k)

noncomputable def poolAuxiliaryTensor (k : ℕ) :
    Tensor ℂ (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) :=
  if k = 1 then Tensor.rankOne (fun _ => 1) (fun _ => 1) (fun _ => 1)
  else groupTensor (PoolAuxiliaryGroup k)

theorem poolAuxiliaryTensor_rankAtMost (k : ℕ) :
    Tensor.RankAtMost (poolAuxiliaryTensor k) (poolAuxiliaryCost k) := by
  classical
  by_cases hk : k = 1
  · simpa only [poolAuxiliaryTensor, poolAuxiliaryCost, ite_eq_left hk] using
      Tensor.rankOne_rankAtMost (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
        (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
        (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
  · simpa only [poolAuxiliaryTensor, poolAuxiliaryCost, ite_eq_right hk,
      PoolAuxiliaryGroup, Separation.card_auxiliaryGroup, Separation.gridGroupOrder]
      using groupTensor_rankAtMost (PoolAuxiliaryGroup k)

omit [DecidableEq Label] in
theorem exact_pool_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T ∈
      Tensor.restrictionOrbit (Tensor.product T
        (groupTensor (Separation.AuxiliaryGroup
          (Separation.gridDimension k) (Separation.gridWidth k)))) := by
  classical
  have hagree : ∀ x y z, T x y z ≠ 0 →
      poolCode pool (poolEnumeration pool k counts) px lx ax x =
        poolCode pool (poolEnumeration pool k counts) py ly ay y := by
    intro x y z h
    exact poolCode_agree pool _ px py lx ly ax ay x y
      (prefixes x y z h) (labels x y z h)
  exact finite_grid_separation_mem_restrictionOrbit T
    (poolCode pool (poolEnumeration pool k counts) px lx ax)
    (poolCode pool (poolEnumeration pool k counts) py ly ay)
    (d := Separation.gridDimension k) (Q := Separation.gridWidth k) (m := k)
    (by simpa only [Fintype.card_fin] using Separation.grid_population_bound k)
    (Separation.grid_population_bound k) hagree

omit [DecidableEq Label] in
theorem exact_pool_raw_prefix_synchronized
    (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix) (pz : Z → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (_ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y ∧ px x = pz z)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    {Pairing : Type*} [DecidableEq Pairing]
    (x : X × Pairing) (y : Y × Pairing) (z : Z × Fin k)
    (h : separatedTensor (poolCode pool enumerate px lx ax) T x y z ≠ 0) :
    (px x.1, lx x.1) = (py y.1, ly y.1) ∧
      (px x.1, lx x.1) = (pz z.1, ((enumerate (pz z.1)).symm z.2).val) := by
  have guard : poolCode pool enumerate px lx ax x.1 = z.2 ∧ x.2 = y.2 := by
    by_contra hn
    exact h (by simp [separatedTensor, hn])
  have hT : T x.1 y.1 z.1 ≠ 0 := by
    simpa [separatedTensor, guard] using h
  obtain ⟨hxy, hxz⟩ := prefixes x.1 y.1 z.1 hT
  have hz : lx x.1 = ((enumerate (pz z.1)).symm z.2).val := by
    rw [← hxz, ← guard.1]
    exact (poolCode_decode pool enumerate px lx ax x.1).symm
  exact ⟨Prod.ext hxy (labels x.1 y.1 z.1 hT), Prod.ext hxz hz⟩

omit [DecidableEq Label] in
theorem exact_pool_rankAtMost
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    {r : ℕ} (hT : Tensor.RankAtMost T r)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost
      (separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T)
      (r * poolAuxiliaryCost k) := by
  classical
  by_cases hk : k = 1
  · subst k
    have hcost : poolAuxiliaryCost 1 = 1 := by simp [poolAuxiliaryCost]
    rw [hcost, mul_one, deterministic_separation_identity]
    exact hT.pullback (fun x : X × Fin 1 => x.1)
      (fun y : Y × Fin 1 => y.1) (fun z : Z × Fin 1 => z.1)
  · have hagree : ∀ x y z, T x y z ≠ 0 →
        poolCode pool (poolEnumeration pool k counts) px lx ax x =
          poolCode pool (poolEnumeration pool k counts) py ly ay y := by
      intro x y z h
      exact poolCode_agree pool _ px py lx ly ax ay x y
        (prefixes x y z h) (labels x y z h)
    have hr := finite_grid_separation_rankAtMost T
      (poolCode pool (poolEnumeration pool k counts) px lx ax)
      (poolCode pool (poolEnumeration pool k counts) py ly ay)
      (d := Separation.gridDimension k) (Q := Separation.gridWidth k) (m := k)
      (lt_of_lt_of_le (by decide : 0 < 2) (Separation.gridWidth_ge_two k))
      (by simpa only [Fintype.card_fin] using Separation.grid_population_bound k)
      (Separation.grid_population_bound k) hT hagree
    simpa only [poolAuxiliaryCost, ite_eq_right hk, Separation.gridGroupOrder] using hr

omit [DecidableEq Label] in
theorem exact_pool_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z]
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    {r : ℕ} (hT : Tensor.BorderRankAtMost T r)
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost
      (separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T)
      (r * poolAuxiliaryCost k) := by
  classical
  by_cases hk : k = 1
  · subst k
    have hcost : poolAuxiliaryCost 1 = 1 := by simp [poolAuxiliaryCost]
    rw [hcost, mul_one, deterministic_separation_identity]
    rw [Tensor.pullback_eq_restrict (fun x : X × Fin 1 => x.1)
      (fun y : Y × Fin 1 => y.1) (fun z : Z × Fin 1 => z.1) T]
    exact hT.restrict (fun (x : X × Fin 1) (original : X) =>
      if original = x.1 then 1 else 0)
      (fun (y : Y × Fin 1) (original : Y) => if original = y.1 then 1 else 0)
      (fun (z : Z × Fin 1) (original : Z) => if original = z.1 then 1 else 0)
  · have hagree : ∀ x y z, T x y z ≠ 0 →
        poolCode pool (poolEnumeration pool k counts) px lx ax x =
          poolCode pool (poolEnumeration pool k counts) py ly ay y := by
      intro x y z h
      exact poolCode_agree pool _ px py lx ly ax ay x y
        (prefixes x y z h) (labels x y z h)
    have hr := finite_grid_separation_borderRankAtMost T
      (poolCode pool (poolEnumeration pool k counts) px lx ax)
      (poolCode pool (poolEnumeration pool k counts) py ly ay)
      (d := Separation.gridDimension k) (Q := Separation.gridWidth k) (m := k)
      (lt_of_lt_of_le (by decide : 0 < 2) (Separation.gridWidth_ge_two k))
      (by simpa only [Fintype.card_fin] using Separation.grid_population_bound k)
      (Separation.grid_population_bound k) hT hagree
    simpa only [poolAuxiliaryCost, ite_eq_right hk, Separation.gridGroupOrder] using hr

omit [DecidableEq Label] in
theorem exact_pool_optimized_pullback
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    ∃ (fx : X × Fin k → PoolAuxiliaryGroup k)
      (fy : Y × Fin k → PoolAuxiliaryGroup k)
      (fz : Z × Fin k → PoolAuxiliaryGroup k),
      Tensor.pullback (fun x => (x.1, fx x)) (fun y => (y.1, fy y))
        (fun z => (z.1, fz z)) (Tensor.product T (poolAuxiliaryTensor k)) =
        separatedTensor
          (poolCode pool (poolEnumeration pool k counts) px lx ax) T := by
  classical
  by_cases hk : k = 1
  · subst k
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
    funext x y z
    simp [Tensor.pullback, Tensor.product, poolAuxiliaryTensor, Tensor.rankOne,
      separatedTensor, Subsingleton.elim x.2 y.2,
      Subsingleton.elim (poolCode pool (poolEnumeration pool 1 counts) px lx ax x.1) z.2]
  · obtain ⟨tag, point, collision⟩ := Separation.exists_modular_separation
      (Separation.grid_population_bound k) (Separation.grid_population_bound k)
    have hagree : ∀ x y z, T x y z ≠ 0 →
        poolCode pool (poolEnumeration pool k counts) px lx ax x =
          poolCode pool (poolEnumeration pool k counts) py ly ay y := by
      intro x y z h
      exact poolCode_agree pool _ px py lx ly ax ay x y
        (prefixes x y z h) (labels x y z h)
    refine ⟨fun x => point
        (poolCode pool (poolEnumeration pool k counts) px lx ax x.1) x.2,
      fun y => tag (poolCode pool (poolEnumeration pool k counts) py ly ay y.1) -
        point (poolCode pool (poolEnumeration pool k counts) py ly ay y.1) y.2,
      fun z => tag z.2, ?_⟩
    simpa only [poolAuxiliaryTensor, ite_eq_right hk] using finite_separation_identity T
      (poolCode pool (poolEnumeration pool k counts) px lx ax)
      (poolCode pool (poolEnumeration pool k counts) py ly ay) tag point hagree collision

omit [DecidableEq Label] in
theorem exact_pool_optimized_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (pool : Prefix → Finset Label) (k : ℕ) (counts : ∀ p, (pool p).card = k)
    (T : Tensor ℂ X Y Z) (px : X → Prefix) (py : Y → Prefix)
    (lx : X → Label) (ly : Y → Label)
    (ax : ∀ x, lx x ∈ pool (px x)) (ay : ∀ y, ly y ∈ pool (py y))
    (prefixes : ∀ x y z, T x y z ≠ 0 → px x = py y)
    (labels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin k)
        (poolCode pool (poolEnumeration pool k counts) px lx ax) T ∈
      Tensor.restrictionOrbit (Tensor.product T (poolAuxiliaryTensor k)) := by
  classical
  obtain ⟨fx, fy, fz, heq⟩ :=
    exact_pool_optimized_pullback pool k counts T px py lx ly ax ay prefixes labels
  rw [← heq]
  exact ⟨_, _, _, Tensor.pullback_eq_restrict _ _ _ _⟩

end ExactPools

section SharedBranches

variable {K X Y Z A B C A' B' C' Label : Type*}
variable [CommSemiring K] [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype A] [Fintype B] [Fintype C] [Fintype Label]

theorem shared_branch_rankAtMost
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (MX : Label → X → A' → A → K) (MY : Label → Y → B' → B → K)
    (MZ : Label → Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (synchronized : LocalMaps.SupportedOn (LocalMaps.Synchronized lx ly lz) T) :
    Tensor.RankAtMost
      (fun x y z => ∑ label,
        LocalMaps.fiberTransform (MX label) (MY label) (MZ label)
          (LocalMaps.originalMask (LocalMaps.InBranch lx ly lz label) T) x y z)
      r := by
  classical
  rw [← LocalMaps.controlled_eq_sum_branches_of_supported
    lx ly lz MX MY MZ T synchronized]
  rw [LocalMaps.fiberTransform_eq_restrict]
  exact hT.restrict _ _ _

end SharedBranches

section FiniteAssembly

universe u

variable {K : Type*} [CommSemiring K]
variable {X Y Z A B C : ℕ → Type*}

def AuxiliaryCoordinates (A : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => AuxiliaryCoordinates A n × A n

instance auxiliaryCoordinatesFintype [∀ n, Fintype (A n)] (n : ℕ) :
    Fintype (AuxiliaryCoordinates A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
      letI : Fintype (AuxiliaryCoordinates A n) := ih
      exact inferInstanceAs (Fintype (AuxiliaryCoordinates A n × A n))

def auxiliaryTensor (E : ∀ n, Tensor K (A n) (B n) (C n)) :
    ∀ n, Tensor K (AuxiliaryCoordinates A n)
      (AuxiliaryCoordinates B n) (AuxiliaryCoordinates C n)
  | 0 => fun _ _ _ => 1
  | n + 1 => Tensor.product (auxiliaryTensor E n) (E n)

def sourceCoordinate (step : ∀ n, X (n + 1) → X n × A n) :
    ∀ n, X n → X 0
  | 0 => id
  | n + 1 => fun x => sourceCoordinate step n (step n x).1

def auxiliaryCoordinate (step : ∀ n, X (n + 1) → X n × A n) :
    ∀ n, X n → AuxiliaryCoordinates A n
  | 0 => fun _ => PUnit.unit
  | n + 1 => fun x => (auxiliaryCoordinate step n (step n x).1, (step n x).2)

def stageTensor (T : Tensor K (X 0) (Y 0) (Z 0))
    (E : ∀ n, Tensor K (A n) (B n) (C n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) :
    ∀ n, Tensor K (X n) (Y n) (Z n)
  | 0 => T
  | n + 1 => Tensor.pullback (fx n) (fy n) (fz n)
      (Tensor.product (stageTensor T E fx fy fz n) (E n))

theorem stageTensor_eq_shared_bank
    (T : Tensor K (X 0) (Y 0) (Z 0))
    (E : ∀ n, Tensor K (A n) (B n) (C n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) (n : ℕ) :
    stageTensor T E fx fy fz n =
      Tensor.pullback
        (fun x => (sourceCoordinate fx n x, auxiliaryCoordinate fx n x))
        (fun y => (sourceCoordinate fy n y, auxiliaryCoordinate fy n y))
        (fun z => (sourceCoordinate fz n z, auxiliaryCoordinate fz n z))
        (Tensor.product T (auxiliaryTensor E n)) := by
  induction n with
  | zero =>
      funext x y z
      simp [stageTensor, Tensor.pullback, Tensor.product, sourceCoordinate,
        auxiliaryTensor]
  | succ n ih =>
      funext x y z
      simp only [stageTensor, Tensor.pullback, Tensor.product]
      rw [ih]
      simp only [Tensor.pullback, Tensor.product, sourceCoordinate,
        auxiliaryCoordinate, auxiliaryTensor, mul_assoc]

theorem auxiliaryTensor_rankAtMost
    (E : ∀ n, Tensor K (A n) (B n) (C n)) (r : ℕ → ℕ)
    (hE : ∀ n, Tensor.RankAtMost (E n) (r n)) (n : ℕ) :
    Tensor.RankAtMost (auxiliaryTensor E n) (∏ j ∈ Finset.range n, r j) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_zero]
      refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
      funext x y z
      simp [auxiliaryTensor, Tensor.rankOne]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      exact ih.product (hE n)

theorem stageTensor_rankAtMost
    (T : Tensor K (X 0) (Y 0) (Z 0)) {rT : ℕ}
    (hT : Tensor.RankAtMost T rT)
    (E : ∀ n, Tensor K (A n) (B n) (C n)) (r : ℕ → ℕ)
    (hE : ∀ n, Tensor.RankAtMost (E n) (r n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) (n : ℕ) :
    Tensor.RankAtMost (stageTensor T E fx fy fz n)
      (rT * ∏ j ∈ Finset.range n, r j) := by
  rw [stageTensor_eq_shared_bank]
  exact (hT.product (auxiliaryTensor_rankAtMost E r hE n)).pullback _ _ _

theorem stageTensor_borderRankAtMost
    [∀ n, Fintype (X n)] [∀ n, Fintype (Y n)] [∀ n, Fintype (Z n)]
    [∀ n, Fintype (A n)] [∀ n, Fintype (B n)] [∀ n, Fintype (C n)]
    (T : Tensor ℂ (X 0) (Y 0) (Z 0)) {rT : ℕ}
    (hT : Tensor.BorderRankAtMost T rT)
    (E : ∀ n, Tensor ℂ (A n) (B n) (C n)) (r : ℕ → ℕ)
    (hE : ∀ n, Tensor.RankAtMost (E n) (r n))
    (fx : ∀ n, X (n + 1) → X n × A n)
    (fy : ∀ n, Y (n + 1) → Y n × B n)
    (fz : ∀ n, Z (n + 1) → Z n × C n) (n : ℕ) :
    Tensor.BorderRankAtMost (stageTensor T E fx fy fz n)
      (rT * ∏ j ∈ Finset.range n, r j) := by
  classical
  rw [stageTensor_eq_shared_bank, Tensor.pullback_eq_restrict]
  exact (hT.product (auxiliaryTensor_rankAtMost E r hE n).borderRankAtMost).restrict _ _ _

end FiniteAssembly

end LabelHierarchySeparation
end MatrixMultiplication.Foundation

end OAI

end FlattenModule100
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexLabelHierarchySeparation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchySeparationRates -/
section FlattenModule101




namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

namespace LabelHierarchySeparation

theorem poolAuxiliaryCost_pos (k : ℕ) : 0 < poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs
  · exact Nat.zero_lt_one
  · exact Separation.gridGroupOrder_pos k

theorem population_le_poolAuxiliaryCost (k : ℕ) : k ≤ poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simp [hk]
  · exact Separation.population_le_gridGroupOrder k

theorem poolAuxiliaryCost_le_gridGroupOrder (k : ℕ) :
    poolAuxiliaryCost k ≤ Separation.gridGroupOrder k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simpa only [hk] using Separation.population_le_gridGroupOrder k
  · exact le_rfl

theorem tendsto_log_poolAuxiliaryCost_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ n, 0 < K n) (hH : 0 ≤ H)
    (hpop : Tendsto (fun n => Real.log (K n : ℝ) / (n : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun n => Real.log (poolAuxiliaryCost (K n) : ℝ) / (n : ℝ))
      atTop (𝓝 H) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hpop
    (Separation.tendsto_log_gridGroupOrder_div_nat hK hH hpop) ?_ ?_
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (hK n))
      (by exact_mod_cast population_le_poolAuxiliaryCost (K n))
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (poolAuxiliaryCost_pos (K n)))
      (by exact_mod_cast poolAuxiliaryCost_le_gridGroupOrder (K n))

end LabelHierarchySeparation

namespace HierarchySeparationRates

universe u v w

def populationEntropyRate {B : Type*} [Fintype B] (counts : B → ℕ) : ℝ :=
  (∑ b, counts b : ℕ) *
    finiteEntropy (fun b => (counts b : ℝ) / (∑ b, counts b : ℕ))

theorem tendsto_log_multinomial_mul_div_repetition {B : Type*} [Fintype B]
    (counts : B → ℕ) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  by_cases hD : 0 < ∑ b, counts b
  · have hD' : ((∑ b, counts b : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
    have h := (tendsto_log_multinomial_mul counts hD).const_mul
      ((∑ b, counts b : ℕ) : ℝ)
    apply h.congr
    intro t
    by_cases ht : t = 0
    · simp [ht]
    have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
    change ((∑ b, counts b : ℕ) : ℝ) *
        (Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) /
          ((t : ℝ) * (∑ b, counts b : ℕ))) = _
    field_simp [hD', ht']
  · have hz : (∑ b, counts b) = 0 := Nat.eq_zero_of_not_pos hD
    have hc (b : B) : counts b = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        counts b ≤ ∑ c, counts c :=
          Finset.single_le_sum (fun c _ => Nat.zero_le _) (Finset.mem_univ b)
        _ = 0 := hz
    simp only [populationEntropyRate, hz, Nat.cast_zero, zero_mul]
    simp [Nat.multinomial, hc]

theorem populationEntropyRate_nonneg {B : Type*} [Fintype B] (counts : B → ℕ) :
    0 ≤ populationEntropyRate counts := by
  apply ge_of_tendsto' (tendsto_log_multinomial_mul_div_repetition counts)
  intro t
  apply div_nonneg _ (Nat.cast_nonneg t)
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (fun b => t * counts b)))

section FinitePools

variable {I : Type u} [Fintype I] {Alphabet : I → Type v}
  [∀ i, Fintype (Alphabet i)]

def poolTypeCount (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (fun b => t * counts i b)

def poolEntropyTotal (counts : ∀ i, Alphabet i → ℕ) : ℝ :=
  ∑ i, populationEntropyRate (counts i)

def pairingProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, poolTypeCount counts i t

def gridProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, Separation.gridGroupOrder (poolTypeCount counts i t)

def auxiliaryProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, LabelHierarchySeparation.poolAuxiliaryCost (poolTypeCount counts i t)

omit [Fintype I] in
theorem poolTypeCount_pos (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) :
    0 < poolTypeCount counts i t := Nat.multinomial_pos _ _

theorem pairingProduct_le_auxiliaryProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) :
    pairingProduct counts t ≤ auxiliaryProduct counts t := by
  exact Finset.prod_le_prod' (fun i _ =>
    LabelHierarchySeparation.population_le_poolAuxiliaryCost (poolTypeCount counts i t))

theorem auxiliaryProduct_le_gridProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) :
    auxiliaryProduct counts t ≤ gridProduct counts t := by
  exact Finset.prod_le_prod' (fun i _ =>
    LabelHierarchySeparation.poolAuxiliaryCost_le_gridGroupOrder (poolTypeCount counts i t))

omit [Fintype I] in
theorem tendsto_log_poolTypeCount_div (counts : ∀ i, Alphabet i → ℕ) (i : I) :
    Tendsto (fun t : ℕ => Real.log (poolTypeCount counts i t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate (counts i))) :=
  tendsto_log_multinomial_mul_div_repetition (counts i)

theorem tendsto_log_pairingProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (pairingProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun i _ t => poolTypeCount_pos counts i t)
    (fun i _ => tendsto_log_poolTypeCount_div counts i)

theorem tendsto_log_gridProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (gridProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_gridGroupOrder_prod_div_nat Finset.univ
    (fun i _ t => poolTypeCount_pos counts i t)
    (fun i _ => populationEntropyRate_nonneg (counts i))
    (fun i _ => tendsto_log_poolTypeCount_div counts i)

theorem tendsto_log_auxiliaryProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (auxiliaryProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun i _ t => LabelHierarchySeparation.poolAuxiliaryCost_pos (poolTypeCount counts i t))
    (fun i _ => LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
      (poolTypeCount_pos counts i) (populationEntropyRate_nonneg (counts i))
      (tendsto_log_poolTypeCount_div counts i))

end FinitePools

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem pushforwardCounts_mul {B : Type*} (counts : A → ℕ) (label : A → B)
    (t : ℕ) (b : B) :
    pushforwardCounts (fun a => t * counts a) label b =
      t * pushforwardCounts counts label b := by
  classical
  unfold pushforwardCounts
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : label a = b <;> simp [h]

omit [∀ n, Fintype (Label n)] in
theorem sourcePrefixCounts_mul (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (t n : ℕ) (r : LabelRecord Label n) :
    LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels n r =
      t * LabelHierarchyCounts.sourcePrefixCounts counts labels n r :=
  pushforwardCounts_mul counts (labelRecordOf labels n) t r

abbrev PrefixPool (Label : ℕ → Type v) (depth : ℕ) :=
  Σ n : Fin depth, LabelRecord Label n.val

def sourcePoolCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (j : PrefixPool Label depth) (s : Label j.1.val) : ℕ :=
  LabelHierarchyCounts.sourcePrefixCounts counts labels (j.1.val + 1) (j.2, s)

theorem pairingProduct_source_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    pairingProduct (sourcePoolCounts counts labels depth) t =
      Nat.multinomial Finset.univ (fun a => t * counts a) := by
  classical
  unfold pairingProduct
  rw [Fintype.prod_sigma]
  have hpool (n : Fin depth) :
      (∏ r : LabelRecord Label n.val,
        poolTypeCount (sourcePoolCounts counts labels depth) ⟨n, r⟩ t) =
      LabelHierarchyCounts.refinementCount
        (LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels) n.val := by
    apply Finset.prod_congr rfl
    intro r _
    change Nat.multinomial Finset.univ
        (fun s : Label n.val => t *
          LabelHierarchyCounts.sourcePrefixCounts counts labels (n.val + 1) (r, s)) =
      Nat.multinomial Finset.univ
        (fun s : Label n.val =>
          LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a)
            labels (n.val + 1) (r, s))
    apply Nat.multinomial_congr
    intro s _
    exact (sourcePrefixCounts_mul counts labels t (n.val + 1) (r, s)).symm
  simp_rw [hpool]
  rw [Fin.prod_univ_eq_prod_range]
  exact LabelHierarchyCounts.source_refinementCount_product
    (fun a => t * counts a) labels depth hinjective

theorem pairingProduct_source_eq_exactWords_card [DecidableEq A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    pairingProduct (sourcePoolCounts counts labels depth) t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [pairingProduct_source_eq counts labels depth hinjective, exactWords_card]

theorem source_poolEntropyTotal_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) :
    poolEntropyTotal (sourcePoolCounts counts labels depth) = populationEntropyRate counts := by
  have hsource : Tendsto
      (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        (t : ℝ)) atTop (𝓝 (populationEntropyRate counts)) := by
    simpa only [pairingProduct_source_eq counts labels depth hinjective] using
      tendsto_log_multinomial_mul_div_repetition counts
  exact tendsto_nhds_unique
    (tendsto_log_pairingProduct_div (sourcePoolCounts counts labels depth)) hsource

private theorem normalized_of_per_repetition (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (K : ℕ → ℕ)
    (h : Tendsto (fun t : ℕ => Real.log (K t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts))) :
    Tendsto (fun t : ℕ => Real.log (K t : ℝ) / ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hmain : populationEntropyRate counts / (∑ a, counts a : ℕ) =
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    unfold populationEntropyRate
    exact mul_div_cancel_left₀ _ hD'
  simpa only [div_div, hmain] using h.div_const ((∑ a, counts a : ℕ) : ℝ)

theorem tendsto_log_source_pairingProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [pairingProduct_source_eq counts labels depth hinjective] using
    tendsto_log_multinomial_mul counts hD

theorem tendsto_log_source_gridProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (gridProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  apply normalized_of_per_repetition counts hD
  simpa only [source_poolEntropyTotal_eq counts labels depth hinjective] using
    tendsto_log_gridProduct_div (sourcePoolCounts counts labels depth)

theorem tendsto_log_source_auxiliaryProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (auxiliaryProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  apply normalized_of_per_repetition counts hD
  simpa only [source_poolEntropyTotal_eq counts labels depth hinjective] using
    tendsto_log_auxiliaryProduct_div (sourcePoolCounts counts labels depth)

theorem rationalLaw_exists_source_rates [DecidableEq A] (p : RationalLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      (∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a) ∧
      Tendsto
        (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (gridProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (auxiliaryProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) := by
  obtain ⟨counts, hD, hmass⟩ := p.exists_type_representation
  have hfun : (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      p.toFiniteLaw.mass := funext hmass
  refine ⟨counts, hD, hmass, ?_, ?_, ?_, ?_⟩
  · simpa only [hfun] using tendsto_log_exactWords_card_mul counts hD
  · simpa only [hfun] using tendsto_log_source_pairingProduct counts hD labels depth hinjective
  · simpa only [hfun] using tendsto_log_source_gridProduct counts hD labels depth hinjective
  · simpa only [hfun] using tendsto_log_source_auxiliaryProduct counts hD labels depth hinjective

end SourceHierarchy

end HierarchySeparationRates
end MatrixMultiplication.Foundation

end

end OAI

end FlattenModule101
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchySeparationRates -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexStageHierarchyResources -/
section FlattenModule102

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.StageHierarchyResources

open Filter HierarchySeparationRates LabelHierarchyCounts
open scoped BigOperators Topology

universe u v

local instance (priority := low) {B : Type*} : DecidableEq B := Classical.decEq B

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

def stageRefinementCount (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : ℕ :=
  refinementCount (sourcePrefixCounts (fun a => t * counts a) labels) n

def stageNodeCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) (s : Label n) : ℕ :=
  sourcePrefixCounts counts labels (n + 1) (r, s)

theorem stageRefinementCount_eq_nodeProduct (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n t : ℕ) :
    stageRefinementCount counts labels n t = pairingProduct (stageNodeCounts counts labels n) t := by
  unfold stageRefinementCount refinementCount pairingProduct
  apply Finset.prod_congr rfl
  intro r hr
  change Nat.multinomial Finset.univ
      (fun s : Label n => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s)) =
    Nat.multinomial Finset.univ
      (fun s : Label n => t * sourcePrefixCounts counts labels (n + 1) (r, s))
  apply Nat.multinomial_congr
  intro s hs
  exact sourcePrefixCounts_mul counts labels t (n + 1) (r, s)

theorem stageRefinementCount_eq_sourcePoolProduct (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ) (n : Fin depth) (t : ℕ) :
    stageRefinementCount counts labels n.val t =
      ∏ r : LabelRecord Label n.val,
        poolTypeCount (sourcePoolCounts counts labels depth) ⟨n, r⟩ t :=
  stageRefinementCount_eq_nodeProduct counts labels n.val t

theorem stageRefinementCount_pos (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : 0 < stageRefinementCount counts labels n t := by
  unfold stageRefinementCount refinementCount
  exact Finset.prod_pos (fun r _ => Nat.multinomial_pos _ _)

theorem stageConditionalWords_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    Fintype.card (ConditionalWords w
      (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))) =
      stageRefinementCount counts labels n t := by
  exact conditionalWords_card w
    (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))
    (fun r => (hword r).trans
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n r))

theorem stageConditionalPool_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    (Finset.univ.filter (fun fine : Position → Label n =>
      ∀ r s, Fintype.card {i // w i = r ∧ fine i = s} =
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))).card =
      stageRefinementCount counts labels n t := by
  simpa only [ConditionalWords, Fintype.card_subtype] using
    stageConditionalWords_card counts labels n t w hword

theorem stageConditionalWords_nonempty {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    Nonempty (ConditionalWords w
      (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))) := by
  apply Fintype.card_pos_iff.mp
  rw [stageConditionalWords_card counts labels n t w hword]
  exact stageRefinementCount_pos counts labels n t

def stageEntropyRate (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ) : ℝ :=
  poolEntropyTotal (stageNodeCounts counts labels n)

theorem stageEntropyRate_nonneg (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n : ℕ) : 0 ≤ stageEntropyRate counts labels n := by
  exact Finset.sum_nonneg (fun r _ => populationEntropyRate_nonneg
    (stageNodeCounts counts labels n r))

theorem tendsto_log_stageRefinementCount_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageRefinementCount counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) := by
  simpa only [stageRefinementCount_eq_nodeProduct, stageEntropyRate] using
    tendsto_log_pairingProduct_div (stageNodeCounts counts labels n)

def stageCost (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ) : ℕ :=
  LabelHierarchySeparation.poolAuxiliaryCost (stageRefinementCount counts labels n t)

theorem tendsto_log_stageCost_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageCost counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) :=
  LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
    (stageRefinementCount_pos counts labels n) (stageEntropyRate_nonneg counts labels n)
    (tendsto_log_stageRefinementCount_div counts labels n)

def stagePairingProduct (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageRefinementCount counts labels n.val t

def stageAuxiliaryBudget (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageCost counts labels n.val t

theorem stagePairingProduct_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stagePairingProduct counts labels (n + 1) t =
      stagePairingProduct counts labels n t * stageRefinementCount counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageRefinementCount counts labels i.val t)

theorem stageAuxiliaryBudget_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stageAuxiliaryBudget counts labels (n + 1) t =
      stageAuxiliaryBudget counts labels n t * stageCost counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageCost counts labels i.val t)

theorem stagePairingProduct_eq_exactWords_card (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    stagePairingProduct counts labels depth t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  unfold stagePairingProduct stageRefinementCount
  rw [Fin.prod_univ_eq_prod_range]
  exact source_refinementCount_product_eq_exactWords_card
    (fun a => t * counts a) labels depth hinjective

theorem stagePairingProduct_le_budget (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    stagePairingProduct counts labels depth t ≤ stageAuxiliaryBudget counts labels depth t := by
  exact Finset.prod_le_prod' (fun n _ =>
    LabelHierarchySeparation.population_le_poolAuxiliaryCost
      (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryBudget_pos (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    0 < stageAuxiliaryBudget counts labels depth t := by
  exact Finset.prod_pos (fun n _ => LabelHierarchySeparation.poolAuxiliaryCost_pos
    (stageRefinementCount counts labels n.val t))

abbrev StageAuxiliaryCoordinates (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) :=
  ∀ n : Fin depth,
    LabelHierarchySeparation.PoolAuxiliaryGroup (stageRefinementCount counts labels n.val t)

def stageAuxiliaryTensor (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) :
    Tensor ℂ (StageAuxiliaryCoordinates counts labels depth t)
      (StageAuxiliaryCoordinates counts labels depth t) (StageAuxiliaryCoordinates counts labels depth t) :=
  LabelHierarchySeparation.bankTensor (fun n : Fin depth =>
    LabelHierarchySeparation.poolAuxiliaryTensor (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryTensor_rankAtMost (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Tensor.RankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t) := by
  exact LabelHierarchySeparation.bankTensor_rankAtMost
    (fun n : Fin depth => LabelHierarchySeparation.poolAuxiliaryTensor
      (stageRefinementCount counts labels n.val t))
    (fun n => stageCost counts labels n.val t)
    (fun n => LabelHierarchySeparation.poolAuxiliaryTensor_rankAtMost
      (stageRefinementCount counts labels n.val t))

theorem stageAuxiliaryTensor_borderRankAtMost (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Tensor.BorderRankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t) :=
  (stageAuxiliaryTensor_rankAtMost counts labels depth t).borderRankAtMost

abbrev StagePairingCoordinates (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) := ∀ n : Fin depth, Fin (stageRefinementCount counts labels n.val t)

theorem card_stagePairingCoordinates (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth t : ℕ) :
    Fintype.card (StagePairingCoordinates counts labels depth t) =
      stagePairingProduct counts labels depth t := by
  simp only [StagePairingCoordinates, Fintype.card_pi, Fintype.card_fin, stagePairingProduct]

theorem sum_stageEntropyRate_eq_nodeEntropyTotal (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) =
      poolEntropyTotal (sourcePoolCounts counts labels depth) := by
  simp only [stageEntropyRate, poolEntropyTotal, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  rfl

theorem sum_stageEntropyRate_eq_source (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) = populationEntropyRate counts := by
  rw [sum_stageEntropyRate_eq_nodeEntropyTotal]
  exact source_poolEntropyTotal_eq counts labels depth hinjective

theorem tendsto_log_stageAuxiliaryBudget_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  have h := Separation.tendsto_log_nat_prod_div_nat (I := Fin depth) Finset.univ
    (fun n _ t => LabelHierarchySeparation.poolAuxiliaryCost_pos
      (stageRefinementCount counts labels n.val t))
    (fun n _ => tendsto_log_stageCost_div counts labels n.val)
  simpa only [stageAuxiliaryBudget, stageCost,
    sum_stageEntropyRate_eq_source counts labels depth hinjective] using h

theorem tendsto_log_stagePairingProduct (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (stagePairingProduct counts labels depth t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [stagePairingProduct_eq_exactWords_card counts labels depth hinjective] using
    tendsto_log_exactWords_card_mul counts hD

theorem tendsto_log_stageAuxiliaryBudget (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hmain : populationEntropyRate counts / (∑ a, counts a : ℕ) =
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    unfold populationEntropyRate
    exact mul_div_cancel_left₀ _ hD'
  simpa only [div_div, hmain] using
    (tendsto_log_stageAuxiliaryBudget_div counts labels depth hinjective).div_const
      ((∑ a, counts a : ℕ) : ℝ)

theorem source_stage_resource_rates (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∀ t, Tensor.RankAtMost (stageAuxiliaryTensor counts labels depth t)
      (stageAuxiliaryBudget counts labels depth t)) ∧
      (∀ t, stagePairingProduct counts labels depth t =
        Fintype.card (ExactWords (fun a => t * counts a))) ∧
      (∀ t, stagePairingProduct counts labels depth t ≤ stageAuxiliaryBudget counts labels depth t) ∧
      Tendsto
        (fun t : ℕ => Real.log (stagePairingProduct counts labels depth t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) ∧
      Tendsto
        (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) :=
  ⟨stageAuxiliaryTensor_rankAtMost counts labels depth,
    stagePairingProduct_eq_exactWords_card counts labels depth hinjective,
    stagePairingProduct_le_budget counts labels depth,
    tendsto_log_stagePairingProduct counts hD labels depth hinjective,
    tendsto_log_stageAuxiliaryBudget counts hD labels depth hinjective⟩

end MatrixMultiplication.Foundation.StageHierarchyResources

end

end OAI

end FlattenModule102
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexStageHierarchyResources -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.AuxiliarySeparation -/
section FlattenModule103


namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators

namespace AuxiliarySeparation

variable {X Y Z Label : Type*} [Fintype Label] [DecidableEq Label]

theorem directSum_rankAtMost (T : Tensor ℂ X Y Z)
    (readX : X → Label) (readY : Y → Label) {R : ℕ}
    (hT : Tensor.RankAtMost T R)
    (readable : ∀ x y z, T x y z ≠ 0 → readX x = readY y) :
    Tensor.RankAtMost (Tensor.dependentDirectSum (fun label =>
      Tensor.product (labelFiberTensor readX readY T label)
        (Tensor.dotPairing (Fin (Fintype.card Label)))))
      (R * Separation.gridGroupOrder (Fintype.card Label)) :=
  auxiliary_separation_directSum_rankAtMost T readX readY hT readable

theorem directSum_borderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (readX : X → Label) (readY : Y → Label) {R : ℕ}
    (hT : Tensor.BorderRankAtMost T R)
    (readable : ∀ x y z, T x y z ≠ 0 → readX x = readY y) :
    Tensor.BorderRankAtMost (Tensor.dependentDirectSum (fun label =>
      Tensor.product (labelFiberTensor readX readY T label)
        (Tensor.dotPairing (Fin (Fintype.card Label)))))
      (R * Separation.gridGroupOrder (Fintype.card Label)) :=
  auxiliary_separation_directSum_borderRankAtMost T readX readY hT readable

theorem logarithmic_cost :
    Tendsto (fun K : ℕ => Real.log (Separation.gridGroupOrder K : ℝ) /
      Real.log (K : ℝ)) atTop (𝓝 1) :=
  auxiliary_separation_logarithmic_cost

theorem cost_minus_population_tendsto_zero {population : ℕ → ℕ} {rate : ℝ}
    (positive : ∀ n, 0 < population n) (rate_nonneg : 0 ≤ rate)
    (population_rate : Tendsto
      (fun n => Real.log (population n : ℝ) / (n : ℝ)) atTop (𝓝 rate)) :
    Tendsto (fun n =>
      (Real.log (LabelHierarchySeparation.poolAuxiliaryCost (population n) : ℝ) -
        Real.log (population n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
    positive rate_nonneg population_rate).sub population_rate
  simpa only [sub_self, sub_div] using h

end AuxiliarySeparation
end MatrixMultiplication

end

end OAI

end FlattenModule103
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Separation.AuxiliarySeparation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels -/
section FlattenModule104


namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators Classical

inductive ReaderPair where
  | xy | xz | yz
  deriving DecidableEq

protected abbrev ReaderPair.enumList : List ReaderPair := [.xy, .xz, .yz]

protected theorem ReaderPair.enumList_getElem?_ctorIdx_eq (x : ReaderPair) :
    ReaderPair.enumList[ReaderPair.ctorIdx x]? = some x := by
  cases x <;> rfl

protected theorem ReaderPair.enumList_nodup : ReaderPair.enumList.Nodup := by
  apply List.Nodup.of_map ReaderPair.ctorIdx
  have h : List.map ReaderPair.ctorIdx ReaderPair.enumList = List.range 3 := rfl
  exact h ▸ List.nodup_range

instance : Fintype ReaderPair where
  elems := Finset.mk ReaderPair.enumList (Multiset.coe_nodup.mpr ReaderPair.enumList_nodup)
  complete := by
    intro x
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_iff_getElem?]
    exact ⟨ReaderPair.ctorIdx x, ReaderPair.enumList_getElem?_ctorIdx_eq x⟩

namespace ConditionalLabels

universe u v

section PairAccounting

variable {I : Type u} [Fintype I]

def pairingSize (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℕ :=
  ∏ i, if reader i = pair then population i else 1

def pairingRate (rate : I → ℝ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℝ :=
  ∑ i, if reader i = pair then rate i else 0

theorem pairingSize_pos (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) (positive : ∀ i, 0 < population i) :
    0 < pairingSize population reader pair := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact positive i
  · exact Nat.zero_lt_one

theorem pairingRate_nonneg (rate : I → ℝ) (reader : I → ReaderPair)
    (pair : ReaderPair) (nonneg : ∀ i, 0 ≤ rate i) :
    0 ≤ pairingRate rate reader pair := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact nonneg i
  · exact le_rfl

theorem pairingSize_product (population : I → ℕ) (reader : I → ReaderPair) :
    pairingSize population reader .xy * pairingSize population reader .xz *
      pairingSize population reader .yz = ∏ i, population i := by
  simp only [pairingSize, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases reader i <;> simp

theorem pairingRate_sum (rate : I → ℝ) (reader : I → ReaderPair) :
    pairingRate rate reader .xy + pairingRate rate reader .xz +
      pairingRate rate reader .yz = ∑ i, rate i := by
  simp only [pairingRate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases reader i <;> simp

theorem tendsto_log_pairingSize (population : I → ℕ → ℕ)
    (rate : I → ℝ) (reader : I → ReaderPair) (pair : ReaderPair)
    (positive : ∀ i n, 0 < population i n)
    (growth : ∀ i, Tendsto (fun n => Real.log (population i n : ℝ) / (n : ℝ))
      atTop (𝓝 (rate i))) :
    Tendsto (fun n => Real.log (pairingSize (fun i => population i n) reader pair : ℝ) /
      (n : ℝ)) atTop (𝓝 (pairingRate rate reader pair)) := by
  apply Separation.tendsto_log_nat_prod_div_nat Finset.univ
  · intro i _ n
    split_ifs
    · exact positive i n
    · exact Nat.zero_lt_one
  · intro i _
    by_cases h : reader i = pair
    · simpa only [h, ite_true] using growth i
    · simpa only [h, ite_false, Nat.cast_one, Real.log_one, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end PairAccounting

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

open StageHierarchyResources HierarchySeparationRates

def stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) (t : ℕ) : ℕ :=
  pairingSize (fun n : Fin depth => stageRefinementCount counts labels n.val t) reader pair

def stagePairingRate (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth => stageEntropyRate counts labels n.val) reader pair

theorem stagePairingSize_product (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    stagePairingSize counts labels depth reader .xy t *
      stagePairingSize counts labels depth reader .xz t *
      stagePairingSize counts labels depth reader .yz t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [stagePairingSize, stagePairingSize, stagePairingSize, pairingSize_product]
  exact stagePairingProduct_eq_exactWords_card counts labels depth complete t

theorem stagePairingRate_sum (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    stagePairingRate counts labels depth reader .xy +
      stagePairingRate counts labels depth reader .xz +
      stagePairingRate counts labels depth reader .yz = populationEntropyRate counts := by
  rw [stagePairingRate, stagePairingRate, stagePairingRate, pairingRate_sum]
  exact sum_stageEntropyRate_eq_source counts labels depth complete

theorem tendsto_log_stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      (t : ℝ)) atTop (𝓝 (stagePairingRate counts labels depth reader pair)) := by
  exact tendsto_log_pairingSize _ _ reader pair
    (fun n => stageRefinementCount_pos counts labels n.val)
    (fun n => tendsto_log_stageRefinementCount_div counts labels n.val)

theorem tendsto_log_stagePairingSize_normalized (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (stagePairingRate counts labels depth reader pair / (∑ a, counts a : ℕ))) := by
  simpa only [div_div] using
    (tendsto_log_stagePairingSize counts labels depth reader pair).div_const
      ((∑ a, counts a : ℕ) : ℝ)

theorem auxiliary_overhead_tendsto_zero (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    Tendsto (fun t =>
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 0) := by
  have h := (tendsto_log_stageAuxiliaryBudget counts hD labels depth complete).sub
    (tendsto_log_exactWords_card_mul counts hD)
  simpa only [sub_self, sub_div] using h

theorem auxiliary_overhead_nonneg (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    0 ≤ Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
      Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) := by
  apply sub_nonneg.mpr
  rw [← stagePairingProduct_eq_exactWords_card counts labels depth complete t]
  apply Real.log_le_log
  · apply Nat.cast_pos.mpr
    exact Finset.prod_pos (fun n _ => stageRefinementCount_pos counts labels n.val t)
  · exact_mod_cast stagePairingProduct_le_budget counts labels depth t

theorem charged_cost_tendsto (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) (C : ℝ) :
    Tendsto (fun t => C +
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 C) := by
  simpa only [add_zero] using
    (auxiliary_overhead_tendsto_zero counts hD labels depth complete).const_add C

theorem limit_le_source_cost (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth))
    {value : ℕ → ℝ} {rate C : ℝ}
    (limit : Tendsto value atTop (𝓝 rate))
    (finite_bound : ∀ᶠ t in atTop, value t ≤ C +
      (Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) -
        Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ)) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) : rate ≤ C :=
  le_of_tendsto_of_tendsto limit
    (charged_cost_tendsto counts hD labels depth complete C) finite_bound

def lawPairingRate (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth =>
    (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val) reader pair

theorem lawPairingRate_sum (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz +
      lawPairingRate p labels depth reader .yz = finiteEntropy p.mass := by
  rw [lawPairingRate, lawPairingRate, lawPairingRate, pairingRate_sum,
    Fin.sum_univ_eq_sum_range]
  exact FiniteLabelHierarchy.ofLawLabels_refinementEntropy_sum p labels depth complete

theorem incident_rate_eq_prefix_entropy (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut) :
    lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz =
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  let hierarchy := FiniteLabelHierarchy.ofLawLabels p labels depth
  have hterms : ∀ n : Fin depth,
      (if reader n = .xy then hierarchy.refinementEntropy n.val else 0) +
        (if reader n = .xz then hierarchy.refinementEntropy n.val else 0) =
        if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
    intro n
    cases hr : reader n with
    | xy =>
        have hn := (incident_prefix n).mp (Or.inl hr)
        simp [hn]
    | xz =>
        have hn := (incident_prefix n).mp (Or.inr hr)
        simp [hn]
    | yz =>
        have hn : ¬n.val < cut := by
          intro h
          rcases (incident_prefix n).mpr h with h | h <;> simp [hr] at h
        simp [hn]
  have hfilter : (Finset.range depth).filter (fun n => n < cut) = Finset.range cut := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    lawPairingRate p labels depth reader .xy +
        lawPairingRate p labels depth reader .xz =
        ∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0 := by
      simp only [lawPairingRate, pairingRate, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => hterms n)
    _ = ∑ n ∈ Finset.range cut, hierarchy.refinementEntropy n := by
      rw [show (∑ n : Fin depth, if n.val < cut then hierarchy.refinementEntropy n.val else 0) =
        ∑ n ∈ Finset.range depth, if n < cut then hierarchy.refinementEntropy n else 0 from
          Fin.sum_univ_eq_sum_range
            (fun n => if n < cut then hierarchy.refinementEntropy n else 0) depth]
      rw [← Finset.sum_filter, hfilter]
    _ = finiteEntropy (hierarchy.prefixLaw cut hcut).mass :=
      (hierarchy.prefixLaw_entropy cut hcut).symm
    _ = finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
      rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass]

theorem remaining_rate_eq_entropy_sub_prefix (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth cut : ℕ) (hcut : cut ≤ depth)
    (reader : Fin depth → ReaderPair)
    (incident_prefix : ∀ n : Fin depth,
      (reader n = .xy ∨ reader n = .xz) ↔ n.val < cut)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    lawPairingRate p labels depth reader .yz = finiteEntropy p.mass -
      finiteEntropy (p.map (labelRecordOf labels cut)).mass := by
  have hsum := lawPairingRate_sum p labels depth reader complete
  have hprefix := incident_rate_eq_prefix_entropy p labels depth cut hcut reader incident_prefix
  linarith

end SourceHierarchy
end ConditionalLabels
end MatrixMultiplication

end

end OAI

end FlattenModule104
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity -/
section FlattenModule105

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.ConditionalLabels

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical

universe u v w
variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem refinementEntropy_eq_prefix_difference (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth n : ℕ) (hn : n < depth) :
    (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n =
      finiteEntropy (p.map (labelRecordOf labels (n + 1))).mass -
        finiteEntropy (p.map (labelRecordOf labels n)).mass := by
  have h := (FiniteLabelHierarchy.ofLawLabels p labels depth).prefixLaw_entropy_succ
    n (Nat.succ_le_of_lt hn)
  rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass,
    FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass] at h
  linarith

theorem tendsto_map_entropy {J : Type w} {filter : Filter J}
    {p : J → FiniteLaw A} {q : FiniteLaw A}
    (mass : ∀ a, Tendsto (fun j => (p j).mass a) filter (𝓝 (q.mass a)))
    {B : Type*} [Fintype B] (label : A → B) :
    Tendsto (fun j => finiteEntropy ((p j).map label).mass) filter
      (𝓝 (finiteEntropy (q.map label).mass)) := by
  apply FiniteLaw.entropy_tendsto
  intro b
  simp only [FiniteLaw.map_mass]
  apply tendsto_finsetSum
  intro a _
  by_cases h : label a = b
  · simpa only [h, ite_true] using mass a
  · simp only [h, ite_false]
    exact tendsto_const_nhds

theorem tendsto_lawPairingRate {J : Type w} {filter : Filter J}
    {p : J → FiniteLaw A} {q : FiniteLaw A}
    (mass : ∀ a, Tendsto (fun j => (p j).mass a) filter (𝓝 (q.mass a)))
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun j => lawPairingRate (p j) labels depth reader pair) filter
      (𝓝 (lawPairingRate q labels depth reader pair)) := by
  unfold lawPairingRate pairingRate
  apply tendsto_finsetSum
  intro n _
  by_cases h : reader n = pair
  · simp only [h, ite_true,
      refinementEntropy_eq_prefix_difference _ labels depth n.val n.isLt]
    exact (tendsto_map_entropy mass (labelRecordOf labels (n.val + 1))).sub
      (tendsto_map_entropy mass (labelRecordOf labels n.val))
  · simp only [h, ite_false]
    exact tendsto_const_nhds

theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.norm_eq_abs, RationalLaw.toFiniteLaw_mass] using (close n a).le
  simpa only [sub_add_cancel, zero_add] using hdifference.add_const (p.mass a)

theorem exists_rational_with_strict_margins (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ) (reader : Fin depth → ReaderPair)
    {k C target : ℝ}
    (positive : 0 < lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz)
    (aspect : k * (lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz) <
      2 * lawPairingRate p labels depth reader .yz)
    (cost : 2 * C < target * (lawPairingRate p labels depth reader .xy +
      lawPairingRate p labels depth reader .xz)) :
    ∃ q : RationalLaw A,
      0 < lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz ∧
      k * (lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz) <
        2 * lawPairingRate q.toFiniteLaw labels depth reader .yz ∧
      2 * C < target * (lawPairingRate q.toFiniteLaw labels depth reader .xy +
        lawPairingRate q.toFiniteLaw labels depth reader .xz) := by
  obtain ⟨q, hq⟩ := exists_rational_law_sequence p
  have hincident := (tendsto_lawPairingRate hq labels depth reader .xy).add
    (tendsto_lawPairingRate hq labels depth reader .xz)
  have hhidden := tendsto_lawPairingRate hq labels depth reader .yz
  have hpos := hincident.eventually_const_lt positive
  have haspect := (hincident.const_mul k).eventually_lt (hhidden.const_mul 2) aspect
  have hcost := (hincident.const_mul target).eventually_const_lt cost
  obtain ⟨n, hnpos, hnaspect, hncost⟩ := (hpos.and (haspect.and hcost)).exists
  exact ⟨q n, hnpos, hnaspect, hncost⟩

end MatrixMultiplication.ConditionalLabels

end

end OAI

end FlattenModule105
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Tag -/
section FlattenModule106





namespace OAI

/-!
# The entropy limit for matched types

The finite hypothesis in this file is an inequality at every integral type.
The conclusion follows by first repeating a fixed type, and then approximating
an arbitrary probability law by rational laws. No entropy inequality is
included in the finite hypothesis.
-/

noncomputable section

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

namespace MatrixMultiplication.AuxiliarySeparation

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The character contribution of all words of one prescribed type. -/
def typeContribution (values : A → ℝ) (p : ℝ) (counts : A → ℕ) (t : ℕ) : ℝ :=
  (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) ^ p *
    ∏ a, values a ^ (t * counts a)

theorem typeContribution_pos (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (t : ℕ) :
    0 < typeContribution values p counts t := by
  unfold typeContribution
  exact mul_pos
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p)
    (Finset.prod_pos (fun a _ => pow_pos (hvalues a) _))

theorem log_typeContribution (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (t : ℕ) :
    Real.log (typeContribution values p counts t) =
      p * Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) +
        (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (values a) := by
  unfold typeContribution
  rw [Real.log_mul
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p).ne'
    (Finset.prod_pos (fun a _ => pow_pos (hvalues a) _)).ne',
    Real.log_rpow (Nat.cast_pos.mpr (exactWords_card_pos _)),
    Real.log_prod (fun a _ => (pow_pos (hvalues a) _).ne')]
  simp only [Real.log_pow, Nat.cast_mul, mul_assoc, Finset.mul_sum]

/-- Repeating one exact type has its Shannon entropy growth rate. -/
theorem typeContribution_rate (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (typeContribution values p counts t) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (p * finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a))) := by
  have hlimit := ((tendsto_log_exactWords_card_mul counts hD).const_mul p).add_const
    (∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a))
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  rw [log_typeContribution values p counts hvalues]
  have ht' : (t : ℝ) ≠ 0 := (Nat.cast_pos.mpr ht).ne'
  have hD' : (∑ a, counts a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  push_cast
  field_simp

/-- A finite bound on each repetition of a fixed type implies its logarithmic
entropy bound; the fixed loss `C` disappears in the limit. -/
theorem log_type_bound (values : A → ℝ) (p source C : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hD : 0 < ∑ a, counts a)
    (hfinite : ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
      ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a) ≤
        Real.log source := by
  apply (Real.le_log_iff_exp_le hsource).2
  apply exp_le_of_tendsto_log_div hsource hC
    (tendsto_id.atTop_mul_const' hD)
    (Eventually.of_forall (typeContribution_pos values p counts hvalues))
  · simpa only [Nat.cast_mul, id_eq] using typeContribution_rate values p counts hvalues hD
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    exact hfinite t ht

/-- Rational laws can be represented by one exact integral type. -/
theorem rational_log_tag_of_finite_type_bounds
    (q : RationalLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy q.toFiniteLaw.mass +
      ∑ a, q.toFiniteLaw.mass a * Real.log (values a) ≤ Real.log source := by
  obtain ⟨counts, hD, hmass⟩ := q.exists_type_representation
  have h := log_type_bound values p source C counts hvalues hsource hC hD
    (hfinite counts hD)
  simpa only [hmass] using h

/-- Integral type bounds imply the tag inequality on the whole finite
probability simplex, including laws with zero coordinates. -/
theorem log_tag_of_finite_type_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy q.mass +
      ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
  obtain ⟨r, hr⟩ := MatrixMultiplication.ConditionalLabels.exists_rational_law_sequence q
  have hlinear : Tendsto
      (fun n => ∑ a, (r n).toFiniteLaw.mass a * Real.log (values a)) atTop
      (𝓝 (∑ a, q.mass a * Real.log (values a))) :=
    tendsto_finsetSum Finset.univ (fun a _ => (hr a).mul_const _)
  have hlimit := ((FiniteLaw.entropy_tendsto hr).const_mul p).add hlinear
  exact le_of_tendsto hlimit (Eventually.of_forall (fun n =>
    rational_log_tag_of_finite_type_bounds (r n) values p source C
      hvalues hsource hC hfinite))

/-- Exponentiating gives the entropy-weighted geometric-mean form. -/
theorem tag_of_finite_type_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  have h := Real.exp_le_exp.mpr
    (log_tag_of_finite_type_bounds q values p source C hvalues hsource hC hfinite)
  rw [Real.exp_log hsource, Real.exp_add, Real.exp_sum] at h
  convert h using 1
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [Real.rpow_def_of_pos (hvalues a), mul_comm]

/-- It suffices to prove one finite inequality for every integral type. -/
theorem log_tag_of_integral_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    p * finiteEntropy q.mass +
      ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
  apply log_tag_of_finite_type_bounds q values p source C hvalues hsource hC
  intro counts hD t ht
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a := by
    rw [Finset.mul_sum]
  have hpositive : 0 < ∑ a, t * counts a := by
    rw [hsum]
    exact Nat.mul_pos ht hD
  simpa only [typeContribution, hsum] using hfinite (fun a => t * counts a) hpositive

/-- The geometric-mean formulation from finite inequalities for integral types. -/
theorem tag_of_integral_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  apply tag_of_finite_type_bounds q values p source C hvalues hsource hC
  intro counts hD t ht
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a := by
    rw [Finset.mul_sum]
  have hpositive : 0 < ∑ a, t * counts a := by
    rw [hsum]
    exact Nat.mul_pos ht hD
  simpa only [typeContribution, hsum] using hfinite (fun a => t * counts a) hpositive

namespace Character

variable {I X Y Z : Type} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [Fintype Z]
  {BX BY BZ : I → Type}
  [∀ a, Fintype (BX a)] [∀ a, Fintype (BY a)] [∀ a, Fintype (BZ a)]

/-- For a character, nonzero tensors supply all positivity needed by the
entropy limit. The only quantitative premise is the finite integral-type
comparison with the paper's fixed loss five. -/
theorem log_tag_of_integral_type_comparison (χ : Character)
    (q : FiniteLaw I) (T : Tensor ℂ X Y Z)
    (B : ∀ a, Tensor ℂ (BX a) (BY a) (BZ a)) (p : ℝ)
    (hT : T ≠ 0) (hB : ∀ a, B a ≠ 0)
    (hfinite : ∀ counts : I → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p *
          ∏ a, χ.value (B a) ^ counts a ≤
        5 * χ.value T ^ (∑ a, counts a)) :
    p * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value T) :=
  MatrixMultiplication.AuxiliarySeparation.log_tag_of_integral_bounds q (fun a => χ.value (B a)) p
    (χ.value T) 5 (fun a => lt_of_lt_of_le zero_lt_one (χ.one_le_value (hB a)))
    (lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)) (by norm_num) hfinite

/-- The entropy-weighted tag bound, once the finite matched-type tensor
comparison has been established. -/
theorem tag_of_integral_type_comparison (χ : Character)
    (q : FiniteLaw I) (T : Tensor ℂ X Y Z)
    (B : ∀ a, Tensor ℂ (BX a) (BY a) (BZ a)) (p : ℝ)
    (hT : T ≠ 0) (hB : ∀ a, B a ≠ 0)
    (hfinite : ∀ counts : I → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p *
          ∏ a, χ.value (B a) ^ counts a ≤
        5 * χ.value T ^ (∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, χ.value (B a) ^ q.mass a ≤
      χ.value T :=
  MatrixMultiplication.AuxiliarySeparation.tag_of_integral_bounds q (fun a => χ.value (B a)) p
    (χ.value T) 5 (fun a => lt_of_lt_of_le zero_lt_one (χ.one_le_value (hB a)))
    (lt_of_lt_of_le zero_lt_one (χ.one_le_value hT)) (by norm_num) hfinite

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule106
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Tag -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Fourier -/
section FlattenModule107


namespace OAI

/-!
# Finite root-of-unity filters

Averaging the integer powers of a primitive root over one period detects
exactly the exponents divisible by that period. This is the finite Fourier
filter used for auxiliary separation.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- The sum over a complete period of a root of unity is zero unless the root is one. -/
lemma sum_pow_root_of_unity (z : ℂ) (L : ℕ) (hz : z ^ L = 1) :
    (∑ r ∈ Finset.range L, z ^ r) = if z = 1 then (L : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · have hsum : (1 - z) * ∑ r ∈ Finset.range L, z ^ r = 0 := by
      rw [mul_neg_geom_sum, hz, sub_self]
    exact (mul_eq_zero.mp hsum).resolve_left (sub_ne_zero.mpr (Ne.symm h))

/-- An unnormalized finite Fourier filter, with an integer exponent. -/
theorem sum_zpow_primitive_root {ζ : ℂ} {L : ℕ}
    (hζ : IsPrimitiveRoot ζ L) (e : ℤ) :
    (∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e)) =
      if (L : ℤ) ∣ e then (L : ℂ) else 0 := by
  have hpow : (ζ ^ e) ^ L = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
  have hterm (r : ℕ) : ζ ^ ((r : ℤ) * e) = (ζ ^ e) ^ r := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  simp_rw [hterm]
  rw [sum_pow_root_of_unity _ _ hpow]
  simp only [hζ.zpow_eq_one_iff_dvd]

/-- Averaging over a primitive root's period selects exactly its divisible exponents. -/
theorem normalized_sum_zpow_primitive_root {ζ : ℂ} {L : ℕ}
    (hL : L ≠ 0) (hζ : IsPrimitiveRoot ζ L) (e : ℤ) :
    (L : ℂ)⁻¹ * (∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e)) =
      if (L : ℤ) ∣ e then 1 else 0 := by
  rw [sum_zpow_primitive_root hζ e]
  split_ifs <;> simp [hL]

/-- Divisibility by a positive period is exact equality to zero inside one period. -/
lemma int_dvd_iff_eq_zero_of_abs_lt {L : ℕ} {e : ℤ} (he : |e| < (L : ℤ)) :
    (L : ℤ) ∣ e ↔ e = 0 := by
  constructor
  · intro hd
    apply abs_eq_zero.mp
    exact Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg e) he
      ((dvd_abs (L : ℤ) e).mpr hd)
  · rintro rfl
    exact dvd_zero _

/-- Within one period, the finite Fourier filter selects exactly exponent zero. -/
theorem normalized_sum_zpow_primitive_root_of_abs_lt {ζ : ℂ} {L : ℕ} {e : ℤ}
    (hL : L ≠ 0) (hζ : IsPrimitiveRoot ζ L) (he : |e| < (L : ℤ)) :
    (L : ℂ)⁻¹ * (∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e)) =
      if e = 0 then 1 else 0 := by
  rw [normalized_sum_zpow_primitive_root hL hζ e]
  simp only [int_dvd_iff_eq_zero_of_abs_lt he]

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule107
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Fourier -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.NoWrap -/
section FlattenModule108


namespace OAI

/-!
# The Fourier projection has no modular wrap

Section 4.1 of *Matrix Multiplication via Auxiliary Separation and Polynomial
Multiplication* uses exactly `5 * M` Fourier phases. The exponent
`u - v + 2 * (g - h)` has absolute value at most `3 * (M - 1)` when all four
labels lie in `{1, ..., M}`. Consequently, divisibility by `5 * M` is equivalent
to the exact integer support equation.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- The explicit bound for the exponent in the finite Fourier projection. -/
theorem fourierPhase_abs_le {M h g u v : ℤ}
    (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |u - v + 2 * (g - h)| ≤ 3 * (M - 1) := by
  rw [abs_le']
  constructor <;> omega

/-- The Fourier modulus exceeds the full possible range of the exponent. -/
theorem fourierRadius_lt_modulus {M : ℤ} (hM : 1 ≤ M) :
    3 * (M - 1) < 5 * M := by
  omega

/-- Every possible exponent lies strictly between minus and plus the modulus. -/
theorem fourierPhase_abs_lt {M h g u v : ℤ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |u - v + 2 * (g - h)| < 5 * M :=
  lt_of_le_of_lt (fourierPhase_abs_le hh hg hu hv) (fourierRadius_lt_modulus hM)

/-- Modular Fourier support is exact integer support for the allowed labels. -/
theorem fourierPhase_eq_zero_of_dvd {M h g u v : ℤ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (hdiv : 5 * M ∣ u - v + 2 * (g - h)) :
    u - v + 2 * (g - h) = 0 :=
  Int.eq_zero_of_abs_lt_dvd hdiv (fourierPhase_abs_lt hM hh hg hu hv)

/-- Characterization of the surviving Fourier support without modular arithmetic. -/
theorem fourierPhase_dvd_iff_eq_zero {M h g u v : ℤ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    (5 * M ∣ u - v + 2 * (g - h)) ↔ u - v + 2 * (g - h) = 0 := by
  constructor
  · exact fourierPhase_eq_zero_of_dvd hM hh hg hu hv
  · intro hzero
    rw [hzero]
    exact ⟨0, by simp⟩

/-- The same exponent bound for natural-number labels, interpreted in `ℤ`. -/
theorem fourierPhase_abs_le_nat {M h g u v : ℕ}
    (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    |(u : ℤ) - v + 2 * ((g : ℤ) - h)| ≤ 3 * ((M : ℤ) - 1) := by
  apply fourierPhase_abs_le <;> omega

/-- Natural-number labels admit no additional solutions modulo `5 * M`. -/
theorem fourierPhase_dvd_iff_eq_zero_nat {M h g u v : ℕ}
    (hM : 1 ≤ M) (hh : 1 ≤ h ∧ h ≤ M) (hg : 1 ≤ g ∧ g ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    ((5 : ℤ) * M ∣ (u : ℤ) - v + 2 * ((g : ℤ) - h)) ↔
      (u : ℤ) - v + 2 * ((g : ℤ) - h) = 0 := by
  apply fourierPhase_dvd_iff_eq_zero <;> omega

/-- Zero-based finite labels have the same exponent as the paper's labels plus one. -/
theorem fourierPhase_abs_le_fin {M : ℕ} (h g u v : Fin M) :
    |(u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val)| ≤
      3 * ((M : ℤ) - 1) := by
  have hh := h.isLt
  have hg := g.isLt
  have hu := u.isLt
  have hv := v.isLt
  rw [abs_le']
  constructor <;> omega

/-- The support test for a Fourier projection indexed by `Fin M`. -/
theorem fourierPhase_dvd_iff_eq_zero_fin {M : ℕ} (h g u v : Fin M) :
    ((5 : ℤ) * M ∣ (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val)) ↔
      (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val) = 0 := by
  constructor
  · intro hdiv
    apply Int.eq_zero_of_abs_lt_dvd hdiv
    apply lt_of_le_of_lt (fourierPhase_abs_le_fin h g u v)
    apply fourierRadius_lt_modulus
    have hh := h.isLt
    omega
  · intro hzero
    rw [hzero]
    exact ⟨0, by simp⟩

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule108
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.NoWrap -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.SquareWeights -/
section FlattenModule109


namespace OAI

/-!+# The square weights in auxiliary separation

Sections 4.1–4.3 use the phase `u - v + 2 * (g - h)` to select monomials.
On a selected monomial, the three integer variable weights add to `(g - h)^2`.
Thus the surviving monomials have nonnegative total degree, although individual
variable weights may be negative. Their degree is zero precisely when the guess
`g` matches the sector `h` and the auxiliary labels agree.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- The exponent occurring in the finite Fourier projection. -/
def phase (g h u v : ℤ) : ℤ := u - v + 2 * (g - h)

/-- Weight on the first tensor leg, which carries the guessed sector label. -/
def firstWeight (g : ℤ) : ℤ := g ^ 2

/-- Weight on the second tensor leg. -/
def secondWeight (h u : ℤ) : ℤ := h * u - h ^ 2

/-- Weight on the third tensor leg. -/
def thirdWeight (h v : ℤ) : ℤ := -(h * v)

/-- Total weight of a target monomial after the three independent substitutions. -/
def totalWeight (g h u v : ℤ) : ℤ :=
  firstWeight g + secondWeight h u + thirdWeight h v

theorem totalWeight_eq_square_add_phase (g h u v : ℤ) :
    totalWeight g h u v = (g - h) ^ 2 + h * phase g h u v := by
  unfold totalWeight firstWeight secondWeight thirdWeight phase
  ring

/-- The projection equation converts the total weight into a square. -/
theorem totalWeight_eq_sq_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = (g - h) ^ 2 := by
  rw [totalWeight_eq_square_add_phase, hphase, mul_zero, add_zero]

theorem totalWeight_nonneg_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) : 0 ≤ totalWeight g h u v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase]
  exact sq_nonneg (g - h)

/-- On the Fourier support, precisely the correctly matched terms have weight zero. -/
theorem totalWeight_eq_zero_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalWeight g h u v = 0 ↔ g = h ∧ u = v := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase, sq_eq_zero_iff]
  constructor
  · intro hzero
    have hgh : g = h := sub_eq_zero.mp hzero
    refine ⟨hgh, ?_⟩
    unfold phase at hphase
    omega
  · rintro ⟨hgh, _⟩
    exact sub_eq_zero.mpr hgh

theorem phase_and_totalWeight_eq_zero_iff (g h u v : ℤ) :
    (phase g h u v = 0 ∧ totalWeight g h u v = 0) ↔ g = h ∧ u = v := by
  constructor
  · rintro ⟨hphase, hweight⟩
    exact (totalWeight_eq_zero_iff_of_phase_eq_zero hphase).mp hweight
  · rintro ⟨rfl, rfl⟩
    simp [phase, totalWeight, firstWeight, secondWeight, thirdWeight]

theorem totalWeight_pos_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    0 < totalWeight g h u v ↔ g ≠ h := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase, sq_pos_iff, sub_ne_zero]

/-- The degree bound in Section 4.3, for sector labels in `1, …, M`. -/
theorem totalWeight_le_of_labels {M g h u v : ℤ}
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hphase : phase g h u v = 0) :
    totalWeight g h u v ≤ (M - 1) ^ 2 := by
  rw [totalWeight_eq_sq_of_phase_eq_zero hphase]
  have hprod : 0 ≤ ((M - 1) - (g - h)) * ((M - 1) + (g - h)) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- The polynomial degree attached to a surviving monomial. -/
def totalDegree (g h u v : ℤ) : ℕ := (totalWeight g h u v).toNat

theorem totalDegree_cast_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    (totalDegree g h u v : ℤ) = totalWeight g h u v := by
  exact Int.toNat_of_nonneg (totalWeight_nonneg_of_phase_eq_zero hphase)

theorem totalDegree_eq_zero_iff_of_phase_eq_zero {g h u v : ℤ}
    (hphase : phase g h u v = 0) :
    totalDegree g h u v = 0 ↔ g = h ∧ u = v := by
  have hcast := totalDegree_cast_of_phase_eq_zero hphase
  have hzero : totalDegree g h u v = 0 ↔ totalWeight g h u v = 0 := by omega
  exact hzero.trans (totalWeight_eq_zero_iff_of_phase_eq_zero hphase)

theorem totalDegree_le_of_labels {M : ℕ} {g h u v : ℤ}
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hphase : phase g h u v = 0) :
    totalDegree g h u v ≤ (M - 1) ^ 2 := by
  have hM : 1 ≤ M := by omega
  have hbound := totalWeight_le_of_labels hg hh hphase
  have hcast := totalDegree_cast_of_phase_eq_zero hphase
  have hsub : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
  exact_mod_cast (show (totalDegree g h u v : ℤ) ≤ ((M - 1 : ℕ) : ℤ) ^ 2 by
    rw [hcast, hsub]
    exact hbound)

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule109
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.SquareWeights -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.FiniteProjection -/
section FlattenModule110




namespace OAI

/-!
# Exact finite Fourier projection and square filtering

The `5 * M`-term Fourier average is applied to an arbitrary branch coefficient.
The label bounds eliminate modular wrap. The weights on the three tensor legs
then give a nonnegative square degree on every surviving branch. Taking the
constant coefficient retains exactly the branches with `g = h` and `u = v`.

The finite-family statements permit arbitrary coefficients and arbitrary
repetitions of labels; they use only linearity of the Fourier projection and
coefficient extraction, without assumptions on an ambient tensor.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- A normalized finite Fourier average of one branch coefficient. -/
noncomputable def finiteFourierCoefficient (ζ : ℂ) (L : ℕ) (e : ℤ) (c : ℂ) : ℂ :=
  (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, ζ ^ ((r : ℤ) * e) * c

/-- The Fourier average is a scalar support indicator, for every coefficient. -/
theorem finiteFourierCoefficient_eq_ite {ζ : ℂ} {L : ℕ}
    (hL : L ≠ 0) (hζ : IsPrimitiveRoot ζ L) (e : ℤ) (c : ℂ) :
    finiteFourierCoefficient ζ L e c = if (L : ℤ) ∣ e then c else 0 := by
  unfold finiteFourierCoefficient
  rw [← Finset.sum_mul, ← mul_assoc, normalized_sum_zpow_primitive_root hL hζ]
  split_ifs <;> simp

/-- Averaging a finite family of branches agrees with averaging each branch. -/
theorem finiteFourierCoefficient_sum {ι : Type*} (s : Finset ι)
    (ζ : ℂ) (L : ℕ) (e : ι → ℤ) (c : ι → ℂ) :
    (L : ℂ)⁻¹ * (∑ r ∈ Finset.range L, ∑ i ∈ s, ζ ^ ((r : ℤ) * e i) * c i) =
      ∑ i ∈ s, finiteFourierCoefficient ζ L (e i) (c i) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  rfl

/-- Exactly `5 * M` phases select the integer support equation. -/
theorem fiveMFourierCoefficient_eq_ite {ζ : ℂ} {M : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : ℂ) :
    finiteFourierCoefficient ζ (5 * M) (phase g h u v) c =
      if phase g h u v = 0 then c else 0 := by
  rw [finiteFourierCoefficient_eq_ite (by omega) hζ]
  have hnoWrap := fourierPhase_dvd_iff_eq_zero (M := (M : ℤ))
    (by omega) hh hg hu hv
  simp only [phase, Nat.cast_mul, Nat.cast_ofNat, hnoWrap]
  rfl

/-- A projected branch, recorded as an ordinary polynomial after Fourier averaging. -/
noncomputable def projectedBranchPolynomial (ζ : ℂ) (M : ℕ)
    (g h u v : ℤ) (c : ℂ) : Polynomial ℂ :=
  Polynomial.monomial (totalDegree g h u v)
    (finiteFourierCoefficient ζ (5 * M) (phase g h u v) c)

/-- The surviving polynomial weight is the square `(g - h)^2`. -/
theorem projectedBranchPolynomial_eq_ite {ζ : ℂ} {M : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : ℂ) :
    projectedBranchPolynomial ζ M g h u v c =
      if phase g h u v = 0 then Polynomial.monomial ((g - h) ^ 2).toNat c else 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hζ hg hh hu hv]
  split_ifs with hp
  · rw [totalDegree, totalWeight_eq_sq_of_phase_eq_zero hp]
  · simp

/-- A coefficient occurs exactly on the Fourier support at its integer total weight. -/
theorem projectedBranchPolynomial_coeff {ζ : ℂ} {M n : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : ℂ) :
    (projectedBranchPolynomial ζ M g h u v c).coeff n =
      if phase g h u v = 0 ∧ totalWeight g h u v = (n : ℤ) then c else 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hζ hg hh hu hv]
  by_cases hp : phase g h u v = 0
  · have hd : totalDegree g h u v = n ↔ totalWeight g h u v = (n : ℤ) := by
      have hcast := totalDegree_cast_of_phase_eq_zero hp
      omega
    simp only [hp, ↓reduceIte, Polynomial.coeff_monomial, hd, true_and]
  · simp [hp]

/-- Each projected branch has no polynomial coefficient above `(M - 1)^2`. -/
theorem projectedBranchPolynomial_coeff_eq_zero_of_lt
    {ζ : ℂ} {M n : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (hn : (M - 1) ^ 2 < n) (c : ℂ) :
    (projectedBranchPolynomial ζ M g h u v c).coeff n = 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hζ hg hh hu hv]
  split_ifs with hp
  · have hd := totalDegree_le_of_labels hg hh hp
    exact Polynomial.coeff_monomial_of_ne c (by omega)
  · simp

/-- Constant coefficient extraction is the exact square filter, with no restriction
on the original complex coefficient. -/
theorem projectedBranchPolynomial_coeff_zero {ζ : ℂ} {M : ℕ} {g h u v : ℤ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : 1 ≤ g ∧ g ≤ M) (hh : 1 ≤ h ∧ h ≤ M)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) (c : ℂ) :
    (projectedBranchPolynomial ζ M g h u v c).coeff 0 =
      if g = h ∧ u = v then c else 0 := by
  unfold projectedBranchPolynomial
  rw [fiveMFourierCoefficient_eq_ite hM hζ hg hh hu hv]
  by_cases hp : phase g h u v = 0
  · simp only [hp, ↓reduceIte, Polynomial.coeff_monomial,
      totalDegree_eq_zero_iff_of_phase_eq_zero hp]
  · have hlabels : ¬ (g = h ∧ u = v) := by
      rintro ⟨rfl, rfl⟩
      exact hp (by simp [phase])
    simp [hp, hlabels]

/-- Apply the finite Fourier projection and square weights branch by branch. -/
noncomputable def projectedPolynomial {ι : Type*} (s : Finset ι)
    (ζ : ℂ) (M : ℕ) (g h u v : ι → ℤ) (c : ι → ℂ) : Polynomial ℂ :=
  ∑ i ∈ s, projectedBranchPolynomial ζ M (g i) (h i) (u i) (v i) (c i)

/-- Every coefficient of the projected polynomial has the exact integer support. -/
theorem projectedPolynomial_coeff {ι : Type*} (s : Finset ι)
    {ζ : ℂ} {M n : ℕ} (g h u v : ι → ℤ) (c : ι → ℂ)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ M g h u v c).coeff n =
      ∑ i ∈ s, if phase (g i) (h i) (u i) (v i) = 0 ∧
        totalWeight (g i) (h i) (u i) (v i) = (n : ℤ) then c i else 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  exact projectedBranchPolynomial_coeff hM hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) (c i)

/-- Exact finite filtering for an arbitrary finite family of branch coefficients. -/
theorem projectedPolynomial_coeff_zero {ι : Type*} (s : Finset ι)
    {ζ : ℂ} {M : ℕ} (g h u v : ι → ℤ) (c : ι → ℂ)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ M g h u v c).coeff 0 =
      ∑ i ∈ s, if g i = h i ∧ u i = v i then c i else 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  exact projectedBranchPolynomial_coeff_zero hM hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) (c i)

/-- The finite projected polynomial has support only in degrees at most `(M - 1)^2`. -/
theorem projectedPolynomial_coeff_eq_zero_of_lt {ι : Type*} (s : Finset ι)
    {ζ : ℂ} {M n : ℕ} (g h u v : ι → ℤ) (c : ι → ℂ)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M)
    (hn : (M - 1) ^ 2 < n) :
    (projectedPolynomial s ζ M g h u v c).coeff n = 0 := by
  classical
  unfold projectedPolynomial
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  exact projectedBranchPolynomial_coeff_eq_zero_of_lt hM hζ (hg i hi) (hh i hi)
    (hu i hi) (hv i hi) hn (c i)

/-- The degree bound is independent of the number or values of the coefficients. -/
theorem projectedPolynomial_natDegree_le {ι : Type*} (s : Finset ι)
    {ζ : ℂ} {M : ℕ} (g h u v : ι → ℤ) (c : ι → ℂ)
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ M) (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ M)
    (hu : ∀ i ∈ s, 1 ≤ u i ∧ u i ≤ M) (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ M) :
    (projectedPolynomial s ζ M g h u v c).natDegree ≤ (M - 1) ^ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact projectedPolynomial_coeff_eq_zero_of_lt s g h u v c hM hζ hg hh hu hv hn

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule110
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.FiniteProjection -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic -/
section FlattenModule111








namespace OAI

/-!
# The tensor map with exactly `5M` copies

The branches have a common first coordinate space and common sizes on the other
two legs. Their second and third coordinates carry a matching sector label.
The three maps below are independent linear substitutions on the three legs of
`5M` complete copies of the source tensor.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X Y Z : Type*}

/-- The paper numbers sectors from one, while `Fin M` numbers them from zero. -/
def sectorNumber (i : Fin M) : ℤ := (i.val : ℤ) + 1

theorem sectorNumber_bounds (i : Fin M) :
    1 ≤ sectorNumber i ∧ sectorNumber i ≤ M := by
  have hi := i.isLt
  unfold sectorNumber
  omega

theorem sectorNumber_injective : Function.Injective (@sectorNumber M) := by
  intro i j hij
  apply Fin.ext
  unfold sectorNumber at hij
  omega

/-- Branches sharing X, with matching and disjoint Y and Z sectors. -/
def sharedFirstTensor (B : Fin M → Tensor ℂ X Y Z) :
    Tensor ℂ X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

/-- The first local Fourier substitution guesses the missing sector. -/
def firstProjectionMap (ζ : ℂ) :
    (X × Fin M) → (Fin (5 * M) × X) → ℂ := by
  classical
  exact fun x r => if r.2 = x.1 then
    ζ ^ ((r.1.val : ℤ) * (2 * sectorNumber x.2)) else 0

/-- The second local map knows the sector through its original coordinate. -/
def secondProjectionMap (ζ : ℂ) :
    ((Fin M × Y) × Fin M) → (Fin (5 * M) × (Fin M × Y)) → ℂ := by
  classical
  exact fun y r => if r.2 = y.1 then
    ζ ^ ((r.1.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) else 0

/-- The third local map carries the single Fourier normalization factor. -/
def thirdProjectionMap (ζ : ℂ) :
    ((Fin M × Z) × Fin M) → (Fin (5 * M) × (Fin M × Z)) → ℂ := by
  classical
  exact fun z r => if r.2 = z.1 then
    (5 * M : ℂ)⁻¹ *
      ζ ^ ((r.1.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1)) else 0

private theorem restrict_constantCopies
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    (T : Tensor K A B C)
    (a : A' → R × A → K) (b : B' → R × B → K) (c : C' → R × C → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict a b c (Tensor.directSum (fun _ : R => T)) x y z =
      ∑ r : R, ∑ i, ∑ j, ∑ k, a x (r, i) * b y (r, j) * c z (r, k) * T i j k := by
  classical
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, mul_ite, ite_and]

private theorem restrict_constantCopies_delta
    {K A B C A' B' C' R : Type*} [CommSemiring K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Tensor K A B C) (fa : A' → A) (fb : B' → B) (fc : C' → C)
    (a : A' → R → K) (b : B' → R → K) (c : C' → R → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict
        (fun x r => if r.2 = fa x then a x r.1 else 0)
        (fun y r => if r.2 = fb y then b y r.1 else 0)
        (fun z r => if r.2 = fc z then c z r.1 else 0)
        (Tensor.directSum (fun _ : R => T)) x y z =
      (∑ r : R, a x r * b y r * c z r) * T (fa x) (fb y) (fc z) := by
  rw [restrict_constantCopies]
  simp [ite_mul, mul_ite, Finset.sum_mul]

/-- The exact coefficient tensor after Fourier projection, before weighting. -/
def projectedTensor (ζ : ℂ) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor ℂ (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if y.1.1 = z.1.1 then
    finiteFourierCoefficient ζ (5 * M)
      (phase (sectorNumber x.2) (sectorNumber y.1.1)
        (sectorNumber y.2) (sectorNumber z.2)) (B y.1.1 x.1 y.1.2 z.1.2)
    else 0

/-- The paper's `5M` copies and its three explicit local Fourier maps realize
the projected tensor by an ordinary restriction. -/
theorem finiteProjection_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (ζ : ℂ) (hζ : ζ ≠ 0) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor.restrict (firstProjectionMap ζ) (secondProjectionMap ζ)
        (thirdProjectionMap ζ)
        (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B)) =
      projectedTensor ζ B := by
  classical
  funext x y z
  unfold firstProjectionMap secondProjectionMap thirdProjectionMap
  rw [restrict_constantCopies_delta (R := Fin (5 * M))
    (sharedFirstTensor B) Prod.fst Prod.fst Prod.fst
    (fun x r => ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)))
    (fun y r => ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)))
    (fun z r => (5 * M : ℂ)⁻¹ *
      ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) x y z]
  by_cases hyz : y.1.1 = z.1.1
  · simp only [sharedFirstTensor, projectedTensor, hyz, ↓reduceIte]
    have hterm (r : Fin (5 * M)) :
        ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)) *
          ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) *
          ((5 * M : ℂ)⁻¹ *
            ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) =
        (5 * M : ℂ)⁻¹ *
          ζ ^ ((r.val : ℤ) * phase (sectorNumber x.2) (sectorNumber y.1.1)
            (sectorNumber y.2) (sectorNumber z.2)) := by
      rw [← hyz]
      calc
        _ = (5 * M : ℂ)⁻¹ *
            (ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2)) *
            ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1)) *
            ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber y.1.1))) := by ring
        _ = (5 * M : ℂ)⁻¹ * ζ ^
            ((r.val : ℤ) * (2 * sectorNumber x.2) +
             (r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1) +
             (r.val : ℤ) * (-sectorNumber z.2 - sectorNumber y.1.1)) := by
          rw [zpow_add₀ hζ, zpow_add₀ hζ]
        _ = _ := by congr 2; unfold phase; ring
    simp only [← hyz] at hterm ⊢
    simp_rw [hterm]
    rw [← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun r : ℕ => ζ ^ ((r : ℤ) *
        phase (sectorNumber x.2) (sectorNumber y.1.1)
          (sectorNumber y.2) (sectorNumber z.2))) (5 * M)]
    unfold finiteFourierCoefficient
    rw [← Finset.sum_mul]
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  · simp [sharedFirstTensor, projectedTensor, hyz]

/-- The polynomial after the Fourier projection and square weighting. -/
def separationPolynomial (ζ : ℂ) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor (Polynomial ℂ) (X × Fin M)
      ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if y.1.1 = z.1.1 then
    projectedBranchPolynomial ζ M (sectorNumber x.2) (sectorNumber y.1.1)
      (sectorNumber y.2) (sectorNumber z.2) (B y.1.1 x.1 y.1.2 z.1.2)
    else 0

/-- The surviving tensor: sector labels match on all three legs, while the
additional second/third coordinates form a dot product. -/
def separationTarget (B : Fin M → Tensor ℂ X Y Z) :
    Tensor ℂ (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 then
    B y.1.1 x.1 y.1.2 z.1.2 else 0

/-- The square-weighted polynomial has exactly the advertised constant tensor. -/
theorem separationPolynomial_coeff_zero {ζ : ℂ} (hM : 0 < M)
    (hζ : IsPrimitiveRoot ζ (5 * M)) (B : Fin M → Tensor ℂ X Y Z) :
    (fun x y z => (separationPolynomial ζ B x y z).coeff 0) =
      separationTarget B := by
  classical
  funext x y z
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, hyz, ↓reduceIte]
    rw [projectedBranchPolynomial_coeff_zero hM hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _)]
    simp only [sectorNumber_injective.eq_iff, separationTarget, hyz, true_and]
  · simp [separationPolynomial, separationTarget, hyz]

/-- Its degree is bounded for each fixed finite separation construction. -/
theorem separationPolynomial_degree {ζ : ℂ} (hM : 0 < M)
    (hζ : IsPrimitiveRoot ζ (5 * M)) (B : Fin M → Tensor ℂ X Y Z)
    (x : X × Fin M) (y : (Fin M × Y) × Fin M) (z : (Fin M × Z) × Fin M) :
    (separationPolynomial ζ B x y z).degree ≤ ((M - 1) ^ 2 : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, hyz, ↓reduceIte]
    exact projectedBranchPolynomial_coeff_eq_zero_of_lt hM hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _) hn _
  · simp [separationPolynomial, hyz]

private theorem restrict_target_scalars
    {A B C A' B' C' : Type*} [Fintype A] [Fintype B] [Fintype C]
    (T : Tensor ℂ A B C) (a : A' → A → ℂ) (b : B' → B → ℂ)
    (c : C' → C → ℂ) (s : A' → ℂ) (t : B' → ℂ) (u : C' → ℂ) :
    Tensor.restrict (fun x i => s x * a x i) (fun y j => t y * b y j)
        (fun z k => u z * c z k) T =
      fun x y z => (s x * t y * u z) * Tensor.restrict a b c T x y z := by
  funext x y z
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The first local Fourier map followed by its integer weight. -/
def firstSeparationMap (ζ t : ℂ) (x : X × Fin M) (r : Fin (5 * M) × X) : ℂ :=
  t ^ firstWeight (sectorNumber x.2) * firstProjectionMap ζ x r

/-- The second local Fourier map followed by its possibly negative weight. -/
def secondSeparationMap (ζ t : ℂ) (y : (Fin M × Y) × Fin M)
    (r : Fin (5 * M) × (Fin M × Y)) : ℂ :=
  t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) * secondProjectionMap ζ y r

/-- The third local Fourier map followed by its possibly negative weight. -/
def thirdSeparationMap (ζ t : ℂ) (z : (Fin M × Z) × Fin M)
    (r : Fin (5 * M) × (Fin M × Z)) : ℂ :=
  t ^ thirdWeight (sectorNumber z.1.1) (sectorNumber z.2) * thirdProjectionMap ζ z r

theorem weightedProjection_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (ζ t : ℂ) (hζ : ζ ≠ 0) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor.restrict (firstSeparationMap ζ t) (secondSeparationMap ζ t)
        (thirdSeparationMap ζ t)
        (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B)) =
      fun x y z =>
        (t ^ firstWeight (sectorNumber x.2) *
          t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) *
          t ^ thirdWeight (sectorNumber z.1.1) (sectorNumber z.2)) *
            projectedTensor ζ B x y z := by
  unfold firstSeparationMap secondSeparationMap thirdSeparationMap
  rw [restrict_target_scalars, finiteProjection_restrict ζ hζ B]

/-- At every nonzero parameter the polynomial tensor is an ordinary restriction
of exactly `5M` complete source copies. -/
theorem separationPolynomial_eval [Fintype X] [Fintype Y] [Fintype Z]
    {ζ : ℂ} (hM : 0 < M) (hζ : IsPrimitiveRoot ζ (5 * M))
    (B : Fin M → Tensor ℂ X Y Z) (t : ℂ) (ht : t ≠ 0) :
    (fun x y z => (separationPolynomial ζ B x y z).eval t) =
      Tensor.restrict (firstSeparationMap ζ t) (secondSeparationMap ζ t)
        (thirdSeparationMap ζ t)
        (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B)) := by
  rw [weightedProjection_restrict ζ t (hζ.ne_zero (by omega)) B]
  funext x y z
  by_cases hyz : y.1.1 = z.1.1
  · simp only [separationPolynomial, projectedTensor, hyz, ↓reduceIte,
      projectedBranchPolynomial, Polynomial.eval_monomial]
    simp only [← hyz]
    rw [fiveMFourierCoefficient_eq_ite hM hζ
      (sectorNumber_bounds _) (sectorNumber_bounds _)
      (sectorNumber_bounds _) (sectorNumber_bounds _)]
    split_ifs with hp
    · have he : t ^ firstWeight (sectorNumber x.2) *
          t ^ secondWeight (sectorNumber y.1.1) (sectorNumber y.2) *
          t ^ thirdWeight (sectorNumber y.1.1) (sectorNumber z.2) =
          t ^ totalWeight (sectorNumber x.2) (sectorNumber y.1.1)
            (sectorNumber y.2) (sectorNumber z.2) := by
        rw [totalWeight, zpow_add₀ ht, zpow_add₀ ht]
      rw [he, ← totalDegree_cast_of_phase_eq_zero hp, zpow_natCast]
      exact mul_comm _ _
    · simp
  · simp [separationPolynomial, projectedTensor, hyz]

private theorem polynomial_degeneration_of_nonzero_restrictions
    {A B C A' B' C' : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [Fintype A'] [Fintype B'] [Fintype C']
    (S : Tensor ℂ A B C) (P : Tensor (Polynomial ℂ) A' B' C')
    (hP : ∀ t : ℂ, t ≠ 0 →
      (fun x y z => (P x y z).eval t) ∈ Tensor.restrictionOrbit S) :
    Tensor.DegeneratesTo S (fun x y z => (P x y z).coeff 0) := by
  let f : ℂ → Tensor ℂ A' B' C' := fun t x y z => (P x y z).eval t
  have hf : Continuous f := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    apply continuous_pi
    intro z
    exact (P x y z).continuous
  have hclosed : IsClosed {t : ℂ | Tensor.DegeneratesTo S (f t)} :=
    isClosed_closure.preimage hf
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ {t : ℂ | Tensor.DegeneratesTo S (f t)} := by
    intro t ht
    exact subset_closure (hP t (by simpa using ht))
  have hz := closure_minimal hsubset hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  change Tensor.DegeneratesTo S (f 0) at hz
  simpa only [f, Polynomial.coeff_zero_eq_eval_zero] using hz

/-- Exact finite separation: `5M` source copies degenerate to all M branches,
each retaining an M-dimensional dot-product factor. -/
theorem finiteSeparation_degeneratesTo [Fintype X] [Fintype Y] [Fintype Z]
    (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor.DegeneratesTo
      (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B))
      (separationTarget B) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (5 * M : ℕ))
  have hζ : IsPrimitiveRoot ζ (5 * M) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  rw [← separationPolynomial_coeff_zero hM hζ B]
  apply polynomial_degeneration_of_nonzero_restrictions _ (separationPolynomial ζ B)
  intro t ht
  exact ⟨firstSeparationMap ζ t, secondSeparationMap ζ t, thirdSeparationMap ζ t,
    separationPolynomial_eval hM hζ B t ht⟩

/-- The first-leg relabeling adds the trivial first coordinate of the dot product. -/
def separationFirstEquiv : (X × Fin M) ≃ (Fin M × (X × Unit)) where
  toFun x := (x.2, (x.1, ()))
  invFun x := (x.2.1, x.1)
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨h, x, u⟩; cases u; rfl

/-- The other two relabelings merely reassociate their coordinates. -/
def separationSideEquiv (A : Type*) : ((Fin M × A) × Fin M) ≃
    (Fin M × (A × Fin M)) := Equiv.prodAssoc _ _ _

/-- The separated target, expressed as a genuine full direct sum of products. -/
theorem separationTarget_eq_directSum (B : Fin M → Tensor ℂ X Y Z) :
    separationTarget B =
      Tensor.pullback
        separationFirstEquiv (separationSideEquiv Y) (separationSideEquiv Z)
        (Tensor.directSum (fun h => Tensor.product (B h)
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin M)))))) := by
  classical
  funext x y z
  simp only [separationTarget, Tensor.pullback, Tensor.directSum, Tensor.product,
    Tensor.cyclic, Tensor.dotPairing, separationFirstEquiv, separationSideEquiv,
    Equiv.coe_fn_mk, Equiv.prodAssoc_apply]
  by_cases hxy : x.2 = y.1.1
  · by_cases hyz : y.1.1 = z.1.1
    · simp [hxy, hyz]
    · simp [hxy, hyz]
  · simp [hxy]

/-- The finite separation theorem with the output written literally as a full
direct sum of the M branch/dot-product tensors. -/
theorem finiteSeparation_directSum_degeneratesTo
    [Fintype X] [Fintype Y] [Fintype Z]
    (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor.DegeneratesTo
      (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B))
      (Tensor.directSum (fun h => Tensor.product (B h)
        (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin M)))))) := by
  classical
  have h := finiteSeparation_degeneratesTo hM B
  have h' := h.restrict
    (fun x x' => if x' = separationFirstEquiv.symm x then 1 else 0)
    (fun y y' => if y' = (separationSideEquiv Y).symm y then 1 else 0)
    (fun z z' => if z' = (separationSideEquiv Z).symm z then 1 else 0)
  rw [← Tensor.pullback_eq_restrict, separationTarget_eq_directSum] at h'
  have heq :
      Tensor.pullback separationFirstEquiv.symm
        (separationSideEquiv Y).symm (separationSideEquiv Z).symm
        (Tensor.pullback separationFirstEquiv
          (separationSideEquiv Y) (separationSideEquiv Z)
          (Tensor.directSum (fun h => Tensor.product (B h)
            (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin M))))))) =
      Tensor.directSum (fun h => Tensor.product (B h)
        (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin M))))) := by
    funext x y z
    simp only [Tensor.pullback, Equiv.apply_symm_apply]
  rw [heq] at h'
  exact h'

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule111
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.FiniteSeparation -/
section FlattenModule112




namespace OAI

/-!
# The character bound from finite separation

The explicit Fourier and square-weight construction gives a polynomial tensor
whose nonzero evaluations restrict from exactly `5M` complete source copies.
Character monotonicity follows by interpolation and tensor powering; it does
not require continuity of the character.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
private theorem polynomial_rank_bound
    (P : Tensor (Polynomial ℂ) X Y Z) :
    Tensor.RankAtMost P (Fintype.card (X × Y)) := by
  classical
  let a : X × Y → X → Polynomial ℂ := fun i x => if i.1 = x then 1 else 0
  let b : X × Y → Y → Polynomial ℂ := fun i y => if i.2 = y then 1 else 0
  let c : X × Y → Z → Polynomial ℂ := fun i z => P i.1 i.2 z
  have heq : P = fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
    funext x y z
    simp [Tensor.rankOne, a, b, c, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- The explicit separation polynomial, viewed as a polynomial approximation
to its constant tensor. Its rank bound is supplied by a coordinate expansion. -/
def separationPolynomialApproximation {ζ : ℂ} (hM : 0 < M)
    (hζ : IsPrimitiveRoot ζ (5 * M)) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor.PolynomialApproximation (separationTarget B)
      (Fintype.card ((X × Fin M) × ((Fin M × Y) × Fin M))) 0 ((M - 1) ^ 2) where
  polynomial := separationPolynomial ζ B
  rank_bound := polynomial_rank_bound _
  vanishes := by
    intro _ _ _ k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact congrFun (congrFun (congrFun (separationPolynomial_coeff_zero hM hζ B) x) y) z
  degree_bound := separationPolynomial_degree hM hζ B

namespace Character

variable (χ : Character)

/-- The separated constant tensor costs at most the character of the `5M`
source copies. This uses the explicit polynomial, not topological continuity. -/
theorem value_separationTarget_le (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    χ.value (separationTarget B) ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  classical
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (5 * M : ℕ))
  have hζ : IsPrimitiveRoot ζ (5 * M) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  have hbound : χ.value (separationTarget B) ≤
      χ.value (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B)) := by
    apply χ.value_le_of_polynomialApproximation
      (separationPolynomialApproximation hM hζ B) (χ.nonneg _)
    intro t ht
    change χ.value (fun x y z => (separationPolynomial ζ B x y z).eval t) ≤ _
    rw [separationPolynomial_eval hM hζ B t ht]
    exact χ.monotone _ _ _ _
  simpa only [χ.value_copies, Nat.cast_mul, Nat.cast_ofNat] using hbound

/-- Character accounting for the genuine direct sum in the separated tensor. -/
theorem value_separationTarget (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    χ.value (separationTarget B) =
      (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX := by
  classical
  rw [separationTarget_eq_directSum, χ.value_reindex, χ.map_directSum]
  simp only [χ.map_product, χ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul]

/-- Exact finite character separation: the common first coordinate can be
separated at a cost of `5M`, retaining an `M`-dimensional first-leg dot factor. -/
theorem finiteSeparation_bound (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  rw [← χ.value_separationTarget hM B]
  exact χ.value_separationTarget_le hM B

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule112
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.FiniteSeparation -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SharedPadding -/
section FlattenModule113


namespace OAI

/-!
# Padding shared-input tensors with different branch dimensions

The finite separation construction uses fixed ambient coordinate spaces on
each leg. A family with a common first leg and varying second and third legs
embeds into that setting without changing any character values. The extra
coordinates introduced by padding have zero coefficients.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X : Type} {Y Z : Fin M → Type}
variable [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

/-- Branches sharing their first input but with independently sized other legs. -/
def sharedFirstDependentTensor (B : ∀ i, Tensor ℂ X (Y i) (Z i)) :
    Tensor ℂ X (Σ i, Y i) (Σ i, Z i) :=
  fun x y z => if h : z.1 = y.1 then B y.1 x y.2 (h ▸ z.2) else 0

/-- A branch in the two common sigma coordinate spaces, with zero padding. -/
def paddedSharedBranch (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M) :
    Tensor ℂ X (Σ i, Y i) (Σ i, Z i) :=
  Tensor.restrict (fun x' x => if x = x' then 1 else 0)
    (fun y b => if Sigma.mk i b = y then 1 else 0)
    (fun z c => if Sigma.mk i c = z then 1 else 0) (B i)

omit [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)] in
@[simp] theorem sharedFirstDependentTensor_matching
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    sharedFirstDependentTensor B x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  simp [sharedFirstDependentTensor]

@[simp] theorem paddedSharedBranch_matching
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    paddedSharedBranch B i x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  simp [paddedSharedBranch, Tensor.restrict, ite_mul, mul_ite]

theorem paddedSharedBranch_pullback
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M) :
    Tensor.pullback id (Sigma.mk i) (Sigma.mk i) (paddedSharedBranch B i) = B i := by
  funext x y z
  exact paddedSharedBranch_matching B i x y z

/-- A nonzero branch remains nonzero after padding. -/
theorem paddedSharedBranch_ne_zero
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M) (hB : B i ≠ 0) :
    paddedSharedBranch B i ≠ 0 := by
  intro h
  apply hB
  rw [← paddedSharedBranch_pullback B i, h]
  rfl

theorem paddedSharedBranch_zero_middle
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hy : y.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  have hzero : ∀ b : Y i, Sigma.mk i b ≠ y :=
    fun b h => hy (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

theorem paddedSharedBranch_zero_right
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hz : z.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  have hzero : ∀ c : Z i, Sigma.mk i c ≠ z :=
    fun c h => hz (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

/-- Redundant branch labels zero-extend the varying-dimension shared tensor. -/
theorem sharedFirstTensor_paddedSharedBranch
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) :
    sharedFirstTensor (paddedSharedBranch B) = Tensor.restrict
      (fun (x' : X) x => if x = x' then 1 else 0)
      (fun (y' : Fin M × (Σ i, Y i)) y => if (y.1, y) = y' then 1 else 0)
      (fun (z' : Fin M × (Σ i, Z i)) z => if (z.1, z) = z' then 1 else 0)
      (sharedFirstDependentTensor B) := by
  funext x' y' z'
  rcases y' with ⟨i, ⟨iy, y⟩⟩
  rcases z' with ⟨j, ⟨iz, z⟩⟩
  have hgraph {A : Type} (f : A → Fin M) (a x : A) (i : Fin M) :
      (f a, a) = (i, x) ↔ a = x ∧ f x = i := by
    constructor
    · intro h
      have ha : a = x := congrArg Prod.snd h
      refine ⟨ha, ?_⟩
      rw [← ha]
      exact congrArg Prod.fst h
    · rintro ⟨rfl, h⟩
      simp [h]
  simp only [Tensor.restrict, hgraph, ite_and]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : iy = i
  · subst iy
    by_cases hz : iz = i
    · subst iz
      by_cases hij : i = j
      · subst j
        simp [sharedFirstTensor, sharedFirstDependentTensor]
      · simp [sharedFirstTensor, hij]
    · simp [sharedFirstTensor, sharedFirstDependentTensor,
        paddedSharedBranch_zero_right B i x' ⟨i, y⟩ ⟨iz, z⟩ hz, hz]
  · simp [sharedFirstTensor,
      paddedSharedBranch_zero_middle B i x' ⟨iy, y⟩ ⟨iz, z⟩ hi, hi]

namespace Character

/-- Padding a branch changes no character value. -/
@[simp] theorem value_paddedSharedBranch (χ : Character)
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) (i : Fin M) :
    χ.value (paddedSharedBranch B i) = χ.value (B i) := by
  simpa only [paddedSharedBranch, id_eq] using
    χ.value_extendByZero (B i) id (Sigma.mk i) (Sigma.mk i)
      Function.injective_id
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

/-- Passing to uniform ambient branch spaces adds no character cost. -/
@[simp] theorem value_sharedFirstTensor_padded (χ : Character)
    (B : ∀ i, Tensor ℂ X (Y i) (Z i)) :
    χ.value (sharedFirstTensor (paddedSharedBranch B)) =
      χ.value (sharedFirstDependentTensor B) := by
  rw [sharedFirstTensor_paddedSharedBranch]
  simpa only [id_eq] using
    χ.value_extendByZero (sharedFirstDependentTensor B) id
      (fun y => (y.1, y)) (fun z => (z.1, z)) Function.injective_id
      (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule113
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SharedPadding -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.TagInequality -/
section FlattenModule114






namespace OAI

/-!
# The shared-input tensor tag inequality

Exact type words in a power of a matched-sector tensor are obtained by explicit
coordinate pullbacks. Their character values depend only on the type counts.
The finite auxiliary separation inequality therefore supplies the integral
bounds required by the entropy limit.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {s : ℕ} {X Y Z : Type}
  [Fintype X] [Fintype Y] [Fintype Z]

/-- A word prescribes one branch tensor at each tensor-product position. -/
def branchWordTensor (B : Fin s → Tensor ℂ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    Tensor ℂ (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, B (w i) (x i) (y i) (z i)

/-- The canonical branch word tensor evaluates multiplicatively. -/
theorem Character.value_branchWordTensor (χ : Character)
    (B : Fin s → Tensor ℂ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    χ.value (branchWordTensor B w) = ∏ i, χ.value (B (w i)) := by
  induction n with
  | zero =>
      have hzero : branchWordTensor B w = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) unitTensor := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, unitTensor]
      rw [hzero, χ.value_reindex, χ.map_one]
      simp
  | succ n ih =>
      have heq : branchWordTensor B w = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product (B (w 0)) (branchWordTensor B (Fin.tail w))) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, Fin.prod_univ_succ]
      rfl

/-- All words of an exact type have the same character value. -/
theorem Character.value_exact_branchWordTensor (χ : Character)
    (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ) (w : ExactWords counts) :
    χ.value (branchWordTensor B w.val) = ∏ a, χ.value (B a) ^ counts a := by
  rw [χ.value_branchWordTensor,
    ← Fintype.prod_fiberwise' w.val (fun a => χ.value (B a))]
  simp only [Finset.prod_const, Finset.card_univ]
  apply Finset.prod_congr rfl
  intro a _
  rw [show Fintype.card {i // w.val i = a} = counts a from w.property a]

/-- A coordinate on a retained split leg remembers its type word. -/
def typeWordCoordinate (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts)
    {U : Type} (y : Fin (Fintype.card (ExactWords counts)) ×
      (Fin (∑ a, counts a) → U)) : Fin (∑ a, counts a) → (Fin s × U) :=
  fun i => ((e y.1).val i, y.2 i)

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Restricting both split legs to one exact type produces a shared-first
tensor whose branches are precisely the prescribed branch products. -/
theorem exactType_power_pullback (B : Fin s → Tensor ℂ X Y Z)
    (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    Tensor.pullback id (typeWordCoordinate counts e) (typeWordCoordinate counts e)
        (Tensor.power (sharedFirstTensor B) (∑ a, counts a)) =
      sharedFirstTensor (fun h => branchWordTensor B (e h).val) := by
  funext x y z
  by_cases h : y.1 = z.1
  · simp [Tensor.pullback, Tensor.power, typeWordCoordinate, sharedFirstTensor,
      branchWordTensor, h]
  · have hword : (e y.1).val ≠ (e z.1).val := by
      intro heq
      exact h (e.injective (Subtype.ext heq))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hword
    simp only [Tensor.pullback, Tensor.power, sharedFirstTensor, h, ↓reduceIte,
      typeWordCoordinate, id_eq]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- The exact-type restriction never exceeds the source power in character. -/
theorem Character.exactType_value_le_power (χ : Character)
    (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    χ.value (sharedFirstTensor (fun h => branchWordTensor B (e h).val)) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  rw [← exactType_power_pullback B counts e, ← χ.value_power]
  exact χ.value_pullback_le _ _ _ _

/-- The finite separation construction and exact-type restriction give the
integral inequality, with no assumed character comparison. -/
theorem Character.integral_type_comparison (χ : Character)
    (B : Fin s → Tensor ℂ X Y Z) (counts : Fin s → ℕ) :
    (Fintype.card (ExactWords counts) : ℝ) ^ χ.pX *
        ∏ a, χ.value (B a) ^ counts a ≤
      5 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  let M := Fintype.card (ExactWords counts)
  let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
  let W : Fin M → Tensor ℂ (Fin (∑ a, counts a) → X)
      (Fin (∑ a, counts a) → Y) (Fin (∑ a, counts a) → Z) :=
    fun h => branchWordTensor B (e h).val
  have hM : 0 < M := by
    simpa only [M, Fintype.card_eq_nat_card] using exactWords_card_pos counts
  have hsep : ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor W) := by
    simpa only [W, χ.value_exact_branchWordTensor, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      χ.finiteSeparation_bound hM W
  have hsource : χ.value (sharedFirstTensor W) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
    χ.exactType_value_le_power B counts e
  have hcancel : (M : ℝ) *
      ((M : ℝ) ^ χ.pX * ∏ a, χ.value (B a) ^ counts a) ≤
        (M : ℝ) * (5 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a)) := by
    calc
      _ = ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX := by ring
      _ ≤ 5 * (M : ℝ) * χ.value (sharedFirstTensor W) := hsep
      _ ≤ 5 * (M : ℝ) * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  have hbound := (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp hcancel
  simpa only [M, Fintype.card_eq_nat_card] using hbound

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- A nonzero branch remains visible in the tensor with a shared first leg. -/
theorem sharedFirstTensor_ne_zero_of_branch (B : Fin s → Tensor ℂ X Y Z)
    (a : Fin s) (ha : B a ≠ 0) : sharedFirstTensor B ≠ 0 := by
  intro h
  apply ha
  funext x y z
  have hxyz := congrFun (congrFun (congrFun h x) (a, y)) (a, z)
  simpa only [sharedFirstTensor, ↓reduceIte, Pi.zero_apply] using hxyz

/-- The actual shared-input tensor tag inequality, including probability laws
with zero coordinates. The branch labels are disjoint on the second and third
legs, while the first coordinate is shared. -/
theorem Character.sharedFirst_tag (χ : Character)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℂ X Y Z)
    (hB : ∀ a, B a ≠ 0) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstTensor B) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  have hT : sharedFirstTensor B ≠ 0 :=
    sharedFirstTensor_ne_zero_of_branch B ⟨0, hs⟩ (hB ⟨0, hs⟩)
  apply χ.tag_of_integral_type_comparison q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using χ.integral_type_comparison B counts

/-- The logarithmic form of the actual tensor tag inequality. -/
theorem Character.log_sharedFirst_tag (χ : Character)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℂ X Y Z)
    (hB : ∀ a, B a ≠ 0) :
    χ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value (sharedFirstTensor B)) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  have hT : sharedFirstTensor B ≠ 0 :=
    sharedFirstTensor_ne_zero_of_branch B ⟨0, hs⟩ (hB ⟨0, hs⟩)
  apply χ.log_tag_of_integral_type_comparison q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using χ.integral_type_comparison B counts

section Dependent

variable {U V : Fin s → Type} [∀ a, Fintype (U a)] [∀ a, Fintype (V a)]

/-- Branches may have different second- and third-leg dimensions. Padding
those spaces preserves their character values and the shared-input tensor. -/
theorem Character.sharedFirstDependent_tag (χ : Character)
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor ℂ X (U a) (V a))
    (hB : ∀ a, B a ≠ 0) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstDependentTensor B) := by
  simpa only [χ.value_paddedSharedBranch, χ.value_sharedFirstTensor_padded] using
    χ.sharedFirst_tag q (paddedSharedBranch B)
      (fun a => paddedSharedBranch_ne_zero B a (hB a))

/-- The logarithmic tag inequality for branches with varying dimensions. -/
theorem Character.log_sharedFirstDependent_tag (χ : Character)
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor ℂ X (U a) (V a))
    (hB : ∀ a, B a ≠ 0) :
    χ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value (sharedFirstDependentTensor B)) := by
  simpa only [χ.value_paddedSharedBranch, χ.value_sharedFirstTensor_padded] using
    χ.log_sharedFirst_tag q (paddedSharedBranch B)
      (fun a => paddedSharedBranch_ne_zero B a (hB a))

end Dependent

end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule114
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.TagInequality -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.BranchTagging -/
section FlattenModule115


namespace OAI

/-!
# Recovering branch tags from coordinate support

When both non-shared coordinates determine a branch label, adding explicit
matching branch tags does not change a character's value. The tags can be
recovered by independent coordinate maps, and forgetting them recovers the
original coefficientwise sum of branches.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Recovering the two coordinate labels identifies the tagged tensor with
the coefficientwise sum of the branches. -/
theorem sharedFirstTensor_pullback_labels
    (B : Fin M → Tensor ℂ X Y Z) (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    Tensor.pullback id (fun y => (ly y, y)) (fun z => (lz z, z))
      (sharedFirstTensor B) = ∑ i, B i := by
  classical
  funext x y z
  simp only [Finset.sum_apply]
  change (if ly y = lz z then B (ly y) x y z else 0) = ∑ i, B i x y z
  have hsum : (∑ i, B i x y z) = B (ly y) x y z := by
    apply Finset.sum_eq_single (ly y)
    · intro i _ hi
      by_contra h
      exact hi (hsupport i x y z h).1.symm
    · simp
  rw [hsum]
  split_ifs with h
  · rfl
  · symm
    by_contra hb
    exact h ((hsupport (ly y) x y z hb).2.symm)

namespace Character

/-- Branch labels determined by both non-shared coordinates can be inserted
or forgotten without changing a character. -/
theorem value_sharedFirstTensor_eq_sum (χ : Character)
    (B : Fin M → Tensor ℂ X Y Z) (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    χ.value (sharedFirstTensor B) = χ.value (∑ i, B i) := by
  have hs : ∀ x y z, sharedFirstTensor B x y z ≠ 0 →
      x ∈ Set.range (id : X → X) ∧
        y ∈ Set.range (fun y => (ly y, y)) ∧
        z ∈ Set.range (fun z => (lz z, z)) := by
    intro x y z h
    have hyz : y.1 = z.1 := by
      by_contra hne
      exact h (by simp [sharedFirstTensor, hne])
    have hb : B y.1 x y.2 z.2 ≠ 0 := by
      simpa only [sharedFirstTensor, hyz, ↓reduceIte] using h
    obtain ⟨hy, hz⟩ := hsupport y.1 x y.2 z.2 hb
    exact ⟨⟨x, rfl⟩, ⟨y.2, Prod.ext hy rfl⟩,
      ⟨z.2, Prod.ext (hz.trans hyz) rfl⟩⟩
  have heq := χ.value_eq_pullback_of_support (sharedFirstTensor B) id
    (fun y => (ly y, y)) (fun z => (lz z, z)) Function.injective_id
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h) hs
  rw [sharedFirstTensor_pullback_labels B ly lz hsupport] at heq
  exact heq

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule115
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.BranchTagging -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Character -/
section FlattenModule116







namespace OAI

/-!
# The determinant inequality for an actual tensor character

The shared-input tag inequality is applied to the two concrete branches of the
checked determinant degeneration. All basis changes and the output-dual change
are supplied by `DeterminantFiltration`.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration

/-- The two graded blocks, padded with zeros in common coordinate spaces. -/
def branch (d e : ℕ) (n : Fin 2) :
    Tensor ℂ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if n = 0 then if i.val + j.val = k.val then 1 else 0 else 0
  | i, .inr j, .inr k => if n = 1 then if i.val + j.val = k.val then 1 else 0 else 0
  | _, _, _ => 0

def branchLabel (e : ℕ) : Index e → Fin 2
  | .inl _ => 0
  | .inr _ => 1

theorem branch_support (d e : ℕ) (n : Fin 2) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) (h : branch d e n i j k ≠ 0) :
    branchLabel e j = n ∧ branchLabel (d + e) k = n := by
  fin_cases n <;> rcases j with j | j <;> rcases k with k | k <;>
    simp_all [branch, branchLabel]

theorem sum_branch (d e : ℕ) : (∑ n, branch d e n) = gradedTensor d e := by
  funext i j k
  rcases j with j | j <;> rcases k with k | k <;>
    simp [branch, gradedTensor]

theorem branch_ne_zero (d e : ℕ) (he : 0 < e) (n : Fin 2) : branch d e n ≠ 0 := by
  intro h
  fin_cases n
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    simp [branch] at hv
  · have hv := congrFun (congrFun (congrFun h ⟨0, by omega⟩)
      (.inr ⟨0, he⟩)) (.inr ⟨0, by omega⟩)
    simp [branch] at hv

end DeterminantFiltration

namespace Character

open DeterminantFiltration

variable (χ : Character)

theorem value_determinant_branch_zero (d e : ℕ) :
    χ.value (branch d e 0) = χ.value (convolution (d + 1) (e + 2)) := by
  let fz : Fin ((d + 1) + (e + 2) - 1) → Index (d + e) :=
    fun k => .inl (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch d e 0 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inl : Fin (e + 2) → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    · exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
    all_goals simp [branch] at h
  have hv := χ.value_eq_pullback_of_support (branch d e 0) id Sum.inl fz
    Function.injective_id Sum.inl_injective hfz hs
  have ht : Tensor.pullback id Sum.inl fz (branch d e 0) =
      convolution (d + 1) (e + 2) := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

theorem value_determinant_branch_one (d e : ℕ) :
    χ.value (branch d e 1) = χ.value (convolution (d + 1) e) := by
  let fz : Fin ((d + 1) + e - 1) → Index (d + e) :=
    fun k => .inr (Fin.cast (by omega) k)
  have hfz : Function.Injective fz := by
    intro a b h
    exact Fin.ext (congrArg (fun z : Index (d + e) =>
      match z with | .inl k => k.val | .inr k => k.val) h)
  have hs : ∀ i j k, branch d e 1 i j k ≠ 0 →
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
      j ∈ Set.range (Sum.inr : Fin e → Index e) ∧ k ∈ Set.range fz := by
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    any_goals simp [branch] at h
    exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz]⟩⟩
  have hv := χ.value_eq_pullback_of_support (branch d e 1) id Sum.inr fz
    Function.injective_id Sum.inr_injective hfz hs
  have ht : Tensor.pullback id Sum.inr fz (branch d e 1) =
      convolution (d + 1) e := by
    funext i j k
    simp [Tensor.pullback, branch, fz, convolution]
  simpa only [ht] using hv

private theorem value_bool_dot :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) Bool))) =
      (2 : ℝ) ^ χ.pX := by
  have hv := χ.value_reindex
    (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) Bool)))
    (Equiv.refl Unit) finTwoEquiv finTwoEquiv
  have ht : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) Bool))) =
        Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℂ) (Fin 2))) := by
    funext i j k
    simp [Tensor.pullback, Tensor.cyclic, Tensor.dotPairing]
  rw [ht] at hv
  exact hv.symm.trans (χ.value_cyclic_cyclic_dotPairing (by decide))

/-- The auxiliary dot product is charged once, on the actual source tensor. -/
theorem value_determinant_source_le (d e : ℕ) :
    χ.value (sourceTensor d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  rw [sourceTensor_product]
  apply (χ.value_pullback_le _ _ _ _).trans_eq
  rw [χ.map_product, χ.value_bool_dot]
  ring

/-- Actual basis-change and degeneration certificates give this comparison. -/
theorem value_determinant_graded_le (d e : ℕ) :
    χ.value (gradedTensor d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  calc
    χ.value (gradedTensor d e) ≤ χ.value (adaptedTensor d e) :=
      χ.value_polynomialRestrictionDegeneration_le (degeneration d e)
    _ ≤ χ.value (sourceTensor d e) := by
      simpa only [sourceTensor_coordinate_change] using
        χ.monotone (sourceTensor d e) (fixedFirst d) (inputChange e)
          (outputDualChange (d + e))
    _ ≤ _ := χ.value_determinant_source_le d e

/-- The binary tag bound before normalizing over all six characters. -/
theorem convolution_concavity_tag_dims (d e : ℕ) (he : 0 < e)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution (d + 1) (e + 2)) ^ q *
        χ.value (convolution (d + 1) e) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution (d + 1) (e + 1)) := by
  have ht := χ.sharedFirst_tag (binaryLaw q hq₀ hq₁) (branch d e)
    (branch_ne_zero d e he)
  rw [χ.value_sharedFirstTensor_eq_sum (branch d e)
    (branchLabel e) (branchLabel (d + e)) (branch_support d e), sum_branch] at ht
  rw [binaryLaw_entropy, binaryLaw_product,
    χ.value_determinant_branch_zero, χ.value_determinant_branch_one] at ht
  apply le_trans (b := χ.value (gradedTensor d e))
  · simpa only [mul_assoc] using ht
  · exact χ.value_determinant_graded_le d e

/-- The determinant inequality in the paper's positive-dimension notation. -/
theorem convolution_concavity_tag (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution a (b + 1)) ^ q *
        χ.value (convolution a (b - 1)) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution a b) := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  obtain ⟨e, rfl, he⟩ : ∃ e, b = e + 1 ∧ 0 < e := ⟨b - 1, by omega, by omega⟩
  simpa [Nat.add_assoc] using χ.convolution_concavity_tag_dims d e he q hq₀ hq₁

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI

end FlattenModule116
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Character -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Weights -/
section FlattenModule117


namespace OAI

/-!
# Interval weights for the three-sector convolution degeneration

Section 5.2 assigns weights to the second and third coordinates of
`C(a, 3 * h + a - 1)`. The total weight is nonnegative on convolution support,
and its zero set consists exactly of the three matching sector blocks.
The middle block is a convolution with the last two legs exchanged and the
first coordinate reversed.
-/

namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Number of second-leg coordinates in the original convolution. -/
def sourceWidth (a h : ℕ) : ℕ := 3 * h + a - 1

/-- Beginning of the right sector on both the second and third legs. -/
def rightStart (a h : ℕ) : ℕ := 2 * h + a - 1

/-- A coefficient-one term of the original convolution tensor. -/
def Support (a h i j k : ℕ) : Prop :=
  i < a ∧ j < sourceWidth a h ∧ k = i + j

/-- The middle interval on the second tensor leg. -/
def MiddleY (a h j : ℕ) : Prop := h ≤ j ∧ j < rightStart a h

/-- The middle interval on the third tensor leg. -/
def MiddleZ (a h k : ℕ) : Prop := h + a - 1 ≤ k ∧ k < rightStart a h

instance (a h j : ℕ) : Decidable (MiddleY a h j) := inferInstanceAs
  (Decidable (h ≤ j ∧ j < rightStart a h))

instance (a h k : ℕ) : Decidable (MiddleZ a h k) := inferInstanceAs
  (Decidable (h + a - 1 ≤ k ∧ k < rightStart a h))

/-- No weight is assigned to the common first leg. -/
def firstWeight (_i : ℕ) : ℤ := 0

/-- Weight one on the middle second-leg interval, zero elsewhere. -/
def secondWeight (a h j : ℕ) : ℤ := if MiddleY a h j then 1 else 0

/-- Weight minus one on the middle third-leg interval, zero elsewhere. -/
def thirdWeight (a h k : ℕ) : ℤ := if MiddleZ a h k then -1 else 0

/-- Exponent of the degeneration parameter on one term. -/
def totalWeight (a h i j k : ℕ) : ℤ :=
  firstWeight i + secondWeight a h j + thirdWeight a h k

/-- The three retained blocks have matching sector labels. -/
def MatchingSectors (a h j k : ℕ) : Prop :=
  (j < h ∧ k < h + a - 1) ∨
  (MiddleY a h j ∧ MiddleZ a h k) ∨
  (rightStart a h ≤ j ∧ rightStart a h ≤ k)

/-- A middle third-leg coordinate can only be reached from the middle second leg. -/
theorem middleY_of_middleZ {a h i j k : ℕ}
    (hs : Support a h i j k) (hz : MiddleZ a h k) : MiddleY a h j := by
  unfold Support at hs
  unfold MiddleY MiddleZ rightStart at *
  omega

/-- Every term has exponent zero or one, so no negative powers occur. -/
theorem totalWeight_eq_zero_or_one {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ∨ totalWeight a h i j k = 1 := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

theorem totalWeight_nonneg {a h i j k : ℕ}
    (hs : Support a h i j k) : 0 ≤ totalWeight a h i j k := by
  rcases totalWeight_eq_zero_or_one hs with hw | hw <;> omega

/-- The constant coefficient consists exactly of the three matching blocks. -/
theorem totalWeight_eq_zero_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔ MatchingSectors a h j k := by
  unfold Support sourceWidth at hs
  unfold MatchingSectors MiddleY MiddleZ rightStart
  unfold totalWeight firstWeight secondWeight thirdWeight MiddleY MiddleZ rightStart
  split_ifs <;> omega

/-- Only a middle second-leg coordinate paired with an outer third-leg coordinate
is erased by the degeneration. -/
theorem totalWeight_eq_one_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 1 ↔ MiddleY a h j ∧ ¬ MiddleZ a h k := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

/-- Parametrization of the left copy of `C(a,h)`. -/
def LeftBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧ j = r ∧ k = u + r

/-- Parametrization of the middle copy with the second and third legs exchanged. -/
def MiddleBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = a - 1 - u ∧
    j = h + u + r ∧ k = h + a - 1 + r

/-- Parametrization of the right translated copy of `C(a,h)`. -/
def RightBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧
    j = rightStart a h + r ∧ k = rightStart a h + u + r

/-- The left block preserves the actual first coordinate. -/
theorem leftBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    LeftBranch a h i j k ↔ j < h ∧ k < h + a - 1 := by
  rcases hs with ⟨hi, hj, hk⟩
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hleft, _⟩
    exact ⟨i, j, hi, hleft, rfl, rfl, hk⟩

/-- The middle support equation becomes convolution after reversing the first
coordinate and exchanging the second and third legs. -/
theorem middleBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    MiddleBranch a h i j k ↔ MiddleY a h j ∧ MiddleZ a h k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold MiddleY MiddleZ rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hy, hz⟩
    refine ⟨a - 1 - i, k - (h + a - 1), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The right block is the same convolution after translating the two outer
coordinates. -/
theorem rightBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    RightBranch a h i j k ↔ rightStart a h ≤ j ∧ rightStart a h ≤ k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold sourceWidth at hj
  unfold RightBranch rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hjr, hkr⟩
    refine ⟨i, j - (2 * h + a - 1), hi, ?_, rfl, ?_, ?_⟩ <;> omega

/-- On the left coordinate block, the support equation is the ordinary
convolution equation. -/
theorem left_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i r s ↔ s = i + r := by
  unfold Support sourceWidth
  omega

/-- Translation of the right block preserves the convolution equation. -/
theorem right_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i (rightStart a h + r) (rightStart a h + s) ↔ s = i + r := by
  unfold Support sourceWidth rightStart
  omega

/-- In middle-block coordinates the support equation is convolution with the
first coordinate reversed and the other two coordinates exchanged. -/
theorem middle_support_coordinates {a h i s r : ℕ}
    (hi : i < a) (hr : r < h) :
    Support a h i (h + s) (h + a - 1 + r) ↔ s = a - 1 - i + r := by
  unfold Support sourceWidth
  omega

/-- Exact retained support of the three-sector degeneration. -/
theorem retained_support_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  rw [totalWeight_eq_zero_iff hs, leftBranch_iff hs, middleBranch_iff hs,
    rightBranch_iff hs]
  rfl

/-- Every displayed left-branch term belongs to the original convolution. -/
theorem LeftBranch.support {a h i j k : ℕ} (hb : LeftBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed middle-branch term belongs to the original convolution. -/
theorem MiddleBranch.support {a h i j k : ℕ} (hb : MiddleBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed right-branch term belongs to the original convolution. -/
theorem RightBranch.support {a h i j k : ℕ} (hb : RightBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth rightStart
  omega

/-- Exact equality of the retained support and the three explicitly
parametrized convolution branches, without a pre-existing support assumption. -/
theorem support_and_weight_zero_iff (a h i j k : ℕ) :
    (Support a h i j k ∧ totalWeight a h i j k = 0) ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  constructor
  · rintro ⟨hs, hw⟩
    exact (retained_support_iff hs).mp hw
  · intro hb
    have hs : Support a h i j k := hb.elim LeftBranch.support
      (fun hb => hb.elim MiddleBranch.support RightBranch.support)
    exact ⟨hs, (retained_support_iff hs).mpr hb⟩

/-- The first-coordinate reversal is involutive on its natural range. -/
theorem reverse_reverse {a u : ℕ} (hu : u < a) :
    a - 1 - (a - 1 - u) = u := by
  omega

/-- The middle branch has unique reversed-convolution coordinates. -/
theorem middleBranch_coordinates_unique {a h i k u r u' r' : ℕ}
    (hu : u < a) (hu' : u' < a)
    (hi : i = a - 1 - u) (hi' : i = a - 1 - u')
    (hk : k = h + a - 1 + r) (hk' : k = h + a - 1 + r') :
    u = u' ∧ r = r' := by
  omega

/-- The left and middle branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_middleBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ MiddleBranch a h i j k := by
  intro hm
  have hl' := (leftBranch_iff hl.support).mp hl
  have hm' := (middleBranch_iff hm.support).mp hm
  unfold MiddleY at hm'
  omega

/-- The left and right branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_rightBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hl' := (leftBranch_iff hl.support).mp hl
  have hr' := (rightBranch_iff hr.support).mp hr
  have hi := hr.support.1
  unfold rightStart at hr'
  omega

/-- The middle and right branches use disjoint second-leg coordinates. -/
theorem middleBranch_not_rightBranch {a h i j k : ℕ}
    (hm : MiddleBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hm' := (middleBranch_iff hm.support).mp hm
  have hr' := (rightBranch_iff hr.support).mp hr
  unfold MiddleY at hm'
  omega

/-- Positivity of the two original dimensions makes the left branch nonempty. -/
theorem leftBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, LeftBranch a h i j k :=
  ⟨0, 0, 0, 0, 0, ha, hh, rfl, rfl, rfl⟩

/-- Positivity makes the exchanged middle branch nonempty as well. -/
theorem middleBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, MiddleBranch a h i j k := by
  refine ⟨a - 1, h, h + a - 1, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

/-- Positivity also makes the translated right branch nonempty. -/
theorem rightBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, RightBranch a h i j k := by
  refine ⟨0, rightStart a h, rightStart a h, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

end MatrixMultiplication.AuxiliarySeparation.Sector

end OAI

end FlattenModule117
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Weights -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Degeneration -/
section FlattenModule118



namespace OAI

/-!
# The actual three-sector polynomial degeneration

The interval weights of `SectorWeights` act by diagonal local maps on the
coefficient tensor `C(a, 3h+a-1)`. Shifting every third-leg weight by one makes
the local maps polynomial. Their restriction is exactly `X * retained +
X^2 * erased`, so the existing polynomial-restriction degeneration interface
applies with leading order one and local degree bounds `(0,1,1)`.
-/

noncomputable section

open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation.Sector

open MatrixMultiplication.Foundation
open Polynomial

abbrev YIndex (a h : ℕ) := Fin (sourceWidth a h)
abbrev ZIndex (a h : ℕ) := Fin (a + sourceWidth a h - 1)

/-- The source coefficient tensor, with its actual shared first-input space. -/
def source (a h : ℕ) : Tensor ℂ (Fin a) (YIndex a h) (ZIndex a h) :=
  convolution a (sourceWidth a h)

theorem source_ne_zero_iff {a h : ℕ} (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    source a h i j k ≠ 0 ↔ Support a h i.val j.val k.val := by
  simp only [source, convolution_ne_zero_iff, Support]
  constructor
  · intro heq
    exact ⟨i.isLt, j.isLt, heq.symm⟩
  · intro hs
    exact hs.2.2.symm

/-- The weight-zero part in the original coordinate spaces. -/
def retained (a h : ℕ) : Tensor ℂ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 0 then source a h i j k else 0

/-- The positive-weight part, all of whose supported terms have weight one. -/
def erased (a h : ℕ) : Tensor ℂ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 1 then source a h i j k else 0

/-- The left retained branch, still in the common ambient coordinate spaces. -/
def leftTensor (a h : ℕ) : Tensor ℂ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if LeftBranch a h i.val j.val k.val then 1 else 0

/-- The middle retained branch; its first leg is the actual shared first leg. -/
def middleTensor (a h : ℕ) : Tensor ℂ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if MiddleBranch a h i.val j.val k.val then 1 else 0

/-- The right retained branch in the original coordinate spaces. -/
def rightTensor (a h : ℕ) : Tensor ℂ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if RightBranch a h i.val j.val k.val then 1 else 0

/-- The retained tensor is exactly the sum of the three stated branches,
with coefficient one on each and the original first-leg coordinates shared. -/
theorem retained_eq_three_branches (a h : ℕ) :
    retained a h = leftTensor a h + middleTensor a h + rightTensor a h := by
  funext i j k
  by_cases hs : Support a h i.val j.val k.val
  · have hsource : source a h i j k = 1 := by
      exact (convolution_eq_one_iff i j k).mpr hs.2.2.symm
    have hw := retained_support_iff hs
    have hlm := leftBranch_not_middleBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hlr := leftBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hmr := middleBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    by_cases hl : LeftBranch a h i.val j.val k.val <;>
      by_cases hm : MiddleBranch a h i.val j.val k.val <;>
      by_cases hr : RightBranch a h i.val j.val k.val
    all_goals simp_all [retained, leftTensor, middleTensor, rightTensor]
  · have hsource : source a h i j k = 0 := by
      by_contra hz
      exact hs ((source_ne_zero_iff i j k).mp hz)
    have hl : ¬ LeftBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hm : ¬ MiddleBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hr : ¬ RightBranch a h i.val j.val k.val := fun hb => hs hb.support
    simp [retained, leftTensor, middleTensor, rightTensor, hsource, hl, hm, hr]

/-- Every source term belongs either to the retained tensor or the erased one. -/
theorem source_eq_retained_add_erased (a h : ℕ) :
    source a h = retained a h + erased a h := by
  funext i j k
  by_cases hs : source a h i j k = 0
  · simp [retained, erased, hs]
  · rcases totalWeight_eq_zero_or_one ((source_ne_zero_iff i j k).mp hs) with hw | hw
    all_goals simp [retained, erased, hw]

/-- The normalized polynomial family appearing in the unshifted weights. -/
def normalizedPolynomial (a h : ℕ) :
    Tensor (Polynomial ℂ) (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => C (retained a h i j k) + X * C (erased a h i j k)

/-- The first local map fixes the common input basis. -/
def leftMap (a : ℕ) (output input : Fin a) : Polynomial ℂ :=
  if input = output then 1 else 0

/-- The second local map assigns weight one to the middle interval. -/
def middleMap (a h : ℕ) (output input : YIndex a h) : Polynomial ℂ :=
  if input = output then (if MiddleY a h output.val then X else 1) else 0

/-- Shift the third-leg weights by one, giving weight zero to the middle
interval and weight one to the two outer intervals. -/
def rightMap (a h : ℕ) (output input : ZIndex a h) : Polynomial ℂ :=
  if input = output then (if MiddleZ a h output.val then 1 else X) else 0

/-- One simultaneous polynomial restriction of the whole source tensor. -/
def polynomial (a h : ℕ) :
    Tensor (Polynomial ℂ) (Fin a) (YIndex a h) (ZIndex a h) :=
  Tensor.restrict (leftMap a) (middleMap a h) (rightMap a h)
    (fun i j k => C (source a h i j k))

theorem polynomial_apply (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial a h i j k =
      (if MiddleY a h j.val then X else 1) *
      (if MiddleZ a h k.val then 1 else X) * C (source a h i j k) := by
  simp [polynomial, Tensor.restrict, leftMap, middleMap, rightMap, ite_mul, mul_ite]

/-- The shifted polynomial restriction has precisely two possible degrees. -/
theorem polynomial_identity (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial a h i j k =
      X * C (retained a h i j k) + X ^ 2 * C (erased a h i j k) := by
  by_cases hs : source a h i j k = 0
  · simp [polynomial_apply, retained, erased, hs]
  · have hsupport := (source_ne_zero_iff i j k).mp hs
    have hmiddle := middleY_of_middleZ hsupport
    by_cases hy : MiddleY a h j.val <;> by_cases hz : MiddleZ a h k.val
    all_goals
      simp_all [polynomial_apply, retained, erased, totalWeight, firstWeight,
        secondWeight, thirdWeight, pow_two]

theorem polynomial_eq_X_mul_normalized (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial a h i j k = X * normalizedPolynomial a h i j k := by
  rw [polynomial_identity, normalizedPolynomial]
  ring

theorem polynomial_coeff (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (n : ℕ) :
    (polynomial a h i j k).coeff n =
      (if n = 1 then retained a h i j k else 0) +
      (if n = 2 then erased a h i j k else 0) := by
  rw [polynomial_identity, Polynomial.coeff_add,
    mul_comm X (C (retained a h i j k)),
    mul_comm (X ^ 2) (C (erased a h i j k)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem leftMap_degree (a : ℕ) (output input : Fin a) :
    (leftMap a output input).degree ≤ 0 := by
  by_cases heq : input = output <;> simp [leftMap, heq]

theorem middleMap_degree (a h : ℕ) (output input : YIndex a h) :
    (middleMap a h output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hy : MiddleY a h output.val <;>
    simp [middleMap, heq, hy]

theorem rightMap_degree (a h : ℕ) (output input : ZIndex a h) :
    (rightMap a h output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hz : MiddleZ a h output.val <;>
    simp [rightMap, heq, hz]

/-- The three-sector construction is an actual polynomial restriction
degeneration in the existing tensor API, with leading order one. -/
def restriction (a h : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (source a h) (retained a h) 1 0 1 1 where
  leftMap := leftMap a
  middleMap := middleMap a h
  rightMap := rightMap a h
  left_degree := leftMap_degree a
  middle_degree := middleMap_degree a h
  right_degree := rightMap_degree a h
  vanishes := by
    intro i j k n hn
    change (polynomial a h i j k).coeff n = 0
    rw [polynomial_coeff]
    have hn0 : n = 0 := by omega
    simp [hn0]
  leading := by
    intro i j k
    change (polynomial a h i j k).coeff 1 = retained a h i j k
    simp [polynomial_coeff]

@[simp] theorem restriction_basePolynomial (a h : ℕ) :
    (restriction a h).basePolynomial = polynomial a h := rfl

/-- Evaluation of the normalized family has exactly the paper's form. -/
theorem normalizedPolynomial_eval (a h : ℕ) (t : ℂ) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) :
    (normalizedPolynomial a h i j k).eval t =
      retained a h i j k + t * erased a h i j k := by
  simp only [normalizedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- At nonzero parameters, the unshifted normalized polynomial is still an
ordinary restriction: divide the first local map by the parameter. -/
theorem normalizedPolynomial_eval_restriction (a h : ℕ) (t : ℂ) (ht : t ≠ 0) :
    (fun i j k => (normalizedPolynomial a h i j k).eval t) =
      Tensor.restrict
        (fun output input => if input = output then t⁻¹ else 0)
        (fun output input => (middleMap a h output input).eval t)
        (fun output input => (rightMap a h output input).eval t)
        (source a h) := by
  funext i j k
  have hev := congrArg (fun p : Polynomial ℂ => p.eval t)
    (polynomial_eq_X_mul_normalized a h i j k)
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hev
  have hscaled :
      Tensor.restrict
          (fun output input => if input = output then t⁻¹ else 0)
          (fun output input => (middleMap a h output input).eval t)
          (fun output input => (rightMap a h output input).eval t)
          (source a h) i j k = t⁻¹ * (polynomial a h i j k).eval t := by
    rw [polynomial_apply]
    simp only [middleMap, rightMap, apply_ite, Polynomial.eval_zero,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
    simp [Tensor.restrict, ite_mul, mul_ite, mul_assoc]
  rw [hscaled, hev, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]

/-- Existing interpolation gives a rank bound with only linear overhead after
tensor powering. -/
theorem retained_power_rankAtMost (a h r n : ℕ)
    (hsource : Tensor.RankAtMost (source a h) r) :
    Tensor.RankAtMost (Tensor.power (retained a h) n) ((2 * n + 1) * r ^ n) := by
  simpa using restrictionDegeneration_power_rankAtMost (restriction a h) hsource n

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI

end FlattenModule118
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Degeneration -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Branches -/
section FlattenModule119



namespace OAI

/-!
# Coordinate identifications of the three retained sectors

Each outer branch is a zero extension of `C(a,h)`, using the same first-leg
coordinates. The middle branch is a zero extension after reversing the first
coordinate and exchanging the second and third tensor legs.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical


namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Embed the left second-leg interval. -/
def leftY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the left third-leg interval. -/
def leftZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle second-leg interval, which carries the convolution output. -/
def middleY (a h : ℕ) (s : Fin (a + h - 1)) : YIndex a h :=
  ⟨h + s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle third-leg interval, which carries the second input. -/
def middleZ (a h : ℕ) (r : Fin h) : ZIndex a h :=
  ⟨h + a - 1 + r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the right second-leg interval. -/
def rightY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨rightStart a h + r.val,
    by have hr := r.isLt; unfold rightStart sourceWidth; omega⟩

/-- Embed the right third-leg interval. -/
def rightZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨rightStart a h + s.val,
    by have hs := s.isLt; unfold rightStart sourceWidth; omega⟩

theorem leftY_injective (a h : ℕ) : Function.Injective (leftY a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : YIndex a h => t.val) heq

theorem leftZ_injective (a h : ℕ) : Function.Injective (leftZ a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : ZIndex a h => t.val) heq

theorem middleY_injective (a h : ℕ) : Function.Injective (middleY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleY] at hv
  omega

theorem middleZ_injective (a h : ℕ) : Function.Injective (middleZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleZ] at hv
  omega

theorem rightY_injective (a h : ℕ) : Function.Injective (rightY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightY] at hv
  omega

theorem rightZ_injective (a h : ℕ) : Function.Injective (rightZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightZ] at hv
  omega

/-- Pulling back the left block gives ordinary convolution. -/
theorem leftTensor_pullback (a h : ℕ) :
    Tensor.pullback id (leftY a h) (leftZ a h) (leftTensor a h) =
      convolution a h := by
  funext i r s
  have hb : LeftBranch a h i.val r.val s.val ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      exact ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, hs.symm⟩
  simp only [Tensor.pullback, leftTensor, leftY, leftZ, id_eq, convolution, hb]

/-- Pulling back the translated right block also gives ordinary convolution. -/
theorem rightTensor_pullback (a h : ℕ) :
    Tensor.pullback id (rightY a h) (rightZ a h) (rightTensor a h) =
      convolution a h := by
  funext i r s
  have hb : RightBranch a h i.val (rightStart a h + r.val)
      (rightStart a h + s.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, ?_⟩
      omega
  simp only [Tensor.pullback, rightTensor, rightY, rightZ, id_eq, convolution, hb]

/-- Exchange the two outer convolution legs while retaining the original input
order in the displayed coefficient equation. -/
def exchangedConvolution (a h : ℕ) :
    Tensor ℂ (Fin a) (Fin (a + h - 1)) (Fin h) :=
  fun i s r => convolution a h i r s

/-- The middle branch is exactly convolution with its last two legs exchanged;
the first-leg reversal occurs solely in this individual branch identification. -/
theorem middleTensor_pullback (a h : ℕ) :
    Tensor.pullback Fin.rev (middleY a h) (middleZ a h) (middleTensor a h) =
      exchangedConvolution a h := by
  funext i s r
  have hi := i.isLt
  have hr := r.isLt
  have hb : MiddleBranch a h (a - (i.val + 1)) (h + s.val)
      (h + a - 1 + r.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hx, hy, hz⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, hi, hr, ?_, ?_, rfl⟩ <;> omega
  simp only [Tensor.pullback, middleTensor, middleY, middleZ,
    exchangedConvolution, convolution, Fin.val_rev, hb]

/-- All nonzero left-branch coordinates lie in the displayed embeddings. -/
theorem leftTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : leftTensor a h i j k ≠ 0) :
    (∃ r, leftY a h r = j) ∧ (∃ s, leftZ a h s = k) := by
  have hb : LeftBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [leftTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · exact ⟨⟨u + r, by omega⟩, Fin.ext hk.symm⟩

/-- All nonzero right-branch coordinates lie in the translated embeddings. -/
theorem rightTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : rightTensor a h i j k ≠ 0) :
    (∃ r, rightY a h r = j) ∧ (∃ s, rightZ a h s = k) := by
  have hb : RightBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [rightTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · refine ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩
    dsimp [rightZ]
    omega

/-- All nonzero middle-branch coordinates lie in the exchanged embeddings. -/
theorem middleTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : middleTensor a h i j k ≠ 0) :
    (∃ u, Fin.rev u = i) ∧ (∃ s, middleY a h s = j) ∧
      (∃ r, middleZ a h r = k) := by
  have hb : MiddleBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [middleTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  refine ⟨⟨⟨u, hu⟩, Fin.ext ?_⟩, ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩,
    ⟨⟨r, hr⟩, Fin.ext ?_⟩⟩
  · simp only [Fin.val_rev]
    omega
  · dsimp [middleY]
    omega
  · exact hk.symm

/-- The left block is the zero extension of the ordinary convolution tensor. -/
theorem leftTensor_eq_extension (a h : ℕ) :
    leftTensor a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if leftY a h r = y then 1 else 0)
      (fun z s => if leftZ a h s = z then 1 else 0) (convolution a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : leftTensor a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (leftY a h) ∧ k ∈ Set.range (leftZ a h) := by
    exact ⟨⟨i, rfl⟩, leftTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (leftTensor a h) id (leftY a h) (leftZ a h)
    Function.injective_id (leftY_injective a h) (leftZ_injective a h) hs
  rw [leftTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The right block is the zero extension along the translated coordinates. -/
theorem rightTensor_eq_extension (a h : ℕ) :
    rightTensor a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if rightY a h r = y then 1 else 0)
      (fun z s => if rightZ a h s = z then 1 else 0) (convolution a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : rightTensor a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (rightY a h) ∧ k ∈ Set.range (rightZ a h) := by
    exact ⟨⟨i, rfl⟩, rightTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (rightTensor a h) id (rightY a h) (rightZ a h)
    Function.injective_id (rightY_injective a h) (rightZ_injective a h) hs
  rw [rightTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The middle block is the zero extension of the exchanged convolution, with
one reversible change of basis on its first leg. -/
theorem middleTensor_eq_extension (a h : ℕ) :
    middleTensor a h = Tensor.restrict
      (fun x i => if Fin.rev i = x then 1 else 0)
      (fun y s => if middleY a h s = y then 1 else 0)
      (fun z r => if middleZ a h r = z then 1 else 0) (exchangedConvolution a h) := by
  classical
  have heq := tensor_eq_extendByZero_pullback (middleTensor a h) Fin.rev (middleY a h)
    (middleZ a h) Fin.rev_injective (middleY_injective a h) (middleZ_injective a h)
    (middleTensor_support a h)
  rw [middleTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> split_ifs <;> rfl

/-- Every character assigns the left branch the value of `C(a,h)`. -/
theorem value_leftTensor (χ : Character) (a h : ℕ) :
    χ.value (leftTensor a h) = χ.value (convolution a h) := by
  rw [leftTensor_eq_extension]
  exact χ.value_extendByZero _ id (leftY a h) (leftZ a h) Function.injective_id
    (leftY_injective a h) (leftZ_injective a h)

/-- Translation of the outer coordinates preserves the right-branch value. -/
theorem value_rightTensor (χ : Character) (a h : ℕ) :
    χ.value (rightTensor a h) = χ.value (convolution a h) := by
  rw [rightTensor_eq_extension]
  exact χ.value_extendByZero _ id (rightY a h) (rightZ a h) Function.injective_id
    (rightY_injective a h) (rightZ_injective a h)

/-- The middle-branch value is the value of the exchanged convolution tensor. -/
theorem value_middleTensor (χ : Character) (a h : ℕ) :
    χ.value (middleTensor a h) = χ.value (exchangedConvolution a h) := by
  rw [middleTensor_eq_extension]
  exact χ.value_extendByZero _ Fin.rev (middleY a h) (middleZ a h)
    Fin.rev_injective (middleY_injective a h) (middleZ_injective a h)

/-- Exchanging two tensor legs preserves nonzeroness. -/
theorem exchangedConvolution_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    exchangedConvolution a h ≠ 0 := by
  intro hz
  apply convolution_nonzero ha hh
  funext i r s
  exact congrFun (congrFun (congrFun hz i) s) r

/-- The left retained branch is nonzero in every positive size. -/
theorem leftTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    leftTensor a h ≠ 0 := by
  intro hz
  have hp := leftTensor_pullback a h
  rw [hz] at hp
  exact convolution_nonzero ha hh hp.symm

/-- The translated right branch is nonzero in every positive size. -/
theorem rightTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    rightTensor a h ≠ 0 := by
  intro hz
  have hp := rightTensor_pullback a h
  rw [hz] at hp
  exact convolution_nonzero ha hh hp.symm

/-- The exchanged middle branch is nonzero in every positive size. -/
theorem middleTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    middleTensor a h ≠ 0 := by
  intro hz
  have hp := middleTensor_pullback a h
  rw [hz] at hp
  exact exchangedConvolution_nonzero ha hh hp.symm

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI

end FlattenModule119
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Branches -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Character -/
section FlattenModule120






namespace OAI

/-!
# The character inequality from the three-sector degeneration

The retained tensor has three branches sharing its actual first-input space.
Their two remaining coordinate intervals determine matching branch labels.
The uniform three-branch tag inequality and polynomial degeneration then yield
the character inequality of Section 5.2 before symmetrization.
-/

noncomputable section

open scoped BigOperators Classical
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- The actual three retained tensors in their original ambient spaces. -/
def branchFamily (a h : ℕ) (b : Fin 3) :
    Tensor ℂ (Fin a) (YIndex a h) (ZIndex a h) :=
  if b = 0 then leftTensor a h else if b = 1 then middleTensor a h else rightTensor a h

@[simp] theorem branchFamily_zero (a h : ℕ) :
    branchFamily a h 0 = leftTensor a h := by simp [branchFamily]

@[simp] theorem branchFamily_one (a h : ℕ) :
    branchFamily a h 1 = middleTensor a h := by simp [branchFamily]

@[simp] theorem branchFamily_two (a h : ℕ) :
    branchFamily a h 2 = rightTensor a h := by simp [branchFamily]

/-- Label a second-leg coordinate by its interval. -/
def yLabel (a h : ℕ) (j : YIndex a h) : Fin 3 :=
  if j.val < h then 0 else if j.val < rightStart a h then 1 else 2

/-- Label a third-leg coordinate by its corresponding interval. -/
def zLabel (a h : ℕ) (k : ZIndex a h) : Fin 3 :=
  if k.val < h + a - 1 then 0 else if k.val < rightStart a h then 1 else 2

/-- Every nonzero branch coefficient lies in the two matching labelled sectors. -/
theorem branchFamily_labels (a h : ℕ) (b : Fin 3) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) (hn : branchFamily a h b i j k ≠ 0) :
    yLabel a h j = b ∧ zLabel a h k = b := by
  fin_cases b
  · have hb : LeftBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, leftTensor, hb])
    have h := (leftBranch_iff hb.support).mp hb
    simp [yLabel, zLabel, h.1, h.2]
  · have hb : MiddleBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, middleTensor, hb])
    rcases (middleBranch_iff hb.support).mp hb with ⟨⟨hy₀, hy₁⟩, ⟨hz₀, hz₁⟩⟩
    simp [yLabel, zLabel, not_lt.mpr hy₀, hy₁, not_lt.mpr hz₀, hz₁]
  · have hb : RightBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, rightTensor, hb])
    rcases (rightBranch_iff hb.support).mp hb with ⟨hy, hz⟩
    have hi := i.isLt
    have hy₀ : h ≤ j.val := by unfold rightStart at hy; omega
    have hz₀ : h + a - 1 ≤ k.val := by unfold rightStart at hz; omega
    simp [yLabel, zLabel, not_lt.mpr hy₀, not_lt.mpr hy,
      not_lt.mpr hz₀, not_lt.mpr hz]

/-- The branch family sums to exactly the retained tensor. -/
theorem sum_branchFamily (a h : ℕ) :
    (∑ b : Fin 3, branchFamily a h b) = retained a h := by
  simp only [Fin.sum_univ_three, branchFamily_zero, branchFamily_one, branchFamily_two]
  exact (retained_eq_three_branches a h).symm

/-- The character comparison uses the actual polynomial degeneration. -/
theorem value_retained_le_source (χ : Character) (a h : ℕ) :
    χ.value (retained a h) ≤ χ.value (source a h) :=
  χ.value_polynomialRestrictionDegeneration_le (restriction a h)

/-- Both interval labels can be recovered without changing the common first
input, so the tagged branch tensor has precisely the retained tensor's value. -/
theorem value_sharedFirst_branchFamily (χ : Character) (a h : ℕ) :
    χ.value (sharedFirstTensor (branchFamily a h)) = χ.value (retained a h) := by
  rw [χ.value_sharedFirstTensor_eq_sum (branchFamily a h)
    (yLabel a h) (zLabel a h) (branchFamily_labels a h), sum_branchFamily]

theorem branchFamily_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h)
    (b : Fin 3) : branchFamily a h b ≠ 0 := by
  fin_cases b
  · simpa [branchFamily] using leftTensor_nonzero ha hh
  · simpa [branchFamily] using middleTensor_nonzero ha hh
  · simpa [branchFamily] using rightTensor_nonzero ha hh

/-- The uniform branch product combines the two outer convolution values. -/
theorem uniform_branchFamily_product (χ : Character) (a h : ℕ)
    (ha : 0 < a) (hh : 0 < h) :
    (∏ b, χ.value (branchFamily a h b) ^ (FiniteLaw.uniform (Fin 3)).mass b) =
      χ.value (convolution a h) ^ (2 / 3 : ℝ) *
        χ.value (exchangedConvolution a h) ^ (1 / 3 : ℝ) := by
  rw [uniformThree_product]
  simp only [branchFamily_zero, branchFamily_one, branchFamily_two,
    value_leftTensor, value_middleTensor, value_rightTensor]
  have hc : 0 < χ.value (convolution a h) :=
    lt_of_lt_of_le zero_lt_one (χ.one_le_value (convolution_nonzero ha hh))
  calc
    χ.value (convolution a h) ^ (1 / 3 : ℝ) *
        χ.value (exchangedConvolution a h) ^ (1 / 3 : ℝ) *
        χ.value (convolution a h) ^ (1 / 3 : ℝ) =
      (χ.value (convolution a h) ^ (1 / 3 : ℝ) *
        χ.value (convolution a h) ^ (1 / 3 : ℝ)) *
          χ.value (exchangedConvolution a h) ^ (1 / 3 : ℝ) := by ring
    _ = _ := by
      rw [← Real.rpow_add hc]
      norm_num

/-- The per-character three-sector inequality, before multiplication over
the six tensor-leg permutations. All tensor values are actual convolution
values, with only the middle branch exchanging its last two legs. -/
theorem convolution_tripling_tag (χ : Character) (a h : ℕ)
    (ha : 0 < a) (hh : 0 < h) :
    (3 : ℝ) ^ χ.pX * χ.value (convolution a h) ^ (2 / 3 : ℝ) *
      χ.value (fun i s r => convolution a h i r s) ^ (1 / 3 : ℝ) ≤
        χ.value (convolution a (3 * h + a - 1)) := by
  have htag := χ.sharedFirst_tag (FiniteLaw.uniform (Fin 3))
    (branchFamily a h) (branchFamily_nonzero ha hh)
  rw [uniformThree_entropy_factor, uniform_branchFamily_product χ a h ha hh,
    value_sharedFirst_branchFamily] at htag
  have hresult := htag.trans (value_retained_le_source χ a h)
  change (3 : ℝ) ^ χ.pX * (χ.value (convolution a h) ^ (2 / 3 : ℝ) *
    χ.value (fun i s r => convolution a h i r s) ^ (1 / 3 : ℝ)) ≤
      χ.value (convolution a (3 * h + a - 1)) at hresult
  simpa only [mul_assoc] using hresult

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI

end FlattenModule120
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Character -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Optimization -/
section FlattenModule121





namespace OAI

/-!
# Entropy optimization for finitely many sectors

The normalized weights `q = A / (A + B)` and `1 - q = B / (A + B)`
make the entropy-weighted geometric mean equal to `A + B`. This is the
scalar identity used in Section 5.1 of the auxiliary-separation argument.
The same calculation also applies to an arbitrary nonempty finite family.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- The logarithmic form of the entropy identity at the normalized weights. -/
theorem binary_entropy_log_partition {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.binEntropy (A / (A + B)) +
        Real.log A * (A / (A + B)) +
        Real.log B * (1 - A / (A + B)) = Real.log (A + B) := by
  have hsum : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
  have hcomplement : 1 - A / (A + B) = B / (A + B) := by
    field_simp
    ring
  rw [Real.binEntropy, hcomplement, Real.log_inv, Real.log_inv,
    Real.log_div hA.ne' hsum, Real.log_div hB.ne' hsum]
  field_simp
  ring

/-- Entropy compensates the weighted geometric mean at the normalized weights. -/
theorem binary_entropy_variational_identity {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.exp (Real.binEntropy (A / (A + B))) *
        A ^ (A / (A + B)) * B ^ (1 - A / (A + B)) = A + B := by
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB,
    ← Real.exp_add, ← Real.exp_add, binary_entropy_log_partition hA hB,
    Real.exp_log (add_pos hA hB)]

/-- The identity with an explicitly named optimizing proportion. -/
theorem binary_entropy_variational_identity_of_ratio {A B q : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hq : q = A / (A + B)) :
    Real.exp (-q * Real.log q - (1 - q) * Real.log (1 - q)) *
        A ^ q * B ^ (1 - q) = A + B := by
  subst q
  have hentropy :
      -(A / (A + B)) * Real.log (A / (A + B)) -
          (1 - A / (A + B)) * Real.log (1 - A / (A + B)) =
        Real.binEntropy (A / (A + B)) := by
    simp only [Real.binEntropy, Real.log_inv]
    ring
  rw [hentropy]
  exact binary_entropy_variational_identity hA hB

/-- The logarithmic entropy identity for positive weights on a finite set. -/
theorem finite_entropy_log_partition {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hs : s.Nonempty) (hA : ∀ i ∈ s, 0 < A i) :
    -(∑ i ∈ s, (A i / (∑ j ∈ s, A j)) * Real.log (A i / (∑ j ∈ s, A j))) +
        (∑ i ∈ s, Real.log (A i) * (A i / (∑ j ∈ s, A j))) =
      Real.log (∑ j ∈ s, A j) := by
  have hsum : 0 < ∑ j ∈ s, A j := Finset.sum_pos hA hs
  calc
    _ = ∑ i ∈ s, (A i / (∑ j ∈ s, A j)) * Real.log (∑ j ∈ s, A j) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_div (hA i hi).ne' hsum.ne']
      ring
    _ = (∑ i ∈ s, A i / (∑ j ∈ s, A j)) * Real.log (∑ j ∈ s, A j) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [← Finset.sum_div, div_self hsum.ne', one_mul]

/-- Normalizing any positive finite family attains its sum in the entropy formula. -/
theorem finite_entropy_variational_identity {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hs : s.Nonempty) (hA : ∀ i ∈ s, 0 < A i) :
    Real.exp (-(∑ i ∈ s, (A i / (∑ j ∈ s, A j)) *
        Real.log (A i / (∑ j ∈ s, A j)))) *
        (∏ i ∈ s, (A i) ^ (A i / (∑ j ∈ s, A j))) = ∑ j ∈ s, A j := by
  have hsum : 0 < ∑ j ∈ s, A j := Finset.sum_pos hA hs
  have hprod : (∏ i ∈ s, (A i) ^ (A i / (∑ j ∈ s, A j))) =
      Real.exp (∑ i ∈ s, Real.log (A i) * (A i / (∑ j ∈ s, A j))) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.rpow_def_of_pos (hA i hi) _
  rw [hprod, ← Real.exp_add, finite_entropy_log_partition s A hs hA,
    Real.exp_log hsum]

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule121
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Optimization -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.ProductBounds -/
section FlattenModule122




namespace OAI

/-!
# Combining the scalar sector bounds

Pointwise character bounds multiply over a finite family of leg orders. After
normalization by the sum of the singleton exponents, the entropy identity gives
the midpoint-concavity bound for the profile.
-/

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- Multiplying the entropy bounds and taking the positive normalization root
gives the midpoint-concavity inequality. -/
theorem finite_product_concavity {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i q, 0 ≤ q → q ≤ 1 →
      Real.exp (p i * Real.binEntropy q) * (B i) ^ q * (C i) ^ (1 - q) ≤
        (2 : ℝ) ^ (p i) * A i) :
    (∏ i, B i) ^ (1 / s) + (∏ i, C i) ^ (1 / s) ≤
      2 * (∏ i, A i) ^ (1 / s) := by
  have hprodA : 0 < ∏ i, A i := Finset.prod_pos (fun i _ => hA i)
  have hprodB : 0 < ∏ i, B i := Finset.prod_pos (fun i _ => hB i)
  have hprodC : 0 < ∏ i, C i := Finset.prod_pos (fun i _ => hC i)
  let a : ℝ := (∏ i, A i) ^ (1 / s)
  let b : ℝ := (∏ i, B i) ^ (1 / s)
  let c : ℝ := (∏ i, C i) ^ (1 / s)
  have ha : 0 < a := Real.rpow_pos_of_pos hprodA _
  have hb : 0 < b := Real.rpow_pos_of_pos hprodB _
  have hc : 0 < c := Real.rpow_pos_of_pos hprodC _
  let q : ℝ := b / (b + c)
  have hq0 : 0 ≤ q := le_of_lt (div_pos hb (add_pos hb hc))
  have hq1 : q ≤ 1 := (div_le_one (add_pos hb hc)).mpr (le_of_lt (lt_add_of_pos_right b hc))
  have hlog : ∀ i, p i * Real.binEntropy q + q * Real.log (B i) +
      (1 - q) * Real.log (C i) ≤ p i * Real.log 2 + Real.log (A i) := by
    intro i
    have hleft1 : 0 < Real.exp (p i * Real.binEntropy q) * (B i) ^ q :=
      mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (hB i) _)
    have h := Real.log_le_log
      (mul_pos hleft1 (Real.rpow_pos_of_pos (hC i) _)) (hbound i q hq0 hq1)
    rw [Real.log_mul hleft1.ne' (Real.rpow_pos_of_pos (hC i) _).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (hB i) _).ne',
      Real.log_exp, Real.log_rpow (hB i), Real.log_rpow (hC i),
      Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
        (hA i).ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h
    simpa only [mul_comm (Real.log 2) (p i)] using h
  have hlogs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlog i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hsum, ← Real.log_prod (fun i _ => (hA i).ne'),
    ← Real.log_prod (fun i _ => (hB i).ne'),
    ← Real.log_prod (fun i _ => (hC i).ne')] at hlogs
  have hnormalized : Real.binEntropy q + Real.log b * q + Real.log c * (1 - q) ≤
      Real.log 2 + Real.log a := by
    dsimp only [a, b, c]
    rw [Real.log_rpow hprodA, Real.log_rpow hprodB, Real.log_rpow hprodC]
    convert div_le_div_of_nonneg_right hlogs hs.le using 1 <;> (first | rfl | field_simp [hs.ne'])
  change Real.binEntropy (b / (b + c)) + Real.log b * (b / (b + c)) +
      Real.log c * (1 - b / (b + c)) ≤ Real.log 2 + Real.log a at hnormalized
  rw [binary_entropy_log_partition hb hc,
    ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne'] at hnormalized
  exact (Real.log_le_log_iff (add_pos hb hc) (mul_pos (by norm_num) ha)).mp hnormalized

/-- Multiplying the cyclic bounds and taking the positive normalization root
gives the factor of three in the tripling inequality. -/
theorem finite_product_tripling {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (_hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i, (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ) ≤ A i)
    (hprod_eq : ∏ i, C i = ∏ i, B i) :
    3 * (∏ i, B i) ^ (1 / s) ≤ (∏ i, A i) ^ (1 / s) := by
  have hBprod : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  have hprod : (3 : ℝ) ^ s * (∏ i, B i) ≤ ∏ i, A i := by
    have hmul := Finset.prod_le_prod (s := Finset.univ)
      (f := fun i => (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ))
      (g := A)
      (fun i _ => mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (hB i).le _))
        (Real.rpow_nonneg (hC i).le _))
      (fun i _ => hbound i)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3) p Finset.univ, hsum,
      Real.finsetProd_rpow Finset.univ B (fun i _ => (hB i).le),
      Real.finsetProd_rpow Finset.univ C (fun i _ => (hC i).le), hprod_eq,
      mul_assoc, ← Real.rpow_add hBprod] at hmul
    norm_num at hmul
    exact hmul
  have hmean := Real.rpow_le_rpow (by positivity) hprod (by positivity : (0 : ℝ) ≤ 1 / s)
  rw [Real.mul_rpow (by positivity) hBprod.le,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_one_div_cancel hs.ne',
    Real.rpow_one] at hmean
  exact hmean

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule122
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.ProductBounds -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ConcaveSlopes -/
section FlattenModule123



namespace OAI

/-!
# Slopes of positive discretely concave sequences

The row sequences in Section 6 have decreasing consecutive increments. A
nonnegative sequence cannot have a negative increment of this kind: every later
increment would be at least as negative. Consequently the increments converge
to a nonnegative limit, and the sequence divided by its index has the same limit.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- The usual second-difference inequality makes the increments decreasing. -/
theorem antitone_increments_of_discrete_concavity {u : ℕ → ℝ}
    (hu : ∀ n, u (n + 2) + u n ≤ 2 * u (n + 1)) :
    Antitone (fun n => u (n + 1) - u n) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hu n
  simp only [Nat.add_assoc] at *
  linarith

/-- A tangent-line upper bound for a sequence with decreasing increments. -/
theorem concave_sequence_le_affine {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) (n k : ℕ) :
    u (n + k) ≤ u n + (k : ℝ) * (u (n + 1) - u n) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hd (show n ≤ n + k by omega)
      simp only at hstep
      rw [Nat.cast_add, Nat.cast_one]
      have hindex : n + (k + 1) = n + k + 1 := by omega
      rw [hindex]
      nlinarith

/-- Every increment of a nonnegative discretely concave sequence is nonnegative. -/
theorem increment_nonneg_of_antitone {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n))
    (n : ℕ) : 0 ≤ u (n + 1) - u n := by
  by_contra hn
  have hneg : u (n + 1) - u n < 0 := lt_of_not_ge hn
  obtain ⟨k, hk⟩ := exists_lt_nsmul (neg_pos.mpr hneg) (u n)
  have hk' : u n < (k : ℝ) * -(u (n + 1) - u n) := by
    simpa only [nsmul_eq_mul] using hk
  have hbound := concave_sequence_le_affine hd n k
  have hnonneg := hu (n + k)
  nlinarith

/-- A nonnegative discretely concave sequence is increasing. -/
theorem monotone_of_nonneg_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    Monotone u := by
  apply monotone_nat_of_le_succ
  intro n
  have := increment_nonneg_of_antitone hu hd n
  linarith

/-- Telescoping and Cesàro convergence identify the linear growth rate. -/
theorem tendsto_div_nat_of_tendsto_increments {u : ℕ → ℝ} {g : ℝ}
    (hd : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g)) :
    Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hmean := hd.cesaro
  simp only [Finset.sum_range_sub] at hmean
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (u 0)
  have hsum := hmean.add hconst
  simpa only [add_zero, div_eq_mul_inv, mul_sub, sub_add_cancel, mul_comm] using hsum

/-- The limiting increment of a nonnegative discretely concave sequence is
nonnegative, and it is also its linear growth rate. -/
theorem exists_nonneg_limit_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    ∃ g : ℝ, 0 ≤ g ∧
      Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g) ∧
      Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hnonneg := increment_nonneg_of_antitone hu hd
  have hbdd : BddBelow (Set.range (fun n => u (n + 1) - u n)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  have hlim := tendsto_atTop_ciInf hd hbdd
  refine ⟨⨅ n, u (n + 1) - u n, ?_, hlim,
    tendsto_div_nat_of_tendsto_increments hlim⟩
  exact ge_of_tendsto hlim (Eventually.of_forall hnonneg)

/-- Positive-index version, suitable for the rows in Section 6. The value at
index zero is irrelevant. -/
theorem exists_concave_slope_limit {P : ℕ → ℝ}
    (hP : ∀ n, 0 < P (n + 1))
    (hd : Antitone (fun n => P (n + 2) - P (n + 1))) :
    ∃ g : ℝ, 0 ≤ g ∧
      (∀ n, g ≤ P (n + 2) - P (n + 1)) ∧
      Tendsto (fun n => P (n + 2) - P (n + 1)) atTop (𝓝 g) ∧
      Tendsto (fun n => P n / (n : ℝ)) atTop (𝓝 g) := by
  have hd' : Antitone (fun n => P ((n + 1) + 1) - P (n + 1)) := by
    simpa only [Nat.add_assoc] using hd
  obtain ⟨g, hg, hlim, hratio⟩ := exists_nonneg_limit_of_antitone_increments
    (u := fun n => P (n + 1)) (fun n => (hP n).le) hd'
  have hmul := hratio.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hshift : Tendsto (fun n => P (n + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 g) := by
    rw [mul_one] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  refine ⟨g, hg, ?_, ?_, (tendsto_add_atTop_iff_nat 1).mp hshift⟩
  · intro n
    exact hd.le_of_tendsto (by simpa only [Nat.add_assoc] using hlim) n
  · simpa only [Nat.add_assoc] using hlim

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule123
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ConcaveSlopes -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ProfileSlopes -/
section FlattenModule124

namespace OAI

/-!
# Shifted tripling and diagonal increments

These are the two estimates on the limiting row slopes used in Section 6.
Iteration retains the additive shift in the tripling inequality. Symmetry
then expresses a diagonal step as one increment in each of two adjacent rows.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- The indices obtained by repeatedly applying the affine tripling map. -/
def shiftedTriplingIndex (c h : ℕ) : ℕ → ℕ
  | 0 => h
  | j + 1 => 3 * shiftedTriplingIndex c h j + c

/-- Starting at a positive index, affine tripling escapes to infinity. -/
theorem shiftedTriplingIndex_lower (c h : ℕ) (hh : 1 ≤ h) (j : ℕ) :
    h + j ≤ shiftedTriplingIndex c h j := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex]
      omega

theorem shiftedTriplingIndex_tendsto (c h : ℕ) (hh : 1 ≤ h) :
    Tendsto (shiftedTriplingIndex c h) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  change j ≤ shiftedTriplingIndex c h j
  have := shiftedTriplingIndex_lower c h hh j
  omega

/-- The exact affine solution, written without truncated natural subtraction. -/
theorem shiftedTriplingIndex_cast (c h j : ℕ) :
    (shiftedTriplingIndex c h j : ℝ) + (c : ℝ) / 2 =
      (3 : ℝ) ^ j * ((h : ℝ) + (c : ℝ) / 2) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        pow_succ]
      nlinarith

/-- Iterating the tripling inequality multiplies the profile by powers of three. -/
theorem shiftedTripling_profile_lower {P : ℕ → ℝ} {c h : ℕ} (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c)) (j : ℕ) :
    (3 : ℝ) ^ j * P h ≤ P (shiftedTriplingIndex c h j) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      have hj : 1 ≤ shiftedTriplingIndex c h j := by
        have := shiftedTriplingIndex_lower c h hh j
        omega
      have hstep := htrip (shiftedTriplingIndex c h j) hj
      simp only [shiftedTriplingIndex, pow_succ]
      nlinarith

/-- A row with a limiting linear slope and shifted tripling lies below the
corresponding affine multiple of that slope. -/
theorem profile_le_affine_slope {P : ℕ → ℝ} {g : ℝ} {c h : ℕ}
    (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c))
    (hlim : Tendsto (fun n : ℕ => P n / (n : ℝ)) atTop (𝓝 g)) :
    P h ≤ ((h : ℝ) + (c : ℝ) / 2) * g := by
  have hpow : Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hzero : Tendsto (fun j : ℕ => ((c : ℝ) / 2) / (3 : ℝ) ^ j)
      atTop (𝓝 0) := hpow.const_div_atTop _
  have hindex : Tendsto
      (fun j : ℕ => (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j)
      atTop (𝓝 ((h : ℝ) + (c : ℝ) / 2)) := by
    have heq (j : ℕ) :
        (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j =
          (h : ℝ) + (c : ℝ) / 2 - ((c : ℝ) / 2) / (3 : ℝ) ^ j := by
      have hj := shiftedTriplingIndex_cast c h j
      have hp : (3 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      nlinarith
    simpa only [heq, sub_zero] using tendsto_const_nhds.sub hzero
  have hproduct := (hlim.comp (shiftedTriplingIndex_tendsto c h hh)).mul hindex
  have hprofile : Tendsto
      (fun j : ℕ => P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j)
      atTop (𝓝 (g * ((h : ℝ) + (c : ℝ) / 2))) := by
    apply hproduct.congr'
    apply Eventually.of_forall
    intro j
    have hj : (shiftedTriplingIndex c h j : ℝ) ≠ 0 := by
      have := shiftedTriplingIndex_lower c h hh j
      exact_mod_cast (show shiftedTriplingIndex c h j ≠ 0 by omega)
    dsimp only [Function.comp_def]
    field_simp
  have hbound : ∀ j : ℕ, P h ≤ P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j := by
    intro j
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) j)).mpr
    simpa only [mul_comm] using shiftedTripling_profile_lower hh htrip j
  simpa only [mul_comm] using ge_of_tendsto hprofile (Eventually.of_forall hbound)

/-- The row estimate in the positive-index notation of the paper. -/
theorem profile_row_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    P a h ≤ ((h : ℝ) + ((a : ℝ) - 1) / 2) * g a := by
  have ht : ∀ n : ℕ, 1 ≤ n → 3 * P a n ≤ P a (3 * n + (a - 1)) := by
    intro n hn
    have hi : 3 * n + (a - 1) = 3 * n + a - 1 := by omega
    rw [hi]
    exact htrip a ha n hn
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha, Nat.cast_one]
  simpa only [hcast] using profile_le_affine_slope hh ht (hlim a ha)

/-- The diagonal is bounded above by the limiting row slope with the precise
coefficient `(3a-1)/2`. -/
theorem profile_diagonal_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a : ℕ) (ha : 1 ≤ a) :
    P a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
  have hc : (a : ℝ) + ((a : ℝ) - 1) / 2 = (3 * (a : ℝ) - 1) / 2 := by ring
  simpa only [hc] using profile_row_le_slope htrip hlim a a ha ha

/-- Symmetry identifies a diagonal step with one increment in each adjacent
row. Only positive-index symmetry and slope bounds are used. -/
theorem diagonal_increment_of_slope_lower {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (hsymm : ∀ a : ℕ, 1 ≤ a → ∀ b : ℕ, 1 ≤ b → P a b = P b a)
    (hinc : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      g a ≤ P a (h + 1) - P a h)
    (n : ℕ) (hn : 1 ≤ n) :
    P n n + g n + g (n + 1) ≤ P (n + 1) (n + 1) := by
  have hfirst := hinc n hn n hn
  have hsecond := hinc (n + 1) (by omega) n hn
  have hsym := hsymm n hn (n + 1) (by omega)
  linarith

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule124
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.ProfileSlopes -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Product -/
section FlattenModule125


namespace OAI

/-!
# Exact growth of the product in Section 6

The paper's sequence starts at `G₁ = 1`. Here `growthProduct n` denotes
`Gₙ₊₁`. Cubing each factor gives an elementary lower bound, so no logarithmic
asymptotics are needed for this part of the argument.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- The product sequence from Section 6, indexed from zero. -/
noncomputable def growthProduct : ℕ → ℝ
  | 0 => 1
  | n + 1 => growthProduct n * (1 + 1 / (3 * ((n : ℝ) + 1)))

@[simp] theorem growthProduct_zero : growthProduct 0 = 1 := rfl

@[simp] theorem growthProduct_succ (n : ℕ) :
    growthProduct (n + 1) = growthProduct n * (1 + 1 / (3 * ((n : ℝ) + 1))) := rfl

theorem growthProduct_pos (n : ℕ) : 0 < growthProduct n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [growthProduct_succ]
    exact mul_pos ih (by positivity)

/-- Cubing one product factor dominates the corresponding telescoping factor. -/
theorem one_add_recip_three_cube_lower {a : ℝ} (ha : 0 < a) :
    1 + 1 / a ≤ (1 + 1 / (3 * a)) ^ 3 := by
  have hnonneg : 0 ≤ 1 / (3 * a) := by positivity
  have hdiv : 1 / a = 3 * (1 / (3 * a)) := by
    field_simp
  rw [hdiv]
  nlinarith [sq_nonneg (1 / (3 * a)),
    mul_nonneg (sq_nonneg (1 / (3 * a))) hnonneg]

/-- The exact lower bound `Gₙ₊₁³ ≥ n + 1`. -/
theorem growthProduct_cube_lower (n : ℕ) :
    (n : ℝ) + 1 ≤ growthProduct n ^ 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hfactor := one_add_recip_three_cube_lower ha
    have hfactor_nonneg : 0 ≤ (1 + 1 / (3 * ((n : ℝ) + 1))) ^ 3 := by
      positivity
    have hfirst := mul_le_mul_of_nonneg_right ih hfactor_nonneg
    have hsecond := mul_le_mul_of_nonneg_left hfactor (le_of_lt ha)
    have htelescoping : ((n : ℝ) + 1) * (1 + 1 / ((n : ℝ) + 1)) =
        (n : ℝ) + 2 := by
      field_simp
      ring
    rw [growthProduct_succ, mul_pow]
    push_cast
    linarith

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule125
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Product -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Recurrence -/
section FlattenModule126

namespace OAI

/-!
# The scalar simultaneous induction in Section 6

The two diagonal inequalities imply, simultaneously, lower bounds for the
limiting row slopes and for the diagonal profile.  All profile properties
needed for this argument are expressed as hypotheses below.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- One step of the Section 6 simultaneous induction, with a positive real
index. The proof uses the diagonal increment inequality to obtain the second
conclusion as well as the first. -/
theorem growthRecurrence_step_real
    {n Dprev Dnext gprev gnext Gprev : ℝ} (hn : 0 < n)
    (hupper : Dnext ≤ ((3 * (n + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * n - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * n)) * Gprev ≤ gnext ∧
      ((3 * (n + 1) - 1) / 2) * ((1 + 1 / (3 * n)) * Gprev) ≤ Dnext := by
  have hden : 0 < 3 * n := by positivity
  have hbound : (3 * n + 1) * Gprev ≤ (3 * n) * gnext := by
    nlinarith
  have hidentity : (1 + 1 / (3 * n)) * Gprev =
      ((3 * n + 1) * Gprev) / (3 * n) := by
    field_simp
  have hgnew : (1 + 1 / (3 * n)) * Gprev ≤ gnext := by
    rw [hidentity]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hbound)
  refine ⟨hgnew, ?_⟩
  have hdiagonal : ((3 * (n + 1) - 1) / 2) *
      ((1 + 1 / (3 * n)) * Gprev) =
      ((3 * n - 1) / 2) * Gprev + Gprev +
        (1 + 1 / (3 * n)) * Gprev := by
    field_simp
    ring
  rw [hdiagonal]
  linarith

/-- The natural-number form of the scalar induction step, indexed by `n + 1`
so that no truncated subtraction occurs in the recurrence. -/
theorem growthRecurrence_step
    {n : ℕ} (hn : 1 ≤ n) {Dprev Dnext gprev gnext Gprev : ℝ}
    (hupper : Dnext ≤ ((3 * ((n : ℝ) + 1) - 1) / 2) * gnext)
    (hincrement : Dprev + gprev + gnext ≤ Dnext)
    (hgprev : Gprev ≤ gprev)
    (hDprev : ((3 * (n : ℝ) - 1) / 2) * Gprev ≤ Dprev) :
    (1 + 1 / (3 * (n : ℝ))) * Gprev ≤ gnext ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) *
        ((1 + 1 / (3 * (n : ℝ))) * Gprev) ≤ Dnext := by
  apply growthRecurrence_step_real
  · exact_mod_cast (show 0 < n by omega)
  · exact hupper
  · exact hincrement
  · exact hgprev
  · exact hDprev

/-- The simultaneous slope and diagonal estimates, conditional only on the
initial values, the recurrence for `G`, and the two diagonal inequalities. -/
theorem growthRecurrence_induction
    (D g G : ℕ → ℝ)
    (hGbase : G 1 = 1)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hGstep : ∀ n : ℕ, 1 ≤ n →
      G (n + 1) = (1 + 1 / (3 * (n : ℝ))) * G n)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → G n ≤ g n ∧ ((3 * (n : ℝ) - 1) / 2) * G n ≤ D n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [hGbase]
      exact ⟨hgbase, hDbase⟩
  | succ n hn ih =>
      have hu : D (n + 1) ≤
          ((3 * ((n : ℝ) + 1) - 1) / 2) * g (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hupper (n + 1) (by omega)
      have hs := growthRecurrence_step hn hu (hincrement n hn) ih.1 ih.2
      simpa only [hGstep n hn, Nat.cast_add, Nat.cast_one] using hs

/-- A zero-indexed version of `growthRecurrence_induction`, convenient when the
initial term of the comparison sequence is stored at index zero. -/
theorem growthRecurrence_induction_shifted
    (D g H : ℕ → ℝ)
    (hHbase : H 0 = 1)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hHstep : ∀ n : ℕ,
      H (n + 1) = (1 + 1 / (3 * ((n : ℝ) + 1))) * H n)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, H n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * H n ≤ D (n + 1) := by
  intro n
  induction n with
  | zero =>
      norm_num [hHbase]
      exact ⟨hgbase, hDbase⟩
  | succ n ih =>
      have hn : 1 ≤ n + 1 := by omega
      have hu : D (n + 1 + 1) ≤
          ((3 * (((n + 1 : ℕ) : ℝ) + 1) - 1) / 2) * g (n + 1 + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hupper (n + 1 + 1) (by omega)
      have hp : ((3 * ((n + 1 : ℕ) : ℝ) - 1) / 2) * H n ≤ D (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      have hs := growthRecurrence_step hn hu (hincrement (n + 1) hn) ih.1 hp
      simpa only [hHstep, Nat.cast_add, Nat.cast_one] using hs

/-- The simultaneous bounds for the explicit comparison product from Section 6. -/
theorem growthProduct_le_slope_and_diagonal
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1)) :
    ∀ n : ℕ, growthProduct n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * growthProduct n ≤ D (n + 1) := by
  apply growthRecurrence_induction_shifted D g growthProduct
    growthProduct_zero hgbase hDbase
  · intro n
    rw [growthProduct_succ, mul_comm]
  · exact hupper
  · exact hincrement

/-- Combining the scalar induction with the elementary product estimate gives
an exact fourth-power lower bound on the cube of each diagonal value. -/
theorem diagonal_fourth_power_lower
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ D (n + 1) ^ 3 := by
  have hdiag := (growthProduct_le_slope_and_diagonal D g hgbase hDbase
    hupper hincrement n).2
  have hpositive := growthProduct_pos n
  have hlinear : ((n : ℝ) + 1) * growthProduct n ≤ D (n + 1) := by
    have hcoeff : (n : ℝ) + 1 ≤ (3 * ((n : ℝ) + 1) - 1) / 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hpositive)).trans hdiag
  calc
    ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) := by ring
    _ ≤ ((n : ℝ) + 1) ^ 3 * growthProduct n ^ 3 :=
      mul_le_mul_of_nonneg_left (growthProduct_cube_lower n) (by positivity)
    _ = (((n : ℝ) + 1) * growthProduct n) ^ 3 := by ring
    _ ≤ D (n + 1) ^ 3 := pow_le_pow_left₀ (by positivity) hlinear 3

/-- The diagonal fourth-power lower bound using the paper's positive indices. -/
theorem diagonal_fourth_power_lower_of_one_le
    (D g : ℕ → ℝ)
    (hgbase : 1 ≤ g 1)
    (hDbase : 1 ≤ D 1)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      D n ≤ ((3 * (n : ℝ) - 1) / 2) * g n)
    (hincrement : ∀ n : ℕ, 1 ≤ n →
      D n + g n + g (n + 1) ≤ D (n + 1))
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ 4 ≤ D n ^ 3 := by
  cases n with
  | zero => omega
  | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        diagonal_fourth_power_lower D g hgbase hDbase hupper hincrement n

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule126
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Recurrence -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Profile -/
section FlattenModule127




namespace OAI

/-!
# Growth of the scalar profile

This file proves the scalar implication of Section 6 (Lemma 6.1). The profile
properties are explicit hypotheses: the construction of a profile from a tensor
character and the proof of those properties are separate arguments.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- The scalar profile hypotheses used in Section 6. Only positive indices
carry mathematical content; the values on either coordinate axis are unused. -/
structure ScalarProfile (t : ℝ) where
  value : ℕ → ℕ → ℝ
  positive : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < value a b
  symmetric : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → value a b = value b a
  boundary : ∀ b : ℕ, 1 ≤ b → value 1 b = (b : ℝ)
  concave : ∀ a h : ℕ, 1 ≤ a → 2 ≤ h →
    value a (h - 1) + value a (h + 1) ≤ 2 * value a h
  tripling : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
    3 * value a h ≤ value a (3 * h + a - 1)
  rank_bound : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    value a b ≤ ((a : ℝ) + (b : ℝ) - 1) ^ (1 / t)

namespace ScalarProfile

/-- Each row has a nonnegative limiting slope that bounds every increment
from below and equals the limit of the row divided by its index. -/
theorem exists_row_slope {t : ℝ} (P : ScalarProfile t) (a : ℕ) (ha : 1 ≤ a) :
    ∃ g : ℝ, 0 ≤ g ∧
      (∀ h : ℕ, 1 ≤ h → g ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 g) := by
  have hd : Antitone (fun n : ℕ => P.value a (n + 2) - P.value a (n + 1)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hc := P.concave a (n + 2) ha (by omega)
    have hpred : n + 2 - 1 = n + 1 := by omega
    rw [hpred] at hc
    simp only [Nat.add_assoc] at *
    linarith
  obtain ⟨g, hg, hinc, _, hratio⟩ := exists_concave_slope_limit
    (P := P.value a) (fun n => P.positive a (n + 1) ha (by omega)) hd
  refine ⟨g, hg, ?_, hratio⟩
  intro h hh
  cases h with
  | zero => omega
  | succ n => simpa only [Nat.add_assoc] using hinc n

/-- Choose the row slopes together, retaining their bounds and limits on all
positive rows. -/
theorem exists_row_slopes {t : ℝ} (P : ScalarProfile t) :
    ∃ g : ℕ → ℝ, ∀ a : ℕ, 1 ≤ a → 0 ≤ g a ∧
      (∀ h : ℕ, 1 ≤ h → g a ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 (g a)) := by
  classical
  have hex (a : ℕ) : ∃ g : ℝ, 1 ≤ a → 0 ≤ g ∧
      (∀ h : ℕ, 1 ≤ h → g ≤ P.value a (h + 1) - P.value a h) ∧
      Tendsto (fun h : ℕ => P.value a h / (h : ℝ)) atTop (𝓝 g) := by
    by_cases ha : 1 ≤ a
    · obtain ⟨g, hg⟩ := P.exists_row_slope a ha
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun ha' => False.elim (ha ha')⟩
  choose g hg using hex
  exact ⟨g, hg⟩

/-- The exact polynomial lower bound on the diagonal, obtained from row
concavity, shifted tripling, and the simultaneous scalar induction. -/
theorem diagonal_fourth_power_lower {t : ℝ} (P : ScalarProfile t)
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ 4 ≤ P.value n n ^ 3 := by
  obtain ⟨g, hg⟩ := P.exists_row_slopes
  have hupper : ∀ a : ℕ, 1 ≤ a →
      P.value a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
    apply profile_diagonal_le_slope
    · intro a ha h hh
      exact P.tripling a h ha hh
    · intro a ha
      exact (hg a ha).2.2
  have hincrement : ∀ a : ℕ, 1 ≤ a →
      P.value a a + g a + g (a + 1) ≤ P.value (a + 1) (a + 1) := by
    apply diagonal_increment_of_slope_lower
    · intro a ha b hb
      exact P.symmetric a b ha hb
    · intro a ha h hh
      exact (hg a ha).2.1 h hh
  have hDbase : 1 ≤ P.value 1 1 := by
    rw [P.boundary 1 (by omega)]
    norm_num
  have hgbase : 1 ≤ g 1 := by
    have hu := hupper 1 (by omega)
    rw [P.boundary 1 (by omega)] at hu
    norm_num at hu
    exact hu
  exact MatrixMultiplication.AuxiliarySeparation.diagonal_fourth_power_lower_of_one_le
    (fun a => P.value a a) g hgbase hDbase hupper hincrement n hn

/-- Lemma 6.1: a positive symmetric profile satisfying the stated concavity,
tripling, boundary, and rank bounds has exponent at most `3/4`. -/
theorem exponent_le_three_quarters {t : ℝ} (P : ScalarProfile t) (ht : 0 < t) :
    t ≤ 3 / 4 := by
  apply diagonal_exponent_le_three_quarters (D := fun a => P.value a a) ht
  · intro n hn
    exact (P.positive n n hn hn).le
  · exact P.diagonal_fourth_power_lower
  · intro n hn
    have hu := P.rank_bound n n hn hn
    simpa only [two_mul] using hu

end ScalarProfile

/-- The scalar profile implication, with every profile assumption displayed
explicitly rather than bundled in `ScalarProfile`. -/
theorem profile_exponent_le_three_quarters {P : ℕ → ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hpositive : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < P a b)
    (hsymmetric : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → P a b = P b a)
    (hboundary : ∀ b : ℕ, 1 ≤ b → P 1 b = (b : ℝ))
    (hconcave : ∀ a h : ℕ, 1 ≤ a → 2 ≤ h →
      P a (h - 1) + P a (h + 1) ≤ 2 * P a h)
    (htripling : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hrank : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      P a b ≤ ((a : ℝ) + (b : ℝ) - 1) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  exact ScalarProfile.exponent_le_three_quarters
    ⟨P, hpositive, hsymmetric, hboundary, hconcave, htripling, hrank⟩ ht

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule127
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Profile -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Inequalities -/
section FlattenModule128







namespace OAI

/-!
# The inequalities for the polynomial profile

The six character values are combined before the common probability law is
optimized. Each first-leg exponent occurs twice, so the total entropy exponent
is exactly six times the mean exponent used to normalize the profile.
-/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character)

/-- All six permuted characters have the same mean singleton-leg exponent. -/
theorem permutedCharacter_meanExponent (i : Fin 6) :
    (χ.permutedCharacter i).meanExponent = χ.meanExponent := by
  fin_cases i <;> simp [permutedCharacter, meanExponent] <;> ring

/-- The exponents of the six permuted characters have the normalization total. -/
theorem sum_permutedCharacter_pX_mean :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 6 * χ.meanExponent := by
  rw [χ.sum_permutedCharacter_pX]
  unfold meanExponent
  ring

/-- All six factors associated to a positive-size polynomial tensor are positive. -/
theorem permutedCharacter_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (i : Fin 6) : 0 < (χ.permutedCharacter i).value (convolution a b) :=
  (χ.permutedCharacter i).value_convolution_pos ha hb

/-- Exchanging the two output-side positions reorders the six convolution factors. -/
theorem prod_permutedCharacter_swapped_convolution (a b : ℕ) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value
      (fun x z y => convolution a b x y z)) =
    ∏ i : Fin 6, (χ.permutedCharacter i).value (convolution a b) := by
  rw [χ.prod_permutedCharacter_value, χ.prod_permutedCharacter_value]
  exact χ.sixfoldProduct_swap23 _

/-- The actual polynomial profile is concave in its second positive index. -/
theorem convolutionProfile_concave {a b : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hb : 2 ≤ b) :
    χ.convolutionProfile a (b - 1) + χ.convolutionProfile a (b + 1) ≤
      2 * χ.convolutionProfile a b := by
  have h := finite_product_concavity
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a b))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a (b + 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a (b - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i q hq₀ hq₁ =>
      (χ.permutedCharacter i).convolution_concavity_tag a b ha hb q hq₀ hq₁)
  simp only [χ.prod_permutedCharacter_value] at h
  change χ.convolutionProfile a (b + 1) + χ.convolutionProfile a (b - 1) ≤
    2 * χ.convolutionProfile a b at h
  simpa only [add_comm] using h

/-- The actual three-sector degeneration triples the normalized profile. -/
theorem convolutionProfile_tripling {a h : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hh : 0 < h) :
    3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3 * h + a - 1) := by
  have hsw : (fun i s r => convolution a h i r s) ≠ 0 := by
    intro hz
    apply convolution_nonzero ha hh
    exact congrArg
      (fun T : Tensor ℂ (Fin a) (Fin (a + h - 1)) (Fin h) => fun i j k => T i k j) hz
  have h := finite_product_tripling
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a (3 * h + a - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (convolution a h))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (fun x z y => convolution a h x y z))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => χ.permutedCharacter_convolution_pos ha (by omega) i)
    (fun i => χ.permutedCharacter_convolution_pos ha hh i)
    (fun i => (χ.permutedCharacter i).value_pos hsw)
    (fun i => Sector.convolution_tripling_tag (χ.permutedCharacter i) a h ha hh)
    (χ.prod_permutedCharacter_swapped_convolution a h)
  simpa only [χ.prod_permutedCharacter_value, convolutionProfile, symmetrizedProfile] using h

/-- The polynomial profile satisfies every hypothesis of the scalar growth theorem. -/
def toScalarProfile (ht : 0 < χ.meanExponent) : ScalarProfile χ.meanExponent where
  value := χ.convolutionProfile
  positive a b ha hb := χ.convolutionProfile_pos (by omega) (by omega)
  symmetric a b _ _ := χ.convolutionProfile_comm a b
  boundary b hb := χ.convolutionProfile_one_left ht (by omega)
  concave a b ha hb := χ.convolutionProfile_concave ht (by omega) hb
  tripling a h ha hh := χ.convolutionProfile_tripling ht (by omega) (by omega)
  rank_bound a b ha hb := by
    have h := χ.convolutionProfile_le (a := a) (b := b) ht
    have hab : 1 ≤ a + b := by omega
    simpa only [Nat.cast_sub hab, Nat.cast_add, Nat.cast_one] using h

/-- Every actual tensor character has mean singleton-leg exponent at most `3/4`. -/
theorem meanExponent_le_three_quarters : χ.meanExponent ≤ 3 / 4 := by
  by_cases ht : 0 < χ.meanExponent
  · exact (χ.toScalarProfile ht).exponent_le_three_quarters ht
  · have hle : χ.meanExponent ≤ 0 := le_of_not_gt ht
    linarith

/-- The three dot-product exponents of an actual character sum to at most `9/4`. -/
theorem exponent_sum_le_nine_quarters : χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  have h := χ.meanExponent_le_three_quarters
  unfold meanExponent at h
  linarith

end MatrixMultiplication.AuxiliarySeparation.Character

end

end OAI

end FlattenModule128
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Inequalities -/

/- BEGIN upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankBound -/
section FlattenModule129



namespace OAI

/-!
# The exact-rank exponent bound

Detecting characters exist by Appendix A. The determinant and three-sector
polynomial constructions bound the sum of their dot-product exponents by
`9/4`. Integer rounding then gives the same bound for the exact-rank exponent.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- The polynomial inequalities bound the actual exact-rank exponent. -/
theorem exactRankExponent_le_nine_quarters : exactRankExponent ≤ (9 : ℝ) / 4 := by
  apply exactRankExponent_le_nine_quarters_of_characters
  · intro d hd k hk
    exact exists_detecting_character hd hk
  · intro χ d hd
    rw [χ.value_matrixMultiplication (by omega)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ d by omega)) χ.exponent_sum_le_nine_quarters

end MatrixMultiplication.AuxiliarySeparation

end OAI

end FlattenModule129
/- END upstream module OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankBound -/

/-- Complex matrix multiplication has arithmetic exponent at most nine quarters. -/
theorem solution : OAI.MatrixMultiplication.Arithmetic.omega ℂ ≤ (9 : ℝ) / 4 :=
  OAI.MatrixMultiplication.AuxiliarySeparation.omega_le_exactRankExponent.trans
    OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters

