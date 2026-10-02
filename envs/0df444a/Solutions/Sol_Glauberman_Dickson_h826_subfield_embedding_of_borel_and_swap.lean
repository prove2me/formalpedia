-- Prove2me | solution 1 for Glauberman.Dickson.h826_subfield_embedding_of_borel_and_swap
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T13:47:05.434307+00:00
-- url     : https://prove2.me/submissions/3e3d9f42-da82-4218-b8bf-02deac656815

/- Original formalization: Qiuzhen-CFSG/CFSG, Glauberman/DicksonClassification.lean
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; Apache-2.0.
Original hPGL_embedding proof, parameterized by its structural hypotheses.
arexychen: extraction, parameterization, target-environment replay and validation.
Only the unused conjugator witness is projected away.
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
import Mathlib.GroupTheory.Complement
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
universe u v
open scoped LinearAlgebra.Projectivization MatrixGroups
namespace CFSGPackSubfieldEmbedding
private abbrev PSL2MatrixGroup (F : Type*) [Field F] := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F
private def h826_pglMap
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) :
    Matrix.ProjGenLinGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F := by
  let f : GL (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjGenLinGroup.mk.comp
      (Matrix.GeneralLinearGroup.map e)
  apply Matrix.ProjGenLinGroup.lift f
  ext a
  change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map e
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.map e a, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.scalar]

set_option backward.isDefEq.respectTransparency false in
private theorem h826_pglMap_mk
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (A : GL (Fin 2) K) :
    h826_pglMap e (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map e A) := by
  unfold h826_pglMap
  exact Matrix.ProjGenLinGroup.lift_mk _ A

private theorem h826_pglMap_injective
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (he : Function.Injective e) :
    Function.Injective (h826_pglMap e) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pglMap_mk] at hx
    have hcenterF :
        Matrix.GeneralLinearGroup.map e A ∈
          Subgroup.center (GL (Fin 2) F) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterF with ⟨c, hc⟩
    have hc00 :
        c = e ((A : Matrix (Fin 2) (Fin 2) K) 0 0) := by
      have h := congrFun (congrFun hc (0 : Fin 2)) (0 : Fin 2)
      simpa [Matrix.GeneralLinearGroup.map_apply] using h
    have hcenterK : A ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
      ext i j
      apply he
      have h := congrFun (congrFun hc i) j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map_apply, hc00] at h ⊢ <;>
        exact h
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker,
      Matrix.ProjGenLinGroup.ker_mk]
    exact hcenterK
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

private def h826_pslToPGL
    {K : Type u} [Field K] :
    PSL2MatrixGroup K →*
      Matrix.ProjGenLinGroup (Fin 2) K := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) K :=
    Matrix.ProjGenLinGroup.mk.comp
      Matrix.SpecialLinearGroup.toGL
  apply QuotientGroup.lift
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) f
  intro A hA
  rw [MonoidHom.mem_ker]
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL A) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
  rcases Matrix.SpecialLinearGroup.mem_center_iff.mp hA with
    ⟨c, _, hc⟩
  exact ⟨c, by simpa using hc⟩

private theorem h826_pslToPGL_mk
    {K : Type u} [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    h826_pslToPGL
        (QuotientGroup.mk'
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.SpecialLinearGroup.toGL A) := by
  rfl

private theorem h826_pslToPGL_injective
    {K : Type u} [Field K] :
    Function.Injective (h826_pslToPGL (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases QuotientGroup.mk'_surjective
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K)) x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pslToPGL_mk] at hx
    have hcenterGL :
        Matrix.SpecialLinearGroup.toGL A ∈
          Subgroup.center (GL (Fin 2) K) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterGL with ⟨c, hc⟩
    have hc_sq : c ^ 2 = 1 := by
      have hc' :
          Matrix.scalar (Fin 2) c =
            (A : Matrix (Fin 2) (Fin 2) K) := by
        simpa using hc
      have hdet := A.property
      rw [← hc'] at hdet
      simpa [Matrix.det_diagonal, Fin.prod_univ_two, pow_two] using hdet
    have hcenterSL :
        A ∈ Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      exact ⟨c, by simpa using hc_sq, by simpa using hc⟩
    exact (QuotientGroup.eq_one_iff A).mpr hcenterSL
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

theorem _root_.solution {F : Type u} [Field F] [Finite F] {p : ℕ}
    (H : Subgroup (PSL2MatrixGroup F)) (P : Sylow p H)
    (U : Subgroup (PSL2MatrixGroup F))
    (conjH' : H →* PSL2MatrixGroup F)
    (hconjH'_injective : Function.Injective conjH')
    (unipotent : AddChar F (PSL2MatrixGroup F))
    (splitTorus : Fˣ →* PSL2MatrixGroup F)
    (hP_map_conjH'_le_U : (P : Subgroup H).map conjH' ≤ U)
    (hU_range : U = unipotent.toMonoidHom.range)
    (hunipotent_matrix : ∀ x : F, unipotent x =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
        ⟨!![1,x;0,1], by simp [Matrix.det_fin_two]⟩)
    (hsplitTorus_matrix : ∀ a : Fˣ, splitTorus a =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
        ⟨!![(a:F),0;0,(a⁻¹:F)], by simp [Matrix.det_fin_two]⟩) :
    let NP := Subgroup.normalizer (P : Set H)
    let PN := (P : Subgroup H).subgroupOf NP
    ∀ (C : Subgroup NP) (hcomp : PN.IsComplement' C)
      (cgen : C) (hcgen : ∀ x : C, x ∈ Subgroup.zpowers cgen),
    let cN : NP := cgen
    ∀ (r : Fˣ) (hcgen_split : conjH' (cN : H) = splitTorus r),
    let P0 := (P : Subgroup H).map conjH'
    let W : AddSubgroup F :=
      { carrier := {x | unipotent x ∈ P0}
        zero_mem' := by change unipotent 0 ∈ P0; simp
        add_mem' := by
          intro x y hx hy
          change unipotent (x+y) ∈ P0
          rw [unipotent.map_add_eq_mul]
          exact P0.mul_mem hx hy
        neg_mem' := by
          intro x hx
          change unipotent (-x) ∈ P0
          rw [unipotent.map_neg_eq_inv]
          exact P0.inv_mem hx }
    ∀ (x0 : W) (hx0_ne_zero : x0 ≠ 0) (hx0_val_ne_zero : (x0:F) ≠ 0)
      (K : Subfield F) (hK : ∀ a : K, ∀ x : F, x ∈ W → (a:F)*x ∈ W)
      (hKcard : Nat.card K = Nat.card W) (hlambda_mem_K : (r:F)*(r:F) ∈ K),
    let lambdaU := r*r
    let lambdaK0 : K := ⟨(lambdaU:F), hlambda_mem_K⟩
    ∀ (hlambdaK0_ne_zero : lambdaK0 ≠ 0),
    let Point := ℙ F (Fin 2 → F)
    let inf : Point := Projectivization.mk F ![(1:F),0] (by simp)
    let zero : Point := Projectivization.mk F ![(0:F),1] (by simp)
    let affine (x : F) : Point := Projectivization.mk F ![x,1] (by simp)
    ∀ (rho : PSL2MatrixGroup F →* Equiv.Perm Point)
      (hrho_apply : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (z : Point),
        rho (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A) z =
          (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL A)).toLinearEquiv • z),
    letI : MulAction (PSL2MatrixGroup F) Point := MulAction.compHom Point rho
    ∀ (hunipotent_affine : ∀ w x : F, unipotent w • affine x = affine (x+w)),
    letI : MulAction H Point := MulAction.compHom Point (rho.comp conjH')
    let S := MulAction.orbit H inf
    ∀ (haffine_injective : Function.Injective affine) (hswap : H)
      (hswap_inf : hswap • inf = zero) (hswap_zero : hswap • zero = inf)
      (hcover : ∀ z : S, (z:Point) ≠ inf → ∃ w : W, (z:Point) = affine (w:F))
      (hgen : NP ⊔ Subgroup.zpowers hswap = ⊤),
      ∃ phi : H →* Matrix.ProjGenLinGroup (Fin 2) K, Function.Injective phi := by
  classical
  intro NP PN C hcomp cgen hcgen cN r hcgen_split P0 W
    x0 hx0_ne_zero hx0_val_ne_zero K hK hKcard hlambda_mem_K
    lambdaU lambdaK0 hlambdaK0_ne_zero Point inf zero affine rho hrho_apply
    hunipotent_affine S haffine_injective hswap hswap_inf hswap_zero hcover hgen
  letI : MulAction (PSL2MatrixGroup F) Point := MulAction.compHom Point rho
  letI : MulAction H Point := MulAction.compHom Point (rho.comp conjH')
  let scalarMap : K → W := fun a =>
    ⟨(a : F) * (x0 : F), hK a (x0 : F) x0.property⟩
  have hscalarMap_inj : Function.Injective scalarMap := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg Subtype.val hab
    exact mul_right_cancel₀ hx0_val_ne_zero hval
  have hscalarMap_card : Nat.card K = Nat.card W := by
    exact hKcard
  have hscalarMap_surj : Function.Surjective scalarMap :=
    (Nat.bijective_iff_injective_and_card scalarMap).mpr
      ⟨hscalarMap_inj, hscalarMap_card⟩ |>.2
  have hW_span (w : W) :
      ∃ k : K, (w : F) = (k : F) * (x0 : F) := by
    obtain ⟨k, hk⟩ := hscalarMap_surj w
    exact ⟨k, congrArg Subtype.val hk.symm⟩
  have haffine_ne_inf (w : W) : affine (w : F) ≠ inf := by
    intro hwi
    dsimp only [affine, inf] at hwi
    rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hwi with
      ⟨a, ha⟩
    have h1 := congrFun ha (1 : Fin 2)
    simp at h1
  let D : GL (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(x0 : F), 0; 0, 1]
      (by simp [Matrix.det_fin_two, hx0_val_ne_zero])
  let Di : GL (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(x0 : F)⁻¹, 0; 0, 1]
      (by simp [Matrix.det_fin_two, hx0_val_ne_zero])
  have hDi : Di = D⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Di, Matrix.mul_apply, hx0_ne_zero]
  let iotaF : PSL2MatrixGroup F →*
      Matrix.ProjGenLinGroup (Fin 2) F :=
    h826_pslToPGL
  let dPGL : Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjGenLinGroup.mk D
  let toF : H →* Matrix.ProjGenLinGroup (Fin 2) F :=
    (MulAut.conj dPGL⁻¹).toMonoidHom.comp
      (iotaF.comp conjH')
  let j : Matrix.ProjGenLinGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F :=
    h826_pglMap K.subtype
  have hj_injective : Function.Injective j :=
    h826_pglMap_injective K.subtype K.subtype_injective
  let L : Subgroup H := j.range.comap toF
  have hP_le_L : (P : Subgroup H) ≤ L := by
    intro x hxP
    have hxU : conjH' x ∈ U :=
      hP_map_conjH'_le_U
        (Subgroup.mem_map_of_mem conjH' hxP)
    rw [hU_range] at hxU
    rcases hxU with ⟨w, hw⟩
    have hwW : w ∈ W := by
      change unipotent.toMonoidHom w ∈ P0
      rw [hw]
      exact Subgroup.mem_map_of_mem conjH' hxP
    obtain ⟨k, hk⟩ := hW_span ⟨w, hwW⟩
    let Usl : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩
    let Ak : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![1, k; 0, 1] (by simp [Matrix.det_fin_two])
    have hmat :
        Di * Matrix.SpecialLinearGroup.toGL Usl * D =
          Matrix.GeneralLinearGroup.map K.subtype Ak := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j0
      fin_cases i
      all_goals fin_cases j0
      all_goals simp [D, Di, Usl, Ak, Matrix.mul_apply,
        hx0_ne_zero, mul_comm]
      all_goals field_simp
      simpa [mul_comm] using hk
    change toF x ∈ j.range
    refine ⟨Matrix.ProjGenLinGroup.mk Ak, ?_⟩
    rw [h826_pglMap_mk]
    have hiota :
        iotaF (conjH' x) =
          Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL Usl) := by
      rw [← hw]
      change iotaF (unipotent (w : F)) =
        Matrix.ProjGenLinGroup.mk
          (Matrix.SpecialLinearGroup.toGL Usl)
      rw [hunipotent_matrix]
      exact h826_pslToPGL_mk Usl
    change
      Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map K.subtype Ak) =
        dPGL⁻¹ * iotaF (conjH' x) * (dPGL⁻¹)⁻¹
    rw [hiota]
    have hd_inv :
        dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
      dsimp only [dPGL]
      rw [← map_inv, ← hDi]
    have hd_inv_inv :
        (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
          Matrix.ProjGenLinGroup.mk D := by
      rw [← map_inv, hDi, inv_inv]
    rw [hd_inv, hd_inv_inv]
    change
      Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map K.subtype Ak) =
        Matrix.ProjGenLinGroup.mk Di *
          Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL Usl) *
          Matrix.ProjGenLinGroup.mk D
    rw [← map_mul, ← map_mul, hmat]
  have hcgen_mem_L : (cN : H) ∈ L := by
    let Bk : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![lambdaK0, 0; 0, 1]
        (by simp [Matrix.det_fin_two, hlambdaK0_ne_zero])
    let BF : GL (Fin 2) F :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(lambdaU : F), 0; 0, 1]
        (by simp [Matrix.det_fin_two])
    let Rgl : GL (Fin 2) F :=
      Matrix.SpecialLinearGroup.toGL
        (⟨!![(r : F), 0; 0, (r⁻¹ : F)],
            by simp [Matrix.det_fin_two]⟩ :
          Matrix.SpecialLinearGroup (Fin 2) F)
    have hmap_Bk :
        Matrix.GeneralLinearGroup.map K.subtype Bk = BF := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j0
      fin_cases i <;> fin_cases j0 <;>
        simp [Bk, BF, lambdaK0, lambdaU]
    have hBF_scalar :
        BF =
          Matrix.GeneralLinearGroup.scalar (Fin 2) r * Rgl := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j0
      fin_cases i <;> fin_cases j0 <;>
        simp [BF, Rgl, lambdaU,
          Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, pow_two]
    have hBF_comm_D : Di * BF * D = BF := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j0
      fin_cases i
      all_goals fin_cases j0
      all_goals simp [D, Di, BF, Matrix.mul_apply]
      all_goals field_simp
    change toF (cN : H) ∈ j.range
    refine ⟨Matrix.ProjGenLinGroup.mk Bk, ?_⟩
    rw [h826_pglMap_mk, hmap_Bk]
    have hiota :
        iotaF (conjH' (cN : H)) =
          Matrix.ProjGenLinGroup.mk BF := by
      rw [hcgen_split, hsplitTorus_matrix,
        h826_pslToPGL_mk]
      rw [hBF_scalar, map_mul,
        Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    change
      Matrix.ProjGenLinGroup.mk BF =
        dPGL⁻¹ * iotaF (conjH' (cN : H)) * (dPGL⁻¹)⁻¹
    rw [hiota]
    have hd_inv :
        dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
      dsimp only [dPGL]
      rw [← map_inv, ← hDi]
    have hd_inv_inv :
        (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
          Matrix.ProjGenLinGroup.mk D := by
      rw [← map_inv, hDi, inv_inv]
    rw [hd_inv, hd_inv_inv]
    change Matrix.ProjGenLinGroup.mk BF =
      Matrix.ProjGenLinGroup.mk Di *
        Matrix.ProjGenLinGroup.mk BF *
          Matrix.ProjGenLinGroup.mk D
    rw [← map_mul, ← map_mul, hBF_comm_D]
  have hswap_mem_L : hswap ∈ L := by
    rcases QuotientGroup.mk'_surjective
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))
        (conjH' hswap) with ⟨A, hA⟩
    have hA00 :
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
      have hfix := hswap_inf
      change rho (conjH' hswap) inf = zero at hfix
      rw [← hA, hrho_apply] at hfix
      dsimp only [inf, zero] at hfix
      rw [Projectivization.smul_mk] at hfix
      rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
        ⟨a, ha⟩
      have h0 := congrFun ha (0 : Fin 2)
      simpa [Matrix.GeneralLinearGroup.toLin_apply,
        Matrix.mulVec, dotProduct] using h0.symm
    have hA11 :
        (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have hfix := hswap_zero
      change rho (conjH' hswap) zero = inf at hfix
      rw [← hA, hrho_apply] at hfix
      dsimp only [inf, zero] at hfix
      rw [Projectivization.smul_mk] at hfix
      rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
        ⟨a, ha⟩
      have h1 := congrFun ha (1 : Fin 2)
      simpa [Matrix.GeneralLinearGroup.toLin_apply,
        Matrix.mulVec, dotProduct] using h1.symm
    have hA10_ne :
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      intro hc
      have hdet := A.property
      rw [Matrix.det_fin_two, hA00, hA11, hc] at hdet
      norm_num at hdet
    have haffine_x0_mem : affine (x0 : F) ∈ S := by
      rcases x0.property with ⟨g, hgP, hg⟩
      refine ⟨g * hswap, ?_⟩
      change (g * hswap) • inf = affine (x0 : F)
      rw [mul_smul, hswap_inf]
      change rho (conjH' g) zero = affine (x0 : F)
      rw [hg]
      change unipotent (x0 : F) • affine 0 = affine (x0 : F)
      simpa using hunipotent_affine (x0 : F) 0
    let zswap : S :=
      ⟨hswap • affine (x0 : F), by
        rcases haffine_x0_mem with ⟨g, hg⟩
        change g • inf = affine (x0 : F) at hg
        refine ⟨hswap * g, ?_⟩
        change (hswap * g) • inf = hswap • affine (x0 : F)
        rw [mul_smul, hg]⟩
    have hzswap_ne_inf : (zswap : Point) ≠ inf := by
      intro hz
      have hzero_eq :
          hswap • zero = hswap • affine (x0 : F) := by
        change hswap • zero = (zswap : Point)
        rw [hswap_zero, hz]
      have hzero_affine : zero = affine (x0 : F) :=
        smul_left_cancel hswap hzero_eq
      have hxzero : (0 : F) = (x0 : F) := by
        apply haffine_injective
        simpa [affine, zero] using hzero_affine
      exact hx0_ne_zero (Subtype.ext hxzero.symm)
    obtain ⟨w, hw⟩ := hcover zswap hzswap_ne_inf
    obtain ⟨k, hk⟩ := hW_span w
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      have hwzero : (w : F) = 0 := by simp [hk, hk0]
      have hz_zero : (zswap : Point) = zero := by
        rw [hw, hwzero]
      have hinf_affine :
          hswap • inf = hswap • affine (x0 : F) := by
        rw [hswap_inf, ← hz_zero]
      have hia : inf = affine (x0 : F) :=
        smul_left_cancel hswap hinf_affine
      exact (haffine_ne_inf x0) hia.symm
    have hact :
        rho (QuotientGroup.mk'
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F)) A)
            (affine (x0 : F)) =
          affine (w : F) := by
      rw [hA]
      exact hw
    dsimp only [affine] at hact
    rw [hrho_apply, Projectivization.smul_mk] at hact
    rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hact with
      ⟨a0, ha0⟩
    have ha0_0 := congrFun ha0 (0 : Fin 2)
    have ha0_1 := congrFun ha0 (1 : Fin 2)
    simp [Matrix.mulVec, dotProduct, hA00, hA11] at ha0_0 ha0_1
    let Ak : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![0, k; 1, 0]
        (by simp [Matrix.det_fin_two, hk_ne_zero])
    let scale : Fˣ := Units.mk0
      ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * (x0 : F))
      (mul_ne_zero hA10_ne hx0_val_ne_zero)
    have hmat :
        Di * Matrix.SpecialLinearGroup.toGL A * D =
          Matrix.GeneralLinearGroup.scalar (Fin 2) scale *
            Matrix.GeneralLinearGroup.map K.subtype Ak := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j0
      fin_cases i <;> fin_cases j0
      · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, hA00]
      · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, hA00]
        rw [← ha0_0, ha0_1, hk]
        field_simp
      · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, hA11]
      · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, hA11]
    change toF hswap ∈ j.range
    refine ⟨Matrix.ProjGenLinGroup.mk Ak, ?_⟩
    rw [h826_pglMap_mk]
    have hiota :
        iotaF (conjH' hswap) =
          Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL A) := by
      rw [← hA]
      exact h826_pslToPGL_mk A
    change
      Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map K.subtype Ak) =
        dPGL⁻¹ * iotaF (conjH' hswap) * (dPGL⁻¹)⁻¹
    rw [hiota]
    have hd_inv :
        dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
      dsimp only [dPGL]
      rw [← map_inv, ← hDi]
    have hd_inv_inv :
        (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
          Matrix.ProjGenLinGroup.mk D := by
      rw [← map_inv, hDi, inv_inv]
    rw [hd_inv, hd_inv_inv]
    change
      Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map K.subtype Ak) =
        Matrix.ProjGenLinGroup.mk Di *
          Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL A) *
          Matrix.ProjGenLinGroup.mk D
    rw [← map_mul, ← map_mul, hmat, map_mul,
      Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  have hNP_le_L : NP ≤ L := by
    have hPN_le : PN ≤ L.comap NP.subtype := by
      intro n hn
      apply hP_le_L
      exact hn
    have hC_le : C ≤ L.comap NP.subtype := by
      intro d hd
      let dc : C := ⟨d, hd⟩
      rcases hcgen dc with ⟨z, hz⟩
      have hzNP : (cgen : NP) ^ z = d :=
        congrArg Subtype.val hz
      have hzH : ((cgen : NP) : H) ^ z = (d : H) :=
        congrArg Subtype.val hzNP
      change ((d : NP) : H) ∈ L
      rw [← hzH]
      simpa only [cN] using L.zpow_mem hcgen_mem_L z
    have htop_le : (⊤ : Subgroup NP) ≤ L.comap NP.subtype := by
      rw [← hcomp.sup_eq_top]
      exact sup_le hPN_le hC_le
    intro n hn
    change (⟨n, hn⟩ : NP) ∈ L.comap NP.subtype
    exact htop_le (Subgroup.mem_top (⟨n, hn⟩ : NP))
  have hLtop : L = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le hNP_le_L
      (Subgroup.zpowers_le.mpr hswap_mem_L)
  have htoF_range : ∀ x : H, toF x ∈ j.range := by
    intro x
    change x ∈ L
    rw [hLtop]
    trivial
  let toRange : H →* j.range :=
    toF.codRestrict j.range htoF_range
  let eJ : Matrix.ProjGenLinGroup (Fin 2) K ≃* j.range :=
    MulEquiv.ofBijective j.rangeRestrict
      ⟨fun a b hab => hj_injective (congrArg Subtype.val hab),
        MonoidHom.rangeRestrict_surjective j⟩
  let phi : H →* Matrix.ProjGenLinGroup (Fin 2) K :=
    eJ.symm.toMonoidHom.comp toRange
  have hphi_injective : Function.Injective phi := by
    intro x y hxy
    apply hconjH'_injective
    apply h826_pslToPGL_injective
    apply (MulAut.conj dPGL⁻¹).injective
    change toF x = toF y
    have hrange : toRange x = toRange y := by
      apply eJ.symm.injective
      exact hxy
    exact congrArg Subtype.val hrange
  exact ⟨phi, hphi_injective⟩

end CFSGPackSubfieldEmbedding
