-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.propagation_of_local_module
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:33:44.624607+00:00
-- url     : https://prove2.me/submissions/089285b1-f3bd-4f4b-88b5-146a41b576ef

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FreeBlocks_base_intertwining
import Theorems.Thm_OAI_Kadison_FreeBlocks_norm_base_mul
import Theorems.Thm_OAI_Kadison_FreeBlocks_repeated_error_norm
import Theorems.Thm_OAI_Kadison_FreeBlocks_repeated_norm

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma inner_mul_wordVector {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    {a : A} (ha : a ∈ S i) :
    inner ℂ (t.functional.gnsStarAlgHom a (wordVector t S w))
      (t.functional.gnsStarAlgHom a (wordVector t S z)) =
      t.functional (star a * a) * inner ℂ (wordVector t S w) (wordVector t S z) := by
  rw [mul_wordVector, mul_wordVector, Completion.inner_coe, inner_wordVector]
  change t.functional (star (a * word w) * (a * word z)) = _
  simpa only [star_mul, mul_assoc] using
    middle_factor t S hfree hw hz hiw hiz (mul_mem (star_mem ha) ha)

include hfree in
lemma inner_mul_tailSpan (i : ι) {a : A} (ha : a ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpan t S i) (hy : y ∈ tailSpan t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, hiw, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, hiz, rfl⟩ := hy
      exact inner_mul_wordVector t S hfree hw hz hiw hiz ha
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz, mul_add]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]; ring
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz, mul_add]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]; ring

include hfree in
lemma inner_mul_tailSpace (i : ι) {a : A} (ha : a ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpace t S i) (hy : y ∈ tailSpace t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y := by
  apply closure_minimal (s := (tailSpan t S i : Set _))
    (t := {x | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y}) ?_ ?_ hx
  · intro x hx
    apply closure_minimal (s := (tailSpan t S i : Set _))
      (t := {y | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
        t.functional (star a * a) * inner ℂ x y}) ?_ ?_ hy
    · intro y hy
      exact inner_mul_tailSpan t S hfree i ha hx hy
    · apply isClosed_eq <;> fun_prop
  · apply isClosed_eq <;> fun_prop

include hfree in
lemma norm_mul_tailSpace (i : ι) {a : A} (ha : a ∈ S i)
    {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    ‖t.functional.gnsStarAlgHom a x‖ = ‖t.functional.toPreGNS a‖ * ‖x‖ := by
  have h := inner_mul_tailSpace t S hfree i ha hx hx
  have hn := t.functional.preGNS_norm_sq (t.functional.toPreGNS a)
  change (‖t.functional.toPreGNS a‖ : ℂ) ^ 2 = t.functional (star a * a) at hn
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← hn] at h
  have hr : ‖t.functional.gnsStarAlgHom a x‖ ^ 2 =
      ‖t.functional.toPreGNS a‖ ^ 2 * ‖x‖ ^ 2 := by
    have hr := congrArg Complex.re h
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re] using hr
  nlinarith [norm_nonneg (t.functional.gnsStarAlgHom a x),
    mul_nonneg (norm_nonneg (t.functional.toPreGNS a)) (norm_nonneg x)]

include hfree in
lemma headSpace_le_tailSpace_orthogonal (i : ι) :
    headSpace t S i ≤ (tailSpace t S i)ᗮ := by
  apply (headSpan t S i).topologicalClosure_minimal ?_ (Submodule.isClosed_orthogonal _)
  rw [tailSpace, Submodule.orthogonal_closure]
  apply Submodule.span_le.mpr
  rintro x ⟨z, hz, ⟨a, z, rfl, ha⟩, rfl⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, hiw, rfl⟩ := hy
    rw [inner_wordVector]
    change t.functional.toLinearMap (star (word w) * word (a :: z)) = 0
    rw [gram_word (fun a => map_star t.functional a) t.normalized hfree _ _ hw hz]
    exact gram_zero_of_colors_ne _ _ (colors_ne_prepend t S hiw a ha)
  | zero => simp
  | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
  | smul c y _ hy => simp [inner_smul_left, hy]

lemma wordVector_mem_head_sup_tail (i : ι) (w : List (Letter t S)) (hw : Reduced w) :
    wordVector t S w ∈ headSpace t S i ⊔ tailSpace t S i := by
  classical
  cases w with
  | nil =>
    apply Submodule.mem_sup_right
    apply (tailSpan t S i).le_topologicalClosure
    exact Submodule.subset_span ⟨[], hw, by simp [CanPrepend], rfl⟩
  | cons a w =>
    by_cases hi : a.color = i
    · apply Submodule.mem_sup_left
      apply (headSpan t S i).le_topologicalClosure
      exact Submodule.subset_span ⟨a :: w, hw, ⟨a, w, rfl, hi⟩, rfl⟩
    · apply Submodule.mem_sup_right
      apply (tailSpan t S i).le_topologicalClosure
      exact Submodule.subset_span ⟨a :: w, hw, by simpa [CanPrepend] using Ne.symm hi, rfl⟩

lemma generated_mem_head_sup_tail (i : ι) {a : A} (ha : a ∈ iSup S) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ headSpace t S i ⊔ tailSpace t S i := by
  have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
    change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
    rw [FreeMoments.reducedAlgebra_eq_iSup]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, hw, rfl⟩ := ha
    exact wordVector_mem_head_sup_tail t S i w hw
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using
      (headSpace t S i ⊔ tailSpace t S i).add_mem ha hb
  | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using
      (headSpace t S i ⊔ tailSpace t S i).smul_mem c ha

lemma total_head_sup_tail (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (headSpace t S i ⊔ tailSpace t S i).topologicalClosure = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using Completion.induction_on with
  | hp => exact (headSpace t S i ⊔ tailSpace t S i).isClosed_topologicalClosure
  | ih x =>
    let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
    have h := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
      (hgen (t.functional.ofPreGNS x)) ξ
    have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS x) ξ =
        (x : t.functional.GNS) := by
      simp [ξ, PositiveLinearMap.gnsStarAlgHom]
    rw [heq] at h
    apply Submodule.topologicalClosure_mono ?_ h
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using generated_mem_head_sup_tail t S i hb

include hfree in
lemma headSpace_eq_tailSpace_orthogonal (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    headSpace t S i = (tailSpace t S i)ᗮ := by
  apply le_antisymm (headSpace_le_tailSpace_orthogonal t S hfree i)
  intro x hx
  let P := headSpace t S i
  have hp : P.starProjection x ∈ P := P.starProjection_apply_mem x
  have hy : x - P.starProjection x ∈ Pᗮ ⊓ (tailSpace t S i)ᗮ :=
    ⟨P.sub_starProjection_mem_orthogonal x,
      (tailSpace t S i)ᗮ.sub_mem hx (headSpace_le_tailSpace_orthogonal t S hfree i hp)⟩
  have hbot : Pᗮ ⊓ (tailSpace t S i)ᗮ = ⊥ := by
    rw [Submodule.inf_orthogonal, ← Submodule.orthogonal_closure,
      total_head_sup_tail t S i hgen, Submodule.top_orthogonal_eq_bot]
  rw [hbot, Submodule.mem_bot] at hy
  rw [sub_eq_zero.mp hy]
  exact hp

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreePropagation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Kadison

open Filter _root_.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma zeroLimitSpace_closed (F : ℕ → H →L[ℂ] H) (hb : ∀ n, ‖F n‖ ≤ 1) :
    IsClosed (zeroLimitSpace F : Set H) := by
  have hF : Equicontinuous (fun n x => F n x) :=
    (LipschitzWith.uniformEquicontinuous (fun n x => F n x) 1
      (fun n => (F n).lipschitz.weaken (by exact_mod_cast hb n))).equicontinuous
  exact hF.isClosed_setOfPred_tendsto continuous_const

end Kadison

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor Filter _root_.Topology

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma tailProjection_mul_tail {i : ι} {a : A} (ha : a ∈ S i)
    {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom a x) =
      t.functional a • x := by
  let c := a - t.functional a • (1 : A)
  have hc : c ∈ S i := sub_mem ha (SMulMemClass.smul_mem _ (one_mem _))
  have hc0 : t.functional c = 0 := by simp [c, t.normalized]
  have hcx := headSpace_le_tailSpace_orthogonal t S hfree i
    (creation_mem_headSpace t S i hc hc0 hx)
  have hp : (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom c x) = 0 := by
    simp only [Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hcx, ZeroMemClass.coe_zero]
  have heq : t.functional.gnsStarAlgHom c x =
      t.functional.gnsStarAlgHom a x - t.functional a • x := by
    simp [c]
  rw [heq, map_sub, map_smul, (tailSpace t S i).starProjection_eq_self_iff.mpr hx] at hp
  exact sub_eq_zero.mp hp

include hfree in
lemma tailProjection_mul_centered_tail {i : ι} {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a=0) {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom a x)=0 := by
  rw [tailProjection_mul_tail t S hfree ha hx, ha0, zero_smul]

include hfree in
lemma norm_tailProjection_mul (i : ι) {a : A} (ha : a ∈ S i) :
    ‖(tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a‖ ≤
      ‖t.functional.toPreGNS (star a)‖ := by
  have hn : ‖t.functional.gnsStarAlgHom (star a) * (tailSpace t S i).starProjection‖ ≤
      ‖t.functional.toPreGNS (star a)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖t.functional.gnsStarAlgHom (star a) ((tailSpace t S i).starProjection x)‖ ≤ _
    rw [norm_mul_tailSpace t S hfree i (star_mem ha)
      ((tailSpace t S i).starProjection_apply_mem x)]
    exact mul_le_mul_of_nonneg_left ((tailSpace t S i).norm_starProjection_apply_le x)
      (norm_nonneg _)
  have heq : star (t.functional.gnsStarAlgHom (star a) * (tailSpace t S i).starProjection) =
      (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a := by
    rw [star_mul, (isSelfAdjoint_starProjection _).star_eq, ← map_star, star_star]
  rw [← heq, norm_star]
  exact hn

lemma wordVector_mem_tail {i : ι} {w : List (Letter t S)}
    (hw : Reduced w) (hi : CanPrepend t S i w) :
    wordVector t S w ∈ tailSpace t S i :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, hw, hi, rfl⟩)

include hfree in
lemma tailProjection_mul_word (i : ι) {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a=0) {w : List (Letter t S)} (hw : Reduced w) :
    (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom a (wordVector t S w)) =
      match w with
      | [] => 0
      | b :: z => if b.color=i then t.functional (a*b.val) • wordVector t S z else 0 := by
  cases w with
  | nil =>
      exact tailProjection_mul_centered_tail t S hfree ha ha0
        (wordVector_mem_tail t S reduced_nil (by simp [CanPrepend]))
  | cons b z =>
    change _ = if b.color=i then t.functional (a*b.val) • wordVector t S z else 0
    by_cases hb : b.color=i
    · rw [ite_eq_left hb]
      have hz : CanPrepend t S i z := by
        cases z with
        | nil => simp [CanPrepend]
        | cons c z =>
          have := hw.rel
          simpa [CanPrepend, hb] using this
      have heq : t.functional.gnsStarAlgHom a (wordVector t S (b::z)) =
          t.functional.gnsStarAlgHom (a*b.val) (wordVector t S z) := by
        simp only [mul_wordVector, word_cons, mul_assoc]
      rw [heq]
      exact tailProjection_mul_tail t S hfree
        (mul_mem ha (by simpa [hb] using b.mem)) (wordVector_mem_tail t S hw.tail hz)
    · rw [ite_eq_right hb]
      exact tailProjection_mul_centered_tail t S hfree ha ha0
        (wordVector_mem_tail t S hw (by simpa [CanPrepend] using Ne.symm hb))

include hfree in
theorem tailProjection_mul_tendsto_zero (i : ι) (x : ℕ → A)
    (hx : ∀ n, x n ∈ S i) (hx0 : ∀ n, t.functional (x n)=0)
    (hbound : ∀ n, ‖t.functional.toPreGNS (star (x n))‖ ≤ 1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (x n*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (y : t.functional.GNS) :
    Tendsto (fun n => (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom (x n) y))
      atTop (𝓝 0) := by
  let F : ℕ → t.functional.GNS →L[ℂ] t.functional.GNS :=
    fun n => (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom (x n)
  let P := zeroLimitSpace F
  have hP : IsClosed (P : Set t.functional.GNS) :=
    zeroLimitSpace_closed F (fun n => (norm_tailProjection_mul t S hfree i (hx n)).trans (hbound n))
  have hw : ∀ w : List (Letter t S), Reduced w → wordVector t S w ∈ P := by
    intro w hw
    change Tendsto _ _ _
    simp only [F, mul_apply_eq_comp,
      tailProjection_mul_word t S hfree i (hx _) (hx0 _) hw]
    cases w with
    | nil => exact tendsto_const_nhds
    | cons b z =>
      by_cases hb : b.color=i
      · simp only [ite_eq_left hb]
        simpa only [zero_smul] using
          (hmoment b.val (by simpa [hb] using b.mem)).smul_const (wordVector t S z)
      · simp only [ite_eq_right hb]
        exact tendsto_const_nhds
  have hg : ∀ a ∈ iSup S, (t.functional.toPreGNS a : t.functional.GNS) ∈ P := by
    intro a ha
    have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
      change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
      rw [FreeMoments.reducedAlgebra_eq_iSup]
      exact ha
    clear ha
    induction ha' using Submodule.span_induction with
    | mem a ha => obtain ⟨w, hr, rfl⟩ := ha; exact hw w hr
    | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
    | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using P.add_mem ha hb
    | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using P.smul_mem c ha
  have hall : ∀ z : t.functional.GNS, z ∈ P := by
    intro z
    induction z using Completion.induction_on with
    | hp => exact hP
    | ih z =>
      let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
      have hz := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
        (hgen (t.functional.ofPreGNS z)) ξ
      have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS z) ξ =
          (z : t.functional.GNS) := by
        simp [ξ, PositiveLinearMap.gnsStarAlgHom]
      rw [heq] at hz
      apply closure_minimal (s := (Kadison.orbitSubmodule (generatedOperators t S) ξ : Set _))
        ?_ hP hz
      rintro f ⟨a, ha, rfl⟩
      obtain ⟨b, hb, rfl⟩ := ha
      simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using hg b hb
  exact hall y

end Kadison.FreeCreation

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor Filter _root_.Topology

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma mul_head_norm {i j : ι} (hij : i ≠ j) {a : A} (ha : a ∈ S j)
    (ha0 : t.functional a=0) (ha1 : ‖t.functional.toPreGNS a‖=1)
    {y : t.functional.GNS} (hy : y ∈ headSpace t S i) :
    t.functional.gnsStarAlgHom a y ∈ headSpace t S j ∧
      ‖t.functional.gnsStarAlgHom a y‖=‖y‖ := by
  have ht := headSpace_le_other_tailSpace t S hij hy
  exact ⟨creation_mem_headSpace t S j ha ha0 ht,
    by rw [norm_mul_tailSpace t S hfree j ha ht, ha1, one_mul]⟩

include hfree in
lemma repeated_prefix_head {i j : ι} (hij : i ≠ j) {x s : A}
    (hx : x ∈ S i) (hx0 : t.functional x=0) (hx1 : ‖t.functional.toPreGNS x‖=1)
    (hs : s ∈ S j) (hs0 : t.functional s=0) (hs1 : ‖t.functional.toPreGNS s‖=1)
    (k : ℕ) {y : t.functional.GNS} (hy : y ∈ headSpace t S i) :
    t.functional.gnsStarAlgHom ((s*x)^k*s) y ∈ headSpace t S j ∧
      ‖t.functional.gnsStarAlgHom ((s*x)^k*s) y‖=‖y‖ := by
  induction k with
  | zero => simpa using mul_head_norm t S hfree hij hs hs0 hs1 hy
  | succ k ih =>
    have h1 := mul_head_norm t S hfree hij.symm hx hx0 hx1 ih.1
    have h2 := mul_head_norm t S hfree hij hs hs0 hs1 h1.1
    have heq : t.functional.gnsStarAlgHom ((s*x)^(k+1)*s) y =
        t.functional.gnsStarAlgHom s (t.functional.gnsStarAlgHom x
          (t.functional.gnsStarAlgHom ((s*x)^k*s) y)) := by
      simp only [pow_succ', mul_assoc, map_mul, mul_apply_eq_comp]
    rw [heq]
    exact ⟨h2.1, h2.2.trans (h1.2.trans ih.2)⟩

include hfree in
lemma prefix_split_bound {i j : ι} (hij : i ≠ j) {x s : A}
    (hx : x ∈ S i) (hx0 : t.functional x=0) (hx1 : ‖t.functional.toPreGNS x‖=1)
    (hs : s ∈ S j) (hs0 : t.functional s=0) (hs1 : ‖t.functional.toPreGNS s‖=1)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (y : t.functional.GNS) :
    ‖t.functional.gnsStarAlgHom ((s*x)^k*s) y‖ ≤ ‖y‖ +
      ‖(s*x)^k*s‖ * ‖(tailSpace t S i).starProjection y‖ := by
  let P := (tailSpace t S i).starProjection
  let L := t.functional.gnsStarAlgHom ((s*x)^k*s)
  have hhead : y-P y ∈ headSpace t S i := by
    rw [headSpace_eq_tailSpace_orthogonal t S hfree i hgen]
    exact (tailSpace t S i).sub_starProjection_mem_orthogonal y
  have hi := (repeated_prefix_head t S hfree hij hx hx0 hx1 hs hs0 hs1 k hhead).2
  have hnorm : ‖y-P y‖ ≤ ‖y‖ := by
    have h := ((tailSpace t S i)ᗮ).norm_starProjection_apply_le y
    simpa only [Submodule.starProjection_orthogonal', sub_apply, one_apply_eq_self] using h
  calc
    ‖L y‖ = ‖L (y-P y)+L (P y)‖ := by rw [← map_add, sub_add_cancel]
    _ ≤ ‖L (y-P y)‖+‖L (P y)‖ := norm_add_le _ _
    _ ≤ ‖y‖+‖L‖*‖P y‖ := add_le_add (hi.le.trans hnorm) (L.le_opNorm _)
    _ ≤ ‖y‖+‖(s*x)^k*s‖*‖P y‖ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le t.functional.gnsStarAlgHom _) (norm_nonneg _))

include hfree in
theorem repeated_prefix_eventual_bound {i j : ι} (hij : i ≠ j)
    (x : ℕ → A) (s : A)
    (hx : ∀ n, x n ∈ S i) (hx0 : ∀ n, t.functional (x n)=0)
    (hx1 : ∀ n, ‖t.functional.toPreGNS (x n)‖=1)
    (hxs : ∀ n, ‖t.functional.toPreGNS (star (x n))‖≤1)
    (hs : s ∈ S j) (hs0 : t.functional s=0) (hs1 : ‖t.functional.toPreGNS s‖=1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (x n*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (M : ℝ) (hM : ∀ n, ‖(s*x n)^k*s‖≤M)
    (y : t.functional.GNS) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n in atTop, ‖t.functional.gnsStarAlgHom ((s*x n)^k*s)
        (t.functional.gnsStarAlgHom (x n) y)‖ ≤
      ‖t.functional.gnsStarAlgHom (x n) y‖+η := by
  have hz := tailProjection_mul_tendsto_zero t S hfree i x hx hx0 hxs hmoment hgen y
  have hz' : Tendsto (fun n => M*‖(tailSpace t S i).starProjection
      (t.functional.gnsStarAlgHom (x n) y)‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hz.norm.const_mul M
  have he : ∀ᶠ n in atTop, M*‖(tailSpace t S i).starProjection
      (t.functional.gnsStarAlgHom (x n) y)‖<η := hz'.eventually_lt_const hη
  filter_upwards [he] with n hn
  exact (prefix_split_bound t S hfree hij (hx n) (hx0 n) (hx1 n) hs hs0 hs1 hgen k _).trans
    (add_le_add le_rfl ((mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _)).trans hn.le))

end Kadison.FreeCreation

namespace Kadison.FreeCreation

open FreeWordTensor

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A)

lemma norm_mul_supported (x q : A) (c : ℝ) (hc : 0 ≤ c)
    (hxx : star x*x=(c : ℂ) • q) (y : t.functional.GNS)
    (hy : t.functional.gnsStarAlgHom q y=y) :
    ‖t.functional.gnsStarAlgHom x y‖=Real.sqrt c*‖y‖ := by
  have hi := ContinuousLinearMap.adjoint_inner_right (t.functional.gnsStarAlgHom x) y
    (t.functional.gnsStarAlgHom x y)
  change inner ℂ y ((star (t.functional.gnsStarAlgHom x)*t.functional.gnsStarAlgHom x) y) = _ at hi
  rw [←map_star, ←map_mul, hxx, map_smul, smul_apply, hy, inner_smul_right,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
  have hr := congrArg Complex.re hi
  have heq : c*‖y‖^2=‖t.functional.gnsStarAlgHom x y‖^2 := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      ←Complex.ofReal_mul, Complex.ofReal_re] using hr
  have hs := Real.sq_sqrt hc
  have hpos := mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg y)
  nlinarith [norm_nonneg (t.functional.gnsStarAlgHom x y)]

end Kadison.FreeCreation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreePropagationEstimate
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open Filter _root_.Topology ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

lemma norm_factorVector (d : D) :
    ‖TracialGNS.algebraVector (factorTrace t f hf) d‖=
      ‖(t.functional.toPreGNS (f d) : t.functional.GNS)‖ := by
  simp only [TracialGNS.algebraVector_apply,UniformSpace.Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.ofPreGNS_toPreGNS,
    pullbackState_apply,map_mul,map_star]

lemma scale_normalization (q : D) (hq : IsStarProjection q) (x : A)
    (hx : ‖t.functional.toPreGNS x‖=1) (hxq : x*f q=x) (c : ℝ) (hc : 0 ≤ c)
    (hxx : star x*x=(c:ℂ) • f q) :
    Real.sqrt c*‖TracialGNS.algebraVector (factorTrace t f hf) q‖=1 := by
  let y : t.functional.GNS := t.functional.toPreGNS (f q)
  have hy : t.functional.gnsStarAlgHom (f q) y=y := by
    change t.functional.gnsStarAlgHom (f q) (t.functional.toPreGNS (f q) : t.functional.GNS)=_
    rw [TracialGNS.left_coe,←map_mul,hq.isIdempotentElem.eq]
  have hn := FreeCreation.norm_mul_supported t x (f q) c hc hxx y hy
  have hn' : ‖t.functional.gnsStarAlgHom x y‖=1 := by
    change ‖t.functional.gnsStarAlgHom x (t.functional.toPreGNS (f q) : t.functional.GNS)‖=1
    rw [TracialGNS.left_coe,hxq,UniformSpace.Completion.norm_coe,hx]
  rw [hn'] at hn
  rw [norm_factorVector]
  exact hn.symm

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

include hB in
theorem propagation_of_local_module_oai
    (s : letterSpace t S j) (hs : ‖s‖=1)
    (q : D) (hq : IsStarProjection q) (c : ℝ) (hc : 0 ≤ c)
    (x : ℕ → letterSpace t S i) (hx : ∀ n, ‖x n‖=1)
    (hxq : ∀ n, letterValue t S i (x n)*f q=letterValue t S i (x n))
    (hxx : ∀ n, star (letterValue t S i (x n))*letterValue t S i (x n)=(c:ℂ) • f q)
    (hxs : ∀ n, ‖t.functional.toPreGNS (star (letterValue t S i (x n)))‖≤1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (letterValue t S i (x n)*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (M : ℝ) (hM : ∀ n, ‖(letterValue t S j s*letterValue t S i (x n))^k*letterValue t S j s‖≤M)
    (δ : ℝ) (hδ : 0≤δ) (v : multiplicityLevel t S j 0)
    (T : t.functional.GNS →L[ℂ] t.functional.GNS)
    (hT : ∀ a : A, T.comp (t.functional.gnsStarAlgHom a)=(t.functional.gnsStarAlgHom a).comp T)
    (happrox : ∀ z ∈ cyclicSubspace t.functional.gnsStarAlgHom.range
        (t.functional.gnsStarAlgHom (f q) (blockEmbedding t S hfree hij 0 v)),
      ‖G z-T z‖≤δ*‖z‖) :
    ‖B (k+1) (repeatInsertion t S s hs (k+1) v)-
      repeatInsertion t S s hs (k+1) (B 0 v)‖≤2*δ*‖v‖ := by
  have hscale : Real.sqrt c*‖TracialGNS.algebraVector (factorTrace t f hf) q‖≤1 := by
    apply (scale_normalization t f hf q hq (letterValue t S i (x 0)) ?_ (hxq 0) c hc (hxx 0)).le
    change ‖t.functional.toPreGNS (t.functional.ofPreGNS (x 0 : preSpace t))‖=1
    rw [PositiveLinearMap.toPreGNS_ofPreGNS]
    exact hx 0
  let L := t.functional.gnsStarAlgHom
  let b0 := blockEmbedding t S hfree hij 0
  let ξ := L (f q) (b0 v)
  let y := T ξ-G ξ
  have hTapp (a : A) (z : t.functional.GNS) : T (L a z)=L a (T z) :=
    congrArg (fun R : t.functional.GNS →L[ℂ] t.functional.GNS => R z) (hT a)
  have hqξ : L (f q) ξ=ξ := by
    change (L (f q)*L (f q)) (b0 v)=L (f q) (b0 v)
    rw [←map_mul,←map_mul,hq.isIdempotentElem.eq]
  have hGξ : G ξ=L (f q) (b0 (B 0 v)) :=
    base_intertwining t S f hf hS hfree hij G B hB s hs (x 0) q v
  have hqy : L (f q) y=y := by
    dsimp only [y]
    rw [map_sub,←hTapp,hqξ,hGξ]
    change T ξ-(L (f q)*L (f q)) (b0 (B 0 v))=T ξ-L (f q) (b0 (B 0 v))
    rw [←map_mul,←map_mul,hq.isIdempotentElem.eq]
  have hy : ‖y‖≤δ*(‖TracialGNS.algebraVector (factorTrace t f hf) q‖*‖v‖) := by
    have he := happrox ξ (mem_cyclicSubspace_self _ _)
    rw [norm_sub_rev] at he
    have hn := norm_base_mul t S f hf hS hfree hij s hs (x 0) q v
    exact he.trans_eq (congrArg (fun r : ℝ => δ*r) hn)
  have hxy (n : ℕ) : ‖L (letterValue t S i (x n)) y‖≤δ*‖v‖ := by
    rw [FreeCreation.norm_mul_supported t _ (f q) c hc (hxx n) y hqy]
    calc
      _ ≤ Real.sqrt c*(δ*(‖TracialGNS.algebraVector (factorTrace t f hf) q‖*‖v‖)) :=
        mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg c)
      _ = (Real.sqrt c*‖TracialGNS.algebraVector (factorTrace t f hf) q‖)*(δ*‖v‖) := by ring
      _ ≤ 1*(δ*‖v‖) := mul_le_mul_of_nonneg_right hscale (mul_nonneg hδ (norm_nonneg _))
      _ = _ := one_mul _
  have hnormx (n : ℕ) : ‖t.functional.toPreGNS (letterValue t S i (x n))‖=1 := by
    change ‖t.functional.toPreGNS (t.functional.ofPreGNS (x n : preSpace t))‖=1
    rw [PositiveLinearMap.toPreGNS_ofPreGNS]
    exact hx n
  have hnorms : ‖t.functional.toPreGNS (letterValue t S j s)‖=1 := by
    change ‖t.functional.toPreGNS (t.functional.ofPreGNS (s : preSpace t))‖=1
    rw [PositiveLinearMap.toPreGNS_ofPreGNS]
    exact hs
  apply le_of_forall_pos_le_add
  intro η hη
  have hevent := FreeCreation.repeated_prefix_eventual_bound t S hfree hij
    (fun n => letterValue t S i (x n)) (letterValue t S j s)
    (fun n => (x n).property.1) (fun n => (x n).property.2) hnormx hxs
    s.property.1 s.property.2 hnorms hmoment hgen k M hM y η hη
  obtain ⟨n, hn⟩ := hevent.exists
  let a := (letterValue t S j s*letterValue t S i (x n))^k*letterValue t S j s
  let ξn := L ((letterValue t S j s*letterValue t S i (x n))^(k+1)) (b0 v)
  have hp : (letterValue t S j s*letterValue t S i (x n))^(k+1)=a*letterValue t S i (x n) := by
    dsimp only [a]
    rw [pow_succ,mul_assoc]
  have hξn : ξn=L (a*letterValue t S i (x n)) ξ := by
    dsimp only [ξn,ξ]
    rw [hp]
    change L (a*letterValue t S i (x n)) (b0 v)=
      (L (a*letterValue t S i (x n))*L (f q)) (b0 v)
    have hsupp : (a*letterValue t S i (x n))*f q=a*letterValue t S i (x n) :=
      (mul_assoc _ _ _).trans (congrArg (fun b : A => a*b) (hxq n))
    rw [←map_mul,hsupp]
  have hmem : ξn ∈ cyclicSubspace L.range ξ := by
    rw [hξn]
    exact cyclicSubspace_invariant L.range ξ (show L _ ∈ L.range from ⟨_,rfl⟩) ξ (mem_cyclicSubspace_self _ _)
  have hξnorm : ‖ξn‖=‖v‖ := repeated_norm t S f hf hS hfree hij s hs (x n) (hx n) (k+1) v
  have hcomp (z : t.functional.GNS) : L a (L (letterValue t S i (x n)) (L (f q) z))=
      L ((letterValue t S j s*letterValue t S i (x n))^(k+1)) z := by
    change (L a*(L (letterValue t S i (x n))*L (f q))) z=_
    rw [←map_mul,hxq n,←map_mul,←hp]
  have heq : G ξn-L ((letterValue t S j s*letterValue t S i (x n))^(k+1)) (b0 (B 0 v))=
      (G ξn-T ξn)+L a (L (letterValue t S i (x n)) y) := by
    rw [hξn,hTapp]
    dsimp only [y]
    rw [map_sub,map_sub,hGξ,hcomp]
    simp only [map_mul,mul_apply_eq_comp]
    abel
  have hfixed := repeated_error_norm t S f hf hS hfree hij G B hB s hs (x n) (hx n) (k+1) v
  rw [←hfixed]
  change ‖G ξn-L _ (b0 (B 0 v))‖≤_
  rw [heq]
  have hfirst := happrox ξn hmem
  rw [hξnorm] at hfirst
  have hsecond : ‖L a (L (letterValue t S i (x n)) y)‖≤δ*‖v‖+η :=
    hn.trans (add_le_add (hxy n) le_rfl)
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.propagation_of_local_module_oai.{u_1} := @OAI.Kadison.FreeBlocks.propagation_of_local_module_oai.{u_1}
