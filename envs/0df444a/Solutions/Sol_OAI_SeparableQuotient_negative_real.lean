-- Prove2me | solution 1 for OAI.SeparableQuotient.negative_real
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:16:13.084988+00:00
-- url     : https://prove2.me/submissions/80a33176-7f12-4a8f-9b0a-dff44c785f61

import Mathlib
import Definitions.Def_SeparableQuotientNegative
import Definitions.Def_OAIQWSQN006

section
-- module Solutions.OAIQW_SeparableQuotient.EvaluationCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

attribute [local instance] OAI.SeparableQuotient.necessityDualGroup
attribute [local instance] OAI.SeparableQuotient.necessityDualSpace
omit [CompleteSpace Y] in
/-- The dual of an infinite-dimensional normed space is infinite-dimensional. -/
lemma dual_infiniteDimensional (hY : ¬ FiniteDimensional 𝕜 Y) :
    ¬ FiniteDimensional 𝕜 (StrongDual 𝕜 Y) := by
  intro h
  let := h
  apply hY
  exact FiniteDimensional.of_injective (NormedSpace.inclusionInDoubleDualLi 𝕜).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi 𝕜).injective

/-- The adjoint of an onto map is bounded below, with the actual open-mapping lift constant. -/
lemma precomp_antilipschitz_of_surjective (T : X →L[𝕜] Y) (hT : Function.Surjective T) :
    ∃ C : NNReal, AntilipschitzWith C
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) := by
  obtain ⟨g, _hg⟩ := T.exists_nonlinearRightInverse_of_surjective (LinearMap.range_eq_top.mpr hT)
  let S : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X := ContinuousLinearMap.precomp 𝕜 T
  refine ⟨g.nnnorm, S.antilipschitz_of_bound ?_⟩
  intro f
  apply f.opNorm_le_bound (mul_nonneg g.nnnorm.coe_nonneg (norm_nonneg _))
  intro y
  calc
    ‖f y‖ = ‖S f (g y)‖ := by
      change ‖f y‖ = ‖f (T (g y))‖
      rw [g.right_inv]
    _ ≤ ‖S f‖ * ‖g y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖S f‖ * (g.nnnorm * ‖y‖) :=
      mul_le_mul_of_nonneg_left (g.bound y) (norm_nonneg _)
    _ = (g.nnnorm * ‖S f‖) * ‖y‖ := by ring

/-- A separable quotient yields an infinite-dimensional dual subspace with norm-separable evaluation. -/
theorem separable_evaluation_of_hasSeparableQuotient (hX : HasSeparableQuotient 𝕜 X) :
    ∃ F : Submodule 𝕜 (StrongDual 𝕜 X), IsClosed (F : Set (StrongDual 𝕜 X)) ∧
      (¬ FiniteDimensional 𝕜 F) ∧
      TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F)) := by
  obtain ⟨Y, hYn, hYs, hYc, hYsep, hYinf, T, hT⟩ := hX
  let := hYn
  let := hYs
  let := hYc
  let := hYsep
  let S : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X := ContinuousLinearMap.precomp 𝕜 T
  obtain ⟨C, hC⟩ := precomp_antilipschitz_of_surjective T hT
  have hSc : IsClosed (Set.range S) := hC.isClosed_range S.uniformContinuous
  let F := S.range
  have hFc : IsClosed (F : Set (StrongDual 𝕜 X)) := hSc
  let e : StrongDual 𝕜 Y ≃L[𝕜] F := S.equivRange hC.injective hSc
  have hFi : ¬ FiniteDimensional 𝕜 F := by
    intro hf
    let := hf
    have : FiniteDimensional 𝕜 (StrongDual 𝕜 Y) := e.toLinearEquiv.symm.finiteDimensional
    exact dual_infiniteDimensional hYinf inferInstance
  let Q : Y →L[𝕜] StrongDual 𝕜 F :=
    (ContinuousLinearMap.precomp 𝕜 e.symm.toContinuousLinearMap).comp
      (NormedSpace.inclusionInDoubleDual 𝕜 Y)
  have he (x : X) : subspaceEvaluation F x = Q (T x) := by
    ext f
    obtain ⟨g, rfl⟩ := e.surjective f
    change (S g) x = (e.symm (e g)) (T x)
    rw [e.symm_apply_apply]
    rfl
  refine ⟨F, hFc, hFi, (TopologicalSpace.isSeparable_range Q.continuous).mono ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨T x, (he x).symm⟩

end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- The completion of c₀₀ under a bounded rational norming set. -/
namespace SeparableQuotient.NormConstruction
open scoped Topology ENNReal
open Filter
universe u
variable {Γ : Type u}

namespace NormingSet
variable (K : NormingSet Γ)

lemma approximating_sequence (x : K.Space) :
    ∃ v : ℕ → Γ →₀ ℝ, Tendsto (fun n => K.includeFinite (v n)) atTop (𝓝 x) := by
  have hx := K.denseRange_includeFinite x
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp hx
  choose w hw using hv
  exact ⟨w, by simpa only [hw] using ht⟩

/-- Every completed vector has countable coordinate support. -/
lemma support_countable (x : K.Space) : Set.Countable {a | K.coordinate a x ≠ 0} := by
  obtain ⟨v, hv⟩ := K.approximating_sequence x
  have hc : Set.Countable (⋃ n, ((v n).support : Set Γ)) :=
    Set.countable_iUnion (fun n => (v n).support.countable_toSet)
  apply hc.mono
  intro a ha
  by_contra h
  have hz : ∀ n, v n a = 0 := by
    intro n
    by_contra hn
    exact h (Set.mem_iUnion.mpr ⟨n, Finsupp.mem_support_iff.mpr hn⟩)
  have ht := (K.coordinate a).continuous.tendsto x |>.comp hv
  have ht0 : Tendsto (fun n => K.coordinate a (K.includeFinite (v n))) atTop (𝓝 0) := by
    simpa only [K.coordinate_includeFinite, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact ha (tendsto_nhds_unique ht ht0)

end NormingSet
end SeparableQuotient.NormConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinateDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

lemma generator_independent : LinearIndependent ℝ K.generator := by
  change LinearIndependent ℝ (fun a : Γ => K.includeFinite (Finsupp.single a 1))
  exact (Finsupp.linearIndependent_single_one (R := ℝ) (ι := Γ)).map_injOn
      K.includeFinite K.includeFinite_injective.injOn

lemma infiniteDimensional [Infinite Γ] : ¬ Module.Finite ℝ K.Space := by
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite K.generator K.generator_independent

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinatePredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

lemma infiniteDimensional : ¬ Module.Finite ℝ E := norming.infiniteDimensional

lemma support_countable (x : E) : Set.Countable {a | coordinate a x ≠ 0} :=
  norming.support_countable x

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.BinaryNodes

lemma child_injective {n m : ℕ} {b c : Bool} (h : child n b = child m c) : n = m ∧ b = c := by
  cases b <;> cases c <;> simp_all [child] <;> omega

lemma ancestors_branch_length (b : ℕ → Bool) (n : ℕ) : (ancestors (branch b n)).length = n+1 := by
  rw [ancestors_branch,List.length_ofFn]

lemma branch_same_level {b c : ℕ → Bool} {n m : ℕ} (h : branch b n = branch c m) : n = m := by
  have hh := congrArg (fun k => (ancestors k).length) h
  simpa only [ancestors_branch_length,Nat.add_right_cancel_iff] using hh

lemma exists_separating_node {b c : ℕ → Bool} (hbc : b ≠ c) :
    ∃ n, ∀ m, branch b n ≠ branch c m := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hbc
  refine ⟨i+1,fun m hm => ?_⟩
  have he := branch_same_level hm
  subst m
  exact hi (child_injective hm).2

end SeparableQuotient.BinaryNodes

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology
namespace TreeNode
variable {f : Family} (z : BlockSequence f)

lemma cross_evaluate {i j : ℕ} (hij : i ≠ j) :
    norming.evaluateArray (norming.includeFinite (node z j).pair.vector) (node z i).pair.piece.value = 0 := by
  apply evaluateArray_finite_disjoint
  apply Finset.disjoint_left.mpr
  intro α hα hβ
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (lt_irrefl α) (vectorCrop_successive (node z i).pair.nonzero (node z j).pair.nonzero
      (successive_vector z hij) α ((node z i).pair.support α hβ)
      α (support_mem_vectorCrop f _ _ α hα)).1
  · exact (lt_irrefl α) (vectorCrop_successive (node z j).pair.nonzero (node z i).pair.nonzero
      (successive_vector z hji) α (support_mem_vectorCrop f _ _ α hα)
      α ((node z i).pair.support α hβ)).1

lemma pathPartial_node (b : ℕ → Bool) (n N : ℕ) (hn : n ≤ N) :
    pathPartial (branchPath z b) N (norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector) =
      norming.evaluateArray (norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector)
        (node z (BinaryNodes.branch b n)).pair.piece.value := by
  rw [pathPartial, ← norming.evaluateArray_eq_functional]
  change norming.evaluateArray _ (∑ j : Fin (N+1), (node z (BinaryNodes.branch b j)).pair.piece.value) = _
  rw [map_sum]
  apply Finset.sum_eq_single (⟨n,by omega⟩ : Fin (N+1))
  · intro j _ hj
    exact cross_evaluate z (fun he => hj (Fin.ext ((BinaryNodes.branch_strict b).injective he)))
  · simp

lemma pathPartial_other (b : ℕ → Bool) (k : ℕ) (hk : ∀ j, BinaryNodes.branch b j ≠ k) (N : ℕ) :
    pathPartial (branchPath z b) N (norming.includeFinite (node z k).pair.vector) = 0 := by
  rw [pathPartial, ← norming.evaluateArray_eq_functional]
  change norming.evaluateArray _ (∑ j : Fin (N+1), (node z (BinaryNodes.branch b j)).pair.piece.value) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun j _ => cross_evaluate z (hk j))

lemma pathFunctional_node (b : ℕ → Bool) (n : ℕ) :
    1/2 ≤ pathFunctional (branchPath z b) (norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector) := by
  let x := norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector
  have he : pathFunctional (branchPath z b) x = norming.evaluateArray x
      (node z (BinaryNodes.branch b n)).pair.piece.value :=
    tendsto_nhds_unique (pathPartial_tendsto (branchPath z b) x)
      (tendsto_const_nhds.congr' ((eventually_ge_atTop n).mono (fun N hN => (pathPartial_node z b n N hN).symm)))
  rw [he]
  exact (node z (BinaryNodes.branch b n)).pair.eval_ge

lemma pathFunctional_other (b : ℕ → Bool) (k : ℕ) (hk : ∀ j, BinaryNodes.branch b j ≠ k) :
    pathFunctional (branchPath z b) (norming.includeFinite (node z k).pair.vector) = 0 :=
  tendsto_nhds_unique (pathPartial_tendsto (branchPath z b) _)
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun N => (pathPartial_other z b k hk N).symm)))

end TreeNode
end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.StrictSingularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set Metric
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z W : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

lemma not_strictlySingular_iff (T : Y →L[𝕜] Z) :
    ¬ StrictlySingular T ↔ ∃ (M : Submodule 𝕜 Y), IsClosed (M : Set Y) ∧
      ¬ FiniteDimensional 𝕜 M ∧ ∃ c : ℝ, 0 < c ∧ ∀ x : M, c*‖x‖ ≤ ‖T x‖ := by
  simp only [StrictlySingular, not_forall, not_exists, not_lt, exists_prop]

lemma lowerBound_antilipschitz (T : Y →L[𝕜] Z) (c : ℝ) (hc : 0 < c)
    (h : ∀ x, c*‖x‖ ≤ ‖T x‖) : AntilipschitzWith ⟨c⁻¹,inv_nonneg.mpr hc.le⟩ T := by
  apply T.antilipschitz_of_bound
  intro x
  change ‖x‖ ≤ c⁻¹*‖T x‖
  exact (le_inv_mul_iff₀ hc).mpr (by simpa [mul_comm] using h x)

lemma lowerBound_isClosed_range [CompleteSpace Y] (T : Y →L[𝕜] Z) (c : ℝ) (hc : 0 < c)
    (h : ∀ x, c*‖x‖ ≤ ‖T x‖) : IsClosed (Set.range T) :=
  (lowerBound_antilipschitz T c hc h).isClosed_range T.uniformContinuous

/-- A non-strictly-singular map furnishes a closed infinite-dimensional image
and a bounded lift into its original domain. -/
theorem exists_lift_of_not_strictlySingular [CompleteSpace Y] [CompleteSpace Z] (T : Y →L[𝕜] Z)
    (hT : ¬ StrictlySingular T) :
    ∃ (H : Submodule 𝕜 Z), IsClosed (H : Set Z) ∧ ¬ FiniteDimensional 𝕜 H ∧
      ∃ U : H →L[𝕜] Y, ∀ x : H, T (U x) = x := by
  obtain ⟨M,hM,hI,c,hc,h⟩ := (not_strictlySingular_iff T).mp hT
  let : CompleteSpace M := hM.completeSpace_coe
  let A := T.comp M.subtypeL
  let e := A.equivRange (lowerBound_antilipschitz A c hc h).injective
    (lowerBound_isClosed_range A c hc h)
  refine ⟨A.range,lowerBound_isClosed_range A c hc h,?_,M.subtypeL.comp e.symm.toContinuousLinearMap,?_⟩
  · intro hF
    let : FiniteDimensional 𝕜 A.range := hF
    exact hI (FiniteDimensional.of_injective e.toLinearMap e.injective)
  · intro x
    exact congrArg (fun x : A.range => (x : Z)) (e.apply_symm_apply x)

lemma StrictlySingular.comp_left (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
    (S : Z →L[𝕜] W) : StrictlySingular (S.comp T) := by
  intro M hM hI c hc
  obtain ⟨x,hx⟩ := hT M hM hI (c/(‖S‖+1)) (div_pos hc (by positivity))
  refine ⟨x,?_⟩
  have hp : 0 < ‖x‖ := by
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (norm_nonneg x)
    rw [hz,mul_zero] at hx
    exact (not_lt_of_ge (norm_nonneg _)) hx
  have hn := S.le_opNorm (T x)
  change ‖S (T x)‖ < _
  have hs : ‖S‖/(‖S‖+1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  calc
    _ ≤ ‖S‖*‖T x‖ := hn
    _ ≤ ‖S‖*((c/(‖S‖+1))*‖x‖) := mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
    _ = (‖S‖/(‖S‖+1))*(c*‖x‖) := by ring
    _ < 1*(c*‖x‖) := mul_lt_mul_of_pos_right hs (mul_pos hc hp)
    _ = _ := one_mul _

lemma StrictlySingular.comp_right [CompleteSpace X] [CompleteSpace Y]
    (T : Y →L[𝕜] Z) (hT : StrictlySingular T) (R : X →L[𝕜] Y) :
    StrictlySingular (T.comp R) := by
  by_contra hTR
  obtain ⟨M,hM,hI,c,hc,h⟩ := (not_strictlySingular_iff _).mp hTR
  let : CompleteSpace M := hM.completeSpace_coe
  let A := R.comp M.subtypeL
  have ha : ∀ x : M, (c/(‖T‖+1))*‖x‖ ≤ ‖A x‖ := by
    intro x
    have ht := T.le_opNorm (R x)
    have hh := h x
    change c*‖x‖ ≤ ‖T (R x)‖ at hh
    change (c/(‖T‖+1))*‖x‖ ≤ ‖R x‖
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < ‖T‖+1)]
    nlinarith [norm_nonneg (R x)]
  have hap : 0 < c/(‖T‖+1) := div_pos hc (by positivity)
  let e := A.equivRange (lowerBound_antilipschitz A _ hap ha).injective
    (lowerBound_isClosed_range A _ hap ha)
  have hAi : ¬ FiniteDimensional 𝕜 A.range := by
    intro hF
    let : FiniteDimensional 𝕜 A.range := hF
    exact hI (FiniteDimensional.of_injective e.toLinearMap e.injective)
  obtain ⟨y,hy⟩ := hT A.range (lowerBound_isClosed_range A _ hap ha) hAi
    (c/(‖R‖+1)) (div_pos hc (by positivity))
  obtain ⟨x,hx⟩ := y.property
  have hr := R.le_opNorm (x : X)
  have hh := h x
  have hxy : (y : Y) = R x := hx.symm
  change ‖T (y : Y)‖ < (c/(‖R‖+1))*‖(y : Y)‖ at hy
  rw [hxy] at hy
  change c*‖x‖ ≤ ‖T (R x)‖ at hh
  have hd : (c/(‖R‖+1))*‖R x‖ ≤ c*‖x‖ := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < ‖R‖+1)]
    change ‖R (x : X)‖ ≤ ‖R‖*‖x‖ at hr
    nlinarith [norm_nonneg x]
  exact (not_lt_of_ge hh) (hy.trans_le hd)

end SeparableQuotient.Singular

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical Topology

/-- The least non-strictly-singular initial projection terminates at an actual
limit cut: every coordinate below it has a strictly larger coordinate below it. -/
lemma exists_minimal_cut (F : Submodule ℝ E) (_hF : IsClosed (F : Set E))
    (hI : ¬ FiniteDimensional ℝ F) :
    ∃ γ : Cut, (¬ StrictlySingular ((initialP γ).comp F.subtypeL)) ∧
      (∀ β < γ, StrictlySingular ((initialP β).comp F.subtypeL)) ∧
      (∀ a : Γ, (a : Cut) < γ → ∃ b : Γ, a < b ∧ (b : Cut) < γ) := by
  have htop : ¬ StrictlySingular ((initialP ⊤).comp F.subtypeL) := by
    rw [not_strictlySingular_iff]
    refine ⟨⊤,isClosed_univ,?_,1,by norm_num,?_⟩
    · exact Singular.top_infinite hI
    · intro x
      simp only [ContinuousLinearMap.comp_apply,Submodule.coe_subtypeL,initialP_top,one_mul]
      exact le_rfl
  obtain ⟨γ,hγ,hmin⟩ := wellFounded_lt.has_min
    {γ : Cut | ¬ StrictlySingular ((initialP γ).comp F.subtypeL)} ⟨⊤,htop⟩
  have hsmall (β : Cut) (hβ : β < γ) : StrictlySingular ((initialP β).comp F.subtypeL) := by
    by_contra hh
    exact hmin β hh hβ
  refine ⟨γ,hγ,hsmall,?_⟩
  intro a ha
  by_contra hh
  have hup (b : Γ) (hb : (b : Cut) < γ) : b ≤ a := by
    by_contra hn
    exact hh ⟨b,lt_of_not_ge hn,hb⟩
  obtain ⟨M,hMc,hMi,c,hc,hcM⟩ := (not_strictlySingular_iff _).mp hγ
  let d : F →L[ℝ] ℝ := (coordinate a).comp F.subtypeL
  obtain ⟨N,hNM,hNc,hNi,hd⟩ := finite_annihilator M hMc hMi {d}
  obtain ⟨x,hx⟩ := hsmall (a : Cut) ha N hNc hNi c hc
  have hax : coordinate a ((x : F) : E) = 0 := hd x x.property d (Finset.mem_singleton_self _)
  have heq : initialP (a : Cut) ((x : F) : E) = initialP γ ((x : F) : E) := by
    apply norming.coordinate_ext
    intro b
    by_cases hb : (b : Cut) < γ
    · have hba := hup b hb
      rcases hba.eq_or_lt with rfl | hba
      · simp only [coordinate_initialP,lt_self_iff_false,ite_false,hax,hb,ite_true]
      · simp only [coordinate_initialP,hb,WithTop.coe_lt_coe.mpr hba,ite_true]
    · have hn : ¬ b < a := fun hba => hb (lt_trans (WithTop.coe_lt_coe.mpr hba) ha)
      simp only [coordinate_initialP,hb,WithTop.coe_lt_coe,hn,ite_false]
  have hy := hcM (⟨x,hNM x.property⟩ : M)
  change c*‖(x : F)‖ ≤ ‖initialP γ ((x : F) : E)‖ at hy
  change ‖initialP (a : Cut) ((x : F) : E)‖ < c*‖(x : F)‖ at hx
  rw [heq] at hx
  exact (not_lt_of_ge hy) hx

/-- Range reduction before the optional single-color reduction. -/
lemma exists_initial_reduction (F : Submodule ℝ E) (hF : IsClosed (F : Set E))
    (hI : ¬ FiniteDimensional ℝ F) :
    ∃ (γ : Cut) (H : Submodule ℝ E), IsClosed (H : Set E) ∧
      ¬ FiniteDimensional ℝ H ∧
      (∀ a : Γ, (a : Cut) < γ → ∃ b : Γ, a < b ∧ (b : Cut) < γ) ∧
      (∀ β < γ, StrictlySingular ((initialP β).comp H.subtypeL)) ∧
      ∃ U : H →L[ℝ] F, ∀ x : H, initialP γ (U x) = x := by
  let : CompleteSpace F := hF.completeSpace_coe
  obtain ⟨γ,hγ,hsmall,hlim⟩ := exists_minimal_cut F hF hI
  obtain ⟨H,hH,hHi,U,hU⟩ := exists_lift_of_not_strictlySingular
    ((initialP γ).comp F.subtypeL) hγ
  let : CompleteSpace H := hH.completeSpace_coe
  refine ⟨γ,H,hH,hHi,hlim,?_,U,hU⟩
  intro β hβ
  have hh := (hsmall β hβ).comp_right _ U
  have he : ((initialP β).comp F.subtypeL).comp U = (initialP β).comp H.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    have hu : initialP γ ((U x : F) : E) = x := hU x
    change initialP β ((U x : F) : E) = initialP β (x : E)
    rw [← hu,initialP_initialP hβ.le]
  rwa [he] at hh

/-- Ordinal and color projections reduce a closed infinite-dimensional subspace to a branch subspace. -/
theorem exists_branchReduction (F : Submodule ℝ E) (hF : IsClosed (F : Set E))
    (hI : ¬ FiniteDimensional ℝ F) : Nonempty (BranchReduction F) := by
  obtain ⟨γ,H,hH,hHi,hlim,hsmall,U,hU⟩ := exists_initial_reduction F hF hI
  let : CompleteSpace H := hH.completeSpace_coe
  by_cases hm : ∀ k, StrictlySingular ((colorP k).comp H.subtypeL)
  · exact ⟨⟨γ,.mixed,H,hH,hHi,hlim,hsmall,fun _ => hm,U,hU⟩⟩
  · push Not at hm
    obtain ⟨k,hk⟩ := hm
    obtain ⟨H',hH',hH'i,V,hV⟩ := exists_lift_of_not_strictlySingular
      ((colorP k).comp H.subtypeL) hk
    let : CompleteSpace H' := hH'.completeSpace_coe
    refine ⟨⟨γ,.pure k,H',hH',hH'i,hlim,?_,by simp,U.comp V,?_⟩⟩
    · intro β hβ
      have hh := ((hsmall β hβ).comp_left _ (colorP k)).comp_right _ V
      have he : ((colorP k).comp ((initialP β).comp H.subtypeL)).comp V =
          (initialP β).comp H'.subtypeL := by
        apply ContinuousLinearMap.ext
        intro x
        change colorP k (initialP β ((V x : H) : E)) = initialP β (x : E)
        rw [← initialP_colorP,show colorP k ((V x : H) : E) = x from hV x]
      rwa [he] at hh
    · intro x
      change colorP k (initialP γ ((U (V x) : F) : E)) = x
      rw [hU]
      exact hV x

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BlockApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming Singular Set
open scoped Classical
variable {F : Submodule ℝ E} (R : BranchReduction F)
namespace BlockApprox

lemma error_sum (s : Finset ℕ) : ∑ n ∈ s, error n ≤ 1/32000 := by
  have h : (∑ n ∈ s, (1/2 : ℝ)^n) ≤ 2 := by
    simpa only [tsum_geometric_two] using summable_geometric_two.sum_le_tsum s (fun n _ => by positivity)
  simp only [error,← Finset.mul_sum]
  linarith

lemma blocks_norm (n : ℕ) : (1/2:ℝ) ≤ ‖(blocks R).embed n‖ := by
  have he := (node R n).approx
  have hu := (node R n).unit
  have h := norm_sub_norm_le ((node R n).x : E) ((blocks R).embed n)
  change ‖(node R n).x‖ - ‖(blocks R).embed n‖ ≤ _ at h
  rw [hu] at h
  have hε := error_le n
  change ‖((node R n).x : E)-((blocks R).embed n)‖ < error n at he
  linarith

lemma blocks_below (n : ℕ) (a : Γ) (ha : a ∈ ((blocks R).vector n).support) :
    (a : Cut) < R.cut := (support_after R ha).2.1

end BlockApprox
end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical
variable {f : Family} (z : BlockSequence f)

lemma BlockSequence.blockProjection_embed (n j : ℕ) :
    intervalProjection (ordinalHull (z.vector n).support (Finsupp.support_nonempty_iff.mpr (z.nonzero n)))
      (ordinalHull_connected _ _) (z.embed j) = if j = n then z.embed n else 0 := by
  by_cases hj : j = n
  · subst j
    rw [ite_eq_left rfl]
    exact intervalProjection_fixed _ _ _ (fun _ ha => mem_ordinalHull _ ha)
  · rw [ite_eq_right hj]
    apply intervalProjection_eq_zero
    intro a ha haI
    rcases lt_or_gt_of_ne hj with hj | hj
    · have hlt := (z.successive j n hj a ha _ ((z.vector n).support.min'_mem (Finsupp.support_nonempty_iff.mpr (z.nonzero n)))).1
      exact (not_lt_of_ge haI.1) hlt
    · have hlt := (z.successive n j hj _ ((z.vector n).support.max'_mem (Finsupp.support_nonempty_iff.mpr (z.nonzero n))) a ha).1
      exact (not_lt_of_ge haI.2) hlt

lemma BlockSequence.coefficient_bound (hz : ∀ n, (1/2 : ℝ) ≤ ‖z.embed n‖)
    (c : ℕ →₀ ℝ) (n : ℕ) : |c n| ≤ 4*‖c.sum (fun i a => a • z.embed i)‖ := by
  let P := intervalProjection
    (ordinalHull (z.vector n).support (Finsupp.support_nonempty_iff.mpr (z.nonzero n)))
      (ordinalHull_connected _ _)
  have he : P (c.sum (fun i a => a • z.embed i)) = c n • z.embed n := by
    rw [Finsupp.sum,map_sum]
    simp only [map_smul,P,BlockSequence.blockProjection_embed]
    by_cases hn : n ∈ c.support
    · rw [Finset.sum_eq_single_of_mem n hn]
      · simp
      · intro j _ hj
        simp [hj]
    · have hc : c n = 0 := Finsupp.notMem_support_iff.mp hn
      rw [hc,zero_smul]
      apply Finset.sum_eq_zero
      intro j hj
      have hjn : j ≠ n := fun hh => hn (hh ▸ hj)
      simp [hjn]
  have hp : ‖P (c.sum (fun i a => a • z.embed i))‖ ≤ ‖c.sum (fun i a => a • z.embed i)‖ :=
    norm_projection_le _ _
  rw [he,norm_smul,Real.norm_eq_abs] at hp
  have := mul_le_mul_of_nonneg_left (hz n) (abs_nonneg (c n))
  nlinarith [norm_nonneg (c.sum (fun i a => a • z.embed i))]

/-- The small-perturbation inequality for finite block combinations. -/
lemma BlockSequence.finite_perturbation (hz : ∀ n, (1/2 : ℝ) ≤ ‖z.embed n‖)
    (h : ℕ → E) (ε : ℕ → ℝ) (_hε : ∀ n, 0 ≤ ε n)
    (he : ∀ n, ‖h n-z.embed n‖ ≤ ε n) (B : ℝ)
    (hs : ∀ s : Finset ℕ, ∑ n ∈ s, ε n ≤ B) (c : ℕ →₀ ℝ) :
    ‖c.sum (fun i a => a • h i) - c.sum (fun i a => a • z.embed i)‖ ≤
      (4*B)*‖c.sum (fun i a => a • z.embed i)‖ := by
  let x := c.sum (fun i a => a • z.embed i)
  calc
    _ = ‖∑ i ∈ c.support, c i • (h i-z.embed i)‖ := by
      congr 1
      simp only [Finsupp.sum,smul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ c.support, |c i| *‖h i-z.embed i‖ := by
      simpa only [norm_smul,Real.norm_eq_abs] using
        norm_sum_le c.support (fun i => c i • (h i-z.embed i))
    _ ≤ ∑ i ∈ c.support, (4*‖x‖)*ε i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (z.coefficient_bound hz c i) (he i) (norm_nonneg _) (by positivity)
    _ = (4*‖x‖)*(∑ i ∈ c.support, ε i) := (Finset.mul_sum _ _ _).symm
    _ ≤ (4*‖x‖)*B := mul_le_mul_of_nonneg_left (hs c.support) (by positivity)
    _ = _ := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology
variable {F : Submodule ℝ E} (R : BranchReduction F)

lemma evaluateArray_familyP (γ : Cut) (f : Family) (x : E) (d : Array)
    (ho : ∀ a ∈ d.support, (a : Cut) < γ)
    (hc : ∀ k, f = .pure k → ∀ a ∈ d.support, Colors.color a = k) :
    norming.evaluateArray (familyP γ f x) d = norming.evaluateArray x d := by
  simp only [norming.evaluateArray_eq]
  apply Finset.sum_congr rfl
  intro a ha
  cases hf : f with
  | mixed => simp only [familyP,coordinate_initialP,ho a ha,ite_true]
  | pure k =>
    simp only [familyP,ContinuousLinearMap.comp_apply,coordinate_colorP,coordinate_initialP,
      ho a ha,hc k hf a ha,ite_true]

namespace BlockApprox

lemma pair_below (i : ℕ) (a : Γ)
    (ha : a ∈ (TreeNode.node (blocks R) i).pair.piece.value.support) :
    (a : Cut) < R.cut := by
  let e := (TreeNode.node (blocks R) i).pair
  have hα : a ∈ (vectorCrop e.vector e.nonzero).ordinal := by
    have h := e.support a ha
    have hh (A : Crop) (f : Family) (hb : a ∈ A.set f) : a ∈ A.ordinal := by
      cases f with
      | pure k => exact hb
      | mixed => exact hb.1
    exact hh _ _ h
  have hb := (blocks R).support_mem_tail _ e.mem_tail
    ((e.vector.support.max'_mem (Finsupp.support_nonempty_iff.mpr e.nonzero)))
  obtain ⟨n,_,hn⟩ := hb
  exact (WithTop.coe_le_coe.mpr hα.2).trans_lt (blocks_below R n _ hn)

lemma pair_color (k : ℕ) (hk : R.family = .pure k) (i : ℕ) (a : Γ)
    (ha : a ∈ (TreeNode.node (blocks R) i).pair.piece.value.support) : Colors.color a = k := by
  have hm := (TreeNode.node (blocks R) i).pair.piece.mem_family
    (TreeNode.node (blocks R) i).pair.child_mem
  have hp : (TreeNode.node (blocks R) i).pair.piece.value ∈ Norming.Pure k := by
    simpa only [hk,Family.norming,Family.base,Norming.Pure] using hm
  by_contra hn
  exact Finsupp.mem_support_iff.mp ha (pure_vanish k _ hp a hn)

lemma pathPartial_familyP (b : ℕ → Bool) (n : ℕ) (x : E) :
    pathPartial (TreeNode.branchPath (blocks R) b) n (familyP R.cut R.family x) =
      pathPartial (TreeNode.branchPath (blocks R) b) n x := by
  simp only [pathPartial,← norming.evaluateArray_eq_functional]
  change norming.evaluateArray _ (∑ j : Fin (n+1), (TreeNode.node (blocks R) (BinaryNodes.branch b j)).pair.piece.value) =
    norming.evaluateArray _ (∑ j : Fin (n+1), (TreeNode.node (blocks R) (BinaryNodes.branch b j)).pair.piece.value)
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact evaluateArray_familyP R.cut R.family x _ (pair_below R _) (fun k hk => pair_color R k hk _)

lemma pathFunctional_familyP (b : ℕ → Bool) (x : E) :
    pathFunctional (TreeNode.branchPath (blocks R) b) (familyP R.cut R.family x) =
      pathFunctional (TreeNode.branchPath (blocks R) b) x :=
  tendsto_nhds_unique (pathPartial_tendsto _ _) ((pathPartial_tendsto _ x).congr
    (fun n => (pathPartial_familyP R b n x).symm))

lemma pair_coefficients (i : ℕ) : ∃ c : ℕ →₀ ℝ,
    c.sum (fun n a => a • (blocks R).embed n) =
      norming.includeFinite (TreeNode.node (blocks R) i).pair.vector := by
  have hm := (blocks R).tailSpan_mono (Nat.zero_le _) (TreeNode.node (blocks R) i).pair.mem_tail
  change _ ∈ Submodule.span ℝ (Set.range (fun n => (blocks R).vector (n+0))) at hm
  simp only [Nat.add_zero] at hm
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  refine ⟨c,?_⟩
  rw [← hc]
  simp only [Finsupp.sum,map_sum,map_smul,BlockSequence.embed]

lemma pair_approximation (i : ℕ) : ∃ h : R.H,
    ‖h‖ ≤ 501 ∧
      ‖(h : E)-norming.includeFinite (TreeNode.node (blocks R) i).pair.vector‖ ≤ 1/16 := by
  obtain ⟨c,hc⟩ := pair_coefficients R i
  let h : R.H := c.sum (fun n a => a • (node R n).x)
  have he : ‖(h : E)-norming.includeFinite (TreeNode.node (blocks R) i).pair.vector‖ ≤ 1/16 := by
    have hp := (blocks R).finite_perturbation (blocks_norm R)
      (fun n => ((node R n).x : E)) error (fun n => (error_pos n).le)
      (fun n => (node R n).approx.le) (1/32000) error_sum c
    have hh : (h : E) = c.sum (fun n a => a • ((node R n).x : E)) := by
      simp only [h,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul_of_tower]
    rw [← hh,hc] at hp
    have hn := (TreeNode.node (blocks R) i).pair.norm_le
    linarith
  refine ⟨h,?_,he⟩
  have ht := norm_le_norm_sub_add ((h : E)) (norming.includeFinite (TreeNode.node (blocks R) i).pair.vector)
  have hn := (TreeNode.node (blocks R) i).pair.norm_le
  change ‖(h : E)‖ ≤ 501
  linarith

lemma separated_on_reduction {b c : ℕ → Bool} (hbc : b ≠ c) :
    ∃ h : R.H, ‖h‖ ≤ 501 ∧ 1/4 ≤
      pathFunctional (TreeNode.branchPath (blocks R) b) (h : E) -
      pathFunctional (TreeNode.branchPath (blocks R) c) (h : E) := by
  obtain ⟨n,hn⟩ := BinaryNodes.exists_separating_node hbc
  let i := BinaryNodes.branch b n
  let y := norming.includeFinite (TreeNode.node (blocks R) i).pair.vector
  obtain ⟨h,hh,he⟩ := pair_approximation R i
  let P := pathFunctional (TreeNode.branchPath (blocks R) b)
  let Q := pathFunctional (TreeNode.branchPath (blocks R) c)
  have hy : 1/2 ≤ P y - Q y := by
    rw [show Q y = 0 from TreeNode.pathFunctional_other (blocks R) c _ (fun j => (hn j).symm),sub_zero]
    exact TreeNode.pathFunctional_node (blocks R) b n
  have hb : ‖P ((h : E)-y)‖ ≤ 1/16 := by
    exact (P.le_opNorm _).trans ((mul_le_mul (norm_pathFunctional_le _) he (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hc : ‖Q ((h : E)-y)‖ ≤ 1/16 := by
    exact (Q.le_opNorm _).trans ((mul_le_mul (norm_pathFunctional_le _) he (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  rw [map_sub,Real.norm_eq_abs] at hb hc
  refine ⟨h,hh,?_⟩
  change 1/4 ≤ P (h : E)-Q (h : E)
  have hb' := (abs_le.mp hb).1
  have hc' := (abs_le.mp hc).2
  linarith

/-- Uniformly separated path restrictions on an arbitrary closed infinite-dimensional subspace. -/
theorem restricted_separated {b c : ℕ → Bool} (hbc : b ≠ c) :
    (1/(2004*(‖R.U‖+1)) : ℝ) ≤
      ‖(pathFunctional (TreeNode.branchPath (blocks R) b)).comp F.subtypeL -
        (pathFunctional (TreeNode.branchPath (blocks R) c)).comp F.subtypeL‖ := by
  obtain ⟨h,hh,he⟩ := separated_on_reduction R hbc
  let T := (pathFunctional (TreeNode.branchPath (blocks R) b)).comp F.subtypeL -
    (pathFunctional (TreeNode.branchPath (blocks R) c)).comp F.subtypeL
  have hb (b : ℕ → Bool) : pathFunctional (TreeNode.branchPath (blocks R) b) (h : E) =
      pathFunctional (TreeNode.branchPath (blocks R) b) (R.U h : E) := by
    rw [← R.lift h,pathFunctional_familyP]
  rw [hb b,hb c] at he
  have hn : ‖R.U h‖ ≤ ‖R.U‖*501 := (R.U.le_opNorm h).trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
  have hop := (T.le_opNorm (R.U h)).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg T))
  have he' : 1/4 ≤ T (R.U h) := he
  rw [Real.norm_eq_abs] at hop
  have hp := le_abs_self (T (R.U h))
  have hd : 0 < 2004*(‖R.U‖+1) := by positivity
  apply (div_le_iff₀ hd).mpr
  change 1 ≤ ‖T‖*(2004*(‖R.U‖+1))
  nlinarith [norm_nonneg T]

end BlockApprox
end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.SeparableSubspaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set Metric TopologicalSpace Module
open scoped Classical Topology

lemma exists_separable_closed_ID {𝕜 Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (hY : ¬ FiniteDimensional 𝕜 Y) :
    ∃ F : Submodule 𝕜 Y, IsClosed (F : Set Y) ∧ ¬ FiniteDimensional 𝕜 F ∧
      IsSeparable (F : Set Y) := by
  let b := Basis.ofVectorSpace 𝕜 Y
  have hi : Infinite (Basis.ofVectorSpaceIndex 𝕜 Y) := by
    by_contra h
    let : Finite (Basis.ofVectorSpaceIndex 𝕜 Y) := not_infinite_iff_finite.mp h
    exact hY (Module.Finite.of_basis b)
  let := hi
  let f : ℕ → Y := b ∘ (Infinite.natEmbedding (Basis.ofVectorSpaceIndex 𝕜 Y))
  have hf : LinearIndependent 𝕜 f := b.linearIndependent.comp _ (Infinite.natEmbedding _).injective
  let F := (Submodule.span 𝕜 (range f)).topologicalClosure
  have hm (n : ℕ) : f n ∈ F := Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self n))
  have hfi : LinearIndependent 𝕜 (fun n => (⟨f n,hm n⟩ : F)) := by
    exact LinearIndependent.of_comp F.subtype hf
  refine ⟨F, Submodule.isClosed_topologicalClosure _, ?_, (countable_range f).isSeparable.span.closure⟩
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite _ hfi

lemma countable_of_separated_range {ι Y : Type*} [MetricSpace Y]
    (f : ι → Y) (hsep : IsSeparable (range f)) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → r ≤ dist (f i) (f j)) : Countable ι := by
  obtain ⟨t,ht,hcl⟩ := hsep
  have he (i : ι) : ∃ y : t, dist (f i) y < r/3 := by
    obtain ⟨y,hy,hyi⟩ := Metric.mem_closure_iff.mp (hcl (mem_range_self i)) (r/3) (by positivity)
    exact ⟨⟨y,hy⟩,hyi⟩
  choose g hg using he
  have hgI : Function.Injective g := by
    intro i j hij
    by_contra hn
    have h := hd i j hn
    have ht := dist_triangle (f i) (g i) (f j)
    have hi := hg i
    have hj := hg j
    rw [← hij,dist_comm (f j)] at hj
    linarith
  let := ht.to_subtype
  exact hgI.countable

end SeparableQuotient

namespace SeparableQuotient
lemma boolSeq_uncountable : ¬ Countable (ℕ → Bool) := by
  intro h
  have hm := Cardinal.mk_le_aleph0_iff.mpr h
  have he : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
    simp only [Cardinal.mk_arrow,Cardinal.mk_bool,Cardinal.mk_nat,Cardinal.lift_ofNat,
      Cardinal.lift_aleph0,Cardinal.two_power_aleph0]
  rw [he] at hm
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hm
end SeparableQuotient

namespace SeparableQuotient
open Set TopologicalSpace
lemma quotient_closure_lift {𝕜 D : Type*} [RCLike 𝕜]
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    (Y X : Submodule 𝕜 D) [IsClosed (Y : Set D)] (z : D)
    (hz : Y.mkQL z ∈ (X.map Y.mkQ).topologicalClosure) :
    z ∈ (X ⊔ Y).topologicalClosure := by
  have he := Y.isOpenMap_mkQ.preimage_closure_eq_closure_preimage Y.mkQL.continuous
    (X.map Y.mkQ : Set (D ⧸ Y))
  have hp : Y.mkQ ⁻¹' (X.map Y.mkQ : Set (D ⧸ Y)) = (X ⊔ Y : Submodule 𝕜 D) := by
    change (Submodule.comap Y.mkQ (X.map Y.mkQ) : Set D) = _
    rw [Submodule.comap_map_eq,Submodule.ker_mkQ]
  rw [hp] at he
  change z ∈ closure ((X ⊔ Y : Submodule 𝕜 D) : Set D)
  rw [← he]
  exact hz
end SeparableQuotient

namespace SeparableQuotient
open Set TopologicalSpace
open scoped Classical
universe u v
variable {X : Type u} {E : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Transfer the necessary evaluation criterion through the actual predual
isomorphism, retaining a separable closed infinite-dimensional subspace. -/
lemma separable_restriction_of_quotient
    (R : E ≃L[ℝ] StrongDual ℝ X) (J : X →L[ℝ] StrongDual ℝ E)
    (hR : ∀ e x, R e x = J x e) (hSQ : HasSeparableQuotient ℝ X) :
    ∃ F : Submodule ℝ E, IsClosed (F : Set E) ∧ ¬ FiniteDimensional ℝ F ∧
      IsSeparable (F : Set E) ∧
      IsSeparable (range (fun x : X => (J x).comp F.subtypeL)) := by
  obtain ⟨H,hH,hHi,hHe⟩ := separable_evaluation_of_hasSeparableQuotient hSQ
  let hNg : NormedAddCommGroup H := inferInstance
  let hNs : NormedSpace ℝ H := inferInstance
  let : CompleteSpace H := hH.completeSpace_coe
  obtain ⟨G,hG,hGi,hGs⟩ := exists_separable_closed_ID (𝕜 := ℝ) (Y := H) hHi
  let gNg : NormedAddCommGroup G := inferInstance
  let gNs : NormedSpace ℝ G := inferInstance
  let : CompleteSpace G := hG.completeSpace_coe
  let : SeparableSpace G := hGs.separableSpace
  let T : G →L[ℝ] E := R.symm.toContinuousLinearMap.comp (H.subtypeL.comp G.subtypeL)
  have hi : Isometry (H.subtypeL.comp G.subtypeL) := fun _ _ => rfl
  have hT : ∃ K, AntilipschitzWith K T := by
    refine ⟨_,R.symm.antilipschitz.comp hi.antilipschitz⟩
  obtain ⟨K,hK⟩ := hT
  let F := T.range
  let fNg : NormedAddCommGroup F := inferInstance
  let fNs : NormedSpace ℝ F := inferInstance
  have hFc : IsClosed (F : Set E) := hK.isClosed_range T.uniformContinuous
  let e : G ≃L[ℝ] F := T.equivRange hK.injective hFc
  have hFi : ¬ FiniteDimensional ℝ F := by
    intro hh
    let := hh
    exact hGi (FiniteDimensional.of_injective e.toLinearMap e.injective)
  have hFs : IsSeparable (F : Set E) := isSeparable_range T.continuous
  let U : F →L[ℝ] H := G.subtypeL.comp e.symm.toContinuousLinearMap
  let A : StrongDual ℝ H →L[ℝ] StrongDual ℝ F := ContinuousLinearMap.precomp ℝ U
  have he (x : X) : (J x).comp F.subtypeL = A (subspaceEvaluation H x) := by
    ext z
    obtain ⟨g,rfl⟩ := e.surjective z
    change J x (T g) = ((U (e g) : H) : StrongDual ℝ X) x
    have hu : U (e g) = (g : H) := by
      change G.subtypeL (e.symm (e g)) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hu]
    change J x (R.symm ((g : H) : StrongDual ℝ X)) = ((g : H) : StrongDual ℝ X) x
    rw [← hR,R.apply_symm_apply]
  refine ⟨F,hFc,hFi,hFs,(hHe.image A.continuous).mono ?_⟩
  rintro _ ⟨x,rfl⟩
  exact ⟨subspaceEvaluation H x,mem_range_self x,(he x).symm⟩

end SeparableQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ChangedPredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.crDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.crDualSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.crSubGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.crSubSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.crSubDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.crSubDualSpace
lemma coordinate_restriction_countable (F : Submodule ℝ E) [SeparableSpace F] :
    Set.Countable {a | restrict F (coordinate a) ≠ 0} := by
  let s : Set Γ := ⋃ n : ℕ, {a | coordinate a (denseSeq F n : E) ≠ 0}
  have hs : s.Countable := countable_iUnion (fun n => support_countable (denseSeq F n : E))
  apply hs.mono
  intro a ha
  by_contra hn
  apply ha
  have hz : ∀ n, coordinate a (denseSeq F n : E) = 0 := by
    intro n
    by_contra h
    exact hn (mem_iUnion.mpr ⟨n,h⟩)
  apply DFunLike.coe_injective
  exact (denseRange_denseSeq F).equalizer (restrict F (coordinate a)).continuous continuous_const
    (funext hz)

/-- Restrictions of the coordinate predual to a separable subspace form a norm-separable set. -/
lemma predual_restriction_separable (F : Submodule ℝ E) [SeparableSpace F] :
    IsSeparable (restrict F '' (X₀ : Set (StrongDual ℝ E))) := by
  let s := {a | restrict F (coordinate a) ≠ 0}
  let Z := (Submodule.span ℝ ((fun a => restrict F (coordinate a)) '' s)).topologicalClosure
  have hZ : IsSeparable (Z : Set (StrongDual ℝ F)) :=
    ((coordinate_restriction_countable F).image _).isSeparable.span.closure
  apply hZ.mono
  rintro _ ⟨y,hy,rfl⟩
  have hc : IsClosed ((Z.comap (restrict F).toLinearMap) : Set (StrongDual ℝ E)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (restrict F).continuous
  have hin : Submodule.span ℝ (range coordinate) ≤ Z.comap (restrict F).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change restrict F (coordinate a) ∈ Z
    by_cases h : restrict F (coordinate a) = 0
    · rw [h]; exact Z.zero_mem
    · exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a,h,rfl⟩)
  exact (Submodule.topologicalClosure_minimal _ hin hc) hy

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.atDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atDualSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXClosed
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atWGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atWSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0Group
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0Space
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0DualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0DualSpace
variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXDualSpace
lemma X_infinite : ¬ FiniteDimensional ℝ (X hCH) := by
  intro hh
  let := hh
  have : FiniteDimensional ℝ (StrongDual ℝ (X hCH)) := inferInstance
  exact infiniteDimensional (FiniteDimensional.of_injective (twistedIso hCH).toLinearMap (twistedIso hCH).injective)

lemma quotient_eq_B_on_X (x : X hCH) : X₀.mkQL x = B hCH x := by
  have h := x.property
  change X₀.mkQL x - B hCH x = 0 at h
  exact sub_eq_zero.mp h

lemma X_quotient_image : (X hCH).map X₀.mkQ = (X hCH).map (B hCH).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,hx,(quotient_eq_B_on_X hCH ⟨x,hx⟩).symm⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,hx,quotient_eq_B_on_X hCH ⟨x,hx⟩⟩

lemma path_mem_twisted_sum {f : Family} (P : InfinitePath f) :
    pathFunctional P ∈ ((X hCH) ⊔ X₀).topologicalClosure := by
  apply quotient_closure_lift X₀ (X hCH)
  rw [X_quotient_image, (twist_data hCH).2]
  let p : PathIndex f := ⟨P.raw,⟨P,rfl⟩⟩
  have he : pathFunctional p.repr = pathFunctional P := pathFunctional_eq_of_raw p.repr_raw
  have hm := pathCoset_mem_B_predual hCH f p
  apply Submodule.le_topologicalClosure _
  simpa only [pathCoset,he] using hm

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.chDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.chDualSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.chSubGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.chSubSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.chSubDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.chSubDualSpace
variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

/-- The branch obstruction for the changed predual, using the open quotient map. -/
lemma X_restriction_nonseparable (F : Submodule ℝ E) (hF : IsClosed (F : Set E))
    (hFi : ¬ FiniteDimensional ℝ F) [SeparableSpace F] :
    ¬ IsSeparable (restrict F '' (X hCH : Set (StrongDual ℝ E))) := by
  intro hsep
  let s := restrict F '' (X hCH : Set (StrongDual ℝ E)) ∪
    restrict F '' (X₀ : Set (StrongDual ℝ E))
  let Z := (Submodule.span ℝ s).topologicalClosure
  have hZ : IsSeparable (Z : Set (StrongDual ℝ F)) :=
    (hsep.union (predual_restriction_separable F)).span.closure
  have hin : X hCH ⊔ X₀ ≤ Z.comap (restrict F).toLinearMap := by
    apply sup_le
    · intro y hy
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inl ⟨y,hy,rfl⟩))
    · intro y hy
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Or.inr ⟨y,hy,rfl⟩))
  have hc : IsClosed ((Z.comap (restrict F).toLinearMap) : Set (StrongDual ℝ E)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (restrict F).continuous
  have hp {f : Family} (P : InfinitePath f) : restrict F (pathFunctional P) ∈ Z :=
    (Submodule.topologicalClosure_minimal _ hin hc) (path_mem_twisted_sum hCH P)
  let R : BranchReduction F := Classical.choice (exists_branchReduction F hF hFi)
  let ψ : (ℕ → Bool) → StrongDual ℝ F := fun b =>
    restrict F (pathFunctional (TreeNode.branchPath (BlockApprox.blocks R) b))
  have hsψ : IsSeparable (range ψ) := hZ.mono (by
    rintro _ ⟨b,rfl⟩
    exact hp _)
  apply boolSeq_uncountable
  apply countable_of_separated_range ψ hsψ (1/(2004*(‖R.U‖+1))) (by positivity)
  intro b c hbc
  rw [dist_eq_norm]
  exact BlockApprox.restricted_separated R hbc

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NegativeReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set TopologicalSpace
open scoped Classical
universe u

/-- CH refutes the real separable quotient assertion in every universe. -/
theorem negative_real_oai (hCH : CH) : ¬ SQ.{u} ℝ := by
  intro hSQ
  let X := ActualSpace.X hCH
  let : NormedAddCommGroup X := inferInstance
  let : NormedSpace ℝ X := inferInstance
  let : CompleteSpace X := ActualSpace.X_complete hCH
  let XU := ULift.{u} X
  let : NormedAddCommGroup XU := inferInstance
  let : NormedSpace ℝ XU := inferInstance
  let : CompleteSpace XU := inferInstance
  let d : XU ≃L[ℝ] X := ContinuousLinearEquiv.ulift
  have hI : ¬ FiniteDimensional ℝ XU := by
    intro hh
    let := hh
    exact ActualSpace.X_infinite hCH
      (FiniteDimensional.of_injective d.symm.toLinearMap d.symm.injective)
  have hsq := hSQ XU hI
  let R : ActualSpace.E ≃L[ℝ] StrongDual ℝ XU :=
    (ActualSpace.twistedIso hCH).trans (d.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  let J : XU →L[ℝ] StrongDual ℝ ActualSpace.E :=
    (ActualSpace.X hCH).subtypeL.comp d.toContinuousLinearMap
  have hR (e : ActualSpace.E) (x : XU) : R e x = J x e := by
    exact ActualSpace.twistedIso_apply hCH e (d x)
  obtain ⟨F,hF,hFi,hFs,hsep⟩ := separable_restriction_of_quotient R J hR hsq
  let := hFs.separableSpace
  apply ActualSpace.X_restriction_nonseparable hCH F hF hFi
  apply hsep.mono
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨d.symm ⟨x,hx⟩,?_⟩
  change (J (d.symm ⟨x,hx⟩)).comp F.subtypeL = (ActualSpace.restrict F) x
  simp only [J,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,d.apply_symm_apply]
  rfl

end SeparableQuotient

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SeparableQuotient.negative_real_oai.{u} := @OAI.SeparableQuotient.negative_real_oai.{u}
