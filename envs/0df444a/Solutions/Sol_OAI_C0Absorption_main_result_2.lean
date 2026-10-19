-- Prove2me | solution 2 for OAI.C0Absorption.main_result
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:56:06.766695+00:00
-- url     : https://prove2.me/submissions/f1e7442b-4bde-4955-9c1a-e51fe1dc6cb2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Main.lean:L33-L37
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.C0Absorption.main_result.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_C0Absorption_main_result) verbatim and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift
import Definitions.Def_OAI_Analysis_C0Absorption_Onto
import Definitions.Def_OAI_Analysis_C0Absorption_Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Aharoni
import Theorems.Thm_OAI_C0Absorption_absorption_inverse_bound
import Theorems.Thm_OAI_C0Absorption_absorption_upper
import Theorems.Thm_OAI_C0Absorption_finiteEmbed_block_outside
import Theorems.Thm_OAI_C0Absorption_finiteRecomputed_global_bounds
import Theorems.Thm_OAI_C0Absorption_finiteRecomputed_local_onto
import Theorems.Thm_OAI_C0Absorption_radialLift_lipschitz
import Theorems.Thm_OAI_C0Absorption_recomputed_global_bounds
import Theorems.Thm_OAI_C0Absorption_source_noLinearC0
import Theorems.Thm_OAI_C0Absorption_surjective_of_punctured_local_onto

-- ---- from OAI.Analysis.C0Absorption.Completion ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedSeminorms

open UniformSpace Completion

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

end CompletedSeminorms

section SelectedCompletion

open UniformSpace Completion

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem zeta_lipschitz : LipschitzWith 1 (zeta L o) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist ((prePoint L o s : PreSpace L o) : Completion (PreSpace L o))
    ((prePoint L o t : PreSpace L o) : Completion (PreSpace L o)) ≤ (1 : ℝ) * dist s t
  rw [Completion.dist_eq]
  exact (prePoint_lipschitz L o).dist_le_mul s t

end SelectedCompletion

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Triangular ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

open Set Filter Topology
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem absorption_onto {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    (hg : Function.Surjective g)
    (hQK : ∀ x : E × U, Q (K x) = g x - x.2) :
    Function.Surjective (absorptionMap Q K) := by
  intro z
  obtain ⟨⟨t,u⟩, htu⟩ := hg (Q z)
  refine ⟨(z-K (t,u),t), ?_⟩
  have hQ : Q (z-K (t,u)) = u := by rw [map_sub, hQK, htu]; abel
  simp only [absorptionMap, hQ]
  abel

end
end C0Absorption

open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Frozen ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem correction_zero (γ : Label) : correction γ ⟨0,by simp⟩=0 := by
  exact map_zero (frozenCorrection (stateWeights _) γ)

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Tags ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem concrete_noLinearC0 : NoLinearC0 ConcreteSpace :=
  source_noLinearC0 concreteTagLocalization concreteRadiusLocalization

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Shift ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem recomputed_lipschitz : LipschitzWith (628/125) recomputedShift := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (recomputed_global_bounds x y).2
  norm_num [eta] at hh ⊢
  exact hh

theorem recomputed_antilipschitz : AntilipschitzWith (125/22) recomputedShift := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (recomputed_global_bounds x y).1
  norm_num [eta] at h ⊢
  nlinarith

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Space ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem correctionQ_coe (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    correctionQ (toTestSpace (sourceClasses concreteBases) c0Origin m)=moleculeCorrection m :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) m

theorem correctionC0_zero : correctionC0 c0Origin=0 := by
  ext γ
  exact correction_zero γ

theorem correctionQ_zeta (s : C0Ball) :
    correctionQ (zeta (sourceClasses concreteBases) c0Origin s)=correctionC0 s := by
  rw [zeta,correctionQ_coe]
  change moleculeCorrection (molecule s c0Origin)=correctionC0 s
  simp only [moleculeCorrection,molecule,LinearMap.comp_apply,Submodule.subtype_apply,map_sub,
    Finsupp.linearCombination_single,one_smul,correctionC0_zero,sub_zero]

theorem concreteLift_lipschitz : LipschitzWith 3 concreteLift :=
  radialLift_lipschitz _ (zeta_lipschitz _ _) (zeta_base _ _)

theorem correctionQ_concreteLift (x : C0) : correctionQ (concreteLift x)=recomputedShift x-inputBlocks x := by
  rw [concreteLift,radialLift,map_smul,correctionQ_zeta]
  change ‖x‖ • (frozenCorrectionL (stateWeights (normalizedBall x)) (normalize x))=_
  rw [← map_smul,norm_smul_normalize]
  change frozenCorrectionL (stateWeights (normalizedBall x)) x=
    (inputBlocks x+frozenCorrectionL (stateWeights (normalizedBall x)) x)-inputBlocks x
  abel

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Finite ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

section Sparse
variable {A : Type*} [Fintype A]

end Sparse

theorem finiteEmbed_row_outside {N : ℕ} (x : FInput N) (i : ℕ) (hi : N < i) : finiteEmbed N x (rowIndex i)=0 := by
  apply sparseC0_outside
  rintro ⟨a,ha⟩
  cases a with
  | inl a => have he := rowIndex_injective ha; have := a.isLt; omega
  | inr γ => exact rowIndex_ne_labelIndex i (fLabel γ) ha.symm

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.FiniteShift ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

theorem finiteRecomputed_lipschitz (N : ℕ) : LipschitzWith (628/125) (finiteRecomputed N) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (finiteRecomputed_global_bounds x y).2
  norm_num [eta] at hh ⊢
  exact hh

theorem finiteRecomputed_antilipschitz (N : ℕ) : AntilipschitzWith (125/22) (finiteRecomputed N) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (finiteRecomputed_global_bounds x y).1
  norm_num [eta] at h ⊢
  nlinarith

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

section FiniteOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end FiniteOperators

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Onto ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem finiteRecomputed_surjective (N : ℕ) (hN : 0 < N) : Function.Surjective (finiteRecomputed N) := by
  apply surjective_of_punctured_local_onto (finiteRecomputed N)
    (finiteRecomputed_antilipschitz N) (finiteRecomputed_lipschitz N) (finiteRecomputed_zero N)
  · apply (isConnected_compl_singleton_of_one_lt_rank (E := FInput N) _ 0).isPreconnected
    change 1 < Module.rank ℝ (FCoord N → ℝ)
    rw [rank_fun']
    have hh : 1 < Fintype.card (FCoord N) := by
      change 1 < Fintype.card (Sum (Fin (N+1)) (FLabel N))
      rw [Fintype.card_sum,Fintype.card_fin]
      omega
    exact_mod_cast hh
  · exact fun x hx => finiteRecomputed_local_onto hx

variable {N : ℕ}

theorem finiteRecomputed_block (x : FInput N) (γ : FLabel N) :
    finiteRecomputed N x (.inr γ)=recomputedShift (finiteEmbed N x) (fLabel γ) :=
  finiteFrozen_block _ x γ

theorem finiteRecomputed_row (x : FInput N) (i : Fin (N+1)) :
    finiteRecomputed N x (.inl i)=
      rowScalar (stateWeights (normalizedBall (finiteEmbed N x))) (i.val,N) (finiteEmbed N x) :=
  finiteRow_eq _ (i,Fin.last N) x

theorem finiteEmbed_rowScalar_outside (W : FrozenWeights) (x : FInput N) (lev : Level)
    (hl : N < lev.1 ∨ N < lev.2) : rowScalar W lev (finiteEmbed N x)=0 := by
  classical
  rw [rowScalar_apply]
  apply Finset.sum_eq_zero
  intro b hb
  change W.row lev b*finiteEmbed N x (labelIndex (blockLabel lev b))=0
  rw [finiteEmbed_block_outside x (blockLabel lev b) hl,mul_zero]

theorem finite_solution_gives_infinite (y : BlockC0) (x : FInput N)
    (hy : ∀ γ : Label, N < γ.level.1 ∨ N < γ.level.2 → y γ=0)
    (hx : finiteRecomputed N x=finiteTarget N y) : recomputedShift (finiteEmbed N x)=y := by
  let W := stateWeights (normalizedBall (finiteEmbed N x))
  have hterminal (i : ℕ) (hi : i≤N) : rowScalar W (i,N) (finiteEmbed N x)=0 := by
    have hh := congrFun hx (.inl ⟨i,by omega⟩)
    rw [finiteRecomputed_row] at hh
    exact hh
  ext γ
  by_cases hγ : γ.level.1≤N ∧ γ.level.2≤N
  · let l : FLevel N := (⟨γ.level.1,by omega⟩,⟨γ.level.2,by omega⟩)
    let b : Block (l.1.val,l.2.val) := ⟨γ.band,γ.tag⟩
    let δ : FLabel N := ⟨l,b⟩
    have he : fLabel δ=γ := by cases γ; rfl
    have hh := congrFun hx (.inr δ)
    rw [finiteRecomputed_block] at hh
    change recomputedShift (finiteEmbed N x) (fLabel δ)=y (fLabel δ) at hh
    simpa only [he] using hh
  · have hout : N < γ.level.1 ∨ N < γ.level.2 := by omega
    rw [hy γ hout]
    change frozenShift W (finiteEmbed N x) γ=0
    rw [frozenShift_apply,finiteEmbed_block_outside x γ hout,frozenCorrection_apply,
      finiteEmbed_rowScalar_outside W x γ.level hout]
    have hp : previousScalar W γ.level (finiteEmbed N x)=0 := by
      rcases hl : γ.level with ⟨i,n⟩
      rw [hl] at hout
      change N < i ∨ N < n at hout
      cases n with
      | zero =>
        change finiteEmbed N x (rowIndex i)=0
        exact finiteEmbed_row_outside x i (by omega)
      | succ n =>
        change rowScalar W (i,n) (finiteEmbed N x)=0
        by_cases hi : N < i
        · exact finiteEmbed_rowScalar_outside W x _ (Or.inl hi)
        · by_cases hn : n=N
          · subst n
            exact hterminal i (by omega)
          · exact finiteEmbed_rowScalar_outside W x _ (Or.inr (by omega))
    rw [hp]
    ring

theorem finite_target_mem_range (N : ℕ) (hN : 0 < N) (y : BlockC0)
    (hy : ∀ γ : Label, N < γ.level.1 ∨ N < γ.level.2 → y γ=0) : y∈Set.range recomputedShift := by
  obtain ⟨x,hx⟩ := finiteRecomputed_surjective N hN (finiteTarget N y)
  exact ⟨finiteEmbed N x,finite_solution_gives_infinite y x hy hx⟩

theorem blockSquare_outside (N : ℕ) (y : BlockC0) (γ : Label)
    (hγ : N < γ.level.1 ∨ N < γ.level.2) : blockSquare N y γ=0 := by
  rw [blockSquare_apply,ite_eq_right (by omega)]

theorem blockSquare_tendsto (y : BlockC0) : Tendsto (fun N => blockSquare N y) atTop (nhds y) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmall : ∀ᶠ γ in cofinite, |y γ|<ε/2 := by
    have hh := Metric.tendsto_nhds.mp (cfun_tendsto y) (ε/2) (half_pos hε)
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hh
  have hfin : {γ : Label | ε/2≤|y γ|}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp hsmall
  let S := hfin.toFinset
  let M := S.sup (fun γ => max γ.level.1 γ.level.2)
  refine ⟨M,fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply cfun_norm_le _ (half_pos hε).le
  intro γ
  change |blockSquare n y γ-y γ|≤ε/2
  rw [blockSquare_apply]
  split_ifs with hγ
  · simpa only [sub_self,abs_zero] using (half_pos hε).le
  · simp only [zero_sub,abs_neg]
    apply le_of_lt
    by_contra hbad
    have hmem : γ∈S := hfin.mem_toFinset.mpr (le_of_not_gt hbad)
    have hb : max γ.level.1 γ.level.2≤M := Finset.le_sup (f := fun γ : Label => max γ.level.1 γ.level.2) hmem
    have h1 := (le_max_left γ.level.1 γ.level.2).trans (hb.trans hn)
    have h2 := (le_max_right γ.level.1 γ.level.2).trans (hb.trans hn)
    exact hγ ⟨h1,h2⟩

theorem recomputedShift_surjective : Function.Surjective recomputedShift := by
  have hclosed : IsClosed (Set.range recomputedShift) :=
    recomputed_antilipschitz.isClosed_range recomputed_lipschitz.uniformContinuous
  intro y
  apply hclosed.mem_of_tendsto (blockSquare_tendsto y)
  apply Filter.eventually_atTop.mpr
  refine ⟨1,fun N hN => finite_target_mem_range N (by omega) (blockSquare N y) ?_⟩
  exact blockSquare_outside N y

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Absorption ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem absorptionK_lipschitz : LipschitzWith 3 absorptionK := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := concreteLift_lipschitz.dist_le_mul (inputCoordinates x) (inputCoordinates y)
  rw [inputCoordinates.isometry.dist_eq] at h
  exact h

theorem absorptionG_surjective : Function.Surjective absorptionG :=
  recomputedShift_surjective.comp inputCoordinates.surjective

theorem absorptionG_lower (x y : C0 × BlockC0) :
    (22/125 : ℝ)*dist x y≤dist (absorptionG x) (absorptionG y) := by
  have h := (recomputed_global_bounds (inputCoordinates x) (inputCoordinates y)).1
  rw [inputCoordinates.isometry.dist_eq] at h
  norm_num [eta] at h
  exact h

theorem absorptionQK (x : C0 × BlockC0) : correctionQ (absorptionK x)=absorptionG x-x.2 := by
  rw [absorptionK,correctionQ_concreteLift]
  have he : inputBlocks (inputCoordinates x)=x.2 := by ext γ; exact joinInputs_block x γ
  rw [he]
  rfl

theorem concreteAbsorption_surjective : Function.Surjective concreteAbsorption :=
  absorption_onto correctionQ absorptionK absorptionG absorptionG_surjective absorptionQK

theorem concreteAbsorption_upper (x y : ConcreteSpace × C0) :
    dist (concreteAbsorption x) (concreteAbsorption y)≤(1+3*max 1 ‖correctionQ‖)*dist x y :=
  absorption_upper correctionQ absorptionK (by norm_num) absorptionK_lipschitz.dist_le_mul x y

theorem concreteAbsorption_inverse_bound (x y : ConcreteSpace × C0) :
    dist x y≤ max (1+3*‖correctionQ‖/(22/125)) (‖correctionQ‖/(22/125))*
      dist (concreteAbsorption x) (concreteAbsorption y) :=
  absorption_inverse_bound correctionQ absorptionK absorptionG (by norm_num) (by norm_num)
    absorptionK_lipschitz.dist_le_mul absorptionG_lower absorptionQK x y

theorem concreteAbsorption_bilip : BiLip concreteAbsorption := by
  let D := max (1+3*‖correctionQ‖/(22/125)) (‖correctionQ‖/(22/125))
  let U := 1+3*max 1 ‖correctionQ‖
  have hD : 0<D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨1/D,max U (1/D),one_div_pos.mpr hD,le_max_right _ _,fun x y => ⟨?_,?_⟩⟩
  · have h := concreteAbsorption_inverse_bound x y
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using h)
  · exact (concreteAbsorption_upper x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)

theorem concreteC0Embedding_bilip : BiLip concreteC0Embedding := by
  obtain ⟨c,C,hc,hcC,h⟩ := concreteAbsorption_bilip
  refine ⟨c,C,hc,hcC,fun x y => ?_⟩
  simpa only [concreteC0Embedding,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using h (0,x) (0,y)

theorem noLinearC0_not_product_equiv {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (hZ : NoLinearC0 Z) : ¬ Nonempty ((Z × C0) ≃L[ℝ] Z) := by
  rintro ⟨e⟩
  let T : C0 →L[ℝ] Z := e.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Z C0)
  let B : ℝ := max 1 ‖e.symm.toContinuousLinearMap‖
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply hZ T
  refine ⟨1/B,one_div_pos.mpr hB,fun x => ?_⟩
  have hh : ‖x‖≤B*‖T x‖ := by
    calc
      ‖x‖ = ‖((0,x) : Z × C0)‖ := by simp
      _ = ‖e.symm (T x)‖ := by simp [T]
      _ ≤ ‖e.symm.toContinuousLinearMap‖*‖T x‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B*‖T x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  rw [one_div,mul_comm,← div_eq_mul_inv]
  exact (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hh)

theorem concrete_not_linearly_isomorphic : ¬ Nonempty ((ConcreteSpace × C0) ≃L[ℝ] ConcreteSpace) :=
  noLinearC0_not_product_equiv concrete_noLinearC0

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Aharoni ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section Aharoni
variable {M : Type*} [MetricSpace M]

theorem le_earlierCut (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) {b : ℝ}
    (hb : b≤ r) (h : ∀ j< n,b≤ dist x (q j)-r/4) : b≤ earlierCut q r n x := by
  induction n with
  | zero => exact hb
  | succ n ih => exact le_min (ih (fun j hj => h j (by omega))) (h n (by omega))

theorem earlierCut_lipschitz (q : ℕ → M) (r : ℝ) (n : ℕ) : LipschitzWith 1 (earlierCut q r n) := by
  induction n with
  | zero => exact (LipschitzWith.const r).weaken (by norm_num)
  | succ n ih =>
    have hd : LipschitzWith 1 (fun x => dist x (q n)-r/4) := by
      simpa only [add_zero] using (LipschitzWith.dist_left (q n)).sub (LipschitzWith.const (r/4))
    simpa only [earlierCut,max_self] using ih.min hd

theorem metricBump_zero_of_far (q : ℕ → M) {r : ℝ} (n : ℕ) (x : M) (h : r≤ dist x (q n)) :
    metricBump q r n x=0 :=
  max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr h))

theorem metricBump_lipschitz (q : ℕ → M) (r : ℝ) (n : ℕ) : LipschitzWith 1 (metricBump q r n) := by
  have ha : LipschitzWith 1 (fun x => r-dist x (q n)) := by
    simpa only [zero_add] using (LipschitzWith.const r).sub (LipschitzWith.dist_left (q n))
  have hb : LipschitzWith 1 (fun x => dist x (q 0)-r) := by
    simpa only [add_zero] using (LipschitzWith.dist_left (q 0)).sub (LipschitzWith.const r)
  have hh := (ha.min (hb.min (earlierCut_lipschitz q r n))).const_max 0
  unfold metricBump
  simpa only [max_self] using hh

theorem dyadicBump_nonneg (q : ℕ → M) (p : ℤ × ℕ) (x : M) : 0 ≤ dyadicBump q p x :=
  metricBump_nonneg q _ _ x

theorem dyadicC0_upper (q : ℕ → M) (hq : DenseRange q) (x y : M) : dist (dyadicC0 q hq x) (dyadicC0 q hq y)≤ dist x y := by
  rw [dist_eq_norm]
  apply cfun_norm_le _ dist_nonneg
  intro p
  change |dyadicBump q p x-dyadicBump q p y|≤ dist x y
  simpa only [dyadicBump,NNReal.coe_one,one_mul,Real.dist_eq] using
    (metricBump_lipschitz q ((2 : ℝ)^p.1) p.2).dist_le_mul x y

end Aharoni
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section AharoniLower
variable {M : Type*} [MetricSpace M]

theorem dyadicBump_separates (q : ℕ → M) (hq : DenseRange q) (x y : M)
    (hxy : 0 < dist x y) (hbase : dist x y/2 ≤ dist x (q 0)) :
    ∃ p : ℤ × ℕ, dist x y/32 ≤ dyadicBump q p x ∧ dyadicBump q p y=0 := by
  classical
  obtain ⟨k,hk,hk'⟩ := exists_mem_Ico_zpow (show 0 < dist x y/4 by positivity)
    (show (1 : ℝ)<2 by norm_num)
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ)≠0)] at hk'
  let r : ℝ := (2 : ℝ)^k
  have hr : 0 < r := zpow_pos (by norm_num) k
  have hr_upper : r≤ dist x y/4 := hk
  have hr_lower : dist x y/8 < r := by change dist x y/4 < r*2 at hk'; linarith
  have hex := hq.exists_dist_lt x (half_pos hr)
  let n := Nat.find hex
  have hn : dist x (q n) < r/2 := Nat.find_spec hex
  have hbefore : ∀ j< n, r/2≤ dist x (q j) := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hcut : r/4≤ earlierCut q r n x := le_earlierCut q r n x (by linarith)
    (fun j hj => by have h := hbefore j hj; linarith)
  have hbx : r/4≤ metricBump q r n x := by
    apply le_trans _ (le_max_right _ _)
    apply le_min (by linarith)
    exact le_min (by linarith) hcut
  have hyfar : r≤ dist y (q n) := by
    have ht := dist_triangle x (q n) y
    rw [dist_comm (q n) y] at ht
    linarith
  exact ⟨(k,n),(by change dist x y/32≤ metricBump q r n x; linarith),
    metricBump_zero_of_far q n y hyfar⟩

theorem dyadicC0_lower (q : ℕ → M) (hq : DenseRange q) (x y : M) :
    (1/32 : ℝ)*dist x y≤ dist (dyadicC0 q hq x) (dyadicC0 q hq y) := by
  by_cases hxy : x=y
  · subst y; simp
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hbase : dist x y/2≤ dist x (q 0) ∨ dist x y/2≤ dist y (q 0) := by
    have ht := dist_triangle x (q 0) y
    rw [dist_comm (q 0) y] at ht
    by_cases h : dist x y/2≤ dist x (q 0)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [dist_eq_norm]
  rcases hbase with hx|hy
  · obtain ⟨p,hp,hp0⟩ := dyadicBump_separates q hq x y hpos hx
    have hb := cfun_norm_apply_le (dyadicC0 q hq x-dyadicC0 q hq y) p
    change |dyadicBump q p x-dyadicBump q p y|≤_ at hb
    rw [hp0,sub_zero,abs_of_nonneg (dyadicBump_nonneg q p x)] at hb
    linarith
  · obtain ⟨p,hp,hp0⟩ := dyadicBump_separates q hq y x (by rwa [dist_comm]) (by rwa [dist_comm])
    have hb := cfun_norm_apply_le (dyadicC0 q hq x-dyadicC0 q hq y) p
    change |dyadicBump q p x-dyadicBump q p y|≤_ at hb
    rw [hp0,zero_sub,abs_neg,abs_of_nonneg (dyadicBump_nonneg q p y)] at hb
    rw [dist_comm y x] at hp
    linarith

end AharoniLower

section C0Reindex
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]

theorem cfunPull_dist_eq_of_surjective (j : A → B) (hj : Tendsto j cofinite cofinite)
    (hs : Function.Surjective j) (f g : C₀(B,ℝ)) :
    dist (cfunPull j hj f) (cfunPull j hj g)=dist f g := by
  rw [dist_eq_norm,dist_eq_norm]
  apply le_antisymm
  · apply cfun_norm_le _ (norm_nonneg _)
    intro a
    exact cfun_norm_apply_le (f-g) (j a)
  · apply cfun_norm_le _ (norm_nonneg _)
    intro b
    obtain ⟨a,rfl⟩ := hs b
    exact cfun_norm_apply_le (cfunPull j hj f-cfunPull j hj g) a

end C0Reindex

section AharoniEmbedding
variable {M : Type*} [MetricSpace M]

theorem aharoniEmbedding_dist (q : ℕ → M) (hq : DenseRange q) (x y : M) :
    dist (aharoniEmbedding q hq x) (aharoniEmbedding q hq y)=dist (dyadicC0 q hq x) (dyadicC0 q hq y) :=
  cfunPull_dist_eq_of_surjective _ _ dyadicEnumeration.symm.surjective _ _

theorem aharoniEmbedding_bilip (q : ℕ → M) (hq : DenseRange q) : BiLip (aharoniEmbedding q hq) := by
  refine ⟨1/32,1,by norm_num,by norm_num,fun x y => ?_⟩
  rw [aharoniEmbedding_dist,one_mul]
  exact ⟨dyadicC0_lower q hq x y,dyadicC0_upper q hq x y⟩

end AharoniEmbedding

theorem c0_metricUniversal : MetricUniversal C0 := by
  intro M instM instSep
  rcases isEmpty_or_nonempty M with hM|hM
  · let := hM
    refine ⟨fun x => isEmptyElim x,1,1,by norm_num,by norm_num,fun x y => ?_⟩
    exact isEmptyElim x
  · let := hM
    obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq M
    exact ⟨aharoniEmbedding q hq,aharoniEmbedding_bilip q hq⟩

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Main ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section

theorem BiLip.comp {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {g : Y → Z} {f : X → Y} (hg : BiLip g) (hf : BiLip f) : BiLip (g ∘ f) := by
  obtain ⟨cg,Cg,hcg,hcgC,hg⟩ := hg
  obtain ⟨cf,Cf,hcf,hcfC,hf⟩ := hf
  have hCg : 0≤Cg := hcg.le.trans hcgC
  have hCf : 0≤Cf := hcf.le.trans hcfC
  refine ⟨cg*cf,Cg*Cf,mul_pos hcg hcf,mul_le_mul hcgC hcfC hcf.le hCg,fun x y => ⟨?_,?_⟩⟩
  · calc
      cg*cf*dist x y = cg*(cf*dist x y) := mul_assoc _ _ _
      _ ≤ cg*dist (f x) (f y) := mul_le_mul_of_nonneg_left (hf x y).1 hcg.le
      _ ≤ dist ((g ∘ f) x) ((g ∘ f) y) := (hg _ _).1
  · calc
      dist ((g ∘ f) x) ((g ∘ f) y) ≤ Cg*dist (f x) (f y) := (hg _ _).2
      _ ≤ Cg*(Cf*dist x y) := mul_le_mul_of_nonneg_left (hf x y).2 hCg
      _ = Cg*Cf*dist x y := (mul_assoc _ _ _).symm

theorem concrete_metricUniversal : MetricUniversal ConcreteSpace := by
  intro M instM instSep
  obtain ⟨f,hf⟩ := c0_metricUniversal M
  exact ⟨concreteC0Embedding ∘ f,concreteC0Embedding_bilip.comp hf⟩

theorem main_result : MainConclusion := by
  refine ⟨ConcreteSpace,inferInstance,inferInstance,inferInstance,inferInstance,
    concrete_noLinearC0,⟨concreteAbsorption,concreteAbsorption_surjective,concreteAbsorption_bilip⟩,
    ⟨concreteC0Embedding,concreteC0Embedding_bilip⟩,concrete_metricUniversal,
    concrete_not_linearly_isomorphic⟩

end
end C0Absorption

end OAI

-- ---- mission target ----
open OAI OAI.C0Absorption
open scoped ZeroAtInfty
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace OAI
namespace C0Absorption
theorem _root_.solution : MainConclusion := by
  first
    | exact OAI.C0Absorption.main_result
    | (apply OAI.C0Absorption.main_result <;> assumption)
    | (intros; apply OAI.C0Absorption.main_result <;> assumption)
end C0Absorption
end OAI
