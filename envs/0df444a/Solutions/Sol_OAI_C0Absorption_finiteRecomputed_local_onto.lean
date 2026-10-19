-- Prove2me | solution 1 for OAI.C0Absorption.finiteRecomputed_local_onto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:53:45.753881+00:00
-- url     : https://prove2.me/submissions/b1afff89-293f-42ee-8694-82a4ae164edb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Continuity.lean:L95-L128
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.finiteRecomputed_local_onto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_C0Absorption_diagonal_neighborhood
import Theorems.Thm_OAI_C0Absorption_finiteInverse_bound
import Theorems.Thm_OAI_C0Absorption_normalization_bound
import Theorems.Thm_OAI_C0Absorption_theta_continuous

-- ---- from OAI.Analysis.C0Absorption.Blocks ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem finiteRadius_smul (I : Finset ℕ) (a : ℝ) (s : C0) :
    finiteRadius I (a • s)=|a| * finiteRadius I s := by
  simp only [finiteRadius,map_smul,norm_smul,Real.norm_eq_abs]

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Correction ----
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

theorem bandRow_continuous (j : ℕ) (ξ : BandGrid j) : Continuous (bandRow j ξ) := by
  exact (bandBump_lipschitz j ξ).continuous.div
    (continuous_finsetSum _ (fun ζ _ => (bandBump_lipschitz j ζ).continuous)) (fun s => (bandDenominator_pos j s).ne')

theorem localRadius_continuous (lev : Level) : Continuous (localRadius lev) :=
  (finiteRadius_lipschitz _).continuous

theorem blockVector_continuous (lev : Level) (b : Block lev) : Continuous (fun s => blockVector lev s b) :=
  ((theta_continuous (levelJ lev) b.1).comp ((localRadius_continuous lev).comp continuous_subtype_val)).mul
    ((bandVector_lipschitz b.1 b.2).continuous.comp (prefixRestrict_lipschitz b.1).continuous)

theorem blockRow_continuous (lev : Level) (b : Block lev) : Continuous (fun s => blockRow lev s b) :=
  ((theta_continuous (levelJ lev) b.1).comp ((localRadius_continuous lev).comp continuous_subtype_val)).mul
    ((bandRow_continuous b.1 b.2).comp (prefixRestrict_lipschitz b.1).continuous)

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.LocalInverse ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators

section LocalOnto
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem range_mem_nhds_of_approx {f : E → F} {a : E} (S : E ≃L[ℝ] F)
    (s : Set E) (hs : s∈nhds a) (c : ℝ≥0)
    (hc : c<‖(S.symm : F →L[ℝ] E)‖₊⁻¹) (ha : ApproximatesLinearOn f (S : E →L[ℝ] F) s c) :
    Set.range f∈nhds (f a) := by
  have hh := ha.image_mem_nhds S.toNonlinearRightInverse hs (Or.inr hc)
  exact mem_of_superset hh (Set.image_subset_range f s)

end LocalOnto
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

theorem WeightError.smul {W V : FrozenWeights} {x : C0} {q : ℝ} (h : WeightError W V x q) (a : ℝ) :
    WeightError W V (a • x) (|a| *q) := by
  constructor
  · intro lev b
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.vector lev b) (abs_nonneg a)
  · intro lev
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.row lev) (abs_nonneg a)

theorem WeightError.mono {W V : FrozenWeights} {x : C0} {q r : ℝ} (h : WeightError W V x q) (hr : q≤r) :
    WeightError W V x r := ⟨fun lev b => (h.vector lev b).trans hr,fun lev => (h.row lev).trans hr⟩

theorem normalized_error_left (x y : C0) : WeightError (stateWeights (normalizedBall x))
    (mixedWeights (normalizedBall x) (normalizedBall y)) x (2*eta*dist x y) := by
  have hh := (mixed_left_error (normalizedBall x) (normalizedBall y)).smul ‖x‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg x)] at hh
  apply hh.mono
  calc
    _ = eta*(‖x‖ * dist (normalize x) (normalize y)) := by rw [Subtype.dist_eq]; ring
    _ ≤ eta*(2*dist x y) := mul_le_mul_of_nonneg_left (normalization_bound x y) eta_pos.le
    _ = _ := by ring

theorem normalized_error_right (x y : C0) : WeightError (stateWeights (normalizedBall y))
    (mixedWeights (normalizedBall x) (normalizedBall y)) y (2*eta*dist x y) := by
  have hh := (mixed_right_error (normalizedBall x) (normalizedBall y)).smul ‖y‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg y)] at hh
  apply hh.mono
  calc
    _ = eta*(‖y‖ * dist (normalize y) (normalize x)) := by rw [Subtype.dist_eq,dist_comm]; ring
    _ ≤ eta*(2*dist y x) := mul_le_mul_of_nonneg_left (normalization_bound y x) eta_pos.le
    _ = _ := by rw [dist_comm]; ring

theorem shift_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) : ‖frozenShift W x-frozenShift V x‖≤6*q := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) hq)
  intro γ
  change |frozenShift W x γ-frozenShift V x γ|≤_
  rw [frozenShift_apply,frozenShift_apply,add_sub_add_left_eq_sub]
  exact correction_weight_error hq h γ

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

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

theorem finiteEquiv_symm_apply (N : ℕ) (W : FrozenWeights) (y : FInput N) :
    (finiteEquiv N W).symm y=finiteInverseFunction W y := by
  apply (finiteEquiv N W).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (finiteFrozen_inverse W y).symm

theorem finiteEquiv_symm_norm (N : ℕ) (W : FrozenWeights) : ‖((finiteEquiv N W).symm : FInput N →L[ℝ] FInput N)‖≤5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [ContinuousLinearEquiv.coe_coe,finiteEquiv_symm_apply]
  exact finiteInverse_bound W y

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

theorem finiteFrozen_weight_error {W V : FrozenWeights} {x : FInput N} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V (finiteEmbed N x) q) :
    ‖finiteFrozen N W x-finiteFrozen N V x‖≤6*q := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hq)).mpr
  rintro (i|γ)
  · change |finiteRow W (i,Fin.last N) x-finiteRow V (i,Fin.last N) x|≤_
    rw [finiteRow_eq,finiteRow_eq]
    exact (rowScalar_weight_error W V _ _ (h.row _)).trans (by linarith)
  · change |finiteFrozenFunction W x (.inr γ)-finiteFrozenFunction V x (.inr γ)|≤_
    rw [finiteFrozen_block,finiteFrozen_block]
    exact (cfun_norm_apply_le (frozenShift W (finiteEmbed N x)-frozenShift V (finiteEmbed N x)) (fLabel γ)).trans
      (shift_weight_error hq h)

theorem finiteRecomputed_mixed_left (x y : FInput N) :
    ‖finiteRecomputed N x-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) x‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_left (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

theorem finiteRecomputed_mixed_right (x y : FInput N) :
    ‖finiteRecomputed N y-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) y‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_right (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

theorem finiteRecomputed_mixed_approx (x y : FInput N) :
    ‖finiteRecomputed N x-finiteRecomputed N y-
      finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) (x-y)‖≤24*eta*dist x y := by
  let W := mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))
  have he : finiteRecomputed N x-finiteRecomputed N y-finiteFrozen N W (x-y)=
      (finiteRecomputed N x-finiteFrozen N W x)-(finiteRecomputed N y-finiteFrozen N W y) := by rw [map_sub]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [finiteRecomputed_mixed_left x y,finiteRecomputed_mixed_right x y])

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

section FiniteOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_operator_norm_le_columns (T : (A → ℝ) →L[ℝ] E) :
    ‖T‖≤∑ a,‖T (Pi.single a 1)‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  intro x
  have he : (∑ a, x a • Pi.single a (1 : ℝ))=x := by
    ext b
    simp [Pi.single_apply]
  have hEq : T x=∑ a,x a • T (Pi.single a 1) := by
    simpa only [map_sum,map_smul] using congrArg T he.symm
  rw [hEq]
  calc
    _ ≤ ∑ a, ‖x a • T (Pi.single a 1)‖ := norm_sum_le _ _
    _ = ∑ a, ‖T (Pi.single a 1)‖*‖x a‖ := by simp only [norm_smul,mul_comm]
    _ ≤ ∑ a, ‖T (Pi.single a 1)‖*‖x‖ := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm x a) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

theorem tendsto_finiteOperator_of_columns {X : Type*} {l : Filter X}
    (T : X → (A → ℝ) →L[ℝ] E) (S : (A → ℝ) →L[ℝ] E)
    (h : ∀ a, Tendsto (fun z => T z (Pi.single a 1)) l (nhds (S (Pi.single a 1)))) :
    Tendsto T l (nhds S) := by
  classical
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun z => norm_nonneg _) (fun z => finite_operator_norm_le_columns (T z-S))
  have hh : Tendsto (fun z => ∑ a, ‖T z (Pi.single a 1)-S (Pi.single a 1)‖) l (nhds (∑ a : A, (0 : ℝ))) :=
    tendsto_finsetSum _ (fun a _ => tendsto_iff_norm_sub_tendsto_zero.mp (h a))
  simpa only [sub_apply,Finset.sum_const_zero] using hh

end FiniteOperators

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Continuity ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem mixed_vector_tendsto (s : C0Ball) (lev : Level) (b : Block lev) :
    Tendsto (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).vector lev b)
      (nhds (s,s)) (nhds ((stateWeights s).vector lev b)) := by
  classical
  have h1 : Tendsto (fun p : C0Ball × C0Ball => blockVector lev p.1 b) (nhds (s,s)) (nhds (blockVector lev s b)) :=
    ((blockVector_continuous lev b).comp continuous_fst).continuousAt
  have h2 : Tendsto (fun p : C0Ball × C0Ball => blockVector lev p.2 b) (nhds (s,s)) (nhds (blockVector lev s b)) :=
    ((blockVector_continuous lev b).comp continuous_snd).continuousAt
  have he : (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).vector lev b)=
      (fun p : C0Ball × C0Ball => if localRadius lev p.2.val≤localRadius lev p.1.val then blockVector lev p.1 b else blockVector lev p.2 b) := by
    funext p
    dsimp only [mixedWeights,mixedState]
    split_ifs <;> rfl
  rw [he]
  exact h1.if' h2

theorem mixed_row_tendsto (s : C0Ball) (lev : Level) (b : Block lev) :
    Tendsto (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).row lev b)
      (nhds (s,s)) (nhds ((stateWeights s).row lev b)) := by
  classical
  have h1 : Tendsto (fun p : C0Ball × C0Ball => blockRow lev p.1 b) (nhds (s,s)) (nhds (blockRow lev s b)) :=
    ((blockRow_continuous lev b).comp continuous_fst).continuousAt
  have h2 : Tendsto (fun p : C0Ball × C0Ball => blockRow lev p.2 b) (nhds (s,s)) (nhds (blockRow lev s b)) :=
    ((blockRow_continuous lev b).comp continuous_snd).continuousAt
  have he : (fun p : C0Ball × C0Ball => (mixedWeights p.1 p.2).row lev b)=
      (fun p : C0Ball × C0Ball => if localRadius lev p.2.val≤localRadius lev p.1.val then blockRow lev p.1 b else blockRow lev p.2 b) := by
    funext p
    dsimp only [mixedWeights,mixedState]
    split_ifs <;> rfl
  rw [he]
  exact h1.if' h2

variable {N : ℕ}

theorem finiteRow_mixed_tendsto (s : C0Ball) (l : FLevel N) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finiteRow (mixedWeights p.1 p.2) l x)
      (nhds (s,s)) (nhds (finiteRow (stateWeights s) l x)) := by
  exact tendsto_finsetSum _ (fun b _ => (mixed_row_tendsto s _ b).mul_const _)

theorem finitePrev_mixed_tendsto (s : C0Ball) (l : FLevel N) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finitePrev (mixedWeights p.1 p.2) l x)
      (nhds (s,s)) (nhds (finitePrev (stateWeights s) l x)) := by
  unfold finitePrev
  split_ifs
  · exact tendsto_const_nhds
  · exact finiteRow_mixed_tendsto s _ x

theorem finiteFrozen_mixed_apply_tendsto (s : C0Ball) (x : FInput N) :
    Tendsto (fun p : C0Ball × C0Ball => finiteFrozen N (mixedWeights p.1 p.2) x)
      (nhds (s,s)) (nhds (finiteFrozen N (stateWeights s) x)) := by
  apply tendsto_pi_nhds.mpr
  rintro (i|⟨l,b⟩)
  · exact finiteRow_mixed_tendsto s (i,Fin.last N) x
  · exact tendsto_const_nhds.add ((mixed_vector_tendsto s _ b).mul
      ((finitePrev_mixed_tendsto s l x).sub (finiteRow_mixed_tendsto s l x)))

theorem finiteFrozen_mixed_tendsto (N : ℕ) (s : C0Ball) :
    Tendsto (fun p : C0Ball × C0Ball => finiteFrozen N (mixedWeights p.1 p.2))
      (nhds (s,s)) (nhds (finiteFrozen N (stateWeights s))) := by
  classical
  exact tendsto_finiteOperator_of_columns _ _ (fun a => finiteFrozen_mixed_apply_tendsto s _)

theorem normalizedBall_continuousAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x≠0) : ContinuousAt (@normalizedBall E _ _ ) x := by
  apply tendsto_subtype_rng.mpr
  exact (continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

theorem finite_normalized_continuousAt {x : FInput N} (hx : x≠0) :
    ContinuousAt (fun y => normalizedBall (finiteEmbed N y)) x := by
  have he : finiteEmbed N x≠0 := fun he => hx ((finiteEmbed N).injective (he.trans (map_zero _).symm))
  exact (normalizedBall_continuousAt he).comp (finiteEmbed N).continuous.continuousAt

theorem finite_mixed_operator_near {x : FInput N} (hx : x≠0) :
    ∃ s : Set (FInput N), s∈nhds x ∧ ∀ y∈s, ∀ z∈s,
      ‖finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N y)) (normalizedBall (finiteEmbed N z)))-
        finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x)))‖ < 1/20 := by
  exact diagonal_neighborhood (fun y => normalizedBall (finiteEmbed N y))
    (finite_normalized_continuousAt hx) (fun p => finiteFrozen N (mixedWeights p.1 p.2))
    (finiteFrozen N (stateWeights (normalizedBall (finiteEmbed N x))))
    (finiteFrozen_mixed_tendsto N _) (by norm_num)

theorem finiteRecomputed_local_onto {x : FInput N} (hx : x≠0) :
    Set.range (finiteRecomputed N)∈nhds (finiteRecomputed N x) := by
  let W := stateWeights (normalizedBall (finiteEmbed N x))
  let S := finiteEquiv N W
  obtain ⟨s,hs,hclose⟩ := finite_mixed_operator_near hx
  apply range_mem_nhds_of_approx S s hs (1/10)
  · have hh : ‖(S.symm : FInput N →L[ℝ] FInput N)‖₊≤5 := by
      exact_mod_cast finiteEquiv_symm_norm N W
    have hpos : 0<‖(S.symm : FInput N →L[ℝ] FInput N)‖₊ := by
      exact S.nnnorm_symm_pos
    rw [inv_eq_one_div,lt_div_iff₀ hpos]
    calc (1/10 : ℝ≥0)*‖(S.symm : FInput N →L[ℝ] FInput N)‖₊ ≤ (1/10)*5 := mul_le_mul_of_nonneg_left hh (by positivity)
         _ < 1 := by norm_num
  · intro y hy z hz
    let V := mixedWeights (normalizedBall (finiteEmbed N y)) (normalizedBall (finiteEmbed N z))
    have he : ‖finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N V (y-z)‖≤24*eta*dist y z :=
      finiteRecomputed_mixed_approx y z
    have hd : ‖(finiteFrozen N V-finiteFrozen N W) (y-z)‖≤(1/20)*dist y z := by
      apply ((finiteFrozen N V-finiteFrozen N W).le_opNorm (y-z)).trans
      rw [← dist_eq_norm y z]
      exact mul_le_mul_of_nonneg_right (hclose y hy z hz).le dist_nonneg
    have hid : finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N W (y-z)=
      (finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N V (y-z))+
        (finiteFrozen N V-finiteFrozen N W) (y-z) := by
      rw [sub_apply]
      abel
    change ‖finiteRecomputed N y-finiteRecomputed N z-finiteFrozen N W (y-z)‖≤(1/10 : ℝ≥0)*‖y-z‖
    rw [hid]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ 24*eta*dist y z+(1/20)*dist y z := add_le_add he hd
      _ = (24*eta+1/20)*dist y z := by ring
      _ ≤ (1/10)*dist y z := mul_le_mul_of_nonneg_right (by norm_num [eta]) dist_nonneg
      _ = _ := by norm_num only [NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]; rw [dist_eq_norm]

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.finiteRecomputed_local_onto := @_root_.OAI.C0Absorption.finiteRecomputed_local_onto
