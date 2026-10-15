-- Prove2me | solution 1 for OAI.ForestSpace.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:11:00.428458+00:00
-- url     : https://prove2.me/submissions/e25bb6e1-7e66-4e45-a8c5-96853737f233

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Main.lean:L13-L27
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ForestSpace.main_theorem.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ForestSpace_main_theorem) verbatim and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components
import Definitions.Def_OAI_Analysis_ForestSpace_FullDual
import Definitions.Def_OAI_Analysis_ForestSpace_Diamonds
import Definitions.Def_OAI_Analysis_ForestSpace_Distortion
import Theorems.Thm_OAI_ForestSpace_Diamond_Network_refine_connected
import Theorems.Thm_OAI_ForestSpace_Diamond_edge_sq_loss
import Theorems.Thm_OAI_ForestSpace_EquivalentNorm_bounded_trees_auc_zero
import Theorems.Thm_OAI_ForestSpace_averageModulus_lower_of_subspaces
import Theorems.Thm_OAI_ForestSpace_exists_head_approx
import Theorems.Thm_OAI_ForestSpace_main_lens
import Theorems.Thm_OAI_ForestSpace_norm_rawRestriction
import Theorems.Thm_OAI_ForestSpace_pair_perturbation
import Theorems.Thm_OAI_ForestSpace_paired_estimate

-- ---- from OAI.Analysis.ForestSpace.Completion ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TestVector
variable {V : Type}
variable [PartialOrder V]
 theorem cut_eq_zero_of_compl {H : Set V} {u : TestVector V}
    (hu : SupportedOn u Hᶜ) : cut H u = 0 := by
  ext v
  by_cases hv : v ∈ H
  · simp [hv, hu v (by simpa using hv)]
  · simp [hv]

end TestVector

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Polar ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section PolarTests
variable {V : Type} [PartialOrder V]

 theorem Annihilates.smul {x : FullDual V} {A : Set V} (hx : Annihilates x A) (t : ℝ) :
    Annihilates (t • x) A := by
  intro u hu
  simp [hx u hu]

end PolarTests

section CoordinateCompletion
variable {W : Type} [PartialOrder W]
variable {V : Type} [PartialOrder V]

end CoordinateCompletion

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Projections ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Projections
variable {V : Type} [PartialOrder V]

 theorem annihilates_P (H : Set V) (hH : IsLowerSet H) (x : FullDual V) :
    Annihilates (P H hH x) Hᶜ := by
  intro u hu
  simp only [P_coe, TestVector.cut_eq_zero_of_compl hu,
    UniformSpace.Completion.coe_zero, map_zero]

 theorem annihilates_Q (H : Set V) (hH : IsLowerSet H) (x : FullDual V) :
    Annihilates (Q H hH x) H := by
  intro u hu
  rw [Q_eq_sub]
  simp only [_root_.sub_apply, P_coe, TestVector.cut_eq_self hu, sub_self]

end Projections

section CoordinateStructure
variable {V : Type} [PartialOrder V]

 theorem linearIndependent_eStar : LinearIndependent ℝ (eStar (V := V)) := by
  apply linearIndependent_iff'.mpr
  intro S a h v hv
  have hh := congrArg (fun x : FullDual V => x (e v)) h
  simp only [_root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, eStar_e, _root_.zero_apply, mul_ite, mul_one, mul_zero] at hh
  simpa [hv] using hh

 theorem separable_X [Countable V] : TopologicalSpace.SeparableSpace (X V) := by
  have hs : TopologicalSpace.IsSeparable (Set.range (eStar (V := V))) :=
    (Set.countable_range _).isSeparable
  have hc := (hs.span (R := ℝ)).closure
  exact hc.separableSpace

end CoordinateStructure

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Coordinates ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section CoordinateBounds
variable {V : Type} [PartialOrder V]

 theorem norm_sum_coordinates_le (S : Finset V) (a : V → ℝ) :
    ‖∑ v ∈ S, a v • eStar v‖ ≤ Real.sqrt (∑ v ∈ S, a v ^ 2) := by
  rw [← norm_rawRestriction (∑ v ∈ S, a v • eStar v)]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  simp only [rawRestriction_apply, _root_.sum_apply, smul_apply, eStar_coe,
    smul_eq_mul, Real.norm_eq_abs]
  have hA : 0 ≤ ∑ v ∈ S, a v ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hA]
  exact (Finset.sum_mul_sq_le_sq_mul_sq S a (fun v => u v)).trans
    (mul_le_mul_of_nonneg_left (coordinate_squares_le S u) hA)

 theorem weakNull_of_l2_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type} (v : I → E)
    (h : ∀ (S : Finset I) (a : I → ℝ), ‖∑ i ∈ S, a i • v i‖ ≤ Real.sqrt (∑ i ∈ S, a i^2))
    (w : ℕ → I) (hw : Function.Injective w) : WeakNull (fun n => v (w n)) := by
  intro φ
  have hs : Summable (fun i : I => (φ (v i))^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) (dual_vectors_squares_le v h φ)
  have ht := (hs.comp_injective hw).tendsto_atTop_zero
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hh

 theorem weakNull_coordinates (v : ℕ → V) (hv : Function.Injective v) :
    WeakNull (fun n => eX (v n)) := by
  apply weakNull_of_l2_bound (E := X V) (eX (V := V)) ?_ v hv
  intro S a
  change ‖(∑ i ∈ S, a i • eX i : X V).val‖ ≤ _
  simpa only [Submodule.coe_sum,Submodule.coe_smul,eX_val] using norm_sum_coordinates_le S a

 theorem norm_segment_functional_le (S : Finset V) (hS : IsSegment S) :
    ‖∑ v ∈ S, eStar v‖ ≤ 1 := by
  rw [← norm_rawRestriction (∑ v ∈ S, eStar v)]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [rawRestriction_apply, _root_.sum_apply, eStar_coe, one_mul, Real.norm_eq_abs]
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)).single hS
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg u)).mp (by
    simpa only [sq_abs, TestVector.norm_eq_rho, segSum] using hh)

 theorem norm_segment_functional (S : Finset V) (hS : IsSegment S) (hne : S.Nonempty) :
    ‖∑ v ∈ S, eStar v‖ = 1 := by
  apply le_antisymm (norm_segment_functional_le S hS)
  obtain ⟨v,hv⟩ := hne
  have hh := (∑ w ∈ S, eStar w).le_opNorm (e v)
  simpa [eStar_e,hv] using hh

 theorem norm_segment_eX (S : Finset V) (hS : IsSegment S) (hne : S.Nonempty) :
    ‖∑ v ∈ S, eX v‖ = 1 := by
  change ‖(∑ v ∈ S, eX v : X V).val‖ = _
  simpa only [Submodule.coe_sum,eX_val] using norm_segment_functional S hS hne

 theorem ancestors_isSegment (hF : ForestOrder V) (v : V) (hfin : (Set.Iic v).Finite) :
    IsSegment hfin.toFinset := by
  constructor
  · intro a ha b hb
    apply hF a b v
    · simpa using ha
    · simpa using hb
  · intro a ha b hb c hac hcb
    have hbv : b ≤ v := by simpa using hb
    simpa using hcb.trans hbv

 theorem norm_pathVector (hF : ForestOrder V) (v : V) (hfin : (Set.Iic v).Finite) :
    ‖pathVector v hfin‖ = 1 := by
  exact norm_segment_eX _ (ancestors_isSegment hF v hfin) ⟨v,by simp⟩

end CoordinateBounds

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Trees ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Words

namespace Word
 theorem forestOrder : ForestOrder Word := by
  intro a b c hac hbc
  rcases le_total a.letters.length b.letters.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le hac hbc h)
  · exact Or.inr (List.prefix_of_prefix_length_le hbc hac h)

 theorem le_child (s : Word) (j : ℕ) : s ≤ child s j := List.prefix_append _ _
 theorem child_not_le (s : Word) (j : ℕ) : ¬child s j ≤ s := by
  intro h
  have hh := h.length_le
  simp only [child,List.length_append,List.length_singleton] at hh
  omega

 theorem le_child_iff (s w : Word) (j : ℕ) :
    w ≤ child s j ↔ w = child s j ∨ w ≤ s := by
  constructor
  · intro h
    by_cases hlen : w.letters.length ≤ s.letters.length
    · exact Or.inr (List.prefix_of_prefix_length_le h (le_child s j) hlen)
    · left
      apply ext
      apply h.eq_of_length
      have hh := h.length_le
      simp only [child,List.length_append,List.length_singleton] at hh ⊢
      omega
  · rintro (rfl | h)
    · exact le_rfl
    · exact h.trans (le_child s j)

end Word

end Words

section FiniteHeightForest

namespace Vertex
 theorem forestOrder : ForestOrder Vertex := by
  intro a b c hac hbc
  rcases Word.forestOrder a.word b.word c.word hac.2 hbc.2 with h | h
  · exact Or.inl ⟨hac.1.trans hbc.1.symm,h⟩
  · exact Or.inr ⟨hbc.1.trans hac.1.symm,h⟩

 theorem child_not_le (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    ¬ child v hv j ≤ v := fun h => Word.child_not_le v.word j h.2

 theorem le_child_iff (v w : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    w ≤ child v hv j ↔ w = child v hv j ∨ w ≤ v := by
  constructor
  · intro hw
    rcases (Word.le_child_iff v.word w.word j).mp hw.2 with h | h
    · exact Or.inl (ext hw.1 h)
    · exact Or.inr ⟨hw.1,h⟩
  · rintro (rfl | h)
    · exact le_rfl
    · exact ⟨h.1,h.2.trans (Word.le_child v.word j)⟩

 theorem ancestor_finset_child (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    (finiteAncestors (child v hv j)).toFinset = insert (child v hv j) (finiteAncestors v).toFinset := by
  ext w
  simp only [Set.Finite.mem_toFinset,Set.mem_Iic,Finset.mem_insert]
  exact le_child_iff v w hv j

 theorem path_child (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    pathVector (child v hv j) (finiteAncestors _) - pathVector v (finiteAncestors _) = eX (child v hv j) := by
  unfold pathVector
  rw [ancestor_finset_child,Finset.sum_insert]
  · abel
  · simpa using child_not_le v hv j

 theorem norm_treePath (h : ℕ) (hh : 1 ≤ h) (s : List ℕ) (hs : s.length ≤ h) :
    ‖treePath h s‖ = 1 := by
  simp only [treePath,dite_eq_left hh,dite_eq_left hs]
  exact norm_pathVector forestOrder _ _

 theorem treePath_child (h : ℕ) (hh : 1 ≤ h) (s : List ℕ) (hs : s.length < h) (j : ℕ) :
    treePath h (s++[j]) - treePath h s =
      eX (child (node h hh s (by omega)) hs j) := by
  have hs' : (s++[j]).length ≤ h := by simp; omega
  simpa only [treePath,dite_eq_left hh,dite_eq_left hs',dite_eq_left (Nat.le_of_lt hs),node,child,Word.child] using
    path_child (node h hh s (Nat.le_of_lt hs)) hs j

end Vertex

end FiniteHeightForest

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Reflexivity ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Reflexivity

 theorem reflexive_dual {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Reflexive E) : Reflexive (StrongDual ℝ E) := by
  intro Φ
  refine ⟨Φ.comp (NormedSpace.inclusionInDoubleDual ℝ E),?_⟩
  ext G
  obtain ⟨x,rfl⟩ := hE G
  rfl

section L2Dual
variable {I : Type} (E : I → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

end L2Dual
end Reflexivity

section CompletionIsomorphism
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

end CompletionIsomorphism

section ComponentHilbert
variable {V : Type} [PartialOrder V]

end ComponentHilbert

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.FullDual ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section CoordinateDensity
variable {V : Type} [PartialOrder V]

 theorem reflexive_main_fullDual : Reflexive (FullDual Vertex) :=
  reflexive_dual reflexive_forest_J

 theorem separable_main_fullDual : TopologicalSpace.SeparableSpace (FullDual Vertex) := by
  let := separable_X (V := Vertex)
  exact fullDualEquiv.surjective.denseRange.separableSpace fullDualEquiv.continuous

 theorem infiniteDimensional_main_fullDual : ¬FiniteDimensional ℝ (FullDual Vertex) := by
  intro h
  let := h
  have : Finite Vertex := linearIndependent_eStar.finite
  exact Infinite.not_finite (inferInstance : Finite Vertex)

 theorem exists_main_head_approx (x : FullDual Vertex) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Finset Vertex, ∃ hH : IsLowerSet (H : Set Vertex),
      ‖x-P (H : Set Vertex) hH x‖ < ε := by
  let z : X Vertex := fullDualEquiv.symm x
  obtain ⟨H,hH,hh⟩ := exists_head_approx Vertex.finiteAncestors z ε hε
  refine ⟨H,hH,?_⟩
  have hz : (z : FullDual Vertex) = x := fullDualEquiv.apply_symm_apply x
  change ‖(z : FullDual Vertex)-P (H : Set Vertex) hH z‖ < ε at hh
  simpa only [hz] using hh

end CoordinateDensity

section MainNorm

 theorem mainFiniteCoordinates_kernel_finite (H : Finset Vertex) :
    FiniteDimensional ℝ ((FullDual Vertex) ⧸ (mainFiniteCoordinates H).toLinearMap.ker) :=
  Module.Finite.equiv (mainFiniteCoordinates H).toLinearMap.quotKerEquivRange.symm

 theorem main_P_eq_zero_of_mem_ker (H : Finset Vertex) (hH : IsLowerSet (H : Set Vertex))
    {y : FullDual Vertex} (hy : y ∈ (mainFiniteCoordinates H).toLinearMap.ker) :
    P (H : Set Vertex) hH y = 0 := by
  have hh : mainFiniteCoordinates H y = 0 := hy
  rw [P_finite_eq_sum]
  apply Finset.sum_eq_zero
  intro v hv
  have hz : y (e v) = 0 := congrFun hh ⟨v,hv⟩
  rw [hz,zero_smul]

 theorem main_average_modulus (t : ℝ) (ht : 0 < t) :
    Real.sqrt (1+t^2/12)-1 ≤ averageModulus (FullDual Vertex) norm t := by
  apply averageModulus_lower_of_subspaces infiniteDimensional_main_fullDual ht.le
  intro x hx ε hε
  obtain ⟨H,hH,hclose⟩ := exists_main_head_approx x (ε/4) (by positivity)
  let F : Cofinite (FullDual Vertex) := ⟨(mainFiniteCoordinates H).toLinearMap.ker,
    (mainFiniteCoordinates H).isClosed_ker, mainFiniteCoordinates_kernel_finite H⟩
  refine ⟨F,?_⟩
  intro y hy hyn
  have he : Q (H : Set Vertex) hH y = y := by
    rw [Q_eq_sub,main_P_eq_zero_of_mem_ker H hH hy,sub_zero]
  have hy' : Annihilates y (H : Set Vertex) := by
    rw [← he]
    exact annihilates_Q _ _ _
  have hpair := paired_estimate Vertex.forestOrder Vertex.finiteAncestors (H : Set Vertex) hH
    (P (H : Set Vertex) hH x) (t • y) (annihilates_P _ _ _) (hy'.smul t)
  rw [norm_smul,Real.norm_of_nonneg ht.le,hyn,mul_one] at hpair
  have hh := pair_perturbation x (P (H : Set Vertex) hH x) (t • y)
    (t^2/12) (by positivity) hx hpair
  linarith

 theorem main_auc_modulus_zero {α β : ℝ} (R : EquivalentNorm (FullDual Vertex) α β) :
    aucModulus (FullDual Vertex) R.N (α/(2*β)) = 0 := by
  apply R.bounded_trees_auc_zero infiniteDimensional_main_fullDual
    (fun h s => (Vertex.treePath h s : FullDual Vertex))
  · exact Vertex.norm_treePath
  · intro h hh s hs j
    change 1 ≤ ‖((Vertex.treePath h (s++[j])-Vertex.treePath h s : X Vertex) : FullDual Vertex)‖
    rw [Vertex.treePath_child h hh s hs j,eX_val,norm_eStar]
  · intro h hh s hs
    have hd := weakNull_coordinates _
      (Vertex.child_injective (Vertex.node h hh s (Nat.le_of_lt hs)) hs)
    intro φ
    have hh' := hd (φ.comp (coordinateSubspace Vertex).subtypeL)
    convert hh' using 1
    ext j
    change φ (((Vertex.treePath h (s++[j])-Vertex.treePath h s : X Vertex) : FullDual Vertex)) = _
    rw [Vertex.treePath_child h hh s hs j]
    rfl

 theorem main_no_equivalent_AUC {α β : ℝ} (R : EquivalentNorm (FullDual Vertex) α β) :
    ¬IsAUC R.N := by
  intro h
  have hp : 0 < α/(2*β) := div_pos R.alpha_pos (mul_pos (by norm_num) (R.alpha_pos.trans_le R.alpha_le_beta))
  have hh := h _ hp
  rw [main_auc_modulus_zero R] at hh
  exact lt_irrefl _ hh

end MainNorm

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Diamonds ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

namespace ForestSpace

attribute [local instance] Classical.propDecidable

namespace Diamond

namespace Network
variable (A : Network)

 theorem edge_adj (e : A.E) : A.graph.Adj (A.left e) (A.right e) :=
  ⟨e,Or.inl ⟨rfl,rfl⟩⟩

 theorem refine_adj_left (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inl (A.left e)) (Sum.inr (e,j)) := by
  exact A.refine.edge_adj (e,j,false)

 theorem refine_adj_right (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inr (e,j)) (Sum.inl (A.right e)) := by
  exact A.refine.edge_adj (e,j,true)

 theorem refine_adj_lift {u v : A.V} (huv : A.graph.Adj u v) :
    ∃ w : A.refine.V, A.refine.graph.Adj (Sum.inl u) w ∧
      A.refine.graph.Adj w (Sum.inl v) := by
  obtain ⟨e,h | h⟩ := huv
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),A.refine_adj_left e 0,A.refine_adj_right e 0⟩
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),(A.refine_adj_right e 0).symm,(A.refine_adj_left e 0).symm⟩

 theorem refine_walk_lift {u v : A.V} (p : A.graph.Walk u v) :
    ∃ q : A.refine.graph.Walk (Sum.inl u) (Sum.inl v), q.length = 2*p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | @cons u v w huv p ih =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨z,huz,hzv⟩ := A.refine_adj_lift huv
    refine ⟨.cons huz (.cons hzv q),?_⟩
    change q.length+1+1 = 2*(p.length+1)
    rw [hq]
    omega

end Network

 theorem potential_bound {V : Type} (G : SimpleGraph V) (f : V → ℝ)
    (hf : ∀ u v, G.Adj u v → |f u-f v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |f u-f v| ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hh := abs_add_le (f u-f v) (f v-f w)
    have he : f u-f v+(f v-f w) = f u-f w := by ring
    rw [he] at hh
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [hf u v huv]

namespace Network

section
variable (A : Network)

 theorem adj_dist_potential (hA : A.graph.Connected) (a : A.V) {u v : A.V}
    (huv : A.graph.Adj u v) :
    |(A.graph.dist a u : ℝ)-(A.graph.dist a v : ℝ)| ≤ 1 := by
  have he : A.graph.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv
  have h1 := hA.dist_triangle (u := a) (v := u) (w := v)
  have h2 := hA.dist_triangle (u := a) (v := v) (w := u)
  rw [he] at h1
  rw [SimpleGraph.dist_comm (u := v) (v := u),he] at h2
  have h1' : (A.graph.dist a v : ℝ) ≤ (A.graph.dist a u : ℝ)+1 := by exact_mod_cast h1
  have h2' : (A.graph.dist a u : ℝ) ≤ (A.graph.dist a v : ℝ)+1 := by exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

 theorem refinePotential_adj (hA : A.graph.Connected) (a : A.V)
    (u v : A.refine.V) (huv : A.refine.graph.Adj u v) :
    |A.refinePotential a u-A.refinePotential a v| ≤ 1 := by
  obtain ⟨⟨e,j,b⟩,h | h⟩ := huv
  all_goals rcases h with ⟨rfl,rfl⟩
  all_goals cases b
  all_goals dsimp [refine,refinePotential]
  all_goals have hh := A.adj_dist_potential hA a (A.edge_adj e)
  all_goals obtain ⟨h1,h2⟩ := abs_le.mp hh
  all_goals exact abs_le.mpr ⟨by linarith,by linarith⟩

 theorem refine_dist_old (hA : A.graph.Connected) (u v : A.V) :
    A.refine.graph.dist (Sum.inl u) (Sum.inl v) = 2*A.graph.dist u v := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := (hA u v).exists_walk_length_eq_dist
    obtain ⟨q,hq⟩ := A.refine_walk_lift p
    have hh := SimpleGraph.dist_le q
    rwa [hq,hp] at hh
  · obtain ⟨p,hp⟩ := (A.refine_connected hA (Sum.inl u) (Sum.inl v)).exists_walk_length_eq_dist
    have hh := potential_bound A.refine.graph (A.refinePotential u) (A.refinePotential_adj hA u) p
    simp only [refinePotential,SimpleGraph.dist_self,Nat.cast_zero,mul_zero,zero_sub,abs_neg,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_nonneg (show (0:ℝ) ≤ (A.graph.dist u v : ℝ) from Nat.cast_nonneg _),hp] at hh
    exact_mod_cast hh

end

 theorem old_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (u v : A.V) :
    (A.iterate n).graph.dist (A.old n u) (A.old n v) = 2^n*A.graph.dist u v := by
  induction n generalizing A with
  | zero => simp [iterate]
  | succ n ih =>
    change (A.refine.iterate n).graph.dist (A.refine.old n (Sum.inl u))
      (A.refine.old n (Sum.inl v)) = _
    rw [ih A.refine (A.refine_connected hA),A.refine_dist_old hA,pow_succ]
    ring

 theorem old_edge_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (e : A.E) :
    (A.iterate n).graph.dist (A.old n (A.left e)) (A.old n (A.right e)) = 2^n := by
  rw [A.old_dist hA,SimpleGraph.dist_eq_one_iff_adj.mpr (A.edge_adj e),mul_one]

end Network

 theorem base_connected : base.graph.Connected := by
  refine @SimpleGraph.Connected.mk _ _ ?_ ⟨false⟩
  intro u v
  cases u <;> cases v
  · exact SimpleGraph.Reachable.refl _
  · exact (base.edge_adj ()).reachable
  · exact (base.edge_adj ()).symm.reachable
  · exact SimpleGraph.Reachable.refl _

end Diamond

end ForestSpace

end

end OAI

-- ---- from OAI.Analysis.ForestSpace.Distortion ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Diamond

noncomputable section

section Distortion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem distortion_lower (hLens : LensProperty E) (k : ℕ)
    (f : (diamond k).V → E) (C : ℝ) (hf : EmbeddingBound k f C) :
    Real.sqrt (1+(k:ℝ)/12) ≤ C := by
  obtain ⟨s,hs,hf⟩ := hf
  let g : (diamond k).V → E := fun v => s⁻¹ • f v
  have hgn : ∀ u v, ‖g u-g v‖ = ‖f u-f v‖/s := by
    intro u v
    dsimp [g]
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    ring
  have hl : ∀ u v, ((base.iterate k).graph.dist u v : ℝ) ≤ ‖g u-g v‖ := by
    intro u v
    rw [hgn]
    exact (le_div_iff₀ hs).mpr (by simpa only [distance,mul_comm] using (hf u v).1)
  have hu : ∀ u v, ‖g u-g v‖ ≤ C*((base.iterate k).graph.dist u v : ℝ) := by
    intro u v
    rw [hgn]
    exact (div_le_iff₀ hs).mpr (by simpa only [distance,mul_assoc,mul_comm,mul_left_comm] using (hf u v).2)
  let a := base.old k (base.left ())
  let b := base.old k (base.right ())
  have hd : ((base.iterate k).graph.dist a b : ℝ) = (2:ℝ)^k := by
    exact_mod_cast (base.old_edge_dist base_connected k ())
  have hc : 1 ≤ C := by
    have hlo := hl a b
    have hup := hu a b
    rw [hd] at hlo hup
    have hpow : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
    nlinarith
  have hbound := edge_sq_loss hLens base base_connected k g C (by linarith) hl hu ()
  have hlo : 1 ≤ ‖g b-g a‖/(2:ℝ)^k := by
    have hh := hl a b
    rw [hd,norm_sub_rev] at hh
    exact (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) k)).mpr (by simpa using hh)
  change (‖g b-g a‖/(2:ℝ)^k)^2+(k:ℝ)/12 ≤ C^2 at hbound
  apply Real.sqrt_le_iff.mpr
  exact ⟨by linarith,by nlinarith⟩

end Distortion

end
end Diamond

/-- The distortion bound, with the positive-scale
bi-Lipschitz convention and the actual shortest-path distance on D_k. -/
theorem main_diamond_distortion (k : ℕ)
    (f : (Diamond.diamond k).V → FullDual Vertex) (C : ℝ)
    (hf : Diamond.EmbeddingBound k f C) :
    Real.sqrt (1+(k:ℝ)/12) ≤ C :=
  Diamond.distortion_lower main_lens k f C hf

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Main ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The space
is the full continuous dual of the specified segment-norm completion, not the
coordinate completion in place of that dual. -/
theorem main_theorem :
    (¬FiniteDimensional ℝ (FullDual Vertex)) ∧
    TopologicalSpace.SeparableSpace (FullDual Vertex) ∧
    Reflexive (FullDual Vertex) ∧
    (∀ (α β : ℝ) (R : EquivalentNorm (FullDual Vertex) α β), ¬IsAUC R.N) ∧
    (∀ t : ℝ, 0 < t →
      Real.sqrt (1+t^2/12)-1 ≤ averageModulus (FullDual Vertex) norm t) ∧
    (∀ (k : ℕ) (f : (Diamond.diamond k).V → FullDual Vertex) (C : ℝ),
      Diamond.EmbeddingBound k f C → Real.sqrt (1+(k:ℝ)/12) ≤ C) := by
  exact ⟨infiniteDimensional_main_fullDual, separable_main_fullDual,
    reflexive_main_fullDual, fun _ _ R => main_no_equivalent_AUC R,
    main_average_modulus, main_diamond_distortion⟩

end

end ForestSpace

end OAI

-- ---- mission target ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem solution :
    (¬FiniteDimensional ℝ (FullDual Vertex)) ∧
    TopologicalSpace.SeparableSpace (FullDual Vertex) ∧
    Reflexive (FullDual Vertex) ∧
    (∀ (α β : ℝ) (R : EquivalentNorm (FullDual Vertex) α β), ¬IsAUC R.N) ∧
    (∀ t : ℝ, 0 < t →
      Real.sqrt (1+t^2/12)-1 ≤ averageModulus (FullDual Vertex) norm t) ∧
    (∀ (k : ℕ) (f : (Diamond.diamond k).V → FullDual Vertex) (C : ℝ),
      Diamond.EmbeddingBound k f C → Real.sqrt (1+(k:ℝ)/12) ≤ C) := by
  first
    | exact OAI.ForestSpace.main_theorem
    | (apply OAI.ForestSpace.main_theorem <;> assumption)
    | (intros; apply OAI.ForestSpace.main_theorem <;> assumption)
