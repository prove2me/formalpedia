-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.triangle_bound_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:55:27.074977+00:00
-- url     : https://prove2.me/submissions/0f363421-41ca-429e-b425-45677b497c64

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/TriangleBound.lean:L78-L138
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.triangle_bound_scale. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Peeling
import Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_inv_scale
import Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_recurrence_bound
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_EdgeProjection_crossMass_edge_sum
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_growth_mono
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_neighborhood_reduction

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

lemma scale_ge {X : ℝ} (hX : 1 ≤ X) (n : ℕ) : X ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 1 ≤ scale X n := hX.trans ih
    dsimp [scale]
    nlinarith

lemma lossRatio_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lossRatio x :=
  div_nonneg (Real.log_nonneg hx) (Real.sqrt_nonneg _)

lemma lossRatio_square {x : ℝ} (hx : 16 ≤ x) : lossRatio (x^2) ≤ (1/2) * lossRatio x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg x
  have hs : 4 ≤ Real.sqrt x := by nlinarith
  unfold lossRatio
  rw [Real.log_pow, Real.sqrt_sq hx0.le]
  norm_num only [Nat.cast_ofNat]
  apply (div_le_iff₀ hx0).2
  rw [mul_assoc, div_mul_eq_mul_div]
  have hid : (Real.log x * x) / Real.sqrt x = Real.log x * Real.sqrt x := by
    apply (div_eq_iff (by linarith : Real.sqrt x ≠ 0)).2
    nlinarith
  have hid' : Real.log x / Real.sqrt x * x = Real.log x * Real.sqrt x := by
    calc
      _ = Real.log x * x / Real.sqrt x := by ring
      _ = _ := hid
  rw [hid']
  nlinarith [mul_le_mul_of_nonneg_left hs hl]

lemma lossRatio_scale {X : ℝ} (hX : 16 ≤ X) (n : ℕ) :
    lossRatio (scale X n) ≤ (1/2 : ℝ)^n * lossRatio X := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 16 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    calc
      _ ≤ (1/2) * lossRatio (scale X n) := lossRatio_square ht
      _ ≤ (1/2) * ((1/2 : ℝ)^n * lossRatio X) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end CliqueFreeIndependence.Numerical

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

omit [Fintype V] in
lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {A B : Finset V} (hAB : A ⊆ B) :
    mass w A ≤ mass w B := sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ ↦ hw v)

omit [Fintype V] in
lemma crossMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : 0 ≤ crossMass G w A B := by
  classical
  exact sum_nonneg fun u _ ↦ sum_nonneg fun v _ ↦ by
    split_ifs
    · exact mul_nonneg (hw u) (hw v)
    · exact le_rfl

lemma crossMass_factor (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ u ∈ A, w u * mass w (B ∩ neighbors G u) := by
  classical
  unfold crossMass mass
  apply sum_congr rfl
  intro u _
  rw [← filter_mem_eq_inter]
  simp only [sum_filter, mem_neighbors, mul_sum, mul_ite, mul_zero]

lemma commonMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u v : V) :
    0 ≤ commonMass G w u v := mass_nonneg hw _

lemma commonMass_le_neighborMass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (u v : V) : commonMass G w u v ≤ neighborMass G w u := by
  classical
  exact mass_mono hw inter_subset_left

lemma edgeMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ edgeMass G w := div_nonneg (crossMass_nonneg G hw _ _) (by norm_num)

lemma triangleAt_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ triangleAt G w u :=
  sum_nonneg fun v _ ↦ mul_nonneg (hw v) (commonMass_nonneg G hw u v)

lemma triangleMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ triangleMass G w := div_nonneg
      (sum_nonneg fun u _ ↦ mul_nonneg (hw u) (triangleAt_nonneg G hw u)) (by norm_num)

lemma edgeMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    2 * edgeMass G w = ∑ u, w u * neighborMass G w u := by
  classical
  rw [edgeMass, crossMass_factor]
  simp only [univ_inter, neighborMass]
  ring

lemma triangleMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    6 * triangleMass G w = ∑ u, w u * triangleAt G w u := by
  unfold triangleMass
  ring

lemma triangleAt_le (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (u : V) :
    triangleAt G w u ≤ L * neighborMass G w u := by
  calc
    _ ≤ ∑ v ∈ neighbors G u, w v * L := sum_le_sum fun v _ ↦
      mul_le_mul_of_nonneg_left ((commonMass_le_neighborMass G hw u v).trans (hL u)) (hw v)
    _ = _ := by rw [← sum_mul]; exact mul_comm _ _

lemma triangleMass_le_of_neighborMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {L : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) :
    triangleMass G w ≤ L / 3 * edgeMass G w := by
  have h : 6 * triangleMass G w ≤ L * (2 * edgeMass G w) := by
    rw [triangleMass_eq_sum, edgeMass_eq_sum, mul_sum]
    exact sum_le_sum fun u _ ↦ by
      have := mul_le_mul_of_nonneg_left (triangleAt_le G hw hL u) (hw u)
      nlinarith
  linarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Projection ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

variable {U : Type v} [Fintype U]

lemma sum_injective_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : J → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ univ.image f, g j := (sum_image (fun _ _ _ _ h ↦ hf h)).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg hg

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

omit [Fintype V] [Fintype U] in
lemma edgeMap_injective (h : EdgeProjection H G π) : Function.Injective h.edgeMap := by
  intro e f hef
  have heq := congrArg Subtype.val hef
  have hpair := h.inj e.src e.dst f.src f.dst e.adj f.adj
    (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  exact Subtype.ext (Prod.ext hpair.1 hpair.2)

omit [Fintype V] [Fintype U] in
lemma mass_image_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset U) :
    mass w (A.image π) ≤ mass (w ∘ π) A := by
  classical
  exact sum_image_le_of_nonneg (fun _ _ ↦ hw _)

lemma crossMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset U) :
    crossMass H (w ∘ π) A B ≤ crossMass G w (A.image π) (B.image π) := by
  classical
  rw [crossMass_edge_sum, crossMass_edge_sum]
  calc
    _ ≤ ∑ e : EdgeState H,
        if (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π
          then w (h.edgeMap e).src * w (h.edgeMap e).dst else 0 := by
      apply sum_le_sum
      intro e _
      by_cases he : e.src ∈ A ∧ e.dst ∈ B
      · have hi : (h.edgeMap e).src ∈ A.image π ∧ (h.edgeMap e).dst ∈ B.image π :=
          ⟨mem_image.2 ⟨e.src, he.1, rfl⟩, mem_image.2 ⟨e.dst, he.2, rfl⟩⟩
        simp only [he, hi]
        exact le_rfl
      · simp only [he, ↓reduceIte]
        split_ifs
        · exact mul_nonneg (hw _) (hw _)
        · exact le_rfl
    _ ≤ _ := sum_injective_le h.edgeMap h.edgeMap_injective
      (fun e ↦ if e.src ∈ A.image π ∧ e.dst ∈ B.image π then w e.src * w e.dst else 0)
      (fun e ↦ by split_ifs; exact mul_nonneg (hw _) (hw _); exact le_rfl)

lemma crossBound (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {C : ℝ} (hC : 0 ≤ C) (hc : CrossBound G w C) : CrossBound H (w ∘ π) C := by
  classical
  intro x hx A B hA hB
  have hAi := mass_image_le (π := π) hw A
  have hBi := mass_image_le (π := π) hw B
  exact (h.crossMass_le hw A B).trans ((hc x hx _ _ (hAi.trans hA) (hBi.trans hB)).trans
    (mul_le_mul_of_nonneg_left (growth_mono hx (mass_nonneg hw _) (mass_nonneg (fun u ↦ hw (π u)) _) hAi) hC))

lemma edgeMass_le (h : EdgeProjection H G π) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    edgeMass H (w ∘ π) ≤ edgeMass G w := by
  classical
  have hsum : (∑ e : EdgeState H, w (π e.src) * w (π e.dst)) ≤
      ∑ e : EdgeState G, w e.src * w e.dst :=
    sum_injective_le h.edgeMap h.edgeMap_injective (fun e ↦ w e.src * w e.dst)
      (fun e ↦ mul_nonneg (hw _) (hw _))
  unfold edgeMass
  rw [crossMass_edge_sum, crossMass_edge_sum]
  simpa only [mem_univ, true_and, ↓reduceIte, Function.comp_apply] using
    div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.TriangleBound ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma splittingConstant_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ splittingConstant C := by
  unfold splittingConstant smoothingConstant entropyConstant exceptionalConstant
  positivity

/-- Uniform triangle bound at the reverse-squaring scale. -/
lemma triangle_bound_scale {C X : ℝ} (hC : 1 ≤ C) (hX : 32 ≤ X)
    (hsmall : splittingConstant C * Numerical.lossRatio X ≤ 1/4) (n : ℕ) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ u, 0 < w u) → CrossBound G w C →
      (∀ u, neighborMass G w u ≤ Real.exp (Numerical.scale X n)) →
      triangleMass G w ≤ (1+Real.exp X/3) * (2-(1/2:ℝ)^n) * edgeMass G w := by
  induction n with
  | zero =>
    intro V _ G w hw hCross hL
    have ht := triangleMass_le_of_neighborMass G (fun v ↦ (hw v).le) hL
    simp only [Numerical.scale, pow_zero] at ht ⊢
    have he := edgeMass_nonneg G (fun v ↦ (hw v).le)
    nlinarith
  | succ n ih =>
    intro V _ G w hw hCross hL
    let x := Numerical.scale X (n+1)
    let q : ℝ := (1/2:ℝ)^(n+1)
    let ε := splittingConstant C * Numerical.lossRatio x
    have hx : 32 ≤ x := hX.trans (Numerical.scale_ge (by linarith) _)
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hε0 : 0 ≤ ε := mul_nonneg (splittingConstant_nonneg hC)
      (Numerical.lossRatio_nonneg (by linarith))
    have hε : ε ≤ q/4 := by
      have hh := mul_le_mul_of_nonneg_left (Numerical.lossRatio_scale (by linarith : 16 ≤ X) (n+1))
        (splittingConstant_nonneg hC)
      have hh2 := mul_le_mul_of_nonneg_left hsmall hq0
      dsimp [ε,x,q]
      nlinarith only [hh,hh2]
    obtain ⟨U,inst,J,π,hproj,hJ,hstep⟩ := neighborhood_reduction G hw hC hCross hx
      (by linarith : ε ≤ 1) hL
    let := inst
    have hsqrt : Real.sqrt x = Numerical.scale X n := by
      dsimp [x,Numerical.scale]
      exact Real.sqrt_sq (by linarith [Numerical.scale_ge (by linarith : 1 ≤ X) n])
    rw [hsqrt] at hJ
    have hJcross := hproj.crossBound (fun v ↦ (hw v).le) (by linarith) hCross
    have hupper := ih J (w ∘ π) (fun a ↦ hw (π a)) hJcross hJ
    have hmass := hproj.edgeMass_le (fun v ↦ (hw v).le)
    have hcoeff : 0 ≤ (1+Real.exp X/3)*(2-(1/2:ℝ)^n) := by
      apply mul_nonneg (by positivity)
      have hp : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hupperG := hupper.trans (mul_le_mul_of_nonneg_left hmass hcoeff)
    have hqeq : (1/2:ℝ)^n = 2*q := by dsimp [q]; rw [pow_succ]; ring
    rw [hqeq] at hupperG
    have hinv : 1/x ≤ q/2 := by
      have hi := Numerical.inv_scale (by linarith : 2 ≤ X) (n+1)
      have hXi : 1/X ≤ 1/2 := (one_div_le_one_div_of_le (by norm_num) (by linarith))
      have hi2 := mul_le_mul_of_nonneg_left hXi hq0
      dsimp [x,q] at *
      linarith
    apply Numerical.recurrence_bound (by linarith [Real.exp_pos X] : 1 ≤ 1+Real.exp X/3)
      hq0 hq1 hε0 hε (triangleMass_nonneg G (fun v ↦ (hw v).le))
      (edgeMass_nonneg G (fun v ↦ (hw v).le)) hinv
    calc
      (1-ε)*triangleMass G w - (1/x)*edgeMass G w =
          (1-ε)*triangleMass G w - edgeMass G w/x := by ring
      _ ≤ triangleMass J (w ∘ π) := hstep
      _ ≤ _ := hupperG

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.triangle_bound_scale.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.triangle_bound_scale.{u}
