-- Prove2me | solution 1 for OAI.DiscreteFree.source_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T11:13:35.274772+00:00
-- url     : https://prove2.me/submissions/76a3f26a-1cc5-40be-8f4a-6ca0698e8f26

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Main.lean:L92-L92
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.DiscreteFree.source_endpoints.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_DiscreteFree_source_endpoints) verbatim and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor
import Definitions.Def_OAI_Analysis_LipschitzFree_Wedge
import Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge
import Definitions.Def_OAI_Analysis_LipschitzFree_WedgeApproximation
import Definitions.Def_OAI_Analysis_LipschitzFree_Main
import Theorems.Thm_OAI_DiscreteFree_BlockConstruction_finite_support_impossible
import Theorems.Thm_OAI_DiscreteFree_MetricWedge_discrete
import Theorems.Thm_OAI_DiscreteFree_MetricWedge_hasAP
import Theorems.Thm_OAI_DiscreteFree_MetricWedge_separated
import Theorems.Thm_OAI_DiscreteFree_finite_support_reduction
import Theorems.Thm_OAI_DiscreteFree_hasBAP_of_contractive_retract

-- ---- from OAI.Analysis.LipschitzFree.PortGraphs ----
namespace OAI

/-!
# Port graphs, reduced walks, and capped-distance labels
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree
open scoped BigOperators Classical

namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)

theorem walk_append (x : X) (u v : List D) :
    G.walk x (u ++ v) = G.walk (G.walk x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih _

theorem near_self (n : ℕ) (x : X) : G.Near n x x := ⟨[], by simp, rfl⟩

end PortGraph

namespace BoundedWords
variable {D : Type*}

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

end PortGraph
end DiscreteFree

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Parameters ----
namespace OAI

/-!
# Quantitative block parameters and strict variation bounds
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.BlockParameters

theorem B_formula (p : ℕ) : (B p : ℝ) = blockBound p := by
  norm_num [B,D,K,R,L,blockBound]
  ring

end DiscreteFree.BlockParameters

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.BoxLabels ----
namespace OAI

/-!
# Finite box labels with the supremum metric
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical

namespace BoxLabel
variable {C : Type*} [Fintype C] {cap : ℕ}

theorem distance_bound (a b : BoxLabel C cap) : distance a b ≤ cap := by
  rw [distance_le_iff]
  intro i
  have ha := (a i).isLt
  have hb := (b i).isLt
  unfold Nat.dist
  omega

end BoxLabel
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.MetricClosure ----
namespace OAI

/-!
# Integer shortest-path metrics and Lipschitz descent
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.NatMetricClosure
open scoped Classical

variable {X : Type*} (w : X → X → ℕ)

theorem path_relation (P : ℕ → X → X → Prop)
    (hedge : ∀ x y, P (w x y) x y)
    (htrans : ∀ a b x y z, P a x y → P b y z → P (a+b) x z)
    (x y : X) : P (distance w x y) x y := by
  have hcost (u : List X) (a : X) : P (cost w a y u) a y := by
    induction u generalizing a with
    | nil => exact hedge a y
    | cons b u ih => exact htrans _ _ _ _ _ (hedge a b) (ih b)
  obtain ⟨u, hu⟩ := exists_shortest w x y
  simpa [hu] using hcost u x

end DiscreteFree.NatMetricClosure

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.MetricBlock ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Metric blocks obtained by adjoining finite label anchors
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

variable [Fact (0 < R)]

theorem dist_eq (u v : Point G color cap R) : dist u v =
    (NatMetricClosure.distance (weight G color cap R) u v : ℝ) := rfl

theorem weight_bound (u v : Point G color cap R) : weight G color cap R u v ≤ 4*R+cap := by
  have hR : 0 < R := Fact.out
  by_cases h : u = v
  · simp [h]
  · cases u <;> cases v <;> simp only [weight, ite_eq_right h]
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · exact (Nat.add_le_add_left (BoxLabel.distance_bound _ _) _).trans (by omega)

theorem diameter_bound (u v : Point G color cap R) : dist u v ≤ (4*R+cap : ℕ) := by
  rw [dist_eq]
  exact_mod_cast (NatMetricClosure.distance_le _ u v).trans (weight_bound G color cap R u v)

end DiscreteFree.MetricBlock
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Attachment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Attachment-length estimates and label compatibility
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical
namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)
theorem near_trans {m n : ℕ} {x y z : X} (hxy : G.Near m x y) (hyz : G.Near n y z) :
    G.Near (m+n) x z := by
  obtain ⟨u, hu, rfl⟩ := hxy
  obtain ⟨v, hv, rfl⟩ := hyz
  exact ⟨u++v, by simpa only [List.length_append] using Nat.add_le_add hu hv, G.walk_append _ _ _⟩
end PortGraph

namespace MetricBlock
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

omit [Fintype C] in
theorem short_self (n : ℕ) (u : Point G color cap R) : ShortRelation G color cap R n u u := by
  cases u with
  | inl x => exact G.near_self n x
  | inr a => rfl

omit [Fintype C] in
theorem short_trans {m n : ℕ} {u v w : Point G color cap R}
    (huv : ShortRelation G color cap R m u v) (hvw : ShortRelation G color cap R n v w) :
    ShortRelation G color cap R (m+n) u w := by
  cases u <;> cases v <;> cases w <;> simp only [ShortRelation] at *
  · exact G.near_trans huv hvw
  · exact huv.trans hvw

theorem short_edge (hR : 0 < R) (u v : Point G color cap R)
    (h : weight G color cap R u v < R) :
    ShortRelation G color cap R (weight G color cap R u v) u v := by
  by_cases he : u = v
  · subst v
    exact short_self G color cap R _ u
  · cases u with
    | inl x =>
      cases v with
      | inl y =>
        simp only [weight, ite_eq_right he] at h ⊢
        split_ifs at h ⊢ with ha
        · obtain ⟨e, rfl⟩ := ha
          exact ⟨[e], by simp, rfl⟩
        · omega
      | inr a =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
    | inr a =>
      cases v with
      | inl x =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
      | inr b =>
        simp only [weight, ite_eq_right he] at h
        omega

theorem short_distance (hR : 0 < R) (u v : Point G color cap R)
    (h : NatMetricClosure.distance (weight G color cap R) u v < R) :
    ShortRelation G color cap R (NatMetricClosure.distance (weight G color cap R) u v) u v := by
  have hp := NatMetricClosure.path_relation (weight G color cap R)
    (fun n x y => n < R → ShortRelation G color cap R n x y)
    (fun x y => short_edge G color cap R hR x y)
    (by
      intro a b x y z hxy hyz hab
      exact short_trans G color cap R (hxy (by omega)) (hyz (by omega))) u v
  exact hp h

variable [Fintype D]

variable [Fact (0 < R)]

end MetricBlock
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.BlockObstruction ----
namespace OAI

/-!
# Signed finite-rank obstruction on countable bounded metric blocks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.BlockConstruction
open scoped Classical BigOperators
open BlockParameters

theorem base_mem (p : ℕ) : base p ∈ anchors p :=
  Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

variable (p : ℕ) [Fact (0 < R p)]

theorem diameter (x y : Block p) : dist x y ≤ (B p : ℝ) :=
  MetricBlock.diameter_bound (graph p) (color p) (D p) (R p) x y

theorem obstruction (hp : 1 ≤ p)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hfin : Module.Finite ℝ (LinearMap.range T.toLinearMap)) (hn : ‖T‖ ≤ (p : ℝ)) :
    ∃ a ∈ anchors p, (1/2 : ℝ) ≤ ‖T (delta (base p) a) - delta (base p) a‖ := by
  by_contra h
  have he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1/2 := by
    simpa only [not_exists,not_and,not_le] using h
  obtain ⟨S,T₁,ho,_,hT,hfixed,hanchor⟩ := finite_support_reduction (base p) (separation p)
    (B p) p (Nat.cast_nonneg _) (by exact_mod_cast hp) (fun x => diameter p x (base p))
    (anchors p) T hfin hn he
  exact finite_support_impossible p hp S ho T₁ hT hfixed hanchor

theorem original_radius (hp : 1 ≤ p) (x : Vertices p) :
    (R p : ℝ) ≤ dist (MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x) (base p) := by
  by_contra h
  have hh : NatMetricClosure.distance (MetricBlock.weight (graph p) (color p) (D p) (R p))
      (MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x) (base p) < R p := by
    have hlt := lt_of_not_ge h
    rw [MetricBlock.dist_eq] at hlt
    exact_mod_cast hlt
  exact MetricBlock.short_distance (graph p) (color p) (D p) (R p) (R_pos hp) _ _ hh

end DiscreteFree.BlockConstruction

namespace DiscreteFree

theorem blocks_proved : BlockStatement := by
  intro p hp
  let : Fact (0 < BlockParameters.R p) := ⟨BlockParameters.R_pos hp⟩
  refine ⟨BlockConstruction.Block p,inferInstance,BlockConstruction.base p,inferInstance,
    BlockConstruction.separation p,?_,BlockConstruction.anchors p,BlockConstruction.base_mem p,
    fun T hT hn => BlockConstruction.obstruction p hp T hT hn⟩
  intro x y
  simpa only [BlockParameters.B_formula] using BlockConstruction.diameter p x y
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.BlockBAP ----
namespace OAI

/-!
# Finite anchor obstructions exclude bounded approximation constants
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree

theorem not_hasBAP_of_finite_obstruction {M : Type*} [MetricSpace M] (o : M)
    (A : Finset M) (p ε : ℝ) (hε : 0 < ε)
    (hobs : ∀ T : FreeSpace o →L[ℝ] FreeSpace o,
      Module.Finite ℝ (LinearMap.range T.toLinearMap) → ‖T‖ ≤ p →
        ∃ a ∈ A, ε ≤ ‖T (delta o a) - delta o a‖)
    (Λ : ℝ) (hΛ : Λ ≤ p) : ¬ HasBAP (FreeSpace o) Λ := by
  intro h
  let C := (delta o) '' (A : Set M)
  have hC : IsCompact C := (A.finite_toSet.image (delta o)).isCompact
  obtain ⟨T,hT,hTnorm,η,hη,he⟩ := h C hC ε hε
  obtain ⟨a,ha,herr⟩ := hobs T hT (hTnorm.trans hΛ)
  have herror := he (delta o a) ⟨a,ha,rfl⟩
  linarith

namespace BlockConstruction
open BlockParameters
variable (p : ℕ) [Fact (0 < R p)]

theorem noBAP (hp : 1 ≤ p) (Λ : ℝ) (hΛ : Λ ≤ (p : ℝ)) :
    ¬ HasBAP (FreeSpace (base p)) Λ :=
  not_hasBAP_of_finite_obstruction (base p) (anchors p) p (1/2) (by norm_num)
    (fun T => obstruction p hp T) Λ hΛ

end BlockConstruction
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Functor ----
namespace OAI

/-!
# Contractive linearization of pointed Lipschitz maps
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

theorem freeMap_bound (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : ‖freeMap o b f hbase hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖u.val.comp (lipPullback o b f hbase hf)‖ ≤ 1*‖u‖
  calc
    _ ≤ ‖u.val‖*‖lipPullback o b f hbase hf‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖u.val‖*1 := mul_le_mul_of_nonneg_left (lipPullback_bound o b f hbase hf) (norm_nonneg _)
    _ = _ := by simp; rfl

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.WedgeApproximation ----
namespace OAI

/-!
# Compact-uniform approximation on wedges and contractive BAP inheritance
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical BigOperators

section OperatorTools
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

end OperatorTools

namespace MetricWedge
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

theorem inclusionL_bound (n : ℕ) : ‖inclusionL M o n‖ ≤ 1 := freeMap_bound ..
theorem retractionL_bound (n : ℕ) : ‖retractionL M o n‖ ≤ 1 := freeMap_bound ..

end MetricWedge
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Main ----
namespace OAI

/-!
# A countable separated free space with AP and no finite BAP constant
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MainConstruction
open scoped Classical

theorem component_separated (n : ℕ) (x y : Piece n) (h : x ≠ y) : 1 ≤ dist x y :=
  BlockConstruction.separation (n+1) x y h

theorem separated (x y : Space) (h : x ≠ y) : 1 ≤ dist x y :=
  MetricWedge.separated Piece pieceBase component_separated x y h

theorem unbounded : ¬ Bornology.IsBounded (Set.univ : Set Space) := by
  intro h
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_ball base).mp h
  obtain ⟨n,hn⟩ := exists_nat_gt r
  let x := MetricBlock.ofVertex (BlockConstruction.graph (n+1)) (BlockConstruction.color (n+1))
    (BlockParameters.D (n+1)) (BlockParameters.R (n+1)) (BlockConstruction.baseVertex (n+1))
  have hdist : dist (MetricWedge.inclusion Piece pieceBase n x) base = dist x (pieceBase n) := by
    rw [show base = MetricWedge.inclusion Piece pieceBase n (pieceBase n) from (MetricWedge.inclusion_base Piece pieceBase n).symm]
    exact (MetricWedge.inclusion_isometry Piece pieceBase n).dist_eq _ _
  have hu : dist (MetricWedge.inclusion Piece pieceBase n x) base < r := hr (Set.mem_univ _)
  rw [hdist] at hu
  have hl := BlockConstruction.original_radius (n+1) (by omega) (BlockConstruction.baseVertex (n+1))
  have hR : (n : ℝ) ≤ (BlockParameters.R (n+1) : ℝ) := by
    exact_mod_cast (show n ≤ BlockParameters.R (n+1) by
      dsimp [BlockParameters.R,BlockParameters.L]
      omega)
  change (BlockParameters.R (n+1) : ℝ) ≤ dist x (pieceBase n) at hl
  linarith

theorem nonproper : ¬ ProperSpace Space := by
  intro h
  let : ProperSpace Space := h
  let : DiscreteTopology Space := MetricWedge.discrete Piece pieceBase component_separated
  have hfin := (isCompact_closedBall base (BlockParameters.B 1 : ℝ)).finite_of_discrete
  have hs : Set.range (MetricWedge.inclusion Piece pieceBase 0) ⊆
      Metric.closedBall base (BlockParameters.B 1 : ℝ) := by
    rintro y ⟨x,rfl⟩
    change dist (MetricWedge.inclusion Piece pieceBase 0 x) base ≤ (BlockParameters.B 1 : ℝ)
    rw [show base = MetricWedge.inclusion Piece pieceBase 0 (pieceBase 0) from (MetricWedge.inclusion_base Piece pieceBase 0).symm]
    rw [(MetricWedge.inclusion_isometry Piece pieceBase 0).dist_eq]
    exact BlockConstruction.diameter 1 x (pieceBase 0)
  exact (Set.infinite_range_of_injective (MetricWedge.inclusion_isometry Piece pieceBase 0).injective) (hfin.subset hs)

theorem hasAP : HasAP (FreeSpace base) :=
  MetricWedge.hasAP Piece pieceBase component_separated
    (fun n => (BlockParameters.B (n+1) : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun n x => BlockConstruction.diameter (n+1) x (pieceBase n))

theorem noBAP (Λ : ℝ) : ¬ HasBAP (FreeSpace base) Λ := by
  intro h
  obtain ⟨n,hn⟩ := exists_nat_ge Λ
  have hblock := hasBAP_of_contractive_retract (MetricWedge.inclusionL Piece pieceBase n)
    (MetricWedge.retractionL Piece pieceBase n) (MetricWedge.inclusionL_bound Piece pieceBase n)
    (MetricWedge.retractionL_bound Piece pieceBase n) (MetricWedge.retractionL_inclusionL Piece pieceBase n) Λ h
  exact BlockConstruction.noBAP (n+1) (by omega) Λ
    (by exact hn.trans (by exact_mod_cast Nat.le_succ n)) hblock

end DiscreteFree.MainConstruction

namespace DiscreteFree

theorem main_proved : MainStatement :=
  ⟨MainConstruction.Space,inferInstance,MainConstruction.base,inferInstance,
    MainConstruction.separated,MainConstruction.unbounded,MainConstruction.nonproper,
    MainConstruction.hasAP,fun Λ _ => MainConstruction.noBAP Λ⟩

end DiscreteFree
end

namespace DiscreteFree

theorem source_endpoints : BlockStatement ∧ MainStatement := ⟨blocks_proved, main_proved⟩

end DiscreteFree

end

end OAI

-- ---- mission target ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
variable {M : Type*} [MetricSpace M]

theorem solution : BlockStatement ∧ MainStatement := by
  first
    | exact OAI.DiscreteFree.source_endpoints
    | (apply OAI.DiscreteFree.source_endpoints <;> assumption)
    | (intros; apply OAI.DiscreteFree.source_endpoints <;> assumption)
