-- Prove2me | solution 1 for OAI.DiscreteFree.MetricWedge.hasAP
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T11:11:55.495586+00:00
-- url     : https://prove2.me/submissions/c48e80e1-5543-4d28-976b-e055c99821dd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean:L156-L177
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.MetricWedge.hasAP. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_DiscreteFree_MetricWedge_separated
import Theorems.Thm_OAI_DiscreteFree_projection_compact
import Theorems.Thm_OAI_DiscreteFree_supportProjection_bound

-- ---- from OAI.Analysis.LipschitzFree.CompactApproximation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Compact-uniform approximation on bounded separated spaces
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

theorem evaluation_span_dense : Dense (Submodule.span ℝ (Set.range (delta o)) : Set (FreeSpace o)) := by
  let S := Submodule.span ℝ (Set.range (delta o))
  have hu : ∀ u : FreeSpace o, u ∈ S.topologicalClosure :=
    freeSpace_induction (fun u => u ∈ S.topologicalClosure)
      (Submodule.isClosed_topologicalClosure S) S.topologicalClosure.zero_mem
      (fun _ _ => S.topologicalClosure.add_mem)
      (fun c _ h => S.topologicalClosure.smul_mem c h)
      (fun x => Submodule.le_topologicalClosure S (Submodule.subset_span ⟨x, rfl⟩))
  intro u
  exact hu u

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem supportProjection_range (F : Finset M) :
    LinearMap.range (supportProjection o sep F).toLinearMap ≤
      Submodule.span ℝ ((delta o) '' (F : Set M)) := by
  rintro u ⟨v, rfl⟩
  change supportProjection o sep F v ∈ _
  rw [supportProjection_apply]
  exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, hj, rfl⟩))

theorem supportProjection_finiteRank (F : Finset M) :
    Module.Finite ℝ (LinearMap.range (supportProjection o sep F).toLinearMap) :=
  (Submodule.fg_iff_finiteDimensional _).mp
    ((Submodule.fg_span (F.finite_toSet.image (delta o))).of_le (supportProjection_range o sep F))

variable (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)

include sep hB hb in

theorem bounded_separated_hasBAP : HasBAP (FreeSpace o) (2*B) := by
  intro C hC ε hε
  obtain ⟨F, hF⟩ := projection_compact o sep B hB hb C hC (ε/2) (by positivity)
  exact ⟨supportProjection o sep F, supportProjection_finiteRank o sep F,
    supportProjection_bound o sep F B hB hb, ε/2, by linarith,
    fun u hu => (hF F le_rfl u hu).le⟩

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

-- ---- from OAI.Analysis.LipschitzFree.RetainedWedge ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Separated metric wedges and bounded finite-component retracts
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricWedge
open scoped Classical BigOperators
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

theorem retained_separated (F : Finset ℕ)
    (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (x y : Retained M o F) (hxy : x ≠ y) : 1 ≤ dist x y :=
  separated M o sep x.val y.val (fun h => hxy (Subtype.ext h))

theorem retained_radius (F : Finset ℕ) (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n (x : M n), dist x (o n) ≤ B n) (x : Retained M o F) :
    dist x (retainedBase M o F) ≤ ∑ n ∈ F, B n := by
  rcases x with ⟨(_ | ⟨n,x⟩),hx⟩
  · change (0 : ℝ) ≤ ∑ n ∈ F, B n
    exact Finset.sum_nonneg (fun n _ => hB n)
  · have hn : n ∈ F := by
      by_contra hn
      simp [retain,hn] at hx
    change dist x.val (o n) ≤ ∑ i ∈ F, B i
    exact (hb n x.val).trans (Finset.single_le_sum (fun i _ => hB i) hn)

end DiscreteFree.MetricWedge
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

theorem contraction_norm (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (u : E) : ‖T u‖ ≤ ‖u‖ := by
  exact (T.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg u))

theorem finiteRank_sandwich (I : G →L[ℝ] H) (T : F →L[ℝ] G) (P : E →L[ℝ] F)
    (hT : Module.Finite ℝ (LinearMap.range T.toLinearMap)) :
    Module.Finite ℝ (LinearMap.range ((I.comp T).comp P).toLinearMap) := by
  have hfg := ((Submodule.fg_iff_finiteDimensional _).mpr hT).map I.toLinearMap
  apply (Submodule.fg_iff_finiteDimensional _).mp
  apply hfg.of_le
  rintro v ⟨u,rfl⟩
  exact ⟨T (P u),⟨P u,rfl⟩,rfl⟩

end OperatorTools

namespace MetricWedge
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

theorem retainL_bound (F : Finset ℕ) : ‖retainL M o F‖ ≤ 1 := freeMap_bound ..

theorem retain_span_fixed {u : FreeSpace (base M o)}
    (hu : u ∈ Submodule.span ℝ (Set.range (delta (base M o)))) :
    ∃ F : Finset ℕ, ∀ G : Finset ℕ, F ⊆ G → retainL M o G u = u := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x,rfl⟩ := hu
    rcases x with _ | ⟨n,x⟩
    · refine ⟨∅,fun G _ => ?_⟩
      change retainL M o G (delta (base M o) (base M o)) = delta (base M o) (base M o)
      rw [delta_base,map_zero]
    · refine ⟨{n},fun G hG => ?_⟩
      have hn : n ∈ G := hG (Finset.mem_singleton_self _)
      change delta (base M o) (retain M o G (some ⟨n,x⟩ : Point M o)) =
        delta (base M o) (some ⟨n,x⟩ : Point M o)
      congr 1
      simp [retain,hn]; rfl
  | zero => exact ⟨∅,fun _ _ => map_zero _⟩
  | add u v hu hv ihu ihv =>
    obtain ⟨F,hF⟩ := ihu
    obtain ⟨G,hG⟩ := ihv
    exact ⟨F∪G,fun K hK => by rw [map_add,hF K (Finset.subset_union_left.trans hK),hG K (Finset.subset_union_right.trans hK)]⟩
  | smul c u hu ih =>
    obtain ⟨F,hF⟩ := ih
    exact ⟨F,fun G hG => by rw [map_smul,hF G hG]⟩

theorem retain_error_bound (F : Finset ℕ) (u : FreeSpace (base M o)) :
    ‖retainL M o F u-u‖ ≤ 2*‖u‖ := by
  calc
    _ ≤ ‖retainL M o F u‖ + ‖u‖ := norm_sub_le _ _
    _ ≤ ‖u‖ + ‖u‖ := add_le_add (contraction_norm _ (retainL_bound M o F) u) le_rfl
    _ = _ := by ring

theorem retain_pointwise (u : FreeSpace (base M o)) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ℕ, ∀ G : Finset ℕ, F ⊆ G → ‖retainL M o G u-u‖ < ε := by
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp (evaluation_span_dense (base M o) u) (ε/2) (by positivity)
  obtain ⟨F,hF⟩ := retain_span_fixed M o hv
  refine ⟨F,fun G hG => ?_⟩
  calc
    ‖retainL M o G u-u‖ = ‖retainL M o G (u-v)-(u-v)‖ := by rw [map_sub,hF G hG]; congr 1; abel
    _ ≤ 2*‖u-v‖ := retain_error_bound M o G (u-v)
    _ < ε := by rw [dist_eq_norm] at huv; linarith

theorem retain_compact (C : Set (FreeSpace (base M o))) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ℕ, ∀ G : Finset ℕ, F ⊆ G → ∀ u ∈ C, ‖retainL M o G u-u‖ < ε := by
  obtain ⟨t,_,ht,hcover⟩ := hC.finite_cover_balls (e := ε/4) (by positivity)
  choose F hF using (fun z : FreeSpace (base M o) => retain_pointwise M o z (ε/2) (by positivity))
  refine ⟨ht.toFinset.biUnion F,fun G hG u hu => ?_⟩
  obtain ⟨z,hz,huz⟩ := Set.mem_iUnion₂.mp (hcover hu)
  have hze := hF z G ((Finset.subset_biUnion_of_mem F (ht.mem_toFinset.mpr hz)).trans hG)
  have huz' : ‖u-z‖ < ε/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using huz
  calc
    ‖retainL M o G u-u‖ = ‖(retainL M o G (u-z)-(u-z))+(retainL M o G z-z)‖ := by
      rw [map_sub]; congr 1; abel
    _ ≤ ‖retainL M o G (u-z)-(u-z)‖ + ‖retainL M o G z-z‖ := norm_add_le _ _
    _ ≤ 2*‖u-z‖ + ‖retainL M o G z-z‖ := add_le_add (retain_error_bound M o G (u-z)) le_rfl
    _ < ε := by linarith

theorem embedL_bound (F : Finset ℕ) : ‖embedL M o F‖ ≤ 1 := freeMap_bound ..

theorem hasAP (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hb : ∀ n (x : M n), dist x (o n) ≤ B n) :
    HasAP (FreeSpace (base M o)) := by
  intro C hC ε hε
  obtain ⟨F,hF⟩ := retain_compact M o C hC (ε/4) (by positivity)
  let P := collapseL M o F
  let I := embedL M o F
  have hAP := bounded_separated_hasBAP (retainedBase M o F) (retained_separated M o F sep)
    (∑ n ∈ F, B n) (Finset.sum_nonneg (fun n _ => hB n)) (retained_radius M o F B hB hb)
  obtain ⟨U,hU,_,η,hη,he⟩ := hAP (P '' C) (hC.image P.continuous) (ε/4) (by positivity)
  let T := (I.comp U).comp P
  refine ⟨T,finiteRank_sandwich I U P hU,ε/2,by linarith,?_⟩
  intro u hu
  have hretain : I (P u) = retainL M o F u := congrArg (fun A : FreeSpace (base M o) →L[ℝ] FreeSpace (base M o) => A u) (embedL_collapseL M o F)
  have he' := he (P u) ⟨u,hu,rfl⟩
  have htail := hF F le_rfl u hu
  calc
    ‖T u-u‖ = ‖I (U (P u)-P u)+(retainL M o F u-u)‖ := by
      rw [map_sub,← hretain]; dsimp [T]; congr 1; abel
    _ ≤ ‖I (U (P u)-P u)‖ + ‖retainL M o F u-u‖ := norm_add_le _ _
    _ ≤ ‖U (P u)-P u‖ + ‖retainL M o F u-u‖ := add_le_add (contraction_norm I (embedL_bound M o F) _) le_rfl
    _ ≤ ε/2 := by linarith

end MetricWedge
end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricWedge
open scoped BigOperators ENNReal
open scoped Classical BigOperators


theorem solution.{u} : type_of% @_root_.OAI.DiscreteFree.MetricWedge.hasAP.{u} := @_root_.OAI.DiscreteFree.MetricWedge.hasAP.{u}
