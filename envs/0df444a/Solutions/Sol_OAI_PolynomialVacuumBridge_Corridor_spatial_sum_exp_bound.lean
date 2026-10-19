-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.spatial_sum_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:40:46.605671+00:00
-- url     : https://prove2.me/submissions/219928d2-0889-4c4d-afea-8eb1664b52f3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/SpatialDecay.lean:L47-L98
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.spatial_sum_exp_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralMass
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripWindows
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_SpatialDecay

-- ---- from OAI.Combinatorics.HoneycombCorridor.RaySeparation ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem rayContraction_range : 0 < rayContraction ∧ rayContraction < 1 := by
  have hc : 0 < Real.cos (3*Real.pi/8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi/8) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hd := mul_pos hc hs
  constructor
  · exact inv_pos.mpr (by linarith)
  · apply (inv_lt_one₀ (by linarith : 0 < 1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))).mpr
    linarith

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.StripDecay ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem strip_index_bounds (h : ℕ) (v : Vertex) (hv : InStrip h v) :
    boxIndex v 1 ≤ boxIndex v 2 ∧ boxIndex v 2 ≤ boxIndex v 1 + (h : ℤ) := by
  cases v <;> simp [InStrip,boxIndex] at * <;> omega

theorem position_index (v : Vertex) :
    (position v).1 = ((boxIndex v 1 : ℝ) + (boxIndex v 2 : ℝ)) / 2 := by
  cases v <;> simp [position,boxIndex] <;> ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.LateralMass ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem tailRate_pos : 0 < tailRate := by
  have h := Real.log_neg rayContraction_range.1 rayContraction_range.2
  exact div_pos (neg_pos.mpr h) (by norm_num)

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.StripWindows ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem mem_vertexWindow (h M : ℕ) (v : Vertex) : v ∈ vertexWindow h M ↔
    -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 ≤ M ∧ InStrip h v := by
  cases v <;>
    simp [vertexWindow,Finset.mem_biUnion,Finset.mem_Icc,
      Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton,InStrip,boxIndex,
      Vertex.up.injEq,Vertex.down.injEq] <;> aesop

theorem vertexWindow_card_le (h M : ℕ) : (vertexWindow h M).card ≤ 2*(2*M+1)*h := by
  have hc := Finset.card_biUnion_le (s := (Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h))
    (t := fun p => {Vertex.up p.1 p.2,Vertex.down p.1 p.2})
  change (vertexWindow h M).card ≤ _ at hc
  have hs : (∑ p ∈ (Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h),
      ({Vertex.up p.1 p.2,Vertex.down p.1 p.2} : Finset Vertex).card) = 2*(2*M+1)*h := by
    have hcast : ((M : ℤ) + 1 + M).toNat = 2*M+1 := by omega
    simp [Finset.card_product,Int.card_Icc,Int.card_Ico,hcast]
    ring
  exact hc.trans_eq hs

theorem bounded_position_mem_window (h n : ℕ) (v : Vertex) (hv : InStrip h v)
    (hx : |(position v).1| < 2*((n : ℝ)+1)*(h+1)) :
    v ∈ vertexWindow h ((2*(n+1)+1)*(h+1)) := by
  have hi := strip_index_bounds h v hv
  have hi0 : (boxIndex v 1 : ℝ) ≤ (boxIndex v 2 : ℝ) := by exact_mod_cast hi.1
  have hi1 : (boxIndex v 2 : ℝ) ≤ (boxIndex v 1 : ℝ) + h := by exact_mod_cast hi.2
  have hab := abs_lt.mp hx
  rw [position_index] at hab
  apply (mem_vertexWindow _ _ _).mpr
  refine ⟨?_,?_,hv⟩
  · have : -(((2*(n+1)+1)*(h+1) : ℕ) : ℝ) ≤ (boxIndex v 1 : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    exact_mod_cast this
  · have : (boxIndex v 1 : ℝ) ≤ (((2*(n+1)+1)*(h+1) : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    exact_mod_cast this

theorem strip_shell_card_le (h n : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) (S : Finset Vertex) (hSD : S ⊆ D)
    (hS : ∀ v ∈ S, |(position v).1| < 2*((n : ℝ)+1)*(h+1)) :
    (S.card : ℝ) ≤ 20*((n : ℝ)+1)*((h : ℝ)+1)^2 := by
  have hsub : S ⊆ vertexWindow h ((2*(n+1)+1)*(h+1)) := by
    intro v hv
    exact bounded_position_mem_window h n v (hstrip v (hSD hv)) (hS v hv)
  have hc := (Finset.card_le_card hsub).trans (vertexWindow_card_le h _)
  have hc' : (S.card : ℝ) ≤ (2*(2*((2*(n+1)+1)*(h+1))+1)*h : ℕ) := by exact_mod_cast hc
  push_cast at hc'
  nlinarith [Nat.cast_nonneg (α := ℝ) h,Nat.cast_nonneg (α := ℝ) n,
    sq_nonneg ((h : ℝ)+1),mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (h : ℝ))]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.SpatialDecay ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

 theorem shellRatio_range : 0 < shellRatio ∧ shellRatio < 1 := by
  constructor
  · exact Real.exp_pos _
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos tailRate_pos)

theorem shellSeries_summable : Summable (fun n : ℕ => ((n : ℝ)+1)*shellRatio^n) := by
  have hn : ‖shellRatio‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos shellRatio_range.1]
    exact shellRatio_range.2
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h0 := summable_geometric_of_norm_lt_one hn
  simpa only [pow_one,add_mul,one_mul] using h1.add h0

theorem shellIndex_bounds (h : ℕ) (v : Vertex) :
    (shellIndex h v : ℝ) ≤ |(position v).1|/(2*((h : ℝ)+1)) ∧
    |(position v).1| < 2*((shellIndex h v : ℝ)+1)*((h : ℝ)+1) := by
  have hd : (0 : ℝ) < 2*((h : ℝ)+1) := by positivity
  refine ⟨Nat.floor_le (div_nonneg (abs_nonneg _) hd.le),?_⟩
  have hh := Nat.lt_floor_add_one (|(position v).1|/(2*((h : ℝ)+1)))
  have hi := (div_lt_iff₀ hd).mp hh
  dsimp [shellIndex]
  nlinarith

theorem spatial_sum_exp_bound (h : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) :
    (∑ v ∈ D, Real.exp (-tailRate*|(position v).1|/(2*(h+1)))) ≤
      spatialConstant*((h : ℝ)+1)^2 := by
  classical
  let S := D.image (shellIndex h)
  have hsplit := Finset.sum_fiberwise_of_maps_to
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩ : ∀ v ∈ D, shellIndex h v ∈ S)
    (fun v => Real.exp (-tailRate*|(position v).1|/(2*(h+1))))
  rw [← hsplit]
  have hs : ∀ n ∈ S,
      (∑ v ∈ D with shellIndex h v = n,
        Real.exp (-tailRate*|(position v).1|/(2*(h+1)))) ≤
      20*((n : ℝ)+1)*((h : ℝ)+1)^2 * shellRatio^n := by
    intro n hn
    have hc := strip_shell_card_le h n D hstrip (D.filter (fun v => shellIndex h v = n))
      (Finset.filter_subset _ _) (by
        intro v hv
        obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
        simpa only [he] using (shellIndex_bounds h v).2)
    calc
      _ ≤ ∑ v ∈ D with shellIndex h v = n, shellRatio^n := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
        rw [shellRatio,← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hl := (shellIndex_bounds h v).1
        rw [he] at hl
        have hm := mul_le_mul_of_nonpos_left hl (neg_nonpos.mpr tailRate_pos.le)
        calc
          -tailRate*|(position v).1|/(2*(h+1)) =
              -tailRate*(|(position v).1|/(2*(h+1))) := by ring
          _ ≤ -tailRate*(n : ℝ) := hm
          _ = (n : ℝ)*-tailRate := by ring
      _ = ((D.filter (fun v => shellIndex h v = n)).card : ℝ) * shellRatio^n := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (pow_nonneg shellRatio_range.1.le _)
  calc
    _ ≤ ∑ n ∈ S, 20*((n : ℝ)+1)*((h : ℝ)+1)^2 * shellRatio^n :=
      Finset.sum_le_sum hs
    _ = 20*((h : ℝ)+1)^2 * ∑ n ∈ S, ((n : ℝ)+1)*shellRatio^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 20*((h : ℝ)+1)^2 * (∑' n : ℕ, ((n : ℝ)+1)*shellRatio^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact shellSeries_summable.sum_le_tsum S
        (fun n _ => mul_nonneg (by positivity) (pow_nonneg shellRatio_range.1.le _))
    _ ≤ spatialConstant*((h : ℝ)+1)^2 := by
      dsimp [spatialConstant]
      nlinarith [sq_nonneg ((h : ℝ)+1)]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.spatial_sum_exp_bound := @_root_.OAI.PolynomialVacuumBridge.Corridor.spatial_sum_exp_bound
