-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.boundary_source_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:23:09.84376+00:00
-- url     : https://prove2.me/submissions/187c533a-cc11-4544-8697-c0e5ab52ff49

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryFlux.lean:L22-L41
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.boundary_source_weight_bound. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_admissiblyConvex_filled
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_boundary_collision_cancellation
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_convex_excursion_turn_bound

-- ---- from OAI.Combinatorics.HoneycombCorridor.Basic ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem stepWeight_sum : stepWeight true + stepWeight false = 1 := by
  have hc : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt critical_cos_pos
  simp only [stepWeight, turnAngle, Bool.false_eq_true, ite_false, ite_true]
  have ht : (3 / 8 : ℝ) * (Real.pi / 3) = Real.pi / 8 := by ring
  have hf : (3 / 8 : ℝ) * -(Real.pi / 3) = -(Real.pi / 8) := by ring
  rw [ht, hf, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  calc
    _ = ((criticalActivity * (2 * Real.cos (Real.pi / 8)) : ℝ) : ℂ) := by
      push_cast
      ring
    _ = 1 := by
      have hw : criticalActivity * (2 * Real.cos (Real.pi / 8)) = 1 :=
        inv_mul_cancel₀ (mul_ne_zero (by norm_num) hc)
      rw [hw]
      norm_num

theorem sum_cons_image (s : Finset (List Bool)) (b : Bool) :
    ∑ w ∈ s.image (List.cons b), wordWeight w =
      stepWeight b * ∑ w ∈ s, wordWeight w := by
  rw [Finset.sum_image]
  · simp only [wordWeight_cons, Finset.mul_sum]
  · intro a ha c hc hac
    exact List.cons.inj hac |>.2

theorem disjoint_cons_images (s t : Finset (List Bool)) :
    Disjoint (s.image (List.cons true)) (t.image (List.cons false)) := by
  apply Finset.disjoint_left.mpr
  intro w hs ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp ht
  exact Bool.false_ne_true (List.cons.inj heq).1

theorem leaf_balance (D : Finset Vertex) (g : Germ) :
    ∑ w ∈ leaves D g, wordWeight w = 1 := by
  induction D using Finset.strongInductionOn generalizing g with
  | _ D ih =>
      rw [leaves]
      by_cases hg : g.1 ∈ D
      · simp only [hg, ite_true]
        rw [Finset.sum_union (disjoint_cons_images _ _), sum_cons_image, sum_cons_image]
        have hers : D.erase g.1 ⊂ D := Finset.erase_ssubset hg
        rw [ih _ hers _, ih _ hers _]
        simpa only [mul_one] using stepWeight_sum
      · simp [hg]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Excursions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem exit_add_collision (D : Finset Vertex) (g : Germ) :
    exitSum D g + collisionSum D g = 1 := by
  classical
  unfold exitSum collisionSum
  rw [← Finset.sum_add_distrib]
  convert leaf_balance D g using 1
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ht : (terminalGerm g w).1 ∈ D <;> simp [ht]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.VisitRecursion ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem wordWeight_re (w : List Bool) : (wordWeight w).re =
    criticalActivity ^ w.length * Real.cos (Real.pi / 8 * (turnUnits w : ℝ)) := by
  rw [wordWeight_turnUnits]
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]

theorem bounded_turn_cos (m : ℤ) (hm : -3 ≤ m ∧ m ≤ 3) :
    Real.cos (3 * Real.pi / 8) ≤ Real.cos (Real.pi / 8 * (m : ℝ)) := by
  have hlow : -(3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
  have hhigh : (m : ℝ) ≤ 3 := by exact_mod_cast hm.2
  have habs : |Real.pi / 8 * (m : ℝ)| ≤ 3 * Real.pi / 8 := by
    apply abs_le.mpr
    constructor <;> nlinarith [Real.pi_pos]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi / 8 * (m : ℝ)))
    (show 3 * Real.pi / 8 ≤ Real.pi by linarith [Real.pi_pos]) habs
  simpa only [Real.cos_abs] using h

theorem convex_wordWeight_re_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    Real.cos (3 * Real.pi / 8) * criticalActivity ^ e.2.length ≤ (wordWeight e.2).re := by
  rw [wordWeight_re,mul_comm (Real.cos _)]
  exact mul_le_mul_of_nonneg_left
    (bounded_turn_cos (turnUnits e.2) (convex_excursion_turn_bound D hD e he))
    (pow_nonneg criticalActivity_pos.le _)

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryFlux ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem boundary_source_flux (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    (∑ w ∈ sourceExits D g, wordWeight w) = 1 := by
  have h := exit_add_collision D g
  rw [(boundary_collision_cancellation D g hD hg).1,add_zero] at h
  simpa only [sourceExits,Finset.sum_filter,exitSum] using h

theorem boundary_source_weight_bound (D : Finset Vertex) (g : Germ)
    (hD : AdmissiblyConvex D) (hg : g.1 ∈ D) (hg' : (reverseGerm g).1 ∉ D) :
    (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤
      (Real.cos (3 * Real.pi / 8))⁻¹ := by
  have hflux := boundary_source_flux D g (admissiblyConvex_filled D hD) hg'
  have hreal := congrArg Complex.re hflux
  rw [Complex.re_sum,Complex.one_re] at hreal
  have hlower : Real.cos (3 * Real.pi / 8) *
      (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤ 1 := by
    rw [← hreal,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
    exact convex_wordWeight_re_lower D hD (g,w) ⟨hg,hg',hs,ht⟩
  have hpos : 0 < Real.cos (3 * Real.pi / 8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hpos).mpr
  rwa [mul_comm]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.boundary_source_weight_bound := @_root_.OAI.PolynomialVacuumBridge.Corridor.boundary_source_weight_bound
