-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.rightIndexMass_geometric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:34:26.137272+00:00
-- url     : https://prove2.me/submissions/92d50c62-2e16-4b9e-9d6c-43d760df4ef2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/StripDecay.lean:L107-L122
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.rightIndexMass_geometric. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_admissiblyConvex_filled
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_boundary_collision_cancellation
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_boundary_source_weight_bound
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_convex_excursion_turn_bound
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_mem_lost_upperCut
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_new_upperCut_turn
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_separated_rays_contract
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_upperCut_convex

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

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.ConvexCuts ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem upperCut_subset (D : Finset Vertex) (k : Fin 3) (A : ℤ) : upperCut D k A ⊆ D :=
  Finset.filter_subset _ _

theorem flux_subtraction (D E : Finset Vertex) (g : Germ)
    (hD : Filled D) (hE : Filled E)
    (hgD : (reverseGerm g).1 ∉ D) (hgE : (reverseGerm g).1 ∉ E) :
    (∑ w ∈ sourceExits D g \ sourceExits E g, wordWeight w) =
      ∑ w ∈ sourceExits E g \ sourceExits D g, wordWeight w := by
  apply sub_eq_zero.mp
  rw [Finset.sum_sdiff_sub_sum_sdiff,boundary_source_flux D g hD hgD,
    boundary_source_flux E g hE hgE,sub_self]

theorem bottomSource_outside_of_strip (h : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) : (reverseGerm bottomSource).1 ∉ D := by
  intro hv
  have hh := (hstrip _ hv).1
  norm_num [bottomSource,reverseGerm,neighbor,boxIndex] at hh

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.RaySeparation ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem positiveWordMass_nonneg (S : Finset (List Bool)) : 0 ≤ positiveWordMass S :=
  Finset.sum_nonneg fun _ _ => pow_nonneg criticalActivity_pos.le _

theorem positiveWordMass_mono {S T : Finset (List Bool)} (h : S ⊆ T) :
    positiveWordMass S ≤ positiveWordMass T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => pow_nonneg criticalActivity_pos.le _)

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

theorem phasedMass_constant_turn (S : Finset (List Bool)) (m : ℤ)
    (h : ∀ w ∈ S, turnUnits w = m) :
    phasedWordMass S = (positiveWordMass S : ℂ) * phase (Real.pi/8 * (m : ℝ)) := by
  simp only [phasedWordMass,positiveWordMass,Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [wordWeight_turnUnits,h w hw,Complex.ofReal_pow]
  rfl

theorem lostCut_phases (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (A : ℤ) (hA : 0 < A) :
    (∃ b : ℝ, 0 ≤ b ∧ phasedWordMass (lostCut D 1 A) = (b : ℂ)*phase (-Real.pi/4)) ∧
    (∃ a : ℝ, 0 ≤ a ∧ phasedWordMass (lostCut D 2 A) = (a : ℂ)*phase (-Real.pi/8)) := by
  have hflux (k : Fin 3) : phasedWordMass (lostCut D k A) =
      phasedWordMass (sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :=
    flux_subtraction D _ bottomSource (admissiblyConvex_filled D hD)
      (admissiblyConvex_filled _ (upperCut_convex D hD k A)) hg'
      (fun hm => hg' (upperCut_subset D k A hm))
  constructor
  · refine ⟨positiveWordMass (sourceExits (upperCut D 1 A) bottomSource \ sourceExits D bottomSource),
      positiveWordMass_nonneg _,?_⟩
    rw [hflux 1,phasedMass_constant_turn _ (-2) (fun w hw =>
      (new_upperCut_turn D hD hg hg' A hA 1 w hw).1 rfl)]
    congr 2
    push_cast
    ring
  · refine ⟨positiveWordMass (sourceExits (upperCut D 2 A) bottomSource \ sourceExits D bottomSource),
      positiveWordMass_nonneg _,?_⟩
    rw [hflux 2,phasedMass_constant_turn _ (-1) (fun w hw =>
      (new_upperCut_turn D hD hg hg' A hA 2 w hw).2 rfl)]
    congr 2
    push_cast
    ring

theorem strip_index_bounds (h : ℕ) (v : Vertex) (hv : InStrip h v) :
    boxIndex v 1 ≤ boxIndex v 2 ∧ boxIndex v 2 ≤ boxIndex v 1 + (h : ℤ) := by
  cases v <;> simp [InStrip,boxIndex] at * <;> omega

theorem lostCut_nested (h : ℕ) (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v)
    (A : ℤ) : lostCut D 1 A ⊆ lostCut D 2 A ∧ lostCut D 2 A ⊆ lostCut D 1 (A-h) := by
  have hm (k : Fin 3) (B : ℤ) (w : List Bool) : w ∈ lostCut D k B ↔
      w ∈ sourceExits D bottomSource ∧ ∃ v ∈ traced bottomSource w, B ≤ boxIndex v k :=
    mem_lost_upperCut D bottomSource k B w
  constructor
  · intro w hw
    obtain ⟨he,v,hv,hA⟩ := (hm 1 A w).mp hw
    have hd := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := strip_index_bounds h v (hstrip v hd)
    exact (hm 2 A w).mpr ⟨he,v,hv,by omega⟩
  · intro w hw
    obtain ⟨he,v,hv,hA⟩ := (hm 2 A w).mp hw
    have hd := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := strip_index_bounds h v (hstrip v hd)
    exact (hm 1 (A-h) w).mpr ⟨he,v,hv,by omega⟩

theorem lostCut_real_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (k : Fin 3) (A : ℤ) :
    Real.cos (3*Real.pi/8)*positiveWordMass (lostCut D k A) ≤
      (phasedWordMass (lostCut D k A)).re := by
  rw [phasedWordMass,Complex.re_sum,positiveWordMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have he := (Finset.mem_sdiff.mp hw).1
  exact convex_wordWeight_re_lower D hD (bottomSource,w)
    ⟨hg,hg',(mem_sourceExits _ _ _).mp he⟩

theorem rightIndexMass_step (h : ℕ) (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hstrip : ∀ v ∈ D, InStrip h v)
    (A : ℤ) (hA : 0 < A) :
    rightIndexMass D A ≤ rayContraction * rightIndexMass D (A-h) := by
  have hout := bottomSource_outside_of_strip h D hstrip
  obtain ⟨⟨b,hb,hb'⟩,⟨a,_,ha'⟩⟩ := lostCut_phases D hD hg hout A hA
  have hn := lostCut_nested h D hstrip A
  have hc := separated_rays_contract (lostCut D 2 A) (lostCut D 1 A) hn.1
    (lostCut_real_lower D hD hg hout 1 A) a b hb ha' hb'
  exact hc.trans (mul_le_mul_of_nonneg_left (positiveWordMass_mono hn.2) rayContraction_range.1.le)

theorem rightIndexMass_total_bound (h : ℕ) (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hstrip : ∀ v ∈ D, InStrip h v) (A : ℤ) :
    rightIndexMass D A ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
  apply (positiveWordMass_mono (show lostCut D 1 A ⊆ sourceExits D bottomSource from
    Finset.sdiff_subset)).trans
  exact boundary_source_weight_bound D bottomSource hD hg (bottomSource_outside_of_strip h D hstrip)

theorem rightIndexMass_geometric (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (n : ℕ) :
    rightIndexMass D ((n : ℤ)*h) ≤ (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := by
  induction n with
  | zero => simpa using rightIndexMass_total_bound h D hD hg hstrip 0
  | succ n ih =>
    have hA : 0 < ((n+1 : ℕ) : ℤ)*(h : ℤ) := by positivity
    have hs := rightIndexMass_step h D hD hg hstrip _ hA
    have hi : ((n+1 : ℕ) : ℤ)*(h : ℤ) - h = (n : ℤ)*h := by push_cast; ring
    rw [hi] at hs
    calc
      _ ≤ rayContraction * rightIndexMass D ((n : ℤ)*h) := hs
      _ ≤ rayContraction * ((Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n) :=
        mul_le_mul_of_nonneg_left ih rayContraction_range.1.le
      _ = _ := by rw [pow_succ]; ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.rightIndexMass_geometric := @_root_.OAI.PolynomialVacuumBridge.Corridor.rightIndexMass_geometric
