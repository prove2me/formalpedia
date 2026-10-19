-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.lateralLengthMass_exp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:42:48.414785+00:00
-- url     : https://prove2.me/submissions/d1e62b57-6926-4fdd-8366-b6d1cbe57cce

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/LateralLength.lean:L87-L107
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.lateralLengthMass_exp. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralLength
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_boundary_source_weight_bound
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_mem_lost_upperCut
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_mirrorDomain_convex
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_rightIndexMass_geometric
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_spatial_sum_exp_bound

-- ---- from OAI.Combinatorics.HoneycombCorridor.ConvexCuts ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

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

theorem strip_index_bounds (h : ℕ) (v : Vertex) (hv : InStrip h v) :
    boxIndex v 1 ≤ boxIndex v 2 ∧ boxIndex v 2 ≤ boxIndex v 1 + (h : ℤ) := by
  cases v <;> simp [InStrip,boxIndex] at * <;> omega

theorem position_index (v : Vertex) :
    (position v).1 = ((boxIndex v 1 : ℝ) + (boxIndex v 2 : ℝ)) / 2 := by
  cases v <;> simp [position,boxIndex] <;> ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Reflection ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem mirrorVertex_injective : Function.Injective mirrorVertex :=
  Function.Involutive.injective mirrorVertex_invol

theorem mirrorWord_injective : Function.Injective mirrorWord :=
  Function.Involutive.injective mirrorWord_invol

theorem mirrorDomain_strip (h : ℕ) (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v) :
    ∀ v ∈ mirrorDomain D, InStrip h v := by
  intro v hv
  have hh := hstrip _ ((mem_mirrorDomain D v).mp hv)
  simpa only [InStrip,(mirror_indices v).1] using hh

theorem mirror_sourceExits (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : w ∈ sourceExits D g) : mirrorWord w ∈ sourceExits (mirrorDomain D) (mirrorGerm g) := by
  obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
  obtain ⟨hn,hm⟩ := stopped_traced D g w hs
  have ht' : (terminalGerm (mirrorGerm g) (mirrorWord w)).1 ∉ mirrorDomain D := by
    rw [mirror_terminal]
    change mirrorVertex (terminalGerm g w).1 ∉ mirrorDomain D
    rwa [mem_mirrorDomain,mirrorVertex_invol]
  apply (mem_sourceExits _ _ _).mpr
  refine ⟨stopped_of_trace _ _ _ ?_ ?_ ht',ht'⟩
  · rw [mirror_traced]
    exact hn.map mirrorVertex_injective
  · intro v hv
    rw [mirror_traced,List.mem_map] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    simpa only [mem_mirrorDomain,mirrorVertex_invol] using hm u hu

theorem mirror_sourceExits_eq (D : Finset Vertex) :
    sourceExits (mirrorDomain D) bottomSource = (sourceExits D bottomSource).image mirrorWord := by
  ext w
  constructor
  · intro hw
    refine Finset.mem_image.mpr ⟨mirrorWord w,?_,mirrorWord_invol w⟩
    simpa only [mirrorDomain_invol,mirror_bottomSource] using
      mirror_sourceExits (mirrorDomain D) bottomSource w hw
  · intro hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    simpa only [mirror_bottomSource] using mirror_sourceExits D bottomSource u hu

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

theorem tailConstant_pos : 0 < tailConstant := by
  have hc : 0 < Real.cos (3*Real.pi/8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr hc)) (Real.exp_pos _)

theorem rightDistanceMass_mono (D : Finset Vertex) (s t : ℝ) (hst : s ≤ t) :
    rightDistanceMass D t ≤ rightDistanceMass D s := by
  classical
  apply positiveWordMass_mono
  intro w hw
  obtain ⟨he,v,hv,ht⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨he,v,hv,hst.trans ht⟩

theorem rightDistanceMass_geometric (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (n : ℕ) :
    rightDistanceMass D (2 * n * (h+1)) ≤
      (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero,mul_zero,zero_mul,pow_zero,mul_one]
    apply (positiveWordMass_mono (Finset.filter_subset _ _)).trans
    exact boundary_source_weight_bound D bottomSource hD hg (bottomSource_outside_of_strip h D hstrip)
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    apply le_trans (positiveWordMass_mono ?_) (rightIndexMass_geometric h hh D hD hg hstrip n)
    intro w hw
    obtain ⟨he,v,hv,ht⟩ := Finset.mem_filter.mp hw
    have hvm := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := (strip_index_bounds h v (hstrip v hvm)).2
    have hi' : (boxIndex v 2 : ℝ) ≤ (boxIndex v 1 : ℝ) + h := by exact_mod_cast hi
    have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have hbound : (n : ℝ)*h ≤ (boxIndex v 1 : ℝ) := by
      rw [position_index] at ht
      nlinarith
    exact (mem_lost_upperCut D bottomSource 1 ((n : ℤ)*h) w).mpr
      ⟨he,v,hv,by exact_mod_cast hbound⟩

theorem rightDistanceMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    rightDistanceMass D t ≤ tailConstant / 2 * Real.exp (-tailRate*t/(h+1)) := by
  let n : ℕ := ⌊t / (2 * (h+1 : ℝ))⌋₊
  have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
  have hd : (0 : ℝ) < 2*((h : ℝ)+1) := by positivity
  have hnlo : (n : ℝ) ≤ t/(2*(h+1)) := Nat.floor_le (div_nonneg ht hd.le)
  have hnhi : t/(2*(h+1)) < (n : ℝ)+1 := Nat.lt_floor_add_one _
  have hthreshold : 2*(n : ℝ)*(h+1) ≤ t := by
    have := (le_div_iff₀ hd).mp hnlo
    nlinarith
  have hgeo := (rightDistanceMass_mono D _ _ hthreshold).trans
    (rightDistanceMass_geometric h hh D hD hg hstrip n)
  have hlog := Real.log_neg rayContraction_range.1 rayContraction_range.2
  have he : (n : ℝ)*Real.log rayContraction ≤
      -Real.log rayContraction + -tailRate*t/(h+1) := by
    have hm := mul_le_mul_of_nonpos_right (le_of_lt hnhi) hlog.le
    have heq : -tailRate*t/(h+1) =
        t/(2*(h+1))*Real.log rayContraction := by
      dsimp [tailRate]
      field_simp
    rw [heq]
    nlinarith [hm]
  have hp : rayContraction ^ n ≤
      Real.exp (-Real.log rayContraction) * Real.exp (-tailRate*t/(h+1)) := by
    rw [← Real.exp_add]
    conv_lhs => rw [← Real.exp_log rayContraction_range.1,← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr he
  have hc : 0 ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
    apply inv_nonneg.mpr
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  calc
    _ ≤ (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := hgeo
    _ ≤ (Real.cos (3*Real.pi/8))⁻¹ *
        (Real.exp (-Real.log rayContraction) * Real.exp (-tailRate*t/(h+1))) :=
      mul_le_mul_of_nonneg_left hp hc
    _ = _ := by dsimp [tailConstant]; ring

theorem lateralMass_le_sides (D : Finset Vertex) (t : ℝ) :
    lateralMass D t ≤ rightDistanceMass D t + rightDistanceMass (mirrorDomain D) t := by
  classical
  simp only [rightDistanceMass,positiveWordMass,Finset.sum_filter,mirror_sourceExits_eq]
  rw [Finset.sum_image (fun a _ b _ hab => mirrorWord_injective hab),← Finset.sum_add_distrib]
  unfold lateralMass
  apply Finset.sum_le_sum
  intro w hw
  simp only [mirrorWord_length]
  by_cases hr : reachesRight t w
  · simp only [hr,ite_true]
    split_ifs <;> nlinarith [pow_nonneg criticalActivity_pos.le w.length]
  · by_cases hl : reachesRight t (mirrorWord w)
    · simp only [hr,hl,ite_false,ite_true,zero_add]
      split_ifs <;> first | exact le_rfl | exact pow_nonneg criticalActivity_pos.le _
    · have hnone : ¬ reachesDistance t w := by
        rintro ⟨v,hv,hv'⟩
        have hab := le_abs.mp hv'
        rcases hab with h | h
        · exact hr ⟨v,hv,h⟩
        · exact hl ((reachesRight_mirror t w).mpr ⟨v,hv,h⟩)
      simp only [hr,hl,hnone,ite_false,zero_add,le_refl]

theorem lateralMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    lateralMass D t ≤ tailConstant * Real.exp (-tailRate*t/(h+1)) := by
  have h1 := rightDistanceMass_exp h hh D hD hg hstrip t ht
  have h2 := rightDistanceMass_exp h hh (mirrorDomain D) (mirrorDomain_convex D hD)
    (by simpa only [mem_mirrorDomain,show mirrorVertex bottomSource.1 = bottomSource.1 from rfl] using hg)
    (mirrorDomain_strip h D hstrip) t ht
  have hs := lateralMass_le_sides D t
  linarith

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.LateralLength ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem sourceExit_visit_sum (D : Finset Vertex) (w : List Bool)
    (hw : w ∈ sourceExits D bottomSource) :
    (∑ v ∈ D, if v ∈ traced bottomSource w then criticalActivity^w.length else 0) =
      (w.length : ℝ)*criticalActivity^w.length := by
  classical
  have hs := stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp hw).1
  have hset : D.filter (fun v => v ∈ traced bottomSource w) = (traced bottomSource w).toFinset := by
    ext v
    simp only [Finset.mem_filter,List.mem_toFinset]
    exact ⟨And.right,fun hv => ⟨hs.2 v hv,hv⟩⟩
  rw [← Finset.sum_filter,hset]
  simp only [Finset.sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup hs.1,traced_length]

theorem lateralLengthMass_fubini (D : Finset Vertex) (t : ℝ) :
    lateralLengthMass D t = ∑ v ∈ D, eventVisitMass D t v := by
  classical
  unfold eventVisitMass
  rw [Finset.sum_comm]
  unfold lateralLengthMass
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ht : reachesDistance t w
  · simp only [ht,true_and,ite_true]
    exact (sourceExit_visit_sum D w hw).symm
  · simp only [ht,false_and,ite_false,Finset.sum_const_zero]

theorem eventVisitMass_le_lateral (D : Finset Vertex) (t : ℝ) (v : Vertex) :
    eventVisitMass D t v ≤ lateralMass D (max t |(position v).1|) := by
  classical
  unfold eventVisitMass lateralMass
  apply Finset.sum_le_sum
  intro w hw
  by_cases he : reachesDistance t w ∧ v ∈ traced bottomSource w
  · have hm : reachesDistance (max t |(position v).1|) w := by
      rcases le_total t |(position v).1| with h | h
      · exact ⟨v,he.2,by rw [max_eq_right h]⟩
      · rw [max_eq_left h]
        exact he.1
    simp [he,hm]
  · simp only [he,ite_false]
    split_ifs <;> first | exact le_rfl | exact pow_nonneg criticalActivity_pos.le _

theorem eventVisitMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) (v : Vertex) :
    eventVisitMass D t v ≤ tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
      Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by
  have hm := lateralMass_exp h hh D hD hg hstrip (max t |(position v).1|)
    (ht.trans (le_max_left _ _))
  have he : Real.exp (-tailRate*max t |(position v).1|/(h+1)) ≤
      Real.exp (-tailRate*t/(2*(h+1))) *
      Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha := le_max_left t |(position v).1|
    have hb := le_max_right t |(position v).1|
    have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
    have hf : -tailRate*max t |(position v).1| ≤
        -tailRate*(t + |(position v).1|)/2 := by
      nlinarith [mul_nonneg tailRate_pos.le (show 0 ≤ 2*max t |(position v).1| - t - |(position v).1| by linarith)]
    have hd := div_le_div_of_nonneg_right hf hH.le
    have heq : -tailRate*t/(2*(h+1)) + -tailRate*|(position v).1|/(2*(h+1)) =
        (-tailRate*(t + |(position v).1|)/2)/(h+1) := by
      field_simp
      ring
    rw [heq]
    exact hd
  calc
    _ ≤ lateralMass D (max t |(position v).1|) := eventVisitMass_le_lateral D t v
    _ ≤ tailConstant * Real.exp (-tailRate*max t |(position v).1|/(h+1)) := hm
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he tailConstant_pos.le

theorem lateralLengthMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    lateralLengthMass D t ≤ tailConstant*spatialConstant*((h : ℝ)+1)^2 *
      Real.exp (-(tailRate/2)*t/(h+1)) := by
  rw [lateralLengthMass_fubini]
  calc
    _ ≤ ∑ v ∈ D, tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        Real.exp (-tailRate*|(position v).1|/(2*(h+1))) :=
      Finset.sum_le_sum (fun v _ => eventVisitMass_exp h hh D hD hg hstrip t ht v)
    _ = tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        ∑ v ∈ D, Real.exp (-tailRate*|(position v).1|/(2*(h+1))) := by rw [Finset.mul_sum]
    _ ≤ tailConstant * Real.exp (-tailRate*t/(2*(h+1))) *
        (spatialConstant*((h : ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_left (spatial_sum_exp_bound h D hstrip)
        (mul_nonneg tailConstant_pos.le (Real.exp_pos _).le)
    _ = _ := by
      have he : -tailRate*t/(2*(h+1)) = -(tailRate/2)*t/(h+1) := by
        field_simp
      rw [he]
      ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.lateralLengthMass_exp := @_root_.OAI.PolynomialVacuumBridge.Corridor.lateralLengthMass_exp
