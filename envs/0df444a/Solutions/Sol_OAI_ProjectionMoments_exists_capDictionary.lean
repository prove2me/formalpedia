-- Prove2me | solution 1 for OAI.ProjectionMoments.exists_capDictionary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:58:25.015719+00:00
-- url     : https://prove2.me/submissions/17bb73f2-4940-4e9b-a0fe-9261692515a5

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Caps.lean:L257-L332
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.exists_capDictionary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Theorems.Thm_OAI_NoiselessRegression_card_le_volume_ratio
import Theorems.Thm_OAI_NoiselessRegression_exists_net_of_finite_packing_bound

-- ---- from OAI.Probability.ProjectionMoments.Caps ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_finite_net {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset E, (∀ c ∈ s, ‖c‖ = 1) ∧
      (∀ c ∈ s, ∀ c' ∈ s, c ≠ c' → r < dist c c') ∧
      ∀ x : E, ‖x‖ = 1 → ∃ c ∈ s, dist x c ≤ r := by
  classical
  let N := ⌈((1+r/2)/(r/2))^Module.finrank ℝ E⌉₊
  obtain ⟨s,hs,hsep,hnet⟩ := NoiselessRegression.exists_net_of_finite_packing_bound
    {x : E | ‖x‖ = 1} hr.le N (by
      intro s hs hsep
      have hh := NoiselessRegression.card_le_volume_ratio s hr (by norm_num : (0:ℝ) ≤ 1)
        (fun c hc => (hs c hc).le) (fun c hc c' hc' hne => (hsep c hc c' hc' hne).le)
      exact_mod_cast hh.trans (Nat.le_ceil _))
  exact ⟨s,hs,hsep,hnet⟩

end

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma reciprocal_scale {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1/4) :
    ∃ j : ℕ, 4*t ≤ 1/((j:ℝ)+1) ∧ 1/((j:ℝ)+1) < 8*t := by
  let n := ⌊1/(4*t)⌋₊
  have hx : 1 ≤ 1/(4*t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr hx
  have hnle : (n:ℝ) ≤ 1/(4*t) := Nat.floor_le (by positivity)
  have hnlt : 1/(4*t) < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have he : ((n-1:ℕ):ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
  refine ⟨n-1, ?_, ?_⟩
  · rw [he]
    rw [le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))]
    rw [le_div_iff₀ (by positivity)] at hnle
    nlinarith
  · rw [he, div_lt_iff₀ (by exact_mod_cast (show 0 < n by omega))]
    rw [div_lt_iff₀ (by positivity)] at hnlt
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

lemma exists_capDictionary {c : E} (hc : ‖c‖ = 1) {r α : ℝ}
    (hr : 0 < r) (hα : 1 ≤ α) : Nonempty (CapDictionary c r α) := by
  classical
  let ρ : ℕ → ℝ := fun j => r/((j:ℝ)+1)
  have hρ : ∀ j, 0 < ρ j := fun j => div_pos hr (by positivity)
  choose net hnetnorm hnetsep hnetcover using
    (fun j : ℕ => sphere_finite_net (E := E) (half_pos (hρ j)))
  let I := Option (Σ j : ℕ, {s : E // s ∈ net j})
  let center : I → E := fun i => match i with | none => c | some p => p.2.val
  let radius : I → ℝ := fun i => match i with | none => r | some p => ρ p.1
  have hw (j : ℕ) : (r/ρ j)^α = ((j:ℝ)+1)^α := by
    congr 1
    dsimp [ρ]
    field_simp
  have hproper : ∀ R : ℝ, {i : I | (r/radius i)^α ≤ R}.Finite := by
    intro R
    have hlevel (j : ℕ) : (j:ℝ) ≤ (r/ρ j)^α := by
      rw [hw]
      calc
        _ ≤ (j:ℝ)+1 := by linarith
        _ = ((j:ℝ)+1)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j]) hα
    have hsubset : {i : I | (r/radius i)^α ≤ R} ⊆
        insert none (⋃ j ∈ Finset.range (⌈R⌉₊+1), Option.some ''
          (Sigma.mk j '' (Set.univ : Set {s : E // s ∈ net j}))) := by
      intro i hi
      cases i with
      | none => exact Set.mem_insert _ _
      | some p =>
        right
        have hjR : (p.1:ℝ) ≤ R := (hlevel p.1).trans hi
        have hj : p.1 ∈ Finset.range (⌈R⌉₊+1) := by
          apply Finset.mem_range.mpr
          have hh : p.1 ≤ ⌈R⌉₊ := by exact_mod_cast hjR.trans (Nat.le_ceil R)
          omega
        exact Set.mem_iUnion₂.mpr ⟨p.1,hj,⟨p,⟨p.2,Set.mem_univ _,rfl⟩,rfl⟩⟩
    apply Set.Finite.subset _ hsubset
    apply Set.Finite.insert
    apply Set.Finite.biUnion (Finset.finite_toSet _)
    intro j hj
    exact ((Set.toFinite (Set.univ : Set {s : E // s ∈ net j})).image (Sigma.mk j)).image Option.some
  refine ⟨{
    I := I
    countable := inferInstance
    center := center
    radius := radius
    center_norm := ?_
    radius_pos := ?_
    radius_le := ?_
    parent := none
    parent_center := rfl
    parent_radius := rfl
    proper := hproper
    cover := ?_ }⟩
  · rintro (_|⟨j,s,hs⟩)
    · exact hc
    · exact hnetnorm j s hs
  · rintro (_|⟨j,s⟩)
    · exact hr
    · exact hρ j
  · rintro (_|⟨j,s⟩)
    · exact le_rfl
    · change r/((j:ℝ)+1) ≤ r
      exact div_le_self hr.le (by linarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j])
  · intro s hs t ht ht4
    obtain ⟨j,hj1,hj2⟩ := reciprocal_scale ht ht4
    obtain ⟨s',hs',hss'⟩ := hnetcover j s hs
    refine ⟨some ⟨j,s',hs'⟩,?_,?_,hss'⟩
    · change 4*r*t ≤ r/((j:ℝ)+1)
      have hh := mul_le_mul_of_nonneg_left hj1 hr.le
      rw [mul_one_div] at hh
      nlinarith only [hh]
    · change r/((j:ℝ)+1) < 8*r*t
      have hh := mul_lt_mul_of_pos_left hj2 hr
      rw [mul_one_div] at hh
      nlinarith only [hh]

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution.{u} : type_of% @_root_.OAI.ProjectionMoments.exists_capDictionary.{u} := @_root_.OAI.ProjectionMoments.exists_capDictionary.{u}
