-- Prove2me | solution 1 for OAI.ShortEgyptian.density_unrolled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:56:30.726281+00:00
-- url     : https://prove2.me/submissions/ff0f7952-d987-4c0b-89b1-2e8579d6e717

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DensityBounds.lean:L52-L71
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.density_unrolled. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Theorems.Thm_OAI_ShortEgyptian_backwards_recurrence_bound
import Theorems.Thm_OAI_ShortEgyptian_density_precise_recurrence
import Theorems.Thm_OAI_ShortEgyptian_depth_bound
import Theorems.Thm_OAI_ShortEgyptian_log_one_sub_inverse_lower
import Theorems.Thm_OAI_ShortEgyptian_residueSystem_terminal_induction

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma scaleM_bounds (S : ℝ) (hlog : 1 ≤ Real.log S) (hS : 4*Real.log S ≤ S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧
      (scaleM S:ℝ) ≤ S := by
  have hl : 0 < Real.log S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hf := Nat.sub_one_lt_floor (S/Real.log S)
  have hu := Nat.floor_le (div_nonneg hS0 hl.le)
  have hx : 4 ≤ S/Real.log S := (le_div_iff₀ hl).mpr (by linarith)
  refine ⟨?_,hu,hu.trans (div_le_self hS0 hlog)⟩
  dsimp [scaleM]
  have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
  rw [heq]
  linarith

lemma level_pos (S : ℝ) (j : ℕ) : 0 < level S j := Real.exp_pos _
lemma scaleRho_le_one (S : ℝ) : scaleRho S ≤ 1 :=
  Real.exp_le_one_iff.mpr (by have hh : (0:ℝ) ≤ scaleM S := Nat.cast_nonneg _; nlinarith)

lemma depth_level (S : ℝ) (hm : 0 < scaleM S) (hmS : (scaleM S:ℝ) ≤ S) :
    level S (depth S) ≤ Real.exp (scaleM S:ℝ) ∧
      Real.exp ((9999/10000:ℝ)*scaleM S) ≤ level S (depth S) := by
  have hmR : 0 < (scaleM S:ℝ) := by exact_mod_cast hm
  have hD : (2:ℝ) ≤ dimX := by norm_num [dimX,dimM]
  have hnum : 0 ≤ (dimX:ℝ)*S-scaleM S := by nlinarith
  have hlo := Nat.le_ceil (((dimX:ℝ)*S-scaleM S)/((1/10000:ℝ)*scaleM S))
  have hhi := Nat.ceil_lt_add_one (div_nonneg hnum (by positivity : (0:ℝ)≤(1/10000:ℝ)*scaleM S))
  have hlo' := (div_le_iff₀ (by positivity : (0:ℝ)<(1/10000:ℝ)*scaleM S)).mp hlo
  have hhi' := mul_lt_mul_of_pos_right hhi (by positivity : (0:ℝ)<(1/10000:ℝ)*scaleM S)
  rw [add_mul,div_mul_cancel₀ _ (by positivity : (1/10000:ℝ)*(scaleM S:ℝ) ≠ 0)] at hhi'
  constructor <;> apply Real.exp_le_exp.mpr <;> dsimp [level,depth] at * <;> nlinarith

lemma levelMultiplier_last (S : ℝ) (C : ℕ) (hm : 0 < scaleM S)
    (hmS : (scaleM S:ℝ) ≤ S) : levelMultiplier S C (depth S) = 1 := by
  apply ite_eq_right
  exact not_lt.mpr ((depth_level S hm hmS).1.trans (Real.exp_le_exp.mpr hmS))

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma ListScale.log_one {S : ℝ} (h : ListScale S) : 1 ≤ Real.log S := by linarith [h.log_large]
lemma ListScale.S_pos {S : ℝ} (h : ListScale S) : 0 < S := by linarith [h.two_le]
lemma ListScale.m_bounds {S : ℝ} (h : ListScale S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧ (scaleM S:ℝ) ≤ S :=
  scaleM_bounds S h.log_one (by linarith [h.log_bound,h.log_large])
lemma ListScale.m_pos {S : ℝ} (h : ListScale S) : 0 < scaleM S := by
  have hh : 0 < (scaleM S:ℝ) := by linarith [h.m_large,h.log_large]
  exact_mod_cast hh
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.TerminalScale ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma terminalSteps_power (S : ℝ) (hS : 0 < S) : S ≤ (10000/9999:ℝ)^terminalSteps S := by
  have hl : 0 < Real.log (10000/9999:ℝ) := Real.log_pos (by norm_num)
  have hh := (div_le_iff₀ hl).mp (Nat.le_ceil (Real.log S/Real.log (10000/9999:ℝ)))
  calc
    S = Real.exp (Real.log S) := (Real.exp_log hS).symm
    _ ≤ Real.exp ((terminalSteps S:ℝ)*Real.log (10000/9999:ℝ)) := Real.exp_le_exp.mpr hh
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (show (0:ℝ)<10000/9999 by norm_num)]

lemma residueSystem_terminal (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C)
    (u : ℕ) (hucap : (u:ℝ) ≤ Real.exp (scaleM S:ℝ)) :
    ∃ ns, IsUnitSum ((u:ℚ)/R.M) ns ∧ ns.length ≤ terminalLength S := by
  apply residueSystem_terminal_induction S h C R (terminalSteps S) u hucap
  by_cases hu : u = 0
  · simp only [hu,Nat.cast_zero,Real.log_zero]; positivity
  have hup : 0 < (u:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hh := (Real.log_le_iff_le_exp hup).mpr hucap
  exact hh.trans (h.m_bounds.2.2.trans (terminalSteps_power S h.S_pos))

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DescentSets ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma mem_levelBad (S : ℝ) (M C K j u : ℕ) :
    u ∈ levelBad S M C K j ↔ 0 < u ∧ (u:ℝ) ≤ level S j ∧
      ¬HasUnitSum M (levelMultiplier S C j) u (K+(depth S-j)) := by
  constructor
  · intro hu
    obtain ⟨hu,hn⟩ := mem_filter.mp hu
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hu
    exact ⟨by omega,(Nat.cast_le.mpr hhi).trans (Nat.floor_le (level_pos S j).le),hn⟩
  · rintro ⟨hu0,hu,hn⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu0,Nat.le_floor hu⟩,hn⟩

lemma levelBad_card_le (S : ℝ) (M C K j : ℕ) :
    ((levelBad S M C K j).card:ℝ) ≤ level S j := by
  have hh : (levelBad S M C K j).card ≤ ⌊level S j⌋₊ := by
    apply (card_le_card (filter_subset _ _)).trans
    simp
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (level_pos S j).le)

lemma levelBad_terminal (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C) :
    levelBad S R.M C (terminalLength S) (depth S) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨_,hu,hn⟩ := (mem_levelBad S R.M C _ _ u).mp hu
  have hc := levelMultiplier_last S C h.m_pos h.m_bounds.2.2
  have hcap := hu.trans (depth_level S h.m_pos h.m_bounds.2.2).1
  obtain ⟨ns,hs,hl⟩ := residueSystem_terminal S h C R u hcap
  apply hn
  refine ⟨ns,?_,by simpa using hl⟩
  simpa only [hc,Nat.cast_one,mul_one] using hs

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.MomentRecurrence ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter

lemma descentR_ge_two : 2 ≤ descentR := by norm_num [descentR]
lemma descentR_eq : descentR=24*dimX*10000 := by norm_num [descentR,dimX,dimM]
lemma descentAlpha_bounds : 0 < descentAlpha ∧ descentAlpha < 1 := by
  have hr : (2:ℝ) ≤ descentR := by exact_mod_cast descentR_ge_two
  have hi : 0 < 1/(descentR:ℝ) := by positivity
  have hi' : 1/(descentR:ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  dsimp [descentAlpha]
  constructor <;> linarith

lemma levelDensity_bounds (S : ℝ) (M C j : ℕ) :
    0 ≤ levelDensity S M C j ∧ levelDensity S M C j ≤ 1 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (level_pos S j).le,?_⟩
  exact (div_le_one (level_pos S j)).mpr (levelBad_card_le S M C _ j)

lemma levelDensity_last (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C) :
    levelDensity S R.M C (depth S) = 0 := by
  simp only [levelDensity,levelBad_terminal S h C R,card_empty,Nat.cast_zero,zero_div]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DensityBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Filter Topology

lemma density_recurrence (S : ℝ) (h : ListScale S) (hm : MomentScale S) (hq : 2 ≤ S^(1/4:ℝ))
    (C : ℕ) (R : ResidueSystem S C) (hClo : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) (j : ℕ) (hj : j < depth S) :
    levelDensity S R.M C j ≤ Real.exp (-(1/1000:ℝ)*scaleM S)+
      Real.exp (2*S^(1/4:ℝ))*(levelDensity S R.M C (j+1))^descentAlpha := by
  have hh := density_precise_recurrence S h hm C R hClo hChi j hj
  have hd := levelDensity_bounds S R.M C (j+1)
  have hp := Real.self_le_rpow_of_le_one hd.1 hd.2 descentAlpha_bounds.2.le
  have hr : (2:ℝ) ≤ descentR := by exact_mod_cast descentR_ge_two
  have hE : Real.exp (S^(1/4:ℝ)/(descentR:ℝ)) ≤ Real.exp (S^(1/4:ℝ)) :=
    Real.exp_le_exp.mpr (div_le_self (by positivity) (by linarith))
  have h3 : 3 ≤ Real.exp (S^(1/4:ℝ)) := by linarith [Real.add_one_le_exp (S^(1/4:ℝ))]
  have hcoef : 1+2*Real.exp (S^(1/4:ℝ)/(descentR:ℝ)) ≤ Real.exp (2*S^(1/4:ℝ)) := by
    rw [show 2*S^(1/4:ℝ)=S^(1/4:ℝ)+S^(1/4:ℝ) by ring,Real.exp_add]
    nlinarith
  have hp0 : 0 ≤ (levelDensity S R.M C (j+1))^descentAlpha := Real.rpow_nonneg hd.1 _
  have hh' := mul_le_mul_of_nonneg_right hcoef hp0
  have hρ := mul_le_mul_of_nonneg_right (scaleRho_le_one S) hd.1
  nlinarith only [hh,hh',hρ,hp]

lemma alpha_depth (S : ℝ) (h : ListScale S) : S^(-(1/4:ℝ)) ≤ descentAlpha^depth S := by
  have hr : (2:ℝ) ≤ descentR := by exact_mod_cast descentR_ge_two
  have hrp : 0 < (descentR:ℝ) := by linarith
  have hl := log_one_sub_inverse_lower (descentR:ℝ) hr
  change -(2/(descentR:ℝ)) ≤ Real.log descentAlpha at hl
  have hd := depth_bound S h.S_pos h.log_one h.m_bounds.1 h.m_bounds.2.2
  have heq : (descentR:ℝ)=8*(3*(dimX:ℝ)*10000) := by rw [descentR_eq]; push_cast; ring
  have hcoef : (2*(depth S:ℝ))/(descentR:ℝ) ≤ (1/4:ℝ)*Real.log S := by
    apply (div_le_iff₀ hrp).mpr
    rw [heq]
    nlinarith
  rw [Real.rpow_def_of_pos h.S_pos]
  have hp : descentAlpha^depth S = Real.exp ((depth S:ℝ)*Real.log descentAlpha) := by
    rw [Real.exp_nat_mul,Real.exp_log descentAlpha_bounds.1]
  rw [hp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (depth S) : (0:ℝ) ≤ depth S)
  rw [show (depth S:ℝ)*-(2/(descentR:ℝ)) = -(2*(depth S:ℝ)/(descentR:ℝ)) by ring] at hh
  linarith

lemma density_unrolled (S : ℝ) (h : ListScale S) (hm : MomentScale S) (hq : 2 ≤ S^(1/4:ℝ))
    (C : ℕ) (R : ResidueSystem S C) (hClo : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    levelDensity S R.M C 0 ≤ (depth S:ℝ)*Real.exp
      (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) := by
  have hrp : 0 < (descentR:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) descentR_ge_two)
  have hfix : 2*S^(1/4:ℝ)+(2*(descentR:ℝ)*S^(1/4:ℝ))*descentAlpha=2*(descentR:ℝ)*S^(1/4:ℝ) := by
    dsimp [descentAlpha]
    field_simp
    ring
  have hh := backwards_recurrence_bound (levelDensity S R.M C) (depth S) descentAlpha
    (2*S^(1/4:ℝ)) (2*(descentR:ℝ)*S^(1/4:ℝ)) ((1/1000:ℝ)*scaleM S)
    descentAlpha_bounds.1 descentAlpha_bounds.2.le (by positivity) (by positivity) hfix
    (fun j => (levelDensity_bounds S R.M C j).1) (levelDensity_last S h C R)
    (fun j hj => by simpa only [neg_mul] using density_recurrence S h hm hq C R hClo hChi j hj)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  have ha := mul_le_mul_of_nonneg_left (alpha_depth S h) (show (0:ℝ) ≤ (1/1000:ℝ)*scaleM S by positivity)
  linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Filter Topology


theorem solution : type_of% @_root_.OAI.ShortEgyptian.density_unrolled := @_root_.OAI.ShortEgyptian.density_unrolled
