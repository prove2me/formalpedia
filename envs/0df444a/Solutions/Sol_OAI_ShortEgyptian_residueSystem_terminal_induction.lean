-- Prove2me | solution 1 for OAI.ShortEgyptian.residueSystem_terminal_induction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:40:30.384168+00:00
-- url     : https://prove2.me/submissions/7da64f49-c19f-4f4d-a3f6-c27eb3709bc9

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TerminalScale.lean:L35-L88
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.residueSystem_terminal_induction. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_binary_unitSum
import Theorems.Thm_OAI_ShortEgyptian_quotient_spec
import Theorems.Thm_OAI_ShortEgyptian_residue_lift

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem residue_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    residue v u (quotient v u) < u ∧
      v + residue v u (quotient v u) = u * quotient v u := by
  obtain ⟨_, hlo, hhi⟩ := quotient_spec hv hu
  unfold residue
  omega

theorem unit_le_sum {n : ℕ} {ns : List ℕ} (hn : n ∈ ns) :
    (1 : ℚ) / n ≤ unitSum ns := by
  unfold unitSum
  apply List.single_le_sum _ _ (List.mem_map.mpr ⟨n, hn, rfl⟩)
  intro x hx
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma binary_power_lower (S : ℝ) (hS : 0 < S) : S^100000 ≤ (2:ℝ)^binaryExponent S := by
  have hh := Nat.le_ceil (100000*Real.log S/Real.log 2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh' := (div_le_iff₀ hl).mp hh
  have he : (2:ℝ)^binaryExponent S = Real.exp ((binaryExponent S:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [←Real.exp_log (pow_pos hS 100000),Real.log_pow,he]
  exact Real.exp_le_exp.mpr (by simpa only [binaryExponent,Nat.cast_ofNat] using hh')

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
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.TerminalExpansion ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma isUnitSum_of_positive {x : ℚ} {ns : List ℕ}
    (hp : ∀ n ∈ ns, 0 < n) (heq : unitSum ns = x) (hx : x < 1) : IsUnitSum x ns := by
  refine ⟨?_,heq⟩
  intro n hn
  have hh := unit_le_sum hn
  rw [heq] at hh
  have hn0 := hp n hn
  by_contra h
  have hn1 : n = 1 := by omega
  subst n
  norm_num at hh
  linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.TerminalScale ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma residueSystem_terminal_induction (S : ℝ) (h : ListScale S) (C : ℕ) (R : ResidueSystem S C)
    (k u : ℕ) (hucap : (u:ℝ) ≤ Real.exp (scaleM S:ℝ))
    (hulog : Real.log u ≤ (10000/9999:ℝ)^k) :
    ∃ ns, IsUnitSum ((u:ℚ)/R.M) ns ∧ ns.length ≤ binaryExponent S+1+k := by
  have hM : 0 < R.M := by exact_mod_cast (Real.exp_pos S).trans R.M_lower
  have huM : u < R.M := by
    exact_mod_cast hucap.trans_lt ((Real.exp_le_exp.mpr h.m_bounds.2.2).trans_lt R.M_lower)
  have hb (u : ℕ) (hu : u ≤ 2^binaryExponent S) (hM' : u < R.M) :
      ∃ ns, IsUnitSum ((u:ℚ)/R.M) ns ∧ ns.length ≤ binaryExponent S+1 := by
    obtain ⟨ns,hns,heq,hlen⟩ := binary_unitSum _ R.M u hM R.binary_dvd hu
    refine ⟨ns,isUnitSum_of_positive hns heq ?_,hlen⟩
    exact (div_lt_one (by exact_mod_cast hM : (0:ℚ)<R.M)).mpr (by exact_mod_cast hM')
  induction k generalizing u with
  | zero =>
    have hu : u ≤ 2^binaryExponent S := by
      by_cases hu0 : u = 0
      · subst u; exact Nat.zero_le _
      have hup : 0 < (u:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hu0)
      have hh := Real.exp_le_exp.mpr hulog
      rw [Real.exp_log hup,pow_zero] at hh
      have hhS : Real.exp 1 ≤ S^100000 := by
        rw [←Real.exp_log (pow_pos h.S_pos 100000),Real.log_pow]
        apply Real.exp_le_exp.mpr
        norm_num
        linarith [h.log_large]
      exact_mod_cast hh.trans (hhS.trans (binary_power_lower S h.S_pos))
    simpa only [Nat.add_zero] using hb u hu huM
  | succ k ih =>
    by_cases husmall : u ≤ 2^binaryExponent S
    · obtain ⟨ns,hns,hlen⟩ := hb u husmall huM
      exact ⟨ns,hns,by omega⟩
    · have hu0 : 0 < u := (Nat.zero_le (2^binaryExponent S)).trans_lt (lt_of_not_ge husmall)
      have hularge : S^100000 < (u:ℝ) := (binary_power_lower S h.S_pos).trans_lt (by exact_mod_cast lt_of_not_ge husmall)
      obtain ⟨t,ht,htM,hres⟩ := R.terminal u hularge hucap
      let v := residue t u (quotient t u)
      have hvu : v < u := (residue_spec ht hu0).1
      have hvM : v < R.M := hvu.trans huM
      have hvcap : (v:ℝ) ≤ Real.exp (scaleM S:ℝ) := (Nat.cast_le.mpr hvu.le).trans hucap
      have hvlog : Real.log v ≤ (10000/9999:ℝ)^k := by
        by_cases hv0 : v = 0
        · simp only [hv0,Nat.cast_zero,Real.log_zero]; positivity
        have hvp : 0 < (v:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hv0)
        have hup : 0 < (u:ℝ) := by exact_mod_cast hu0
        have hh := Real.log_le_log hvp hres
        rw [Real.log_rpow hup] at hh
        have hp : (9999/10000:ℝ)*(10000/9999:ℝ)^(k+1) = (10000/9999:ℝ)^k := by
          rw [pow_succ]; ring
        exact hh.trans ((mul_le_mul_of_nonneg_left hulog (by norm_num : (0:ℝ)≤9999/10000)).trans_eq hp)
      obtain ⟨ns,hns,hlen⟩ := ih v hvcap hvlog hvM
      have hr : ∃ ns, IsUnitSum ((residue (1*t) u (quotient (1*t) u):ℚ)/(R.M*1)) ns ∧
          ns.length ≤ binaryExponent S+1+k := by simpa only [one_mul,mul_one] using And.intro hns hlen |> fun hh => ⟨ns,hh⟩
      have hh := residue_lift hM (by norm_num : 0 < (1:ℕ)) (by norm_num : 0 < (1:ℕ))
        (dvd_refl 1) hu0 (by simpa using huM) ht htM hr
      simpa only [Nat.cast_one,mul_one,Nat.add_assoc] using hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.residueSystem_terminal_induction := @_root_.OAI.ShortEgyptian.residueSystem_terminal_induction
