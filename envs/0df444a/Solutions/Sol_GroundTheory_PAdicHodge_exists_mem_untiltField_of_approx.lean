-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_mem_untiltField_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:29.788458+00:00
-- url     : https://prove2.me/submissions/4793a963-10e1-41f9-8581-02d4e9eb7eb5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Theorems.Thm_GroundTheory_PAdicHodge_perfectField_of_isPerfectoidField
import Theorems.Thm_GroundTheory_PAdicHodge_exists_untiltField_norm_sub_le
import Theorems.Thm_GroundTheory_PAdicHodge_exists_lt_one_le_pow
import Theorems.Thm_GroundTheory_PAdicHodge_mem_range_of_norm_sub_lt
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsAlgClosed C] [IsAlgClosed C♭]
    (hfin : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      FiniteDimensional K (untiltField K C p N))
    (happrox : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
        ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ α ∈ untiltField K C p N := by
  classical
  set d := (minpoly K α).natDegree
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_lt_one_le_pow
    (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)) d
  set ε := (1 + μ) / 2
  have hε0 : 0 < ε := by simp only [ε]; linarith
  have hε1 : ε < 1 := by simp only [ε]; linarith
  set lam := μ / ε
  have hlam0 : 0 ≤ lam := div_nonneg hμ0.le hε0.le
  have hlam1 : lam < 1 := by
    rw [div_lt_one hε0]; simp only [ε]; linarith

  have iter : ∀ k : ℕ, ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧
      ∃ β ∈ untiltField K C p N, ‖α - β‖ ≤ lam ^ k * ‖α‖ := by
    intro k
    induction k with
    | zero => exact ⟨⊥, inferInstance, 0, zero_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨N, hN, β, hβ, hβα⟩ := ih
      have := hN
      have := hfin N hN
      obtain ⟨N', -, hN', β', hβ', hle⟩ := exists_untiltField_norm_sub_le N (happrox N hN) hα
        hμ0.le hμ1.le hμ hε0 hε1 hβ
      refine ⟨N', hN', β', hβ', hle.trans ?_⟩
      rw [pow_succ, mul_comm (lam ^ k) lam, mul_assoc]
      exact mul_le_mul_of_nonneg_left hβα hlam0

  set T : Finset C := ((minpoly K α).aroots C).toFinset.erase α
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ α' ∈ T, ρ ≤ ‖α - α'‖ := by
    by_cases hT : T.Nonempty
    · refine ⟨T.inf' hT fun α' => ‖α - α'‖, ?_, fun α' h => Finset.inf'_le _ h⟩
      rw [Finset.lt_inf'_iff]
      intro α' h
      exact norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase h)))
    · exact ⟨1, one_pos, fun α' h => absurd ⟨α', h⟩ hT⟩
  by_cases hα0 : α = 0
  · exact ⟨⊥, inferInstance, by rw [hα0]; exact zero_mem _⟩
  have hαn : 0 < ‖α‖ := norm_pos_iff.2 hα0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hρ0 hαn) hlam1
  obtain ⟨N, hN, β, hβ, hβα⟩ := iter k
  have hclose : ‖α - β‖ < ρ := by
    refine hβα.trans_lt ?_
    rwa [lt_div_iff₀ hαn] at hk
  have := hN
  have := hfin N hN
  set F := untiltField K C p N
  have : CompleteSpace K := IsPerfectoidField.completeSpace p
  have : CompleteSpace F := FiniteDimensional.complete K F
  have : PerfectField K := perfectField_of_isPerfectoidField K p
  have hsepK : IsSeparable K α := Algebra.IsSeparable.isSeparable K (⟨α, hα⟩ :
    algebraicClosure K C) |> fun h => by
      rwa [IsSeparable, IntermediateField.minpoly_eq] at h
  have hsep : IsSeparable F α := hsepK.tower_top F
  refine ⟨N, hN, ?_⟩
  obtain ⟨c, hc⟩ := mem_range_of_norm_sub_lt (F := F) (E := C) ⟨β, hβ⟩ hsep fun α' hα' hne => by
    refine hclose.trans_le (hρ α' ?_)
    rw [Finset.mem_erase, Multiset.mem_toFinset]
    refine ⟨Ne.symm hne, ?_⟩
    have hαF : IsIntegral F α := hα.tower_top
    have h1 : aeval α' (minpoly F α) = 0 := by
      rw [hα']; exact minpoly.aeval F α'
    have h2 : aeval α' ((minpoly K α).map (algebraMap K F)) = 0 := by
      obtain ⟨r, hr⟩ := minpoly.dvd_map_of_isScalarTower K F α
      rw [hr, map_mul, h1, zero_mul]
    rw [aeval_map_algebraMap] at h2
    rw [mem_aroots]
    exact ⟨minpoly.ne_zero hα, h2⟩
  rw [← hc]
  exact (c : F).2
end GroundTheory.PAdicHodge
