-- Prove2me | solution 1 for MilnorDynamics.not_locally_bounded_diverges
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-01T14:24:11.540919+00:00
-- url     : https://prove2.me/submissions/d11899cb-a78a-4816-bf50-1e3b6be2bcc4

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- The counterexample family: constant `2` at even indices, constant `2n+3` at odd ones. -/
noncomputable def nlbF : ℕ → ℂ → ℂ :=
  fun n _ => if Even n then (2 : ℂ) else ((2 * n + 3 : ℕ) : ℂ)

lemma nlbF_apply_even {n : ℕ} (h : Even n) (z : ℂ) : nlbF n z = (2 : ℂ) := by
  simp [nlbF, h]

lemma nlbF_apply_odd {n : ℕ} (h : ¬ Even n) (z : ℂ) :
    nlbF n z = ((2 * n + 3 : ℕ) : ℂ) := by
  simp [nlbF, h]

lemma nlbF_norm_cast (n : ℕ) : ‖((2 * n + 3 : ℕ) : ℂ)‖ = ((2 * n + 3 : ℕ) : ℝ) :=
  Complex.norm_natCast (2 * n + 3)

lemma nlbF_ne_zero_one (n : ℕ) (z : ℂ) : nlbF n z ≠ (0 : ℂ) ∧ nlbF n z ≠ (1 : ℂ) := by
  by_cases h : Even n
  · rw [nlbF_apply_even h z]
    constructor <;> norm_num
  · rw [nlbF_apply_odd h z]
    constructor
    · intro hz
      have h0 : ‖((2 * n + 3 : ℕ) : ℂ)‖ = 0 := by rw [hz]; exact norm_zero
      rw [nlbF_norm_cast] at h0
      have h0' : (2 * n + 3 : ℕ) = 0 := by exact_mod_cast h0
      omega
    · intro hz
      have h1 : ‖((2 * n + 3 : ℕ) : ℂ)‖ = 1 := by rw [hz]; simp
      rw [nlbF_norm_cast] at h1
      have h1' : (2 * n + 3 : ℕ) = 1 := by exact_mod_cast h1
      omega

lemma nlbF_differentiable (n : ℕ) : DifferentiableOn ℂ (nlbF n) (Set.univ : Set ℂ) := by
  by_cases h : Even n
  · have hfun : nlbF n = fun _ => (2 : ℂ) := funext fun z => nlbF_apply_even h z
    rw [hfun]
    exact differentiableOn_const (2 : ℂ)
  · have hfun : nlbF n = fun _ => ((2 * n + 3 : ℕ) : ℂ) :=
      funext fun z => nlbF_apply_odd h z
    rw [hfun]
    exact differentiableOn_const _

lemma nlbF_mapsTo (n : ℕ) : MapsTo (nlbF n) (Set.univ : Set ℂ) ({0, 1}ᶜ : Set ℂ) := by
  intro z _
  obtain ⟨h0, h1⟩ := nlbF_ne_zero_one n z
  simpa [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, h0, h1]

lemma nlbF_unbounded : ∃ K ⊆ (Set.univ : Set ℂ), IsCompact K ∧
    ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖nlbF n z‖ ≤ M) := by
  refine ⟨{0}, by simp, isCompact_singleton, ?_⟩
  rintro ⟨M, hM⟩
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hodd : ¬ Even (2 * N + 1) := by
    intro he
    obtain ⟨k, hk⟩ := he
    omega
  have hle : ((2 * (2 * N + 1) + 3 : ℕ) : ℝ) ≤ M := by
    have h := hM (2 * N + 1) 0 (by simp : (0 : ℂ) ∈ ({0} : Set ℂ))
    rw [nlbF_apply_odd hodd 0, nlbF_norm_cast] at h
    exact h
  have hge : (N : ℝ) < ((2 * (2 * N + 1) + 3 : ℕ) : ℝ) := by
    have hnat : N < 2 * (2 * N + 1) + 3 := by omega
    exact_mod_cast hnat
  linarith

lemma nlbF_not_diverges :
    ¬ DivergesLocallyUniformlyFrom nlbF (Set.univ : Set ℂ) ({0, 1}ᶜ : Set ℂ) := by
  intro hdiv
  have hb : ∀ᶠ n in atTop, ∀ x ∈ ({0} : Set ℂ), nlbF n x ∉ ({2} : Set ℂ) :=
    hdiv ({0} : Set ℂ) (by simp) isCompact_singleton ({2} : Set ℂ) (by simp)
      isCompact_singleton
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  have heven : Even (N + N) := ⟨N, by ring⟩
  have hn0 : nlbF (N + N) 0 ∉ ({2} : Set ℂ) :=
    hN (N + N) (by omega) 0 (by simp : (0 : ℂ) ∈ ({0} : Set ℂ))
  have h2 : nlbF (N + N) 0 = (2 : ℂ) := nlbF_apply_even heven 0
  exact hn0 (by simp [h2])

theorem solution :
    ¬ (∀ (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U) (f : ℕ → ℂ → ℂ),
      (∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ)) →
      (∃ K ⊆ U, IsCompact K ∧ ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) →
      DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ)) := by
  intro h
  have hf : ∀ n, DifferentiableOn ℂ (nlbF n) (Set.univ : Set ℂ) ∧
      MapsTo (nlbF n) (Set.univ : Set ℂ) ({0, 1}ᶜ : Set ℂ) :=
    fun n => ⟨nlbF_differentiable n, nlbF_mapsTo n⟩
  exact nlbF_not_diverges
    (h Set.univ isOpen_univ isConnected_univ nlbF hf nlbF_unbounded)
