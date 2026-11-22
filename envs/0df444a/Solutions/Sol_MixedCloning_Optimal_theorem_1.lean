-- Prove2me | solution 1 for MixedCloning.Optimal.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T01:31:15.807447+00:00
-- url     : https://prove2.me/submissions/14bcb5c9-dbc3-409c-8b2e-5e15a86706a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MixedCloning_Optimal_proposition_10
import Theorems.Thm_MixedCloning_Optimal_proposition_11
import Theorems.Thm_MixedCloning_Optimal_rpc_exists

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A rank-`s` orthogonal projector has trace `s`. -/
lemma thm1_projector_trace (d s : ℕ) (P : Op (Fin d)) (hP : IsProjector s P) :
    P.trace = s := by
  obtain ⟨_, hidem, hrank⟩ := hP
  have hI : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hidem]
  have h := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hI)
  rw [Matrix.trace_toLin'_eq] at h
  rw [h, ← hrank]
  rfl

/-- The projector state `P/s` of a rank-`s` projector (`s ≥ 1`) is a quantum state. -/
lemma thm1_projectorState_isState (d s : ℕ) (hs : 1 ≤ s) (P : Op (Fin d))
    (hP : IsProjector s P) : IsState (projectorState s P) := by
  have htr := thm1_projector_trace d s P hP
  obtain ⟨hherm, hidem, _⟩ := hP
  have hpsd : P.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [hherm.eq, hidem] at h
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hc : (0 : ℂ) ≤ (s : ℂ)⁻¹ := by
    have : (s : ℂ)⁻¹ = (((s : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Complex.zero_le_real.mpr (by positivity)
  refine ⟨hpsd.smul hc, ?_⟩
  simp only [projectorState, Matrix.trace_smul, htr, smul_eq_mul]
  exact inv_mul_cancel₀ hs'

/-- The projector state of a rank-`s` projector has rank `s`. -/
lemma thm1_projectorState_rank (d s : ℕ) (hs : 1 ≤ s) (P : Op (Fin d))
    (hP : IsProjector s P) : (projectorState s P).rank = s := by
  have hs' : ((s : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast (show s ≠ 0 by omega))
  unfold projectorState
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors P (mem_nonZeroDivisors_of_ne_zero hs')]
  exact hP.2.2

/-- Lower bound for every rank-`≤ r` cloner, by restricting to projector states of rank
`min(r, ⌊d/2⌋)` and invoking Proposition 11. -/
lemma thm1_lower (d r k : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) (hk : 1 ≤ k) :
    ∀ (eps : ℝ), 0 < eps → eps ≤ 1/16 → 2 ≤ d →
      ∀ (n : ℕ) (C : Cloner d n (n+k)), Clones d r n k eps C →
        (k : ℝ) * ((min r (d/2) : ℕ) : ℝ) * d / (8*eps) ≤ n ∧ (k : ℝ)*r*d/(24*eps) ≤ n := by
  intro eps heps heps16 hd2 n C hC
  have hs1 : 1 ≤ min r (d/2) := le_min hr (by omega)
  have hs2 : 2 * min r (d/2) ≤ d := by have := min_le_right r (d/2); omega
  have hsr : min r (d/2) ≤ r := min_le_left _ _
  have h1 : (k : ℝ) * ((min r (d/2) : ℕ) : ℝ) * d / (8*eps) ≤ n :=
    proposition_11 d (min r (d/2)) n k hd2 hs1 hs2 hk eps heps heps16 C hC.1
      (fun P hP => hC.2 _ (thm1_projectorState_isState d _ hs1 P hP)
        (by rw [thm1_projectorState_rank d _ hs1 P hP]; exact hsr))
  refine ⟨h1, ?_⟩
  have h3n : r ≤ 3 * min r (d/2) := by
    rcases le_total r (d/2) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  have h3 : (r : ℝ) ≤ 3 * ((min r (d/2) : ℕ) : ℝ) := by exact_mod_cast h3n
  calc (k : ℝ) * r * d / (24*eps)
      ≤ (k : ℝ) * (3 * ((min r (d/2) : ℕ) : ℝ)) * d / (24*eps) := by gcongr
    _ = (k : ℝ) * ((min r (d/2) : ℕ) : ℝ) * d / (8*eps) := by field_simp; ring
    _ ≤ n := h1

/-- Some quantum state on any nonempty finite register: the maximally mixed state. -/
lemma thm1_exists_state (a : Type) [Fintype a] [DecidableEq a] [Nonempty a] :
    ∃ tau : Op a, IsState tau := by
  have hcard : (Fintype.card a : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (0 : ℂ) ≤ (Fintype.card a : ℂ)⁻¹ := by
    have : (Fintype.card a : ℂ)⁻¹ = (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Complex.zero_le_real.mpr (by positivity)
  refine ⟨(Fintype.card a : ℂ)⁻¹ • (1 : Op a), Matrix.PosSemidef.one.smul hc, ?_⟩
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  exact inv_mul_cancel₀ hcard

theorem solution (d r k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) (hk : 1 ≤ k) :
    (∀ (eps : ℝ), 0 < eps → eps ≤ 1/16 → 2 ≤ d →
      ∀ (n : ℕ) (C : Cloner d n (n+k)), Clones d r n k eps C →
        (k : ℝ) * ((min r (d/2) : ℕ) : ℝ) * d / (8*eps) ≤ n ∧ (k : ℝ)*r*d/(24*eps) ≤ n) ∧
    (∀ n : ℕ, ∃ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n),
      IsRPC d r n R) ∧
    (∀ (n : ℕ), 1 ≤ n →
      ∀ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n), IsRPC d r n R →
      ∀ tau : Op (Word (Fin d × Fin r) (n+k)), IsState tau →
        Clones d r n k ((k : ℝ)*r*d/n) (pct d r n k R tau) ∧
        ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
          Clones d r n k eps (pct d r n k R tau)) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1/16 → 2 ≤ d →
      (feasibleSamples d r k eps).Nonempty ∧
      (k : ℝ)*r*d/(24*eps) ≤ sampleComplexity d r k eps ∧
      sampleComplexity d r k eps ≤ Nat.ceil ((k : ℝ)*r*d/eps)) := by
  have hlow := thm1_lower d r k hr hrd hk
  have hrpc : ∀ n : ℕ, ∃ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n),
      IsRPC d r n R := fun n => rpc_exists d r n hd hr hrd
  have hup : ∀ (n : ℕ), 1 ≤ n →
      ∀ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n), IsRPC d r n R →
      ∀ tau : Op (Word (Fin d × Fin r) (n+k)), IsState tau →
        Clones d r n k ((k : ℝ)*r*d/n) (pct d r n k R tau) ∧
        ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
          Clones d r n k eps (pct d r n k R tau) :=
    fun n hn R hR tau htau => proposition_10 d r n k hd hr hrd hn R hR tau htau
  refine ⟨hlow, hrpc, hup, ?_⟩
  intro eps heps heps16 hd2
  set N := Nat.ceil ((k : ℝ)*r*d/eps) with hNdef
  have hpos : (0 : ℝ) < (k : ℝ)*r*d/eps := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hpos).ne'
  obtain ⟨R, hR⟩ := hrpc N
  have : Nonempty (Word (Fin d × Fin r) (N+k)) := ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨tau, htau⟩ := thm1_exists_state (Word (Fin d × Fin r) (N+k))
  have hmem : N ∈ feasibleSamples d r k eps :=
    ⟨pct d r N k R tau, (hup N hN R hR tau htau).2 eps heps le_rfl⟩
  have hne : (feasibleSamples d r k eps).Nonempty := ⟨N, hmem⟩
  refine ⟨hne, ?_, Nat.sInf_le hmem⟩
  obtain ⟨C, hC⟩ := Nat.sInf_mem hne
  exact (hlow eps heps heps16 hd2 _ C hC).2
