-- Prove2me | solution 1 for NatureSLT.GrowthFunction.vcDim_iff_growthFunction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:12:09.201595+00:00
-- url     : https://prove2.me/submissions/9ceb6b08-3677-409d-af77-9af6ee290c53

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_growthFunction
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

open NatureSLT.GrowthFunction

theorem g69f_supP_top (P : ℕ → Prop) (hdown : ∀ m k, P m → k ≤ m → P k) :
    (⨆ (h : ℕ) (_ : P h), (h : ℕ∞)) = ⊤ ↔ ∀ n, P n := by
  constructor
  · intro htop n
    by_contra hn
    have : (⨆ (h : ℕ) (_ : P h), (h : ℕ∞)) ≤ n := by
      refine iSup₂_le fun k hk => ?_
      have : k < n := by
        by_contra hkn; exact hn (hdown k n hk (by omega))
      exact_mod_cast this.le
    rw [htop] at this
    exact absurd this (by simp)
  · intro hall
    refine eq_top_iff.mpr ?_
    refine ENat.forall_natCast_le_iff_le.mp fun n _ => ?_
    exact le_iSup₂_of_le (f := fun (h : ℕ) (_ : P h) => (h : ℕ∞)) n (hall n) le_rfl

theorem g69f_supP_eq (P : ℕ → Prop) (hdown : ∀ m k, P m → k ≤ m → P k) (h0 : P 0) (h : ℕ) :
    (⨆ (k : ℕ) (_ : P k), (k : ℕ∞)) = (h : ℕ∞) ↔ P h ∧ ¬ P (h + 1) := by
  constructor
  · intro heq
    constructor
    · by_contra hn
      have hpos : 0 < h := by
        rcases Nat.eq_zero_or_pos h with rfl | hp
        · exact absurd h0 hn
        · exact hp
      have : (⨆ (k : ℕ) (_ : P k), (k : ℕ∞)) ≤ ((h - 1 : ℕ) : ℕ∞) := by
        refine iSup₂_le fun k hk => ?_
        have : k < h := by
          by_contra hkn; exact hn (hdown k h hk (by omega))
        exact_mod_cast (show k ≤ h - 1 by omega)
      rw [heq] at this
      have := ENat.coe_le_coe.mp this
      omega
    · intro hn
      have : ((h + 1 : ℕ) : ℕ∞) ≤ (⨆ (k : ℕ) (_ : P k), (k : ℕ∞)) :=
        le_iSup₂_of_le (f := fun (k : ℕ) (_ : P k) => (k : ℕ∞)) (h + 1) hn le_rfl
      rw [heq] at this
      have := ENat.coe_le_coe.mp this
      omega
  · rintro ⟨hh, hn⟩
    apply le_antisymm
    · refine iSup₂_le fun k hk => ?_
      have : k ≤ h := by
        by_contra hkn; exact hn (hdown k (h + 1) hk (by omega))
      exact_mod_cast this
    · exact le_iSup₂_of_le (f := fun (k : ℕ) (_ : P k) => (k : ℕ∞)) h hh le_rfl

theorem g69f_shatters_down {Z Λ : Type*} (Q : Λ → Z → Bool) (m k : ℕ)
    (hm : ∃ z : Fin m → Z, Shatters Q z) (hkm : k ≤ m) : ∃ z : Fin k → Z, Shatters Q z := by
  obtain ⟨z, hz⟩ := hm
  refine ⟨fun i => z (Fin.castLE hkm i), fun δ => ?_⟩
  obtain ⟨α, hα⟩ := hz (fun j => if hj : (j : ℕ) < k then δ ⟨j, hj⟩ else false)
  refine ⟨α, fun i => ?_⟩
  have := hα (Fin.castLE hkm i)
  simpa [i.isLt] using this

theorem g69f_numSep_le {Z Λ : Type*} (Q : Λ → Z → Bool) {ℓ : ℕ} (z : Fin ℓ → Z) :
    numSeparations Q z ≤ 2 ^ ℓ := by
  unfold numSeparations
  calc _ ≤ (Set.univ : Set (Fin ℓ → Bool)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = 2 ^ ℓ := by simp [Set.ncard_univ]

theorem g69f_numSep_eq_iff {Z Λ : Type*} (Q : Λ → Z → Bool) {ℓ : ℕ} (z : Fin ℓ → Z) :
    numSeparations Q z = 2 ^ ℓ ↔ Shatters Q z := by
  unfold numSeparations Shatters
  have hu : (Set.univ : Set (Fin ℓ → Bool)).ncard = 2 ^ ℓ := by simp [Set.ncard_univ]
  constructor
  · intro h δ
    have : Set.range (fun α : Λ => fun i : Fin ℓ => Q α (z i)) = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [hu, h]) (Set.toFinite _)
    have hδ : δ ∈ Set.range (fun α : Λ => fun i : Fin ℓ => Q α (z i)) := by rw [this]; trivial
    obtain ⟨α, hα⟩ := hδ
    exact ⟨α, fun i => congrFun hα i⟩
  · intro h
    have : Set.range (fun α : Λ => fun i : Fin ℓ => Q α (z i)) = Set.univ := by
      ext δ; simp only [Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨α, hα⟩ := h δ; exact ⟨α, funext hα⟩
    rw [this, hu]

theorem g69f_numSep_pos {Z Λ : Type*} [Nonempty Λ] (Q : Λ → Z → Bool) {ℓ : ℕ} (z : Fin ℓ → Z) :
    1 ≤ numSeparations Q z := by
  unfold numSeparations
  have : (Set.range (fun α : Λ => fun i : Fin ℓ => Q α (z i))).Nonempty := Set.range_nonempty _
  exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (Set.toFinite _)).mpr this).ne'

theorem g69f_maxSep_le {Z Λ : Type*} [Nonempty Z] (Q : Λ → Z → Bool) (ℓ : ℕ) :
    maxSeparations Q ℓ ≤ 2 ^ ℓ := by
  unfold maxSeparations
  exact ciSup_le fun z => g69f_numSep_le Q z

theorem g69f_maxSep_bdd {Z Λ : Type*} (Q : Λ → Z → Bool) (ℓ : ℕ) :
    BddAbove (Set.range fun z : Fin ℓ → Z => numSeparations Q z) :=
  ⟨2 ^ ℓ, by rintro _ ⟨z, rfl⟩; exact g69f_numSep_le Q z⟩

theorem g69f_maxSep_pos {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool) (ℓ : ℕ) :
    1 ≤ maxSeparations Q ℓ := by
  unfold maxSeparations
  obtain ⟨z⟩ : Nonempty (Fin ℓ → Z) := inferInstance
  exact (g69f_numSep_pos Q z).trans (le_ciSup (g69f_maxSep_bdd Q ℓ) z)

theorem g69f_maxSep_eq_iff {Z Λ : Type*} [Nonempty Z] (Q : Λ → Z → Bool) (ℓ : ℕ) :
    maxSeparations Q ℓ = 2 ^ ℓ ↔ ∃ z : Fin ℓ → Z, Shatters Q z := by
  constructor
  · intro h
    have hmem : sSup (Set.range fun z : Fin ℓ → Z => numSeparations Q z) ∈
        Set.range fun z : Fin ℓ → Z => numSeparations Q z :=
      Nat.sSup_mem (Set.range_nonempty _) (g69f_maxSep_bdd Q ℓ)
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, (g69f_numSep_eq_iff Q z).mp ?_⟩
    have hz' : numSeparations Q z = maxSeparations Q ℓ := hz
    rw [hz']; exact h
  · rintro ⟨z, hz⟩
    apply le_antisymm (g69f_maxSep_le Q ℓ)
    rw [← (g69f_numSep_eq_iff Q z).mpr hz]
    exact le_ciSup (g69f_maxSep_bdd Q ℓ) z

theorem g69f_G_eq_iff {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool) (ℓ : ℕ) :
    growthFunction Q ℓ = (ℓ : ℝ) * Real.log 2 ↔ ∃ z : Fin ℓ → Z, Shatters Q z := by
  rw [← g69f_maxSep_eq_iff, growthFunction, ← Real.log_pow]
  have h1 : (0:ℝ) < maxSeparations Q ℓ := by exact_mod_cast g69f_maxSep_pos Q ℓ
  constructor
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr (by positivity)) h
    exact_mod_cast this
  · intro h; rw [h]; push_cast; rfl

theorem g69f_G_lt_iff {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool) (ℓ : ℕ) :
    growthFunction Q ℓ < (ℓ : ℝ) * Real.log 2 ↔ ¬ ∃ z : Fin ℓ → Z, Shatters Q z := by
  rw [← g69f_maxSep_eq_iff, growthFunction, ← Real.log_pow]
  have h1 : (0:ℝ) < maxSeparations Q ℓ := by exact_mod_cast g69f_maxSep_pos Q ℓ
  rw [Real.log_lt_log_iff h1 (by positivity)]
  have := g69f_maxSep_le Q ℓ
  constructor
  · intro h heq; rw [heq] at h; push_cast at h; exact lt_irrefl _ h
  · intro h
    have : maxSeparations Q ℓ < 2 ^ ℓ := lt_of_le_of_ne this h
    exact_mod_cast this

theorem solution {Z Λ : Type*} [Nonempty Z] [Nonempty Λ] (Q : Λ → Z → Bool) :
    (vcDim Q = ⊤ ↔ ∀ ℓ : ℕ, growthFunction Q ℓ = (ℓ : ℝ) * Real.log 2) ∧
    ∀ h : ℕ, (vcDim Q = (h : ℕ∞) ↔
      (growthFunction Q h = (h : ℝ) * Real.log 2 ∧
        growthFunction Q (h + 1) < ((h + 1 : ℕ) : ℝ) * Real.log 2)) := by
  have hdown : ∀ m k, (∃ z : Fin m → Z, Shatters Q z) → k ≤ m → ∃ z : Fin k → Z, Shatters Q z :=
    fun m k hm hkm => g69f_shatters_down Q m k hm hkm
  have h0 : ∃ z : Fin 0 → Z, Shatters Q z := by
    obtain ⟨α⟩ : Nonempty Λ := inferInstance
    exact ⟨Fin.elim0, fun δ => ⟨α, fun i => i.elim0⟩⟩
  refine ⟨?_, fun h => ?_⟩
  · rw [vcDim, g69f_supP_top _ hdown]
    simp only [g69f_G_eq_iff]
  · rw [vcDim, g69f_supP_eq _ hdown h0, g69f_G_eq_iff, g69f_G_lt_iff]
