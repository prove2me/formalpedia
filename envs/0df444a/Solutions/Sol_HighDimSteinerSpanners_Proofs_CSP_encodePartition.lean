-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.encodePartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:00.516848+00:00
-- url     : https://prove2.me/submissions/8071086f-6c48-4db7-8262-c76f6f352d3c

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N K k : ℕ} (hk : k ≤ K) (M : Finset (Fin N))
    (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N))
    (hMpart : M ⊆ Finset.univ.biUnion A ∪ I_k)
    (hAdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hAIdisjoint : ∀ r, Disjoint (A r) I_k) :
    ∃ τ : Fin N → Fin (K + 1),
      (∀ u ∈ M, τ u = 0 ↔ u ∈ I_k) ∧
      (∀ (r : Fin K) (hr : r.1 < k), ∀ u ∈ M, τ u = r.succ ↔ u ∈ A ⟨r.1, hr⟩) ∧
      (∀ u ∈ M, (τ u).1 ≤ k) ∧
      (∀ (r : Fin K) (hr : r.1 < k),
        M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) =
          M ∩ ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k)) ∧
      (∀ u, u ∉ M → τ u = 0) := by
  classical
  let τ : Fin N → Fin (K + 1) := fun u =>
    if u ∈ M then
      if h : ∃ r : Fin k, u ∈ A r then
        (⟨(Classical.choose h).1, lt_of_lt_of_le (Classical.choose h).2 hk⟩ : Fin K).succ
      else 0
    else 0
  have hτ_zero_iff : ∀ u ∈ M, τ u = 0 ↔ u ∈ I_k := by
    intro u huM
    dsimp [τ]
    rw [if_pos huM]
    have huI : u ∈ Finset.univ.biUnion A ∪ I_k := hMpart huM
    by_cases hex : ∃ r : Fin k, u ∈ A r
    · rw [dif_pos hex]
      have hne0 :
          (⟨(Classical.choose hex).1,
            lt_of_lt_of_le (Classical.choose hex).2 hk⟩ : Fin K).succ ≠ 0 :=
        Fin.succ_ne_zero _
      obtain ⟨r, hur⟩ := hex
      have hnotIk : u ∉ I_k := Finset.disjoint_left.mp (hAIdisjoint r) hur
      exact iff_of_false hne0 hnotIk
    · rw [dif_neg hex]
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at huI
      rcases huI with ⟨r, hur⟩ | huIk
      · exact absurd ⟨r, hur⟩ hex
      · exact iff_of_true rfl huIk
  have hτ_succ_iff : ∀ (r : Fin K) (hr : r.1 < k), ∀ u ∈ M,
      τ u = r.succ ↔ u ∈ A ⟨r.1, hr⟩ := by
    intro r hr u huM
    dsimp only [τ]
    rw [if_pos huM]
    constructor
    · intro hτ
      by_cases hex : ∃ j : Fin k, u ∈ A j
      · rw [dif_pos hex] at hτ
        have hval : (Classical.choose hex).1 + 1 = r.1 + 1 := by
          simpa [Fin.ext_iff, Fin.val_succ] using hτ
        have hj_eq : Classical.choose hex = ⟨r.1, hr⟩ :=
          Fin.ext (by change (Classical.choose hex).1 = r.1; omega)
        exact hj_eq ▸ Classical.choose_spec hex
      · rw [dif_neg hex] at hτ
        exact absurd hτ.symm (Fin.succ_ne_zero r)
    · intro huA
      have hex : ∃ j : Fin k, u ∈ A j := ⟨⟨r.1, hr⟩, huA⟩
      rw [dif_pos hex]
      have hch_eq : Classical.choose hex = ⟨r.1, hr⟩ := by
        by_contra hne
        exact Finset.disjoint_left.mp (hAdisjoint hne) (Classical.choose_spec hex) huA
      ext
      simp [hch_eq]
  have hτ_le_k : ∀ u ∈ M, (τ u).1 ≤ k := by
    intro u huM
    dsimp [τ]
    rw [if_pos huM]
    split_ifs with hex
    · exact (Classical.choose hex).2
    · exact Nat.zero_le k
  have hIt_eq : ∀ (r : Fin K) (hr : r.1 < k),
      M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) =
        M ∩ ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) := by
    intro r hr
    ext u
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨huM, h0 | hgt⟩
      · exact ⟨huM, Or.inr ((hτ_zero_iff u huM).mp h0)⟩
      · have hne0 : τ u ≠ 0 := by intro h; simp [h] at hgt
        have hle : (τ u).1 ≤ k := hτ_le_k u huM
        let j0 : Fin K := ⟨(τ u).1 - 1, lt_of_lt_of_le (by omega) hk⟩
        have hj0_lt : j0.1 < k := by dsimp [j0]; omega
        have hτ_j0 : τ u = j0.succ := by ext; dsimp [j0]; omega
        have huAj0 : u ∈ A ⟨j0.1, hj0_lt⟩ := (hτ_succ_iff j0 hj0_lt u huM).mp hτ_j0
        refine ⟨huM, Or.inl ⟨⟨j0.1, hj0_lt⟩, ?_, huAj0⟩⟩
        simp only [Fin.lt_def, j0]; omega
    · rintro ⟨huM, ⟨j, hrj, huAj⟩ | huIk⟩
      · have hjK : j.1 < K := lt_of_lt_of_le j.2 hk
        have hτj : τ u = (⟨j.1, hjK⟩ : Fin K).succ :=
          (hτ_succ_iff ⟨j.1, hjK⟩ j.2 u huM).mpr huAj
        refine ⟨huM, Or.inr ?_⟩
        rw [hτj, Fin.val_succ]
        dsimp only
        simp only [Fin.lt_def] at hrj
        omega
      · exact ⟨huM, Or.inl ((hτ_zero_iff u huM).mpr huIk)⟩
  exact ⟨τ, hτ_zero_iff, hτ_succ_iff, hτ_le_k, hIt_eq,
    fun u hu => by simp only [τ, if_neg hu]⟩
end HighDimSteinerSpanners.Proofs.CSP
