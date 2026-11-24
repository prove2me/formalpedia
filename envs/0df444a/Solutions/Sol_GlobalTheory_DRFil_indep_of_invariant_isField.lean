-- Prove2me | solution 1 for GlobalTheory.DRFil.indep_of_invariant_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:16.502802+00:00
-- url     : https://prove2.me/submissions/717dcf94-c927-4c06-b8fa-7f8c799a0f86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOfLinearIndependentDdRE
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul


section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
namespace GlobalTheory.DRFil
private theorem eq_zero_of_sum_smul_invariant_eq_zero_of_card_support_le {G E M ι : Type} [CommRing E] [DecidableEq E] [DecidableEq ι]
    (hE : IsField E) [AddCommGroup M] [Module E M] [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0) :
    ∀ n : ℕ, ∀ c : ι → E, (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n →
      ∑ i, c i • v i = 0 → ∀ i, c i = 0 := by
  intro n
  induction n with
  | zero =>
    intro c hcard _ i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [hi]
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ n ih =>
    intro c hcard hsum
    by_contra hne
    push_neg at hne
    obtain ⟨i₀, hi₀⟩ := hne
    obtain ⟨b, hb⟩ := hE.mul_inv_cancel hi₀

    obtain ⟨c', hc'⟩ : ∃ c' : ι → E, ∀ i, c' i = b * c i := ⟨fun i => b * c i, fun _ => rfl⟩
    have hsum' : ∑ i, c' i • v i = 0 := by
      simp only [hc', mul_smul, ← Finset.smul_sum, hsum, smul_zero]
    have hone : c' i₀ = 1 := by rw [hc', mul_comm, hb]
    have hsupp : ∀ i, c' i ≠ 0 → c i ≠ 0 := by
      intro i h hci
      exact h (by rw [hc', hci, mul_zero])
    have hinv : ∀ g i, σ g (c' i) = c' i := by
      intro g

      obtain ⟨d, hd⟩ : ∃ d : ι → E, ∀ i, d i = σ g (c' i) - c' i := ⟨fun i => σ g (c' i) - c' i, fun _ => rfl⟩
      have h1 : ∑ i, σ g (c' i) • v i = 0 := by
        have hmap : ρ g (∑ i, c' i • v i) = ∑ i, σ g (c' i) • v i := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hρ, hv]
        rw [← hmap, hsum', map_zero]
      have hdsum : ∑ i, d i • v i = 0 := by
        simp only [hd, sub_smul, Finset.sum_sub_distrib, h1, hsum', sub_zero]
      have hdcard : (Finset.univ.filter (fun i => d i ≠ 0)).card ≤ n := by
        have hsub : Finset.univ.filter (fun i => d i ≠ 0) ⊆
            (Finset.univ.filter (fun i => c i ≠ 0)).erase i₀ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · rintro rfl
            apply hi
            rw [hd, hone, map_one, sub_self]
          · apply hsupp
            intro h0
            apply hi
            rw [hd, h0, map_zero, sub_zero]
        have hmem : i₀ ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [hi₀]
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem] at hle
        omega
      intro i
      have h0 := ih d hdcard hdsum i
      rw [hd, sub_eq_zero] at h0
      exact h0
    have h1 := hind c' hinv hsum' i₀
    rw [hone] at h1
    haveI : Nontrivial E := ⟨hE.exists_pair_ne⟩
    exact one_ne_zero h1
end GlobalTheory.DRFil
end

set_option autoImplicit false
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
open GlobalTheory GlobalTheory.DRFil
namespace GlobalTheory.DRFil
theorem _root_.solution {G E M ι : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (c : ι → E) (hc : ∑ i, c i • v i = 0) : ∀ i, c i = 0 := by
  classical
  exact eq_zero_of_sum_smul_invariant_eq_zero_of_card_support_le hE σ ρ hρ v hv hind
    (Finset.univ.filter (fun i => c i ≠ 0)).card c le_rfl hc
end GlobalTheory.DRFil
