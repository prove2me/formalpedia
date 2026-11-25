-- Prove2me | solution 1 for GlobalTheory.DoubleCosetIndicator.exists_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:23.926339+00:00
-- url     : https://prove2.me/submissions/68997177-b691-4a99-a7f9-b1ca823f8b74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqSumIndicator
import Theorems.Thm_GlobalTheory_DoubleCosetIndicator_dc_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetIndicator
namespace GlobalTheory.DoubleCosetIndicator
theorem _root_.solution {G : Type} [Group G] {M : Type} [AddCommMonoid M]
    (R K : Subgroup G) (T : Finset G) (φ : G → M)
    (hR : ∀ r ∈ R, ∀ x : G, φ (r * x) = φ x) (hK : ∀ κ ∈ K, ∀ x : G, φ (x * κ) = φ x)
    (hT : ∀ x : G, φ x ≠ 0 → ∃ t ∈ T, x ∈ dc R K t) :
    ∃ c : G → M, (∀ t : G, c t = 0 ∨ c t = φ t) ∧
      ∀ x : G, φ x = ∑ t ∈ T, Set.indicator (dc R K t) (fun _ => c t) x := by
  classical

  let S : G → Finset G := fun t => T.filter (fun t' => dc R K t' = dc R K t)
  let rep : G → G := fun t => if h : (S t).Nonempty then h.choose else t
  let c : G → M := fun t => if t ∈ T ∧ rep t = t then φ t else 0
  have hdc_eq : ∀ {s t x : G}, x ∈ dc R K s → x ∈ dc R K t → dc R K s = dc R K t := fun hs ht =>
    Set.Subset.antisymm (dc_subset R K hs ht) (dc_subset R K ht hs)
  have hinv : ∀ {s x : G}, x ∈ dc R K s → φ x = φ s := by
    rintro s x ⟨r, hr, κ, hκ, rfl⟩
    rw [hK κ hκ, hR r hr]
  refine ⟨c, fun t => ?_, fun x => ?_⟩
  · simp only [c]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases hx : ∃ t ∈ T, x ∈ dc R K t
  · obtain ⟨t0, ht0, hxt0⟩ := hx
    have hS : (S t0).Nonempty := ⟨t0, Finset.mem_filter.mpr ⟨ht0, rfl⟩⟩
    obtain ⟨ht1T, ht1dc⟩ := Finset.mem_filter.mp hS.choose_spec
    have hrep : ∀ t, dc R K t = dc R K t0 → rep t = hS.choose := by
      intro t ht
      have hSt : S t = S t0 := by simp only [S, ht]
      simp only [rep, hSt, dif_pos hS]
    have hxt1 : x ∈ dc R K hS.choose := by rw [ht1dc]; exact hxt0
    rw [Finset.sum_eq_single hS.choose]
    · have hc1 : c hS.choose = φ hS.choose := by
        simp only [c]
        rw [if_pos ⟨ht1T, hrep _ ht1dc⟩]
      rw [Set.indicator_of_mem hxt1, hc1, hinv hxt1]
    · intro t _ hne
      by_cases hxt : x ∈ dc R K t
      · have hc0 : c t = 0 := by
          simp only [c]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (h.symm.trans (hrep t (hdc_eq hxt hxt0)))
        rw [Set.indicator_of_mem hxt, hc0]
      · rw [Set.indicator_of_notMem hxt]
    · intro h
      exact absurd ht1T h
  · push_neg at hx
    have hφ : φ x = 0 := by
      by_contra h
      obtain ⟨t, ht, hxt⟩ := hT x h
      exact hx t ht hxt
    rw [hφ]
    symm
    exact Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (hx t ht) _
end GlobalTheory.DoubleCosetIndicator
