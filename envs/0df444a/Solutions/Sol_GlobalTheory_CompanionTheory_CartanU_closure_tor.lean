-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.closure_tor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:38:13.613329+00:00
-- url     : https://prove2.me/submissions/3fb06652-1460-4d46-9976-f188ae6b1435

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_ind_antitone
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution {M : Type} [Monoid M] {l : ℕ} (T : (Fin l → ℕ) → M) (h0 : T 0 = 1)
    (hadd : ∀ a b, T (a + b) = T a * T b) (g : M) :
    g ∈ Submonoid.closure (Set.range fun i : Fin l => T (ind i)) ↔
      ∃ r : Fin l → ℕ, Antitone r ∧ g = T r := by
  constructor
  · intro hg
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨ind i, ind_antitone i, rfl⟩
    | one => exact ⟨0, fun _ _ _ => le_rfl, h0.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, ha.add hb, (hadd a b).symm⟩
  · rintro ⟨r, hr, rfl⟩
    have key : ∀ m : ℕ, ∀ r : Fin l → ℕ, ∑ j, r j = m → Antitone r →
        T r ∈ Submonoid.closure (Set.range fun i : Fin l => T (ind i)) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro r hm hr
        by_cases h : r = 0
        · rw [h, h0]; exact one_mem _
        · obtain ⟨j₀, hj₀⟩ : ∃ j, r j ≠ 0 := by
            by_contra hc
            push_neg at hc
            exact h (funext hc)
          have hS : (Finset.univ.filter fun j => r j ≠ 0).Nonempty := ⟨j₀, by simp [hj₀]⟩
          obtain ⟨i, hidef⟩ : ∃ i, i = (Finset.univ.filter fun j => r j ≠ 0).max' hS := ⟨_, rfl⟩
          have hi : r i ≠ 0 := by
            have := Finset.max'_mem _ hS
            rw [← hidef] at this
            simpa using this
          have hlt : ∀ j, ¬ j ≤ i → r j = 0 := fun j hj => by
            by_contra hc
            apply hj
            rw [hidef]
            exact Finset.le_max' _ j (by simp [hc])
          have hpos : ∀ j, j ≤ i → 1 ≤ r j := fun j hj => by
            have := hr hj
            omega
          have hsplit : r = ind i + (r - ind i) := by
            funext j
            simp only [Pi.add_apply, Pi.sub_apply, ind]
            split_ifs with hj
            · have := hpos j hj
              omega
            · omega
          have hanti : Antitone (r - ind i) := by
            intro a b hab
            simp only [Pi.sub_apply, ind]
            have hab' := hr hab
            split_ifs with h1 h2 h2
            · omega
            · exact absurd (hab.trans h1) h2
            · have := hlt b h1
              omega
            · omega
          have hsum : ∑ j, (r - ind i) j < m := by
            have h1 : ∑ j, r j = ∑ j, ind i j + ∑ j, (r - ind i) j := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun j _ => congrFun hsplit j
            have h2 : ind i i ≤ ∑ j, ind i j :=
              Finset.single_le_sum (f := ind i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            have h3 : ind i i = 1 := by simp [ind]
            omega
          rw [show T r = T (ind i) * T (r - ind i) by rw [← hadd, ← hsplit]]
          exact mul_mem (Submonoid.subset_closure ⟨i, rfl⟩) (ih _ hsum _ rfl hanti)
    exact key _ r rfl hr
end GlobalTheory.CompanionTheory.CartanU
