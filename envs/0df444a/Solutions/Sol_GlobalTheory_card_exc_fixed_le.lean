-- Prove2me | solution 1 for GlobalTheory.card_exc_fixed_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:52.360157+00:00
-- url     : https://prove2.me/submissions/2a80fa33-57d2-419d-9889-ec46d1e4ccaa

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
import Theorems.Thm_GlobalTheory_card_class_in_dyadic_le
import Theorems.Thm_GlobalTheory_div_le_rpow_three_quarters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) (Y : ℝ) (hY : 2 ≤ Y) (ℓ d : ℕ)
    (hd : 1 ≤ d) (T : Finset ℕ)
    (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ Formalism.CyclotomicNorms.Exc g d ℓ) :
    (T.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  rcases T.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (by linarith)
  obtain ⟨g0, hg0, hmin⟩ := T.exists_min_image (fun g => padicValNat ℓ (g ^ d - 1)) hne
  obtain ⟨w, hw⟩ : ∃ w, w = padicValNat ℓ (g0 ^ d - 1) := ⟨_, rfl⟩
  have hmin' : ∀ g ∈ T, w ≤ padicValNat ℓ (g ^ d - 1) := by
    intro g hg
    rw [hw]
    exact hmin g hg
  have hg1 : ∀ g ∈ T, 1 ≤ g := fun g hg => by
    have h := (hT g hg).1
    have : (1 : ℝ) ≤ g := by linarith
    exact_mod_cast this
  have hgd : ∀ g ∈ T, 1 ≤ g ^ d := fun g hg => Nat.one_le_pow _ _ (hg1 g hg)
  obtain ⟨hℓ, hlt0⟩ := (hT g0 hg0).2.2
  rw [← hw] at hlt0
  have hw1 : 1 ≤ w := by
    by_contra h0
    have h00 : w = 0 := by omega
    rw [h00, mul_zero, pow_zero] at hlt0
    have := hgd g0 hg0
    omega
  have hM0 : 0 < ℓ ^ w := pow_pos hℓ.pos _
  have : NeZero (ℓ ^ w) := ⟨hM0.ne'⟩
  have hroot : ∀ g ∈ T, ((g : ZMod (ℓ ^ w))) ^ d = 1 := by
    intro g hg
    have h1 : ℓ ^ w ∣ g ^ d - 1 := (pow_dvd_pow ℓ (hmin' g hg)).trans pow_padicValNat_dvd
    have h2 : 1 ≡ g ^ d [MOD ℓ ^ w] := (Nat.modEq_iff_dvd' (hgd g hg)).2 h1
    have h3 := (ZMod.natCast_eq_natCast_iff 1 (g ^ d) (ℓ ^ w)).2 h2
    push_cast at h3
    exact h3.symm
  have hYM : Y < ((ℓ ^ w : ℕ) : ℝ) ^ 4 := by
    have h1 : (g0 : ℝ) ≤ ((g0 ^ d : ℕ) : ℝ) := by exact_mod_cast Nat.le_self_pow (by omega) g0
    have h2 : g0 ^ d < (ℓ ^ w) ^ 4 := by rw [← pow_mul, mul_comm]; exact hlt0
    have h3 : ((g0 ^ d : ℕ) : ℝ) < (((ℓ ^ w) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_pow (ℓ ^ w) 4] at h3
    linarith [(hT g0 hg0).1]
  have hfib : ∀ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))),
      ((T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    intro a _
    have h1 := card_class_in_dyadic_le Y (by linarith) (ℓ ^ w) hM0
      (T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a)
      (fun g hg => ⟨(hT g (Finset.mem_filter.1 hg).1).1, (hT g (Finset.mem_filter.1 hg).1).2.1⟩)
      (fun g hg g' hg' => (ZMod.natCast_eq_natCast_iff g g' (ℓ ^ w)).1
        ((Finset.mem_filter.1 hg).2.trans (Finset.mem_filter.1 hg').2.symm))
    have h2 := div_le_rpow_three_quarters Y ((ℓ ^ w : ℕ) : ℝ) (by linarith)
      (by exact_mod_cast hM0) hYM
    linarith
  have himg : (T.image fun g : ℕ => (g : ZMod (ℓ ^ w))).card ≤ 2 * d := by
    have hsub : T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))) ⊆
        Finset.univ.filter (fun x : ZMod (ℓ ^ w) => x ^ d = 1) := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hroot g hg⟩
    refine (Finset.card_le_card hsub).trans ?_
    have h1 := (hR ℓ w d hℓ hw1 hd).2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    exact h1
  rw [Finset.card_eq_sum_card_image (fun g : ℕ => (g : ZMod (ℓ ^ w))) T]
  push_cast
  calc ∑ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))),
        ((T.filter fun g : ℕ => (g : ZMod (ℓ ^ w)) = a).card : ℝ)
      ≤ ∑ a ∈ T.image (fun g : ℕ => (g : ZMod (ℓ ^ w))), (Y ^ ((3 : ℝ) / 4) + 1) :=
        Finset.sum_le_sum hfib
    _ = ((T.image fun g : ℕ => (g : ZMod (ℓ ^ w))).card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact_mod_cast himg
end GlobalTheory
