-- Prove2me | solution 1 for GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:34.503511+00:00
-- url     : https://prove2.me/submissions/9b5aa83a-3b65-4bca-b8b9-fd13d6ee8dd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndepOnOfFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LinearIndependentFixed
namespace GlobalTheory.LinearIndependentFixed
theorem _root_.solution {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W]
    [Module.IsTorsionFree B W] (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), σ g (b • w) = a g b • σ g w)
    (hK : ∀ (b b' : B), b ≠ 0 → (∀ g : G, b * a g b' = a g b * b') →
      ∃ c : K, b' = algebraMap K B c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), σ g (v i) = v i)
    (s : Finset ι) (hs : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by
  classical
  have hsli : LinearIndependent K (fun x : (↑s : Set ι) => v x) := hs
  rw [LinearIndepOn, Fintype.linearIndependent_iff] at hs ⊢

  suffices H : ∀ k : ℕ, ∀ b : (↑s : Set ι) → B,
      (Finset.univ.filter fun j => b j ≠ 0).card ≤ k → ∑ j, b j • v j = 0 → ∀ j, b j = 0 by
    intro b hb
    exact H _ b le_rfl hb
  intro k
  induction k with
  | zero =>
    intro b hcard _ j
    by_contra hj
    have hmem : j ∈ Finset.univ.filter fun j => b j ≠ 0 := by simp [hj]
    have := Finset.card_pos.mpr ⟨j, hmem⟩
    omega
  | succ k ih =>
    intro b hcard hsum
    by_contra hnot
    obtain ⟨j0, hj0⟩ := not_forall.mp hnot
    have hvj0 : v j0 ≠ 0 := hsli.ne_zero j0
    have ha0 : ∀ g, a g 0 = 0 := by
      intro g
      have h := hσ g 0 (v j0)
      rw [zero_smul, map_zero, hv] at h
      exact (smul_eq_zero.mp h.symm).resolve_right hvj0

    have hrel : ∀ g, ∀ j, b j0 * a g (b j) = a g (b j0) * b j := by
      intro g
      obtain ⟨b', hb'⟩ : ∃ b' : (↑s : Set ι) → B, b' = fun j => b j0 * a g (b j) - a g (b j0) * b j :=
        ⟨_, rfl⟩
      have hbeq : ∀ j, b' j = b j0 * a g (b j) - a g (b j0) * b j := fun j => by rw [hb']
      have hσsum : ∑ j, a g (b j) • v j = 0 := by
        have := congrArg (σ g) hsum
        rw [map_sum, map_zero] at this
        simpa [hσ, hv] using this
      have hsum' : ∑ j, b' j • v j = 0 := by
        calc ∑ j, b' j • v j = b j0 • ∑ j, a g (b j) • v j - a g (b j0) • ∑ j, b j • v j := by
              simp only [hbeq, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
          _ = 0 := by rw [hσsum, hsum, smul_zero, smul_zero, sub_zero]
      have hsub : (Finset.univ.filter fun j => b' j ≠ 0) ⊆ (Finset.univ.filter fun j => b j ≠ 0).erase j0 := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact hj (by rw [hbeq]; ring)
        · intro hbj
          exact hj (by rw [hbeq, hbj, ha0]; ring)
      have hc : (Finset.univ.filter fun j => b' j ≠ 0).card ≤ k := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by simp [hj0])] at h1
        omega
      intro j
      have h2 := ih b' hc hsum' j
      rw [hbeq] at h2
      exact sub_eq_zero.mp h2

    choose c hc using fun j => hK (b j0) (b j) hj0 (fun g => hrel g j)
    have hcsum : ∑ j, c j • v j = 0 := by
      have h1 : ∑ j, b j • v j = b j0 • ∑ j, c j • v j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc j, mul_comm, mul_smul, algebraMap_smul]
      rw [h1] at hsum
      exact (smul_eq_zero.mp hsum).resolve_left hj0
    have hcj0 := hs c hcsum j0
    have hb0 := hc j0
    rw [hcj0, map_zero, zero_mul] at hb0
    exact hj0 hb0
end GlobalTheory.LinearIndependentFixed
