-- Prove2me | solution 1 for GlobalTheory.packing_geometric_mean_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:12.176414+00:00
-- url     : https://prove2.me/submissions/bfd9fbeb-3ca7-4378-936d-3db714320626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PackingGeometricMeanSeparated
import Theorems.Thm_GlobalTheory_card_le_of_separated_in_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : ι → Type) [∀ v, NormedAddCommGroup (W v)] [∀ v, NormedSpace ℝ (W v)] [∀ v, FiniteDimensional ℝ (W v)] (N : ℕ), 1 ≤ N → (∀ v, Module.finrank ℝ (W v) = N) → ∀ (la : ℝ) (S : Set (∀ v, W v)) (X : ι → ℝ), 0 < la → (∀ v, 0 < X v) → (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ≤ (∏ v, ‖s v - s' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → {s ∈ S | ∀ v, ‖s v‖ ≤ X v}.Finite ∧ (({s ∈ S | ∀ v, ‖s v‖ ≤ X v}.ncard : ℕ) : ℝ) ≤ (1 + 2 * (∏ v, X v) ^ ((1 : ℝ) / Fintype.card ι) / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ N hN hdim la S X hla hX hsep
  classical
  set k := Fintype.card ι with hk
  have hkpos : 0 < k := Fintype.card_pos
  set P := ∏ v, X v with hP
  have hPpos : 0 < P := Finset.prod_pos (fun v _ => hX v)
  set G := P ^ ((1 : ℝ) / k) with hG
  have hGpos : 0 < G := Real.rpow_pos_of_pos hPpos _
  have hGk : G ^ k = P := by
    rw [hG, one_div]
    exact Real.rpow_inv_natCast_pow hPpos.le hkpos.ne'
  set c : ι → ℝ := fun v => G / X v with hc
  have hcpos : ∀ v, 0 < c v := fun v => div_pos hGpos (hX v)
  have hcprod : ∏ v, c v = 1 := by
    rw [hc, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← hk, hGk]
    exact div_self hPpos.ne'
  let φ : (∀ v, W v) → (∀ v, W v) := fun s v => c v • s v
  have hφinj : Function.Injective φ := by
    intro s s' h
    funext v
    exact smul_right_injective _ (hcpos v).ne' (congrFun h v)
  set A := {s ∈ S | ∀ v, ‖s v‖ ≤ X v} with hA
  have hdimPi : Module.finrank ℝ (∀ v, W v) = N * k := by
    rw [Module.finrank_pi_fintype]
    simp [hdim, hk, mul_comm]
  have key : ∀ F : Finset (∀ v, W v), (↑F : Set (∀ v, W v)) ⊆ A →
      (F.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * k) := by
    intro F hF
    have hbound := card_le_of_separated_in_ball (F.image φ) G la hGpos.le hla ?_ ?_
    · rw [Finset.card_image_of_injective _ hφinj, hdimPi] at hbound
      exact hbound
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      have hsA := hF hs
      refine (pi_norm_le_iff_of_nonneg hGpos.le).mpr (fun v => ?_)
      simp only [φ, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos v)]
      calc c v * ‖s v‖ ≤ c v * X v := mul_le_mul_of_nonneg_left (hsA.2 v) (hcpos v).le
        _ = G := by
          simp only [hc]
          field_simp [(hX v).ne']
    · intro y hy y' hy' hne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hy'
      have hss : s ≠ s' := fun h => hne (by rw [h])
      have h1 := hsep s (hF hs).1 s' (hF hs').1 hss
      have hprod : ∏ v, ‖(φ s - φ s') v‖ = ∏ v, ‖s v - s' v‖ := by
        simp only [φ, Pi.sub_apply, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos _),
          Finset.prod_mul_distrib, hcprod, one_mul]
      have hgm : (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ ‖φ s - φ s'‖ := by
        have hle : ∏ v, ‖(φ s - φ s') v‖ ≤ ‖φ s - φ s'‖ ^ k := by
          rw [hk, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod (fun v _ => norm_nonneg _) (fun v _ => norm_le_pi_norm _ v)
        calc (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ (‖φ s - φ s'‖ ^ k) ^ ((1 : ℝ) / k) :=
              Real.rpow_le_rpow (Finset.prod_nonneg (fun v _ => norm_nonneg _)) hle (by positivity)
          _ = ‖φ s - φ s'‖ := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
                mul_one_div_cancel (by exact_mod_cast hkpos.ne'), Real.rpow_one]
      rw [hprod] at hgm
      exact h1.trans hgm
  have hfin : A.Finite := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf (⌈(1 + 2 * G / la) ^ (N * k)⌉₊ + 1)
    have h3 := key F hF
    rw [hcard] at h3
    push_cast at h3
    linarith [Nat.le_ceil ((1 + 2 * G / la) ^ (N * k))]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card A hfin]
  exact key _ (by simp)
end GlobalTheory
