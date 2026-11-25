-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.highest_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:56.882064+00:00
-- url     : https://prove2.me/submissions/d0d34635-6113-4a3f-9166-32b1c74b3008

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Theorems.Thm_GlobalTheory_KTypeCompare_torus_mem
import Theorems.Thm_GlobalTheory_KTypeCompare_cptLE_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.KTypeCompare
theorem _root_.solution {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H}
    (hσ : HarishChandraRootData.IsUnitaryRepOn (HarishChandraRootData.grpK ε) σ) {S : Submodule ℂ H} {Λ : Fin n → ℝ}
    (h : HarishChandraRootData.IsKType ε σ S Λ) {a b : Fin n} (hab : a < b) (hε : ε a = ε b) : Λ b ≤ Λ a := by
  set s : Equiv.Perm (Fin n) := Equiv.swap a b with hs_def
  have hεs : ∀ i, ε (s i) = ε i := by
    intro i
    rw [hs_def, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hε]
    · rw [h2, hε]
    · rfl
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ,
      P = Matrix.of fun i j => if s i = j then (1 : ℂ) else 0 := ⟨_, rfl⟩
  have hPl : ∀ M : Matrix (Fin n) (Fin n) ℂ, P * M = M.submatrix s id := by
    intro M
    ext i k
    simp [hP, Matrix.mul_apply, ite_mul]
  have hPr : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * P = M.submatrix id s := by
    intro M
    ext i k
    simp [hP, Matrix.mul_apply, mul_ite, hs_def, Equiv.swap_apply_eq_iff]
  have hPstar : star P = P := by
    ext i j
    simp only [hP, Matrix.star_apply, Matrix.of_apply]
    by_cases hij : s i = j
    · have hji : s j = i := by rw [← hij, hs_def, Equiv.swap_apply_self]
      simp [hij, hji]
    · have hji : s j ≠ i := fun h' => hij (by rw [← h', hs_def, Equiv.swap_apply_self])
      simp [hij, hji]
  have hPP : P * P = 1 := by
    rw [hPl]
    ext i k
    simp [hP, Matrix.one_apply, hs_def]
  have hPK : P ∈ HarishChandraRootData.grpK ε := by
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, hPstar, hPP]
    · rw [hP, Matrix.of_apply, if_neg]
      rintro rfl
      exact hij (hεs i).symm
  have hcomm : ∀ θ : Fin n → ℝ, HarishChandraRootData.torus θ * P = P * HarishChandraRootData.torus (fun i => θ (s i)) := by
    intro θ
    rw [hPl, hPr]
    ext i k
    simp only [HarishChandraRootData.torus, Matrix.submatrix_apply, id, Matrix.diagonal_apply]
    by_cases hik : i = s k
    · have hk : s i = k := by rw [hik, hs_def, Equiv.swap_apply_self]
      rw [if_pos hik, if_pos hk, hk, ← hik]
    · have hk : s i ≠ k := fun h' => hik (by rw [← h', hs_def, Equiv.swap_apply_self])
      rw [if_neg hik, if_neg hk]
  have hTK : ∀ θ, HarishChandraRootData.torus θ ∈ HarishChandraRootData.grpK ε := torus_mem ε
  obtain ⟨v, hvS, hv0, hvw⟩ := h.exists_highest
  have hvw' : ∀ θ, σ (HarishChandraRootData.torus θ) v = HarishChandraRootData.wtChar Λ θ • v := hvw
  have hwS : σ P v ∈ S := h.stable P hPK v hvS
  have hw0 : σ P v ≠ 0 := by
    intro h0
    apply hv0
    have hn := hσ.norm_map P hPK v
    rw [h0, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm
  have hww : HarishChandraRootData.IsWeightVector σ (fun i => Λ (s i)) (σ P v) := by
    refine ⟨hw0, ?_⟩
    show ∀ θ : Fin n → ℝ,
      σ (HarishChandraRootData.torus θ) (σ P v) = HarishChandraRootData.wtChar (fun i => Λ (s i)) θ • σ P v
    intro θ
    have hre : ∑ i, Λ i * θ (s i) = ∑ i, Λ (s i) * θ i := by
      rw [← Equiv.sum_comp s (fun i => Λ i * θ (s i))]
      simp [hs_def, Equiv.swap_apply_self]
    calc σ (HarishChandraRootData.torus θ) (σ P v) = σ (HarishChandraRootData.torus θ * P) v := by
          rw [hσ.map_mul _ (hTK θ) _ hPK]
          rfl
      _ = σ (P * HarishChandraRootData.torus (fun i => θ (s i))) v := by rw [hcomm]
      _ = σ P (σ (HarishChandraRootData.torus (fun i => θ (s i))) v) := by
          rw [hσ.map_mul _ hPK _ (hTK _)]
          rfl
      _ = HarishChandraRootData.wtChar Λ (fun i => θ (s i)) • σ P v := by
          rw [hvw', ContinuousLinearMap.map_smul]
      _ = HarishChandraRootData.wtChar (fun i => Λ (s i)) θ • σ P v := by
          unfold HarishChandraRootData.wtChar
          rw [hre]
  have hle := cptLE_pair (h.le_highest _ (σ P v) hwS hww)
  have hsum : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - fun i => Λ (s i)) i =
      (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * (Λ a - Λ b) := by
    rw [Fintype.sum_eq_add a b (ne_of_lt hab)]
    · simp only [Pi.sub_apply, hs_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · rintro x ⟨hxa, hxb⟩
      simp [hs_def, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  rw [hsum] at hle
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  nlinarith
end GlobalTheory.KTypeCompare
