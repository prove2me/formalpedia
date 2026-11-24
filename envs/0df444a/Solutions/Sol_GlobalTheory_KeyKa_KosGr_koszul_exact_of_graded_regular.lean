-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:53.389456+00:00
-- url     : https://prove2.me/submissions/74465bf2-403e-4c00-b0c8-2c2923046656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_exact_dd
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_kosD_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution : ∀ (K : Type) [CommRing K] (g : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K), (∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2)) → (∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g → (m i j (j + 1)).mulVec y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' j (j + 1)).mulVecLin) → y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' (j + 1) (j + 2)).mulVecLin) → ∀ v : KIx g 0 N → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w : KIx g 0 N → K, ∀ p : (Σ I : Finset (Fin g), Fin (N I.card)), p.1 ≠ ∅ → v (.inl p) = (kosD m (fun _ => 0)).mulVec w (.inl p) := by
  intro K _ g N m hcomm hreg v hv
  let x : Fin g → ∀ j, (Fin (N (j + 1)) → K) →ₗ[K] (Fin (N j) → K) :=
    fun i j => (m i j (j + 1)).mulVecLin
  have hc : ∀ i i' j (y : Fin (N (j + 2)) → K), j + 2 ≤ g →
      x i j (x i' (j + 1) y) = x i' j (x i (j + 1) y) := by
    intro i i' j y hj
    simp only [x, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hcomm i i' j hj]
  have hr' : ∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g →
      x i j y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' j)) →
      y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' (j + 1)) :=
    fun i j y hj hy => hreg i j y hj hy
  let c : Finset (Fin g) → ∀ j, Fin (N j) → K :=
    fun I => Function.update (0 : ∀ j, Fin (N j) → K) I.card (fun a => v (.inl ⟨I, a⟩))
  have hcv : ∀ (I : Finset (Fin g)) (a : Fin (N I.card)), v (.inl ⟨I, a⟩) = c I I.card a := by
    intro I a
    simp [c]
  have hcyc : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < g) → ∀ j, j = 0 + I.card → dd x g c I j = 0 := by
    intro I _ j hj
    rw [zero_add] at hj
    subst hj
    funext a
    have h1 := kosD_mulVec m v c hcv I a
    rw [hv] at h1
    exact h1.symm
  obtain ⟨w', hw'⟩ := exact_dd x hc hr' g 0 (by simp) c hcyc
  let W : KIx g 0 N → K := fun q => Sum.elim (fun p => w' p.1 p.1.card p.2) (fun _ => 0) q
  refine ⟨W, ?_⟩
  rintro ⟨I, a⟩ hI
  rw [kosD_mulVec m W w' (fun I a => rfl) I a, hcv I a,
    hw' I (fun k _ => k.isLt) hI I.card (by rw [zero_add])]
end GlobalTheory.KeyKa.KosGr
