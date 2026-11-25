-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:41:44.00815+00:00
-- url     : https://prove2.me/submissions/eff835c5-8d82-4e47-81be-893252f53afa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_two_avoid
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_finrank_sup_span
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_not_le_of_finrank
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_update_of_lt
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_update_self
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_ge
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_mem_spanFrom_update
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_image_fin
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_step_core
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (Fs : ℕ → Submodule k W) (hmono : ∀ m, Fs m ≤ Fs (m + 1))
    (hdim : ∀ m, finrank k (Fs m) = min m (finrank k W)) (A B : Submodule k W) (hN : 2 ≤ finrank k W)
    (hAB : A ≤ B) (hA : finrank k A = 1) (hB : finrank k B + 1 = finrank k W) :
    ∃ b : Basis (Fin (finrank k W)) k W, (∀ a : Fin (finrank k W), (a : ℕ) = 0 → b a ∈ A) ∧
      (∀ a : Fin (finrank k W), (a : ℕ) + 1 < finrank k W → b a ∈ B) ∧
      ∀ m, Disjoint (Fs m) (Submodule.span k (b '' {a : Fin (finrank k W) | m ≤ (a : ℕ)})) := by
  set N := finrank k W with hNdef
  let Q : ℕ → Prop := fun m => ∃ f : ℕ → W, ¬ spanFrom k f N m ≤ B ∧
    (∀ a, m ≤ a → a + 1 < N → f a ∈ B) ∧ Inv Fs A f m
  have base : Q (N - 1) := by
    have hF : ¬ (⊤ : Submodule k W) ≤ Fs (N - 1) := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_top, hdim] at this
      omega
    have hBt : ¬ (⊤ : Submodule k W) ≤ B := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_top] at this
      omega
    obtain ⟨v, -, hv1, hvB⟩ := two_avoid ⊤ _ _ hF hBt
    let f0 : ℕ → W := fun _ => 0
    have hG : spanFrom k f0 N (N - 1 + 1) = ⊥ := spanFrom_ge f0 N _ (by omega)
    refine ⟨Function.update f0 (N - 1) v, fun h => hvB (h (mem_spanFrom_update f0 N _ v (by omega))),
      fun a h1 h2 => by omega, step_core Fs hmono A f0 (N - 1) (by omega) v ?_ ?_ ?_⟩
    · rw [hG, sup_bot_eq]; exact hv1
    · rw [hG, sup_bot_eq]; exact fun h => hvB (hAB h)
    · intro m' hm'
      rw [spanFrom_ge f0 N m' (by omega)]
      refine ⟨disjoint_bot_right, disjoint_bot_right, ?_⟩
      rw [finrank_bot]
      omega
  have step : ∀ m, 1 ≤ m → m + 1 < N → Q (m + 1) → Q m := by
    rintro m hm1 hmN ⟨f, hfB, hmem, hinv⟩
    set G := spanFrom k f N (m + 1) with hGdef
    obtain ⟨-, -, hGd⟩ := hinv (m + 1) le_rfl
    have h1 : ¬ B ≤ Fs m ⊔ G := by
      refine not_le_of_finrank B _ G hfB le_sup_right ?_
      have := Submodule.finrank_add_le_finrank_add_finrank (Fs m) G
      rw [hdim, hGd] at this
      have : min m N = m := min_eq_left (by omega)
      omega
    have h2 : ¬ B ≤ A ⊔ G := by
      refine not_le_of_finrank B _ G hfB le_sup_right ?_
      have := Submodule.finrank_add_le_finrank_add_finrank A G
      rw [hA, hGd] at this
      omega
    obtain ⟨v, hvB, hv1, hv2⟩ := two_avoid B _ _ h1 h2
    refine ⟨Function.update f m v, fun h => hfB ?_, fun a ha1 ha2 => ?_,
      step_core Fs hmono A f m (by omega) v hv1 hv2 hinv⟩
    · rw [spanFrom_update_self f N m v (by omega)] at h
      exact le_sup_left.trans h
    · rcases ha1.eq_or_lt with rfl | hlt
      · rw [Function.update_self]; exact hvB
      · rw [Function.update_of_ne hlt.ne']; exact hmem a hlt ha2
  have all : ∀ t, t + 2 ≤ N → Q (N - 1 - t) := by
    intro t
    induction t with
    | zero => intro _; simpa using base
    | succ t ih =>
      intro ht
      have := step (N - 1 - (t + 1)) (by omega) (by omega)
      rw [show N - 1 - (t + 1) + 1 = N - 1 - t by omega] at this
      exact this (ih (by omega))
  obtain ⟨f, -, hmem, hinv⟩ : Q 1 := by
    have := all (N - 2) (by omega)
    rwa [show N - 1 - (N - 2) = 1 by omega] at this
  have hAne : A ≠ ⊥ := fun h => by rw [h, finrank_bot] at hA; omega
  obtain ⟨a, haA, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAne
  obtain ⟨-, hA1, hd1⟩ := hinv 1 le_rfl
  have haG : a ∉ spanFrom k f N 1 := fun h => ha0 (Submodule.disjoint_def.1 hA1 a haA h)
  have hF0 : Fs 0 = ⊥ := Submodule.finrank_eq_zero.1 (by rw [hdim]; simp)
  set f' := Function.update f 0 a with hf'
  have htop : spanFrom k f' N 0 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hf', spanFrom_update_self f N 0 a (by omega), finrank_sup_span _ _ haG]
    change finrank k (spanFrom k f (finrank k W) 1) + 1 = _
    omega
  have hdisj : ∀ m, Disjoint (Fs m) (spanFrom k f' N m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hF0]; exact disjoint_bot_left
    · rw [hf', spanFrom_update_of_lt f N 0 m a hm]
      exact (hinv m hm).1
  have hspan : ⊤ ≤ Submodule.span k (Set.range (fun i : Fin N => f' i)) := by
    rw [← Set.image_univ, show (Set.univ : Set (Fin N)) = {a : Fin N | 0 ≤ (a : ℕ)} by ext; simp, image_fin]
    exact htop.ge
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i : Fin N => f' i) hspan (Fintype.card_fin _), fun i hi => ?_,
    fun i hi => ?_, fun m => ?_⟩
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank]
    simp only [hi, hf', Function.update_self]
    exact haA
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · simp only [h0, hf', Function.update_self]
      exact hAB haA
    · simp only [hf']
      rw [Function.update_of_ne hpos.ne']
      exact hmem i hpos hi
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank, image_fin]
    exact hdisj m
end GlobalTheory.FlagPts.SphericalEisensteinCover
