-- Prove2me | solution 1 for MechanismDesign.VCG.dsic_iff_cyclically_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:07:53.666371+00:00
-- url     : https://prove2.me/submissions/07dbe39e-cab0-4f62-aa0a-d2e192e31652

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

lemma cm_fin_telescope : ∀ (k : ℕ) (V : Fin (k + 1) → ℝ),
    ∑ κ : Fin k, (V κ.succ - V κ.castSucc) = V (Fin.last k) - V 0
  | 0, V => by simp
  | k + 1, V => by
    rw [Fin.sum_univ_castSucc]
    have ih := cm_fin_telescope k (fun j => V j.castSucc)
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

section single
variable {A T : Type*} (v : A → T → ℝ) (g : T → A)

def cmW (x y : T) : ℝ := v (g x) y - v (g x) x

def cmChain (c x : T) : Set ℝ :=
  {s | ∃ (k : ℕ) (f : ℕ → T), f 0 = c ∧ f k = x ∧ s = ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1))}

noncomputable def cmPot (c x : T) : ℝ := sSup (cmChain v g c x)

lemma cm_ext_sum (f : ℕ → T) (k : ℕ) (y : T) :
    ∑ κ ∈ Finset.range (k + 1), cmW v g ((fun m => if m ≤ k then f m else y) κ)
        ((fun m => if m ≤ k then f m else y) (κ + 1))
      = ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1)) + cmW v g (f k) y := by
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro κ hκ
    have h1 := Finset.mem_range.mp hκ
    simp only [show κ ≤ k by omega, show κ + 1 ≤ k by omega, if_true]
  · simp

variable {v g}

lemma cm_ext_mem {c x : T} (y : T) {s : ℝ} (hs : s ∈ cmChain v g c x) :
    s + cmW v g x y ∈ cmChain v g c y := by
  obtain ⟨k, f, h0, hk, rfl⟩ := hs
  refine ⟨k + 1, fun m => if m ≤ k then f m else y, by simpa using h0, by simp, ?_⟩
  rw [cm_ext_sum, hk]

lemma cm_nonempty (c x : T) : (cmChain v g c x).Nonempty :=
  ⟨_, cm_ext_mem x (s := 0) ⟨0, fun _ => c, rfl, rfl, by simp⟩⟩

variable (hcm : ∀ (k : ℕ) (f : ℕ → T), f k = f 0 →
    ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1)) ≤ 0)
include hcm

lemma cm_bdd (c x : T) : BddAbove (cmChain v g c x) := by
  refine ⟨-cmW v g x c, fun s hs => ?_⟩
  have hm := cm_ext_mem c hs
  obtain ⟨k, f, h0, hk, he⟩ := hm
  have := hcm k f (by rw [hk, h0])
  linarith

lemma cm_pot_ineq (c x y : T) : cmPot v g c x + cmW v g x y ≤ cmPot v g c y := by
  have : cmPot v g c x ≤ cmPot v g c y - cmW v g x y := by
    apply csSup_le (cm_nonempty c x)
    intro s hs
    have := le_csSup (cm_bdd hcm c y) (cm_ext_mem y hs)
    unfold cmPot
    linarith
  linarith

end single

theorem dsic_iff_cyclically_monotone_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j) (k : ℕ) (θs : Fin (k + 1) → Θ i), θs (Fin.last k) = θs 0 →
        ∑ κ : Fin k, (u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.succ)
          - u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.castSucc)) ≤ 0 := by
  constructor
  · rintro ⟨t, ht⟩ i θ k θs hlast
    let V : Fin (k + 1) → ℝ := fun m =>
      u i (q (Function.update θ i (θs m))) (θs m) - t i (Function.update θ i (θs m))
    have hle : ∀ κ : Fin k, (u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.succ)
          - u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.castSucc)) ≤ V κ.succ - V κ.castSucc := by
      intro κ
      have h := ht (Function.update θ i (θs κ.succ)) i (θs κ.castSucc)
      simp only [Function.update_self, Function.update_idem] at h
      simp only [V]
      linarith
    calc _ ≤ ∑ κ : Fin k, (V κ.succ - V κ.castSucc) := Finset.sum_le_sum (fun κ _ => hle κ)
      _ = V (Fin.last k) - V 0 := cm_fin_telescope k V
      _ = 0 := by simp only [V, hlast]; ring
  · intro H
    classical
    refine ⟨fun i θ => u i (q θ) (θ i) -
      cmPot (u i) (fun x => q (Function.update θ i x)) (Classical.choice ⟨θ i⟩) (θ i), ?_⟩
    intro θ i x
    simp only
    have hcm : ∀ (k : ℕ) (f : ℕ → Θ i), f k = f 0 →
        ∑ κ ∈ Finset.range k, cmW (u i) (fun x => q (Function.update θ i x)) (f κ) (f (κ + 1)) ≤ 0 := by
      intro k f hf
      have := H i θ k (fun m => f m.val) (by simpa using hf)
      rw [Finset.sum_range (fun κ => cmW (u i) (fun x => q (Function.update θ i x)) (f κ) (f (κ + 1)))]
      exact this
    have hg : (fun y => q (Function.update (Function.update θ i x) i y)) =
        (fun y => q (Function.update θ i y)) := by
      funext y; rw [Function.update_idem]
    rw [hg]
    simp only [Function.update_self]
    have hp := cm_pot_ineq hcm (Classical.choice ⟨θ i⟩) x (θ i)
    have hq : q θ = q (Function.update θ i (θ i)) := by rw [Function.update_eq_self]
    simp only [cmW] at hp
    rw [hq]
    simp only [Function.update_eq_self] at hp ⊢
    linarith

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j) (k : ℕ) (θs : Fin (k + 1) → Θ i), θs (Fin.last k) = θs 0 →
        ∑ κ : Fin k, (u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.succ)
          - u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.castSucc)) ≤ 0 := by
  exact dsic_iff_cyclically_monotone_core u q
