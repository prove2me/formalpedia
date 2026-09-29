-- Prove2me | solution 1 for NonmonotoneSubmod.RandomSet.random_set_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T14:31:17.27199+00:00
-- url     : https://prove2.me/submissions/c8657c2f-8dc3-4340-96d2-34372b874937

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F



namespace NonmonotoneSubmod.RandomSet

open NonmonotoneSubmod.Shared
open scoped symmDiff

lemma F_half {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) :
    F f (fun _ => 1 / 2) = (∑ S : Finset X, f S) * (1 / 2) ^ Fintype.card X := by
  unfold F
  rw [Finset.sum_mul]
  congr 1; funext S
  congr 1
  have : ∀ i : X, (if i ∈ S then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := fun i => by
    split_ifs <;> norm_num
  simp only [this, Finset.prod_const, Finset.card_univ]

lemma quad {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (O S : Finset X) :
    f Finset.univ + f O + f Oᶜ + f ∅ ≤ f S + f (S ∆ O) + f (S ∆ Oᶜ) + f Sᶜ := by
  have e1 : S ∪ S ∆ O = O ∪ S := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e2 : S ∩ S ∆ O = S \ O := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e3 : S ∆ Oᶜ ∪ Sᶜ = O ∪ Sᶜ := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e4 : S ∆ Oᶜ ∩ Sᶜ = Sᶜ \ O := by ext x; simp [Finset.mem_symmDiff]; tauto
  have e5 : (O ∪ S) ∪ (O ∪ Sᶜ) = Finset.univ := by ext x; simp; tauto
  have e6 : (O ∪ S) ∩ (O ∪ Sᶜ) = O := by ext x; simp; tauto
  have e7 : (S \ O) ∪ (Sᶜ \ O) = Oᶜ := by ext x; simp; tauto
  have e8 : (S \ O) ∩ (Sᶜ \ O) = ∅ := by ext x; simp; tauto
  have h1 := hf S (S ∆ O)
  have h2 := hf (S ∆ Oᶜ) Sᶜ
  have h3 := hf (O ∪ S) (O ∪ Sᶜ)
  have h4 := hf (S \ O) (Sᶜ \ O)
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [e5, e6] at h3
  rw [e7, e8] at h4
  linarith

theorem random_set_main {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    (1 / 4) * OPT f ≤ F f (fun _ => 1 / 2) ∧
      (SymmetricSetFun f → (1 / 2) * OPT f ≤ F f (fun _ => 1 / 2)) := by
  obtain ⟨O, -, hO⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  have hOPT : OPT f = f O := hO
  set n := Fintype.card X with hn
  set Sf := ∑ S : Finset X, f S with hSf
  -- the four sums coincide
  have s1 : ∑ S : Finset X, f (S ∆ O) = Sf :=
    Fintype.sum_bijective (fun S => S ∆ O)
      (Function.Involutive.bijective (fun S => by simp [symmDiff_symmDiff_cancel_right]))
      _ _ (fun _ => rfl)
  have s2 : ∑ S : Finset X, f (S ∆ Oᶜ) = Sf :=
    Fintype.sum_bijective (fun S => S ∆ Oᶜ)
      (Function.Involutive.bijective (fun S => by simp [symmDiff_symmDiff_cancel_right]))
      _ _ (fun _ => rfl)
  have s3 : ∑ S : Finset X, f Sᶜ = Sf :=
    Fintype.sum_bijective (fun S => Sᶜ) (Function.Involutive.bijective compl_compl)
      _ _ (fun _ => rfl)
  have hsum : (2 : ℝ) ^ n * (f Finset.univ + f O + f Oᶜ + f ∅) ≤ 4 * Sf := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset X)))
      (fun S _ => quad f hf0 hf O S)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul] at this
    simp only [Finset.sum_add_distrib] at this
    rw [s1, s2, s3, ← hSf] at this
    push_cast at this
    linarith
  have hF := F_half f
  rw [← hSf] at hF
  have hpow : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  have hpos : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have key : (f Finset.univ + f O + f Oᶜ + f ∅) / 4 ≤ F f (fun _ => 1 / 2) := by
    rw [hF]
    have := mul_le_mul_of_nonneg_left hsum hpos.le
    rw [← mul_assoc, hpow, one_mul] at this
    linarith
  have h0 := hf0 Finset.univ
  have h1 := hf0 Oᶜ
  have h2 := hf0 ∅
  refine ⟨by rw [hOPT]; linarith, fun hsym => ?_⟩
  have e1 : f Oᶜ = f O := hsym O
  have e2 : f Finset.univ = f ∅ := by
    have := hsym ∅; rwa [Finset.compl_empty] at this
  rw [hOPT]; rw [e1, e2] at key; linarith

end NonmonotoneSubmod.RandomSet

open NonmonotoneSubmod.RandomSet

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    (1 / 4) * NonmonotoneSubmod.Shared.OPT f ≤ NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) ∧
      (NonmonotoneSubmod.Shared.SymmetricSetFun f → (1 / 2) * NonmonotoneSubmod.Shared.OPT f ≤ NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2)) := by
  exact random_set_main f hf0 hf
