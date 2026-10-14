-- Prove2me | solution 1 for IntMul.HvdH.thm_4_1_fp
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T01:23:13.036992+00:00
-- url     : https://prove2.me/submissions/af7c7452-d718-475f-83cd-f6eab3e69ece

import Theorems.Thm_IntMul_HvdH_prop_4_7_fp
import Theorems.Thm_IntMul_HvdH_fp_tensor
import Theorems.Thm_IntMul_HvdH_lip_tensor

open IntMul.HvdH in
theorem solution {d : ℕ} (p α : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : ∀ i, s i ≤ α ^ 2 * (t i - s i))
    (hp : ∀ i, 100 * (jIter p (s i) (t i) α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p) :
    ∃ (A : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (t i) → ℂ))
      (B : ∀ i, (ZMod (t i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ)),
      (∀ i, ‖A i‖ ≤ 1 ∧ ‖B i‖ ≤ 1 ∧ ∀ u, (s i : ℂ)⁻¹ • ZMod.dft u =
        (2 : ℂ) ^ (2 * α ^ 2) • B i ((t i : ℂ)⁻¹ • ZMod.dft (A i u))) ∧
      FPApprox p (tensorMapZ fun i => Sapprox p (s i) (t i) α)
        (tensorMap fun i (x : ℕ → ℂ) (k : ℕ) => A i (fun j => x j.val) (k : ZMod (t i)))
        (∑ _i : Fin d, (6 * sWidth p α + 4 : ℝ)) ∧
      FPApprox p (tensorMapZ fun i => Bapprox p (s i) (t i) α)
        (tensorMap fun i (x : ℕ → ℂ) (j : ℕ) => B i (fun k => x k.val) (j : ZMod (s i)))
        (∑ i, ((jIter p (s i) (t i) α : ℝ) * (10 * eWidth p α + 12) + 4)) ∧
      SupLip (tensorMap fun i (x : ℕ → ℂ) (k : ℕ) => A i (fun j => x j.val) (k : ZMod (t i))) ∧
      SupLip (tensorMap fun i (x : ℕ → ℂ) (j : ℕ) => B i (fun k => x k.val) (j : ZMod (s i))) := by
  have h := fun i => prop_4_7_fp p (s i) (t i) α (hst i) (hcop i) hα hαp (hx i) (hp i) hpA
  choose A B hA hB hF hSa hBa hLA hLB using h
  refine ⟨A, B, fun i => ⟨hA i, hB i, hF i⟩, ?_, ?_, lip_tensor _ hLA, lip_tensor _ hLB⟩
  · exact fp_tensor p _ _ (fun _ => (6 * sWidth p α + 4 : ℝ)) hSa hLA
  · exact fp_tensor p _ _ (fun i => (jIter p (s i) (t i) α : ℝ) * (10 * eWidth p α + 12) + 4) (fun i => by
      have := hBa i; push_cast at this ⊢; exact this) hLB
