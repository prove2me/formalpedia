-- Prove2me | solution 1 for ModernOnlineLearning.Dynamic.proof_14_2_sum
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:29:55.560062+00:00
-- url     : https://prove2.me/submissions/2883eba7-800a-43c6-bc47-0cca11073299

import Theorems.Thm_ModernOnlineLearning_Dynamic_lemma_6_10

set_option autoImplicit false
open ModernOnlineLearning.Dynamic
open BeckTeboulleMD.EMDA (bregman)

private lemma telescope (P : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 n, (P t - P (t + 1))) = P 1 - P (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X V : Set E) (ψ : E → ℝ) (η : ℝ) (ℓ : ℕ → E → ℝ)
    (x u : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) (lam : ℝ)
    (hT : 1 ≤ T) (hη : 0 < η) (hlam : 0 < lam)
    (hVsub : V ⊆ X) (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVconv : Convex ℝ V) (hXconv : Convex ℝ X)
    (hψclosed : ClosedRegularizerOn X ψ)
    (hψstrict : StrictConvexOn ℝ X ψ)
    (hψdiff : DifferentiableOn ℝ ψ (interior X))
    (hψstrong : StrongConvexOn (V ∩ interior X) lam ψ)
    (hrun : IsOMDRun X V ψ (fun _ => η) ℓ x g T)
    (hu : ∀ t ∈ Finset.Icc 1 (T + 1), u t ∈ V) :
    dynamicRegret ℓ x u T ≤
      (BeckTeboulleMD.EMDA.bregman ψ (u (T + 1)) (x 1) -
        BeckTeboulleMD.EMDA.bregman ψ (u (T + 1)) (x (T + 1))) / η +
      (η / (2 * lam)) * (∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) +
      (1 / η) * (∑ t ∈ Finset.Icc 1 T,
        (fderiv ℝ ψ (x (t + 1)) - fderiv ℝ ψ (x 1)) (u t - u (t + 1)))  := by
  let P : ℕ → ℝ := fun t => bregman ψ (u t) (x t) - bregman ψ (u t) (x 1)
  let C : ℕ → ℝ := fun t =>
    (fderiv ℝ ψ (x (t + 1)) - fderiv ℝ ψ (x 1)) (u t - u (t + 1))
  have hid (t : ℕ) : bregman ψ (u t) (x t) - bregman ψ (u t) (x (t+1)) =
      P t - P (t+1) + C t := by
    dsimp only [P, C, bregman]
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    ring
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 T) (fun t ht => show
      η * (ℓ t (x t) - ℓ t (u t)) ≤
        (P t - P (t + 1)) + (η^2 / (2 * lam)) * ‖g t‖^2 + C t from by
    have hut := hu t (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1,
      (Finset.mem_Icc.mp ht).2.trans (Nat.le_succ T)⟩)
    have h := ModernOnlineLearning.Dynamic.lemma_6_10 X V ψ (fun _ => η) ℓ x g T lam
      hVsub hVne hVclosed hVconv hXconv hψclosed hψstrict hψdiff hlam hψstrong hrun t ht (u t) hut
    have hbound := h.1.trans (h.2.1.trans h.2.2)
    rw [hid] at hbound
    linarith)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [telescope] at hs
  have hp1 : P 1 = 0 := by dsimp only [P]; ring
  rw [hp1] at hs
  apply (mul_le_mul_iff_right₀ hη).mp
  change η * (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t (u t))) ≤ _
  calc
    _ ≤ 0 - P (T+1) + (η^2 / (2*lam)) * (∑ t ∈ Finset.Icc 1 T, ‖g t‖^2) +
        ∑ t ∈ Finset.Icc 1 T, C t := hs
    _ = _ := by
      dsimp only [P, C]
      field_simp [ne_of_gt hη, ne_of_gt hlam]
      <;> ring

