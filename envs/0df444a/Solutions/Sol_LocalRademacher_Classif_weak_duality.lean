-- Prove2me | solution 1 for LocalRademacher.Classif.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:19:10.825553+00:00
-- url     : https://prove2.me/submissions/0602e76c-001d-496a-b303-61a9a388a519

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

set_option autoImplicit false

namespace LocalRademacher.Classif

theorem wd_ell_nonneg (y y' : ℝ) : 0 ≤ ell y y' := by
  unfold ell; split_ifs <;> norm_num

theorem wd_empLoss_nonneg {X : Type*} {n : ℕ} (xs : Fin n → X) (z : Fin n → ℝ) (f : X → ℝ) :
    0 ≤ empLoss xs z f := by
  unfold empLoss
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg fun i _ => wd_ell_nonneg _ _

end LocalRademacher.Classif

open LocalRademacher.Classif in
theorem solution {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (σ : Fin n → Bool) (r α : ℝ) (hα : 0 < α) (μ : ℝ) (hμ : 0 ≤ μ)
    (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ 2 * r / α ^ 2) :
    (∀ f ∈ F, empLoss xs ys f ≤ 2 * r / α ^ 2 →
        empLoss xs (UnderstandingML.signVec σ) f ≥
          empLoss xs (UnderstandingML.signVec σ) f + μ * (empLoss xs ys f - 2 * r / α ^ 2)) ∧
      (⨅ f : {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ 2 * r / α ^ 2},
          empLoss xs (UnderstandingML.signVec σ) f.1) ≥
        ⨅ f : F, (empLoss xs (UnderstandingML.signVec σ) f.1
          + μ * (empLoss xs ys f.1 - 2 * r / α ^ 2)) := by
  have part1 : ∀ f ∈ F, empLoss xs ys f ≤ 2 * r / α ^ 2 →
        empLoss xs (UnderstandingML.signVec σ) f ≥
          empLoss xs (UnderstandingML.signVec σ) f + μ * (empLoss xs ys f - 2 * r / α ^ 2) := by
    intro f _ hf
    have : μ * (empLoss xs ys f - 2 * r / α ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hμ (by linarith)
    linarith
  refine ⟨part1, ?_⟩
  obtain ⟨f0, hf0F, hf0⟩ := hfeas
  haveI : Nonempty {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ 2 * r / α ^ 2} := ⟨⟨f0, hf0F, hf0⟩⟩
  have hbdd : BddBelow (Set.range fun f : F => (empLoss xs (UnderstandingML.signVec σ) f.1
          + μ * (empLoss xs ys f.1 - 2 * r / α ^ 2))) := by
    refine ⟨-(μ * (2 * r / α ^ 2)), ?_⟩
    rintro _ ⟨f, rfl⟩
    have h1 := wd_empLoss_nonneg xs (UnderstandingML.signVec σ) f.1
    have h2 := wd_empLoss_nonneg xs ys f.1
    have h3 : 0 ≤ μ * empLoss xs ys f.1 := mul_nonneg hμ h2
    show -(μ * (2 * r / α ^ 2)) ≤ _
    nlinarith
  show _ ≤ _
  refine le_ciInf fun g => ?_
  exact (ciInf_le hbdd ⟨g.1, g.2.1⟩).trans (part1 g.1 g.2.1 g.2.2)
