-- Prove2me | solution 1 for HardyFLocal.clumping_from_product_experiments
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T01:09:59.243999+00:00
-- url     : https://prove2.me/submissions/369cd9f2-38c7-4b3d-afcf-855800f9dcf2

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_grid_region_expansion
open HardyCausaloid
namespace HardyFLocal
open HardyCausaloid

end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {m n : ℕ} (ρ : GlobalMat m n)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M)
    (S : FiducialFamily) (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (hL : IsFiducialLabels S L) (O : Finset (X m n))
    (productExperiment : ∀ (l : ∀ x : O, omegaOne L x.val) (s : ∀ x, Label (Setting m n) (Outcome m n) x),
      (∀ x, x ∉ O → s x ∈ omegaOne L x) →
      regionTable M O (fun x => (l x).val) s =
        ∑ k : omegaC L O, (actualCausaloid S L).Λ O l k * (actualCausaloid S L).state M O s k) :
    ∀ (α : Lab (Setting m n) (Outcome m n) O) (s : ∀ x, Label (Setting m n) (Outcome m n) x),
      regionTable M O α s = (actualCausaloid S L).r O α ⬝ᵥ (actualCausaloid S L).state M O s := by
  classical
  intro α s
  let C := actualCausaloid S L
  let ext (g : ∀ x : ↥Oᶜ, omegaOne L x.val) := glue Oᶜ (fun x => (g x).val) s
  let w (g : ∀ x : ↥Oᶜ, omegaOne L x.val) := ∏ x : ↥Oᶜ,
    elemCoeff S (labelOp (s x.val)) (decode L x.val (g x).val)
  have hext (a : Lab (Setting m n) (Outcome m n) O) : regionTable M O a s =
      ∑ g : ∀ x : ↥Oᶜ, omegaOne L x.val, w g * regionTable M O a (ext g) := by
    have base := grid_region_expansion ρ M hM S L hL Oᶜ (fun x => s x.val) (glue O a s)
    have swap (b : Lab (Setting m n) (Outcome m n) Oᶜ) :
        glue Oᶜ b (glue O a s) = glue O a (glue Oᶜ b s) := by
      funext x
      by_cases h : x ∈ O <;> simp [glue,h]
    have keep : glue O a (glue Oᶜ (fun x => s x.val) s) = glue O a s := by
      funext x
      by_cases h : x ∈ O <;> simp [glue,h]
    simpa only [regionTable,swap,keep,w,ext] using base
  have row (l : ∀ x : O, omegaOne L x.val) : regionTable M O (fun x => (l x).val) s =
      ∑ k : omegaC L O, C.Λ O l k * C.state M O s k := by
    rw [hext]
    have products g : ∀ x, x ∉ O → ext g x ∈ omegaOne L x := by
      intro x hx
      simpa [ext,glue,hx] using (g ⟨x,Finset.mem_compl.mpr hx⟩).property
    simp_rw [productExperiment l _ (products _), Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    change _ = C.Λ O l k * regionTable M O (C.embed O k.val) s
    rw [hext, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    change w g * (C.Λ O l k * regionTable M O _ (ext g)) = C.Λ O l k * (w g * regionTable M O _ (ext g))
    ring
  rw [grid_region_expansion ρ M hM S L hL O α s]
  simp_rw [row, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [← mul_assoc]
  exact (Finset.sum_mul _ _ _).symm

