-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.thm3_claim1_trivial_of_empty_interior
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:57:30.410689+00:00
-- url     : https://prove2.me/submissions/9bb0487d-208a-43f7-8eee-8ad2770de549

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

set_option autoImplicit false

namespace MaxLatticeFree.Inequalities

theorem b9646048_key {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ)
    (hsub : IsSublinear ψ) (T : Finset W) (c : W → ℝ) (hc : ∀ r ∈ T, 0 ≤ c r) :
    ψ (∑ r ∈ T, c r • r) ≤ ∑ r ∈ T, ψ r * c r := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have h0 := hsub.1 0 0 le_rfl
    simp at h0
    simp [h0]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := hsub.2 (c a • a) (∑ r ∈ T, c r • r)
    have h2 := hsub.1 a (c a) (hc a (Finset.mem_insert_self a T))
    have h3 := ih (fun r hr => hc r (Finset.mem_insert_of_mem hr))
    rw [h2] at h1
    nlinarith [h1, h3]

end MaxLatticeFree.Inequalities

open MaxLatticeFree.Inequalities in
theorem solution {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ : W → ℝ) (α : ℝ)
    (hvalid : IsValid f W ψ α) (hsub : IsSublinear ψ)
    (hempty : Disjoint (intBpsi f W ψ α) (affHullInt f W : Set (EuclideanSpace ℝ (Fin q)))) :
    IsTrivial f W ψ α := by
  intro s hs hnn
  have hv : combo W s = ((∑ r ∈ s.support, s r • r : W) : EuclideanSpace ℝ (Fin q)) := by
    simp [combo, Finsupp.sum]
  have hx : f + combo W s - f = ((∑ r ∈ s.support, s r • r : W) : EuclideanSpace ℝ (Fin q)) := by
    rw [hv]; abel
  by_contra hlt
  rw [not_le] at hlt
  have hmem : f + combo W s ∈ intBpsi f W ψ α := by
    refine ⟨by rw [hx]; exact Subtype.mem _, ?_⟩
    have he : (⟨f + combo W s - f, by rw [hx]; exact Subtype.mem _⟩ : W)
        = ∑ r ∈ s.support, s r • r := Subtype.ext hx
    rw [he]
    refine lt_of_le_of_lt (b9646048_key ψ hsub s.support s (fun r _ => hnn r)) ?_
    simpa [linVal, Finsupp.sum] using hlt
  exact Set.disjoint_left.mp hempty hmem hs

