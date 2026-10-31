-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.gramOp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:20:02.604925+00:00
-- url     : https://prove2.me/submissions/267ee21b-eb08-4ebd-88d1-3f0a375b3ed7

import Mathlib
import Definitions.Def_OAIQ019N044

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SL3Certificate
variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

theorem dot_eq_sum_getD (N : ℕ) (q r : List ℤ) (hq : q.length ≤ N) (hr : r.length ≤ N) :
    dot q r = ∑ k ∈ Finset.range N, q.getD k 0 * r.getD k 0 := by
  induction N generalizing q r with
  | zero =>
    have hq' : q = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hq)
    have hr' : r = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hr)
    simp [hq', hr']
  | succ N ih =>
    cases q with
    | nil => simp
    | cons a q =>
      cases r with
      | nil => simp
      | cons b r =>
        rw [dot, ih q r (by simpa using hq) (by simpa using hr), Finset.sum_range_succ']
        simp [add_comm]

omit [PartialOrder A] [StarOrderedRing A] in
theorem star_list_sum (v : List A) : star v.sum = (v.map star).sum := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih]

omit [StarRing A] [PartialOrder A] [StarOrderedRing A] in
theorem list_sum_finset {ι J : Type*} (v : List ι) (s : Finset J) (f : ι → J → A) :
    (v.map (fun i => ∑ k ∈ s, f i k)).sum = ∑ k ∈ s, (v.map (fun i => f i k)).sum := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih, Finset.sum_add_distrib]

omit [PartialOrder A] [StarOrderedRing A] in
theorem list_gram_identity (N : ℕ) (v : List (A × List ℤ))
    (h : ∀ p ∈ v, p.2.length ≤ N) :
    (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum =
      ∑ k ∈ Finset.range N,
        star ((v.map (fun p => (p.2.getD k 0) • p.1)).sum) *
          ((v.map (fun p => (p.2.getD k 0) • p.1)).sum) := by
  have hm (n m : ℤ) (x y : A) : (n*m) • (x*y) = (n • x) * (m • y) := by
    simp only [zsmul_eq_mul, Int.cast_mul, mul_assoc]
    rw [← mul_assoc x (m : A) y, ← (Int.cast_commute m x).eq, mul_assoc]
  have hdot : (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum =
      (v.map (fun p => (v.map (fun q =>
        ∑ k ∈ Finset.range N, (p.2.getD k 0 • star p.1) * (q.2.getD k 0 • q.1))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro p hp
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [dot_eq_sum_getD N _ _ (h p hp) (h q hq), Finset.sum_smul]
    simp only [hm]
  rw [hdot]
  simp only [list_sum_finset]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [List.sum_map_mul_left, List.sum_map_mul_right, star_list_sum,
    List.map_map, Function.comp_def, star_zsmul]

theorem list_gram_nonneg (N : ℕ) (v : List (A × List ℤ))
    (h : ∀ p ∈ v, p.2.length ≤ N) :
    0 ≤ (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum := by
  rw [list_gram_identity N v h]
  exact Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
end NuclearUltrapower.SL3Certificate
end

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate

theorem columns_length : columns.map List.length = List.replicate 121 120 := by decide +kernel

theorem columns_bound : ∀ q ∈ columns, q.length ≤ 120 := by
  intro q hq
  have h := List.mem_map_of_mem (f := List.length) hq
  rw [columns_length] at h
  have : q.length = 120 := (List.mem_replicate.mp h).2
  omega

section Operator
variable {A : Type*} [Ring A] [StarRing A]

theorem gramValue_nonneg [PartialOrder A] [StarOrderedRing A] (f : Mat3 → A) :
    0 ≤ gramValue f := by
  have h := list_gram_nonneg 120
    (rootPairs.map (fun p => (f p.1, p.2))) (by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact columns_bound q.2 (List.of_mem_zip hq).2)
  simpa only [gramValue, List.map_map, Function.comp_def] using h

end Operator
end NuclearUltrapower.SOS
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gramOp_nonneg_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : 0 ≤ gramOp ρ :=
  zsmul_nonneg (gramValue_nonneg _) (by norm_num)

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.gramOp_nonneg_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.gramOp_nonneg_oai.{u_1}
