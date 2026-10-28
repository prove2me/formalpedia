-- Prove2me | solution 1 for OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:47:57.105154+00:00
-- url     : https://prove2.me/submissions/396b601f-0edd-452f-bdac-913e27f021be

import Mathlib
import Definitions.Def_OAIQ039C046

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FiniteTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

lemma projection_trace_pos
    (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
    {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0) : 0<(τ p).re := by
  have hn := τ.map_nonneg hp.nonneg
  apply lt_of_le_of_ne hn.1
  intro heq
  have hz : τ p=0 := Complex.ext heq.symm hn.2.symm
  apply hpn
  apply hfaith p hpM
  rwa [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

lemma restrict_tracial (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a)) :
    ∀ a b : M, restrict M τ (a*b)=restrict M τ (b*a) :=
  fun a b => hτ a a.property b b.property

lemma restrict_faithful (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0) :
    ∀ a : M, restrict M τ (star a*a)=0 → a=0 :=
  fun a ha => Subtype.ext (hfaith a a.property ha)

theorem noMinimal_of_small (hM : FactorCorner.IsFactor M)
    (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
    (hsmall : ∀ ε : ℝ, 0<ε → ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε) :
    DiffuseProjection.HasNoMinimalProjections M := by
  intro p hpM hp hpn
  obtain ⟨q,hqM,hq,hqn,hqt⟩ := hsmall (τ p).re (projection_trace_pos M τ hfaith hpM hp hpn)
  have hle : τ q≤τ p := ⟨hqt.le,(τ.map_nonneg hq.nonneg).2.symm.trans (τ.map_nonneg hp.nonneg).2⟩
  obtain ⟨v,hvi⟩ := PartialIsometryOrder.finite_factor_comparison M hM (restrict M τ)
    (restrict_tracial M τ hτ) (restrict_faithful M τ hfaith) hqM hpM hq hp hle
  have htrace : τ v.final=τ q := by
    have h := (v.trace_initial_final (restrict M τ) (restrict_tracial M τ hτ)).symm
    change τ v.final=τ v.initial at h
    rwa [hvi] at h
  have hpos : 0<(τ v.final).re := by rw [htrace]; exact projection_trace_pos M τ hfaith hqM hq hqn
  refine ⟨v.final,v.final_mem,v.final_projection,?_,?_,v.target_le⟩
  · intro hz
    rw [hz,map_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  · intro heq
    rw [heq] at htrace
    exact (ne_of_lt hqt) (congrArg Complex.re htrace.symm)

end Kadison.FiniteTrace

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiffuse
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.MatrixDiffuse

open Matrix

lemma diagonal_trace {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (φ : Matrix I I ℂ →ₗ[ℂ] ℂ) (htr : ∀ x y, φ (x*y)=φ (y*x)) (hunit : φ 1=1)
    (i : I) : φ (single i i 1)=(Fintype.card I : ℂ)⁻¹ := by
  have hdiag : ∀ j : I, φ (single i i 1)=φ (single j j 1) := by
    intro j
    simpa using htr (single i j 1) (single j i 1)
  have hcard : (Fintype.card I : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have h : (Fintype.card I : ℂ)*φ (single i i 1)=1 := by
    calc
      _=∑ j : I, φ (single j j 1) := by
        simp only [←hdiag,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _=φ 1 := by rw [←map_sum,Matrix.sum_single_one]
      _=1 := hunit
  apply mul_left_cancel₀ hcard
  rw [h,mul_inv_cancel₀ hcard]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

include hτ h1

lemma exists_matrix_projection {n : ℕ} (hn : 0<n)
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] M) :
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ (τ q).re=(n : ℝ)⁻¹ := by
  let i : Fin n := ⟨0,hn⟩
  let : Nonempty (Fin n) := ⟨i⟩
  let ψ := M.toStarSubalgebra.subtype.comp φ
  have hdiag : τ (ψ (single i i 1))=(n : ℂ)⁻¹ := by
    have hd := diagonal_trace (τ.toLinearMap.comp ψ.toLinearMap)
      (fun x y => by
        change τ (ψ (x*y))=τ (ψ (y*x))
        simp only [map_mul]
        exact hτ _ (φ x).property _ (φ y).property)
      (by change τ (ψ 1)=1; simpa only [map_one] using h1) i
    change τ (ψ (single i i 1))=(Fintype.card (Fin n) : ℂ)⁻¹ at hd
    simpa only [Fintype.card_fin] using hd
  have hp : IsStarProjection (single i i (1 : ℂ)) := by
    constructor
    · change single i i (1 : ℂ)*single i i 1=single i i 1
      simp
    · change star (single i i (1 : ℂ))=single i i 1
      simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,star_one]
  refine ⟨ψ (single i i 1),(φ (single i i 1)).property,hp.map ψ,?_,?_⟩
  · intro hz
    have h := hdiag
    rw [hz,map_zero] at h
    have hnn : (n : ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
    exact (inv_ne_zero hnn) h.symm
  · rw [hdiag]
    have hcast : (n : ℂ)=(n : ℝ) := by simp
    rw [hcast,←Complex.ofReal_inv,Complex.ofReal_re]

theorem exists_small_of_matrix_stages (n : ℕ → ℕ)
    (φ : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ →⋆ₐ[ℂ] M)
    (hsize : ∀ N : ℕ, ∃ j, N<n j) {ε : ℝ} (hε : 0<ε) :
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε := by
  obtain ⟨N,hN,hNε⟩ := Real.exists_nat_pos_inv_lt hε
  obtain ⟨j,hj⟩ := hsize N
  obtain ⟨q,hqM,hq,hqn,hqt⟩ := exists_matrix_projection M τ hτ h1 (hN.trans hj) (φ j)
  refine ⟨q,hqM,hq,hqn,?_⟩
  rw [hqt]
  have hcastN : (0 : ℝ)<N := by exact_mod_cast hN
  have hcastj : (N : ℝ)<n j := by exact_mod_cast hj
  exact (inv_anti₀ hcastN hcastj.le).trans_lt hNε

theorem noMinimal_of_matrix_stages_oai (hM : FactorCorner.IsFactor M)
    (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
    (n : ℕ → ℕ) (φ : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ →⋆ₐ[ℂ] M)
    (hsize : ∀ N : ℕ, ∃ j, N<n j) : DiffuseProjection.HasNoMinimalProjections M := by
  apply FiniteTrace.noMinimal_of_small M τ hM hτ hfaith
  intro ε hε
  exact exists_small_of_matrix_stages M τ hτ h1 n φ hsize hε

end Kadison.MatrixDiffuse

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages_oai.{u_1} := @OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages_oai.{u_1}
