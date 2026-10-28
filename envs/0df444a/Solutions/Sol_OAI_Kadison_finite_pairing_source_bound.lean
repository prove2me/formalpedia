-- Prove2me | solution 1 for OAI.Kadison.finite_pairing_source_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:19:53.113468+00:00
-- url     : https://prove2.me/submissions/3a916598-f5d3-4aa5-b837-5cec71774a0e

import Mathlib
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C014
import Definitions.Def_OAIQ039C015
import Definitions.Def_OAIQ039C026

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertTensors2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.PreHilbert

theorem pure_orthonormal (E : PreHilbert) {ι : Type*} (v : ι → E)
    (hv : Orthonormal ℂ v) (n : ℕ) :
    Orthonormal ℂ (fun b : Fin n → ι => pure E n (fun i => v (b i))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro b c
  rw [inner_pure]
  simp_rw [orthonormal_iff_ite.mp hv]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_const, Finset.prod_const_one]
  congr 1
  exact propext funext_iff.symm

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FinitePairings
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.PreHilbert

lemma word_orthonormal (E F : PreHilbert) (Ω : E) (hΩ : ‖Ω‖ = 1)
    {ι : Type*} (v : ι → F) (hv : Orthonormal ℂ v) (n : ℕ) :
    Orthonormal ℂ (fun b : Fin n → ι => word E F n Ω (fun i => v (b i))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro b c
  rw [inner_word, inner_self_eq_norm_sq_to_K, hΩ]
  have hh := orthonormal_iff_ite.mp (pure_orthonormal F v hv n) b c
  simpa [inner_pure] using hh

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_Pairings
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

namespace Pairing

variable {J : Type*}

variable [LinearOrder J]

theorem repr_eq_iff (σ : Pairing J) (i j : J) :
    repr σ i = repr σ j ↔ j = i ∨ j = σ i := by
  constructor
  · intro h
    unfold repr at h
    rcases le_total i (σ i) with hi | hi <;>
      rcases le_total j (σ j) with hj | hj
    · rw [min_eq_left hi, min_eq_left hj] at h
      exact Or.inl h.symm
    · rw [min_eq_left hi, min_eq_right hj] at h
      exact Or.inr (by simpa only [apply_apply] using congrArg σ h.symm)
    · rw [min_eq_right hi, min_eq_left hj] at h
      exact Or.inr h.symm
    · rw [min_eq_right hi, min_eq_right hj] at h
      exact Or.inl (σ.injective h).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (repr_apply σ i).symm

variable [Fintype J]

omit [Fintype J] in
theorem pair_tests_iff {L : Type*} (σ : Pairing J) (f : J → L) :
    (∀ j, j < σ j → f j = f (σ j)) ↔ ∀ j, f j = f (σ j) := by
  constructor
  · intro h j
    rcases lt_or_gt_of_ne (σ.apply_ne j).symm with hj | hj
    · exact h j hj
    · have hh := h (σ j) (by simpa only [apply_apply] using hj)
      simpa only [apply_apply] using hh.symm
  · intro h j _
    exact h j

end Pairing

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FinitePairings2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

@[simp] lemma finiteLabels_eq_iff (σ : Pairing J) (p : J) {N : ℕ}
    (n : Fin (N+1)) (i j : J) :
    finiteLabels σ p n i = finiteLabels σ p n j ↔ j = i ∨ j = σ i := by
  constructor
  · intro h
    exact (repr_eq_iff σ i j).mp (congrArg Prod.fst h)
  · intro h
    have hh := (repr_eq_iff σ i j).mpr h
    simp only [finiteLabels, hh]

variable [Fintype J]

lemma finite_contraction_isolation {E : Type*} (τ σ : Pairing J) (p : J) {N : ℕ}
    (n : Fin (N+1)) (v : J × Fin (N+1) → E) (B : E → E → ℂ)
    (hv : ∀ a b, B (v a) (v b) = if a = b then 1 else 0) :
    contraction σ B (fun j => v (finiteLabels τ p n j)) = if σ = τ then 1 else 0 := by
  classical
  unfold contraction
  simp_rw [hv]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.prod_const_one]
  have he : (∀ j, j < σ j → finiteLabels τ p n j = finiteLabels τ p n (σ j)) ↔ σ = τ := by
    rw [pair_tests_iff]
    constructor
    · intro h
      apply ext
      intro j
      rcases (finiteLabels_eq_iff τ p n j (σ j)).mp (h j) with hh | hh
      · exact (σ.apply_ne j hh).elim
      · exact hh
    · rintro rfl j
      exact (finiteLabels_eq_iff σ p n j (σ j)).mpr (Or.inr rfl)
  simp only [he]

end Kadison.Pairing
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FinitePairings3
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

open PreHilbert

lemma finite_constant_coefficient_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {N : ℕ} (T : E →L[ℂ] F) (v : Fin (N+1) → E) (hv : Orthonormal ℂ v)
    (w : F) (hw : ‖w‖ = 1) (c : ℂ) (hc : ∀ n, inner ℂ w (T (v n)) = c) :
    (N+1 : ℝ) * ‖c‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  have hh := hv.sum_inner_products_le (T.adjoint w) (s := Finset.univ)
  have hc' (n) : ‖inner ℂ (v n) (T.adjoint w)‖ = ‖c‖ := by
    rw [← norm_inner_symm, ContinuousLinearMap.adjoint_inner_left, hc]
  simp only [hc', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hh
  have hn := T.adjoint.le_opNorm w
  rw [ContinuousLinearMap.adjoint.norm_map, hw, mul_one] at hn
  exact hh.trans (pow_le_pow_left₀ (norm_nonneg _) hn 2)

lemma finite_pairing_source_bound_oai (E F : PreHilbert) (k l N : ℕ)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (T : wordSpace E F k →L[ℂ] wordSpace E F l)
    (c : Pairing (TailSlots k l) → ℂ) (h : TailSlots k l × Fin (N+1) → F)
    (horth : Orthonormal ℂ h)
    (hexp : ∀ v : TailSlots k l → TailSlots k l × Fin (N+1),
      inner ℂ (word E F l Ω (fun j => h (v (.inr j))))
        (T (word E F k Ω (fun i => h (v (.inl i))))) =
        ∑ σ, c σ * Pairing.contraction σ (fun a b => if a = b then 1 else 0) v)
    (τ : Pairing (TailSlots k l)) (a b : Fin k) (hab : τ (.inl a) = .inl b) :
    (N+1 : ℝ) * ‖c τ‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  classical
  let labels := fun (n : Fin (N+1)) => Pairing.finiteLabels τ (.inl a) n
  let source := fun n (i : Fin k) => labels n (.inl i)
  let test := fun (j : Fin l) => labels (0 : Fin (N+1)) (.inr j)
  have htest (n : Fin (N+1)) (j : Fin l) : labels n (.inr j) = test j := by
    have hne : Pairing.repr τ (.inr j) ≠ Pairing.repr τ (.inl a) := by
      intro hh
      rcases (Pairing.repr_eq_iff τ (.inl a) (.inr j)).mp hh.symm with hh | hh
      · cases hh
      · rw [hab] at hh
        cases hh
    simp only [labels, test, Pairing.finiteLabels, ite_eq_right hne]
  have hinj : Function.Injective source := by
    intro n m he
    have hh := congrArg Prod.snd (congrFun he a)
    simpa only [source, labels, Pairing.finiteLabels, ite_true] using hh
  have hsource : Orthonormal ℂ
      (fun n => word E F k Ω (fun i => h (source n i))) :=
    (word_orthonormal E F Ω hΩ h horth k).comp source hinj
  refine finite_constant_coefficient_bound T _ hsource
    (word E F l Ω (fun j => h (test j))) ?_ (c τ) ?_
  · rw [norm_word, hΩ]
    simp only [horth.norm_eq_one, Finset.prod_const_one, mul_one]
  · intro n
    have hh := hexp (labels n)
    have hsum : (∑ σ, c σ * Pairing.contraction σ
        (fun a b => if a = b then 1 else 0) (labels n)) = c τ := by
      have hcon (σ) : Pairing.contraction σ
          (fun a b => if a = b then 1 else 0) (labels n) = if σ = τ then 1 else 0 := by
        exact Pairing.finite_contraction_isolation τ σ (.inl a) n
          id (fun a b => if a = b then 1 else 0) (fun _ _ => rfl)
      simp only [hcon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [hsum] at hh
    simpa only [source, htest] using hh

end Kadison
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.finite_pairing_source_bound_oai := @OAI.Kadison.finite_pairing_source_bound_oai
