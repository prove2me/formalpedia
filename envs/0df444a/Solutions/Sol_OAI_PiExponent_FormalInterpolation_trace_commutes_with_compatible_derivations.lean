-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.trace_commutes_with_compatible_derivations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:06:37.086166+00:00
-- url     : https://prove2.me/submissions/78240f78-bcc9-4bf5-84e5-9b7e303dcc8a

import Mathlib

namespace S35H

theorem repr_D (k L E : Type) [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E]
    [IsScalarTower k L E] {ι : Type} [Fintype ι] (b : Module.Basis ι L E)
    (d : Derivation k L L) (D : Derivation k E E)
    (hcompat : ∀ a : L, D (algebraMap L E a) = algebraMap L E (d a))
    (e : E) (j : ι) :
    b.repr (D e) j = d (b.repr e j) + ∑ i, b.repr e i * b.repr (D (b i)) j := by
  classical
  conv_lhs => rw [← b.sum_repr e]
  simp only [map_sum, Algebra.smul_def, Derivation.leibniz, hcompat, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finset.sum_apply' (f := fun i => b.repr _)] <;> try rfl
  simp only [map_add, Finsupp.add_apply]
  rw [Finset.sum_add_distrib]
  have h1 : ∀ i, b.repr (algebraMap L E (b.repr e i) * D (b i)) j = b.repr e i * b.repr (D (b i)) j := by
    intro i; rw [← Algebra.smul_def, map_smul]; rfl
  have h2 : ∀ i, b.repr (b i * algebraMap L E (d (b.repr e i))) j = if i = j then d (b.repr e j) else 0 := by
    intro i; rw [mul_comm, ← Algebra.smul_def, map_smul, b.repr_self]
    simp [Finsupp.single_apply]; split_ifs <;> simp_all
  simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end S35H

theorem solution
    (k L E : Type) [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E]
    [IsScalarTower k L E] [FiniteDimensional L E]
    (d : Derivation k L L) (D : Derivation k E E)
    (hcompat : ∀ a : L, D (algebraMap L E a) = algebraMap L E (d a))
    (x : E) :
    d (Algebra.trace L E x) = Algebra.trace L E (D x) := by
  classical
  let b := Module.finBasis L E
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  have key : ∀ j, b.repr (D x * b j) j = d (b.repr (x * b j) j)
      + ∑ i, b.repr (x * b j) i * b.repr (D (b i)) j - ∑ l, b.repr (D (b j)) l * b.repr (x * b l) j := by
    intro j
    have h := S35H.repr_D k L E b d D hcompat (x * b j) j
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, Finsupp.add_apply] at h
    have h3 : b.repr (x * D (b j)) j = ∑ l, b.repr (D (b j)) l * b.repr (x * b l) j := by
      conv_lhs => rw [← b.sum_repr (D (b j))]
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul]
      rw [Finset.sum_apply']
      rfl
    rw [h3, mul_comm (b j)] at h
    linear_combination h
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j l => b.repr (D (b j)) l * b.repr (x * b l) j)]
  simp only [mul_comm]
  ring
