-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/53cfdd11-dcb3-5129-a064-23405f51cea2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "NumberField P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.NumberField TensorProduct Matrix"
open scoped TensorProduct.RightActions

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace"
namespace ArchTraceForm
p2m_open "NumberField"

section Structures

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev F : Type := InfiniteAdeleRing K

abbrev E : Type := L ⊗[K] InfiniteAdeleRing K

abbrev algRF : Algebra ℝ (F K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

attribute [local instance] algRF

abbrev algRE : Algebra ℝ (E K L) :=
  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
    (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra

attribute [local instance] algRE

def mixedAlgEquiv : F K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) fun r => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r)) = _
    exact RingEquiv.apply_symm_apply _ _

scoped instance moduleFree_F : Module.Free ℝ (F K) :=
  Module.Free.of_equiv (mixedAlgEquiv K).symm.toLinearEquiv

scoped instance moduleFinite_F : Module.Finite ℝ (F K) :=
  Module.Finite.equiv (mixedAlgEquiv K).symm.toLinearEquiv

theorem algebraMap_FE_apply (a : F K) :
    algebraMap (F K) (E K L) a = (1 : L) ⊗ₜ a := rfl

scoped instance isScalarTower_RFE : IsScalarTower ℝ (F K) (E K L) :=
  IsScalarTower.of_algebraMap_eq (R := ℝ) (S := F K) (A := E K L) fun _ => rfl

scoped instance moduleFree_FE : Module.Free (F K) (E K L) := inferInstance

scoped instance moduleFinite_FE : Module.Finite (F K) (E K L) := inferInstance

end Structures

section MixedSpace

theorem trace_pi_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) :
    Algebra.trace R (ι → R) x = ∑ i, x i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun R ι)]
  have h : Algebra.leftMulMatrix (Pi.basisFun R ι) x = Matrix.diagonal x := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.diagonal_apply, Pi.basisFun_apply, Pi.basisFun_repr,
      Pi.mul_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg hij, mul_zero]
  rw [h, Matrix.trace_diagonal]

theorem trace_prod_apply {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (a : A) (b : B) : Algebra.trace R (A × B) (a, b) = Algebra.trace R A a + Algebra.trace R B b := by
  rw [Algebra.trace_apply, Algebra.trace_apply, Algebra.trace_apply]
  have : (Algebra.lmul R (A × B) (a, b) : (A × B) →ₗ[R] (A × B)) =
      LinearMap.prodMap (Algebra.lmul R A a) (Algebra.lmul R B b) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    rfl
  rw [this, LinearMap.trace_prodMap']

variable (K : Type) [Field K] [NumberField K]

open scoped Classical

theorem trace_pi_complex_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ℂ) :
    Algebra.trace ℝ (ι → ℂ) z = 2 * (∑ i, z i).re := by
  rw [← Algebra.trace_trace (S := ℂ), trace_pi_apply, Algebra.trace_complex_apply]

theorem trace_mixedSpace_apply (x : mixedEmbedding.mixedSpace K) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace K) x = (∑ w, x.1 w) + 2 * (∑ w, x.2 w).re := by
  classical
  obtain ⟨x₁, x₂⟩ := x
  rw [trace_prod_apply, trace_pi_apply, trace_pi_complex_apply]

theorem separatingLeft_traceForm_mixedSpace :
    (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace K)).SeparatingLeft := by
  classical
  intro x hx
  obtain ⟨x₁, x₂⟩ := x
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  ·
    have h := hx (Pi.single w 1, 0)
    rw [Algebra.traceForm_apply, Prod.mk_mul_mk, mul_zero, trace_mixedSpace_apply] at h
    simp only [Finset.sum_const_zero, Pi.zero_apply, Complex.zero_re, mul_zero, add_zero] at h
    have : (∑ v, ((x₁ * Pi.single w (1 : ℝ) : {w : InfinitePlace K // w.IsReal} → ℝ)) v) = x₁ w := by
      rw [Finset.sum_eq_single w]
      · simp
      · intro v _ hv; simp [Pi.single_apply, hv]
      · intro h; exact absurd (Finset.mem_univ w) h
    rw [this] at h
    exact h
  ·
    have h := hx (0, Pi.single w (starRingEnd ℂ (x₂ w)))
    rw [Algebra.traceForm_apply, Prod.mk_mul_mk, mul_zero, trace_mixedSpace_apply] at h
    simp only [Pi.zero_apply, Finset.sum_const_zero, zero_add] at h
    have hsum : (∑ v, ((x₂ * Pi.single w (starRingEnd ℂ (x₂ w)) : {w : InfinitePlace K // w.IsComplex} → ℂ)) v) =
        x₂ w * starRingEnd ℂ (x₂ w) := by
      rw [Finset.sum_eq_single w]
      · simp
      · intro v _ hv; simp [Pi.single_apply, hv]
      · intro h'; exact absurd (Finset.mem_univ w) h'
    rw [hsum, Complex.mul_conj, Complex.ofReal_re] at h
    have h2 : Complex.normSq (x₂ w) = 0 := by linarith [Complex.normSq_nonneg (x₂ w)]
    exact Complex.normSq_eq_zero.1 h2

attribute [local instance] algRF

theorem separatingLeft_traceForm_F : (Algebra.traceForm ℝ (F K)).SeparatingLeft := by
  intro x hx
  set e := mixedAlgEquiv K with he
  have : e x = 0 := by
    refine separatingLeft_traceForm_mixedSpace K (e x) fun y => ?_
    have h := hx (e.symm y)
    rw [Algebra.traceForm_apply] at h ⊢
    rw [← Algebra.trace_eq_of_algEquiv e, map_mul, AlgEquiv.apply_symm_apply] at h
    exact h
  simpa using this

end MixedSpace

section BaseChange

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algRF algRE

theorem lmul_one_tmul (l : L) :
    (Algebra.lmul (F K) ((F K) ⊗[K] L) ((1 : F K) ⊗ₜ[K] l) : (F K) ⊗[K] L →ₗ[F K] (F K) ⊗[K] L) =
      (Algebra.lmul K L l : L →ₗ[K] L).baseChange (F K) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [LinearMap.baseChange_tmul]
      show ((1 : F K) ⊗ₜ[K] l) * (a ⊗ₜ[K] m) = a ⊗ₜ[K] (Algebra.lmul K L l) m
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem trace_one_tmul (l : L) :
    Algebra.trace (F K) ((F K) ⊗[K] L) ((1 : F K) ⊗ₜ[K] l) = algebraMap K (F K) (Algebra.trace K L l) := by
  rw [Algebra.trace_apply, lmul_one_tmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

def commEF : (F K) ⊗[K] L ≃ₐ[F K] E K L :=
  TensorProduct.RightActions.Algebra.TensorProduct.comm K (F K) L

theorem commEF_tmul (a : F K) (l : L) : commEF K L (a ⊗ₜ l) = l ⊗ₜ a := rfl

theorem trace_EF_tmul_one (l : L) :
    Algebra.trace (F K) (E K L) (l ⊗ₜ[K] (1 : F K)) = algebraMap K (F K) (Algebra.trace K L l) := by
  rw [← commEF_tmul K L 1 l, Algebra.trace_eq_of_algEquiv (commEF K L), trace_one_tmul]

def bE {ι : Type*} (b : Module.Basis ι K L) : Module.Basis ι (F K) (E K L) :=
  TensorProduct.RightActions.Algebra.TensorProduct.basis (F K) b

theorem bE_apply {ι : Type*} (b : Module.Basis ι K L) (i : ι) : bE K L b i = b i ⊗ₜ (1 : F K) := by
  rw [bE, TensorProduct.RightActions.Algebra.TensorProduct.basis, Module.Basis.map_apply,
    Algebra.TensorProduct.basis_apply]
  rfl

theorem traceForm_bE {ι : Type*} (b : Module.Basis ι K L) (i j : ι) :
    Algebra.traceForm (F K) (E K L) (bE K L b i) (bE K L b j) =
      algebraMap K (F K) (Algebra.traceForm K L (b i) (b j)) := by
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply, bE_apply, bE_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, trace_EF_tmul_one]

theorem isUnit_algebraMap_KF {c : K} (hc : c ≠ 0) : IsUnit (algebraMap K (F K) c) :=
  (IsUnit.mk0 c hc).map _

theorem separatingLeft_traceForm_EF : (Algebra.traceForm (F K) (E K L)).SeparatingLeft := by
  classical
  intro x hx
  set b := Module.finBasis K L with hb
  set n := Module.finrank K L
  set B := bE K L b with hB

  set G : Matrix (Fin n) (Fin n) K := (Algebra.traceForm K L).toMatrix b with hG
  set G' : Matrix (Fin n) (Fin n) (F K) := G.map (algebraMap K (F K)) with hG'
  have hGdet : G.det ≠ 0 := det_traceForm_ne_zero b
  have hG'det : IsUnit G'.det := by
    rw [hG', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_algebraMap_KF K hGdet

  set a : Fin n → F K := ⇑(B.repr x) with ha
  have hxsum : x = ∑ i, a i • B i := (B.sum_repr x).symm
  have hvec : a ᵥ* G' = 0 := by
    funext j
    have h := hx (B j)
    rw [hxsum, map_sum, LinearMap.sum_apply] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [Matrix.vecMul, dotProduct, Pi.zero_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG', Matrix.map_apply, hG, LinearMap.BilinForm.toMatrix_apply, ← traceForm_bE K L b i j]

  have ha0 : a = 0 := by
    have : a ᵥ* G' ᵥ* G'⁻¹ = a := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG'det, Matrix.vecMul_one]
    rw [← this, hvec, Matrix.zero_vecMul]
  rw [hxsum]
  simp [ha0]

end BaseChange

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algRF algRE

theorem separatingLeft_traceForm_E : (Algebra.traceForm ℝ (E K L)).SeparatingLeft := by
  intro x hx

  refine separatingLeft_traceForm_EF K L x fun y => ?_
  refine separatingLeft_traceForm_F K (Algebra.traceForm (F K) (E K L) x y) fun a => ?_
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
  have key : a * Algebra.trace (F K) (E K L) (x * y) =
      Algebra.trace (F K) (E K L) (algebraMap (F K) (E K L) a * (x * y)) := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
  have h := hx (algebraMap (F K) (E K L) a * y)
  rw [Algebra.traceForm_apply, ← Algebra.trace_trace (S := F K), mul_left_comm, ← key] at h
  rw [mul_comm]
  exact h

theorem nondegenerate_traceForm_F : (Algebra.traceForm ℝ (F K)).Nondegenerate := by
  have hs : (Algebra.traceForm ℝ (F K)).IsSymm := @Algebra.traceForm_isSymm ℝ (F K) _ _ _
  exact hs.isRefl.nondegenerate_iff_separatingLeft.2 (separatingLeft_traceForm_F K)

theorem nondegenerate_traceForm_E : (Algebra.traceForm ℝ (E K L)).Nondegenerate := by
  have hs : (Algebra.traceForm ℝ (E K L)).IsSymm := @Algebra.traceForm_isSymm ℝ (E K L) _ _ _
  exact hs.isRefl.nondegenerate_iff_separatingLeft.2 (separatingLeft_traceForm_E K L)

end Main

end NumberField.ArchTraceForm
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.NumberField P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.NumberField.ArchTraceForm"
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.NumberField P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.NumberField.ArchTraceForm"

open _root_.NumberField _root_.P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.NumberField NumberField.ArchTraceForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    (Algebra.traceForm ℝ (InfiniteAdeleRing K)).Nondegenerate ∧
      (Algebra.traceForm ℝ (L ⊗[K] InfiniteAdeleRing K)).Nondegenerate :=
  ⟨nondegenerate_traceForm_F K, nondegenerate_traceForm_E K L⟩

end S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate (solution)
