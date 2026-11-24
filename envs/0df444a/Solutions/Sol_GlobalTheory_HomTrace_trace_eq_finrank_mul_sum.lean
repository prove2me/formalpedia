-- Prove2me | solution 1 for GlobalTheory.HomTrace.trace_eq_finrank_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:09.86313+00:00
-- url     : https://prove2.me/submissions/e357caf5-3335-46b6-b637-181737701377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TraceEqFinrankMulSum
import Theorems.Thm_GlobalTheory_HomTrace_finrank_hom
import Theorems.Thm_GlobalTheory_HomTrace_finite_hom
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_complex
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_finrank_int_eq_mul_of_finite
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.HomTrace
namespace GlobalTheory.HomTrace
theorem _root_.solution (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (a : 𝓞 E) (f : (X →+ ℂ) →ₗ[ℂ] (X →+ ℂ))
    (hf : ∀ l x, f l x = l (a • x)) :
    LinearMap.trace ℂ (X →+ ℂ) f = (Module.finrank (𝓞 E) X : ℂ) * ∑ τ : E →+* ℂ, τ (a : E) := by
  classical
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X with hr
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) hr.le
  let j : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) v
  let F : Submodule (𝓞 E) X := Submodule.span (𝓞 E) (Set.range v)
  have hF : Module.finrank (𝓞 E) F = r := by simpa using finrank_span_eq_card hv
  have h0 : Module.finrank (𝓞 E) (X ⧸ F) = 0 := by
    have := F.finrank_quotient_add_finrank
    omega
  have htor : ∀ x : X, ∃ n : ℤ, n ≠ 0 ∧ ∃ y, j y = n • x := by
    intro x
    rw [Module.finrank_eq_zero_iff] at h0
    obtain ⟨c, hc, hx⟩ := h0 (Submodule.Quotient.mk x)
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hc)
    refine ⟨n, hn, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    have h1 : n • x ∈ F := by
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul]
      exact F.smul_mem _ hx
    rw [show F = LinearMap.range j from (Fintype.range_linearCombination _ _).symm] at h1
    exact h1
  let R : (X →+ ℂ) →ₗ[ℂ] ((Fin r → 𝓞 E) →+ ℂ) :=
    { toFun := fun l => l.comp j.toAddMonoidHom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : ∀ l y, R l y = l (j y) := fun _ _ => rfl
  have hinj : Function.Injective R := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    ext x
    obtain ⟨n, hn, y, hy⟩ := htor x
    have h1 : l (j y) = 0 := by rw [← hR, hl]; rfl
    rw [hy, map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn)
  have := finite_hom X
  have := finite_hom (Fin r → 𝓞 E)
  have hdY : Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) = r * Module.finrank ℚ E := by
    rw [finrank_hom, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  have hdim : Module.finrank ℂ (X →+ ℂ) = Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) := by
    rw [hdY, finrank_hom, finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank, mul_comm]
  let e := LinearMap.linearEquivOfInjective R hinj hdim
  let g : (E →+* ℂ) → (𝓞 E →* ℂ) := fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hg : Function.Injective g := by
    intro φ ψ hφ
    apply (EigenSplit.isSplitting_complex E).injective
    ext a
    exact DFunLike.congr_fun hφ a
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp g hg
  let w : Fin r × (E →+* ℂ) → ((Fin r → 𝓞 E) →+ ℂ) := fun p =>
    ((p.2.comp (algebraMap (𝓞 E) E)).toAddMonoidHom).comp (Pi.evalAddMonoidHom (fun _ => 𝓞 E) p.1)
  have hw : ∀ p y, w p y = p.2 (y p.1 : E) := fun _ _ => rfl
  have hwli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨i, τ⟩
    refine Fintype.linearIndependent_iff.1 hli (fun φ => c (i, φ)) ?_ τ
    funext y
    have h1 := DFunLike.congr_fun hc (Pi.single i y)
    rw [AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i] at h1
    · simpa [hw, g] using h1
    · intro k _ hk
      simp [hw, Pi.single_eq_of_ne hk]
    · simp
  let b := basisOfLinearIndependentOfCardEqFinrank' w hwli (by
    rw [hdY, Fintype.card_prod, Fintype.card_fin, Embeddings.card])
  let c := b.map e.symm
  have hc : ∀ p, R (c p) = w p := fun p => by
    have : e (c p) = b p := by simp [c]
    rw [← show b p = w p by simp [b], ← this]; rfl
  have hfc : ∀ p, f (c p) = p.2 (a : E) • c p := fun p => by
    apply hinj
    refine AddMonoidHom.ext fun y => ?_
    rw [map_smul, hR, hf, ← j.map_smul, ← hR, hc, AddMonoidHom.smul_apply, hw, hw]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℂ c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, hfc, Fintype.sum_prod_type]
end GlobalTheory.HomTrace
