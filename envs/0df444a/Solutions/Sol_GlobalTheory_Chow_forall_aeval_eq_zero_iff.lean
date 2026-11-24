-- Prove2me | solution 1 for GlobalTheory.Chow.forall_aeval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:18.246991+00:00
-- url     : https://prove2.me/submissions/ef4f5c4d-9703-40ab-8c38-c2c41f053a36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Theorems.Thm_GlobalTheory_Chow_exists_C_mul_X_pow_mem
import Theorems.Thm_GlobalTheory_Chow_aeval_eq_zero_of_homogeneousComponent
import Theorems.Thm_GlobalTheory_Chow_C_mem_incidenceIdeal
import Theorems.Thm_GlobalTheory_Chow_aeval_eq_zero_of_mem_elimIdeal
import Theorems.Thm_GlobalTheory_Chow_genericForm_eq
import Theorems.Thm_GlobalTheory_Chow_genericForm_mem_incidenceIdeal
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [CommRing K] {σ β : Type*}
namespace GlobalTheory.Chow
theorem _root_.solution [Fintype σ] {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {p : Ideal (MvPolynomial σ K)} (hp : p.IsHomogeneous (homogeneousSubmodule σ K))
    (t : β × σ → Ω) :
    (∀ f ∈ elimIdeal β p, aeval t f = 0) ↔
      ∃ x : σ → Ω, x ≠ 0 ∧ (∀ g ∈ p, aeval x g = 0) ∧ ∀ i, ∑ j, t (i, j) * x j = 0 := by
  refine ⟨fun h => ?_, fun ⟨x, hx, hp, ht⟩ f hf => aeval_eq_zero_of_mem_elimIdeal hp hx ht hf⟩
  by_contra hc
  let R := MvPolynomial (β × σ) K
  let φ : R →+* Ω := (aeval t : R →ₐ[K] Ω).toRingHom
  let L : β → MvPolynomial σ R := fun i => ∑ j, C (X (i, j)) * X j
  let I : Ideal (MvPolynomial σ R) := Ideal.span
    ({h | ∃ g ∈ p, ∃ n, map C (homogeneousComponent n g) = h} ∪ Set.range L)
  have hI : I.IsHomogeneous (homogeneousSubmodule σ R) := by
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ (⟨g, -, n, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨n, (homogeneousComponent_isHomogeneous n g).map _⟩
    · exact ⟨1, IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _⟩
  obtain ⟨r, hr, m, hm⟩ := exists_C_mul_X_pow_mem φ hI (by
    intro x hx
    by_contra hx0
    refine hc ⟨x, hx0, fun g hg => aeval_eq_zero_of_homogeneousComponent fun n => ?_, fun i => ?_⟩
    · have := hx _ (Ideal.subset_span (Or.inl ⟨g, hg, n, rfl⟩))
      have hC : φ.comp C = algebraMap K Ω := by ext; simp [φ, R]
      rwa [map_map, hC, eval_map, ← aeval_def] at this
    · have := hx _ (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
      simpa [L, φ, R] using this)
  refine hr (h r ⟨m, fun j => ?_⟩)
  let s : MvPolynomial σ R →+* MvPolynomial (β × σ) (MvPolynomial σ K) :=
    eval₂Hom (map C) fun j => C (X j)
  have hs : s.comp (map C) = C := by
    ext1 <;> [ext1; skip] <;> simp [s, R]
  have hle : I ≤ (incidenceIdeal β p).comap s := by
    rw [Ideal.span_le]
    rintro _ (⟨g, hg, n, rfl⟩ | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe, Ideal.mem_comap, ← RingHom.comp_apply, hs]
      exact C_mem_incidenceIdeal (homogeneousComponent_mem_of_mem hp hg n)
    · have := genericForm_mem_incidenceIdeal p i
      rw [genericForm_eq] at this
      simpa [s, L, R, mul_comm] using this
  have := hle (hm j)
  simpa [s, Ideal.mem_comap] using this
end GlobalTheory.Chow
