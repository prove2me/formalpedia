-- Prove2me | solution 1 for GlobalTheory.closure_generic_fibre_clopen_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:30.153614+00:00
-- url     : https://prove2.me/submissions/17a3ad4b-3dc5-4e93-96cc-325ae2d2ab42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosureGenericFibreClopenSplit
import Theorems.Thm_GlobalTheory_T_exists_idempotent_tmul_one_eq_of_smooth_algebra
import Theorems.Thm_GlobalTheory_T_range_comap_includeRight_eq_comap_eq_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
namespace GlobalTheory
theorem _root_.solution : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  intro R A _ _ _ _ _ hsm C C' hU hd1 hd2
  let K := FractionRing R
  let f : A →+* A ⊗[R] K := (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] K).toRingHom
  let φ := PrimeSpectrum.comap f
  have hφc : Continuous φ := PrimeSpectrum.continuous_comap f

  have hF : {r : PrimeSpectrum A | r.asIdeal.comap (algebraMap R A) = ⊥} = Set.range φ := by
    have h1 := GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker R A K
    have hker : RingHom.ker (algebraMap R K) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    rw [hker] at h1
    rw [← h1]
    let e := (Algebra.TensorProduct.comm R A K).toRingEquiv
    have hg : (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom = e.toRingHom.comp f := by
      ext a
      simp [f, e]
    rw [hg, PrimeSpectrum.comap_comp, Set.range_comp]
    have hsurj : Set.range (PrimeSpectrum.comap e.toRingHom) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ⟨PrimeSpectrum.comap e.symm.toRingHom y, ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply, RingEquiv.symm_toRingHom_comp_toRingHom]
      rfl
    rw [hsurj, Set.image_univ]

  have hinj : Function.Injective f := by
    have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R K)
      (IsFractionRing.injective R K)
    intro x y hxy
    have : (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm x) =
        (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm y) := by
      simpa [f] using hxy
    exact (TensorProduct.rid R A).symm.injective (hl this)
  have hdense : DenseRange φ :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2
      (by rw [(RingHom.injective_iff_ker_eq_bot f).1 hinj]; exact bot_le)
  have hCC' : Disjoint C C' := hd1.mono_right subset_closure
  have hunion : φ ⁻¹' C ∪ φ ⁻¹' C' = Set.univ := by
    rw [← Set.preimage_union, hU, hF, Set.preimage_range]
  have hcompl : IsCompl (φ ⁻¹' C) (φ ⁻¹' C') :=
    ⟨hCC'.preimage φ, codisjoint_iff.2 hunion⟩
  have hS1 : φ ⁻¹' closure C = φ ⁻¹' C := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hd2 hx)
  have hclosed : IsClosed (φ ⁻¹' C) := hS1 ▸ isClosed_closure.preimage hφc
  have hS2 : φ ⁻¹' closure C' = φ ⁻¹' C' := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact absurd hx (Set.disjoint_left.1 hd1 h)
    · exact h
  have hclosed' : IsClosed (φ ⁻¹' C') := hS2 ▸ isClosed_closure.preimage hφc
  have hopen : IsOpen (φ ⁻¹' C) := by
    rw [← isClosed_compl_iff, hcompl.compl_eq]; exact hclosed'
  obtain ⟨ε, hε, hεS⟩ := PrimeSpectrum.isClopen_iff.1 ⟨hclosed, hopen⟩
  obtain ⟨a, ha, haε⟩ := GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra R A hsm ε hε
  have hfa : f a = ε := by simp [f, haε]
  have hpre : φ ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) = φ ⁻¹' C := by
    rw [hεS, ← hfa]
    ext x
    simp [φ, PrimeSpectrum.mem_basicOpen]
  have hCa : C ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inl hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ φ ⁻¹' C := hx
    rw [← hpre] at hy
    exact hy
  have hC'a : C' ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))ᶜ := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inr hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ (φ ⁻¹' C)ᶜ := hcompl.compl_eq ▸ hx
    rw [← hpre] at hy
    exact hy
  have hclo : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · exact (disjoint_compl_right (a := (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)))).mono
      (closure_minimal hCa hclo.isClosed) (closure_minimal hC'a hclo.isOpen.isClosed_compl)
  · rw [← closure_union, hU, hF]
    exact hdense.closure_range
end GlobalTheory
