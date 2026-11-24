-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimInf.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:34.88962+00:00
-- url     : https://prove2.me/submissions/6eb62cea-f42e-44ed-86ec-e6b1ac5cb1b1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_exists_delta
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_exists_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_exists_tau
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_exists_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PrimInf
theorem _root_.solution (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ Φ : (Ainf F ⊗[F] E) ≃+* (InfinitePlace F → ℂ), IsHomeomorph Φ := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_delta σ h
  obtain ⟨b, hb0, hb1⟩ := exists_basis σ h hδ hδ0
  haveI hTR : IsTotallyReal F := h.1
  choose τ hτ using fun w : InfinitePlace F => exists_tau (E := E) w
  let ρ : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have hρc : ∀ w, Continuous (ρ w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous
  have hρs : ∀ w, Continuous (ρ w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous
  have hρF : ∀ (w : InfinitePlace F) (x : F),
      ((ρ w (algebraMap F (Ainf F) x w) : ℝ) : ℂ) = τ w (algebraMap F E x) := by
    intro w x
    have h1 : τ w (algebraMap F E x) = w.embedding x := DFunLike.congr_fun (hτ w) x
    rw [h1, InfiniteAdeleRing.algebraMap_apply]
    simp only [ρ]
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact InfinitePlace.Completion.extensionEmbedding_coe w _
  let t : InfinitePlace F → ℂ := fun w => τ w δ
  have htre : ∀ w, (t w).re = 0 := by
    intro w
    have h1 : τ w (σ δ) = star (τ w δ) := h.2.2.2 (τ w) δ
    rw [hδ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    simp only [t]
    linarith
  have htim : ∀ w, (t w).im ≠ 0 := by
    intro w h0
    exact hδ0 ((map_eq_zero (τ w)).mp (Complex.ext (htre w) h0))
  let f : Ainf F →+* (InfinitePlace F → ℂ) :=
    Pi.ringHom fun w => (Complex.ofRealHom.comp (ρ w).toRingHom).comp (Pi.evalRingHom _ w)
  let g : E →+* (InfinitePlace F → ℂ) := Pi.ringHom τ
  letI alg : Algebra F (InfinitePlace F → ℂ) := (g.comp (algebraMap F E)).toAlgebra
  let fA : Ainf F →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := f
      commutes' := fun x => funext fun w => hρF w x }
  let gA : E →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := g
      commutes' := fun _ => rfl }
  let Φ₀ : Ainf F ⊗[F] E →ₐ[F] (InfinitePlace F → ℂ) := Algebra.TensorProduct.productMap fA gA
  obtain ⟨Ψ, hΨ⟩ := exists_psi ρ hρc hρs t htre htim
  let C : (Ainf F ⊗[F] E) ≃ₜ (Fin 2 → Ainf F) := TopK.coordHomeo (Ainf F) b
  have hC : ∀ x k, C x k = (Algebra.TensorProduct.basis (Ainf F) b).repr x k := fun _ _ => rfl
  have hform : ∀ a c : Ainf F, Φ₀ (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) =
      fun w => ((ρ w (a w) : ℝ) : ℂ) + ((ρ w (c w) : ℝ) : ℂ) * t w := by
    intro a c
    funext w
    rw [map_add]
    simp only [Φ₀, Algebra.TensorProduct.productMap_apply_tmul]
    show ((ρ w (a w) : ℝ) : ℂ) * τ w 1 + ((ρ w (c w) : ℝ) : ℂ) * τ w δ = _
    rw [map_one, mul_one]
  have hΦ : ⇑Φ₀ = Ψ ∘ C := by
    funext x
    have hx : x = (C x 0) ⊗ₜ[F] (1 : E) + (C x 1) ⊗ₜ[F] δ := by
      conv_lhs => rw [← (Algebra.TensorProduct.basis (Ainf F) b).sum_repr x]
      rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb0, hb1,
        hC, hC, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    calc Φ₀ x = Φ₀ ((C x 0) ⊗ₜ[F] (1 : E) + (C x 1) ⊗ₜ[F] δ) := congrArg Φ₀ hx
      _ = Ψ (C x) := (hform _ _).trans (funext fun w => (hΨ (C x) w).symm)
  have hhom : IsHomeomorph Φ₀ := by
    rw [hΦ]
    exact (C.trans Ψ).isHomeomorph
  exact ⟨RingEquiv.ofBijective (Φ₀ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ)) hhom.bijective, hhom⟩
end GlobalTheory.CompanionTheory.SW.PrimInf
