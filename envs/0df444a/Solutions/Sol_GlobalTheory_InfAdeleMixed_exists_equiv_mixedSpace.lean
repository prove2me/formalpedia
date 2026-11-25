-- Prove2me | solution 1 for GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:07.684864+00:00
-- url     : https://prove2.me/submissions/03e5b11d-9d08-4462-b7d4-fc42aa188f0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInfiniteAdeleTensorEquivMixedSpace
import Theorems.Thm_GlobalTheory_InfAdeleMixed_mixed_ext
import Theorems.Thm_GlobalTheory_InfAdeleMixed_exists_place_over
import Theorems.Thm_GlobalTheory_InfAdeleCM_eq_or_conj
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_decomp
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_delta
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_hom
import Theorems.Thm_GlobalTheory_InfAdeleCM_ext_eq_ofReal
import Theorems.Thm_GlobalTheory_InfAdeleCM_hom_tmul
import Theorems.Thm_GlobalTheory_InfAdeleCM_mk_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.InfAdeleMixed
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleMixed
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E, (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧ Continuous θ.symm ∧ ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) → ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hθ := fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)
  obtain ⟨δ, hδ0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hc' τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact hδ0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ v : InfinitePlace F, v.Completion ≃ᵢ ℝ := fun v =>
    InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v x, r v x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x :=
    fun _ _ => rfl
  let p : {w : InfinitePlace E // w.IsComplex} → InfinitePlace F := fun w =>
    InfinitePlace.mk (w.1.embedding.comp (algebraMap F E))
  let Θ : InfiniteAdeleRing F ⊗[F] E →+* mixedSpace E := toMixed fun w => θ0 w.1.embedding
  have hΘ : ∀ z w, (Θ z).2 w = θ0 w.1.embedding z := fun _ _ => rfl
  have hval : ∀ (w) (a b : InfiniteAdeleRing F), (Θ (a ⊗ₜ 1 + b ⊗ₜ δ)).2 w =
      ⟨r _ (a (p w)), r _ (b (p w)) * (w.1.embedding δ).im⟩ := by
    intro w a b
    rw [hΘ, map_add, hθ, hθ, GlobalTheory.InfAdeleCM.ext_eq_ofReal, GlobalTheory.InfAdeleCM.ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, hr, p]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, hr, p]
  choose t ht using exists_place_over (F := F) (E := E)
  have ht' : ∀ v, p (t v) = v := ht
  have htp : ∀ w, t (p w) = w := by
    intro w
    apply Subtype.ext
    rw [← InfinitePlace.mk_embedding (t (p w)).1, ← InfinitePlace.mk_embedding w.1]
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' hδ0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff (ht (p w))) with e | e
    · rw [e]
    · rw [e, InfinitePlace.mk_conjugate_eq]
  let A : (({w : InfinitePlace E // w.IsComplex}) → ℝ) → InfiniteAdeleRing F := fun y v => (r v).symm (y (t v))
  have hA : Continuous A := continuous_pi fun v => (r v).symm.continuous.comp (continuous_apply (t v))
  have hA' : ∀ y w, r _ (A y (p w)) = y w := by
    intro y w
    simp only [A, IsometryEquiv.apply_symm_apply, htp]
  let G : mixedSpace E → InfiniteAdeleRing F ⊗[F] E := fun z =>
    A (fun w => (z.2 w).re) ⊗ₜ[F] (1 : E) + A (fun w => (z.2 w).im / (w.1.embedding δ).im) ⊗ₜ[F] δ
  have hG : ∀ z, Θ (G z) = z := by
    intro z
    refine mixed_ext fun w => ?_
    rw [hval]
    refine Complex.ext (hA' (fun w => (z.2 w).re) w) ?_
    have h := hA' (fun w => (z.2 w).im / (w.1.embedding δ).im) w
    exact (congrArg (· * (w.1.embedding δ).im) h).trans (div_mul_cancel₀ _ (him _))
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, b, rfl⟩ := GlobalTheory.InfAdeleCM.exists_decomp hs z
    have key : ∀ v, a v = 0 ∧ b v = 0 := by
      intro v
      have h := hval (t v) a b
      rw [hz, ht' v] at h
      have h1 := congrArg Complex.re h
      have h3 := congrArg Complex.im h
      simp only [Prod.snd_zero, Pi.zero_apply, Complex.zero_re, Complex.zero_im] at h1 h3
      have z0 : r v 0 = 0 := by rw [hr, map_zero]
      exact ⟨(r v).injective (by rw [z0, ← h1]),
        (r v).injective (by rw [z0]; exact (mul_eq_zero.1 h3.symm).resolve_right (him _))⟩
    have ha : a = 0 := funext fun v => (key v).1
    have hb : b = 0 := funext fun v => (key v).2
    rw [ha, hb, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  let e : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E := RingEquiv.ofBijective Θ ⟨hinj, fun z => ⟨G z, hG z⟩⟩
  have he : ∀ z, e z = Θ z := fun _ => rfl
  have htm : ∀ x : E, Continuous fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x := by
    intro x
    have : (fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x) = fun a => a • ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) := by
      funext a
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.fun_smul continuous_id' continuous_const
  refine ⟨e, fun x => mixed_ext fun w => ?_, ?_, fun u hu => ?_⟩
  · rw [he, hΘ, h0, mixedEmbedding_apply_isComplex]
  · have : (e.symm : mixedSpace E → _) = G := by
      funext z
      rw [RingEquiv.symm_apply_eq, he, hG]
    rw [this]
    have c1 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).re) := by fun_prop
    have c2 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).im / (w.1.embedding δ).im) := by fun_prop
    exact Continuous.fun_add ((htm 1).comp' (hA.comp' c1)) ((htm δ).comp' (hA.comp' c2))
  · have hne : ∀ w, ((u : mixedSpace E).2 w).re ≠ 0 := by
      intro w h
      have h1 : (u : mixedSpace E).2 w = 0 := Complex.ext h (hu w)
      have h3 := congrArg (fun z : mixedSpace E => z.2 w) u.mul_inv
      simp only [Prod.snd_mul, Pi.mul_apply, h1, zero_mul, Prod.snd_one, Pi.one_apply] at h3
      exact zero_ne_one h3
    have hunit : IsUnit (A fun w => ((u : mixedSpace E).2 w).re) := by
      refine Pi.isUnit_iff.2 fun v => IsUnit.mk0 _ fun h => hne (t v) ?_
      have h1 : (r v).symm ((u : mixedSpace E).2 (t v)).re = 0 := h
      have h3 := congrArg (r v) h1
      rwa [IsometryEquiv.apply_symm_apply, hr, map_zero] at h3
    refine ⟨hunit.unit, mixed_ext fun w => ?_⟩
    have h := hval w (A fun w => ((u : mixedSpace E).2 w).re) 0
    rw [TensorProduct.zero_tmul, add_zero] at h
    rw [IsUnit.unit_spec, he, h]
    refine Complex.ext (hA' (fun w => ((u : mixedSpace E).2 w).re) w) ?_
    have z0 : r (p w) ((0 : InfiniteAdeleRing F) (p w)) = 0 := by
      rw [hr]
      exact map_zero _
    rw [hu w]
    simp only [z0, zero_mul]
end GlobalTheory.InfAdeleMixed
