-- Prove2me | solution 1 for GlobalTheory.exists_global_near_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:13.300143+00:00
-- url     : https://prove2.me/submissions/a9ef2793-ea81-41b5-ab80-2d3454374738

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlobalElementNearIdempotentAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E E' : Type) [Field E] [NumberField E] [Field E']
    [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E)
    (e : w.adicCompletion E ⊗[E] E') (he : e * e = e) (hψ : ψ e = 1)
    (p q : w.adicCompletion E ⊗[E] E') (n : ℕ) :
    ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧
      Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) -
        Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  set K := w.adicCompletion E with hK
  set B := Algebra.TensorProduct.basis K b with hB
  set Φ : (ι → K) → K ⊗[E] E' := fun t => ∑ i, t i • B i with hΦ
  have hrepr : ∀ t, B.repr (Φ t) = Finsupp.equivFunOnFinite.symm t := by
    intro t
    ext i
    simp [hΦ, map_sum, Finsupp.smul_apply, Finsupp.single_apply]
  have hM : Continuous fun t => Algebra.leftMulMatrix B (Φ t) := by
    have h : (fun t => Algebra.leftMulMatrix B (Φ t)) =
        fun t => ∑ i, t i • Algebra.leftMulMatrix B (B i) := by
      funext t
      simp only [hΦ, map_sum, map_smul]
    rw [h]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

  set f1 : (ι → K) → ι → K := fun t => B.repr (Φ t * Φ t - Φ t) with hf1
  set f2 : (ι → K) → K := fun t => ψ (Φ t) - 1 with hf2
  set f3 : (ι → K) → K := fun t => Algebra.norm K (p + q * (Φ t - e)) - Algebra.norm K p with hf3
  have hf1c : Continuous f1 := by
    have h : f1 = fun t => Matrix.mulVec (Algebra.leftMulMatrix B (Φ t)) t - t := by
      funext t
      funext i
      simp only [hf1, map_sub, Finsupp.coe_sub, Pi.sub_apply]
      rw [← Algebra.leftMulMatrix_mulVec_repr, hrepr]
      simp
    rw [h]
    exact (hM.matrix_mulVec continuous_id).sub continuous_id
  have hf2c : Continuous f2 := by
    have hl : Continuous fun t => ψ (Φ t) := by
      have h := LinearMap.continuous_on_pi (ψ.toLinearMap ∘ₗ B.equivFun.symm.toLinearMap)
      convert h using 1
      funext t
      simp [hΦ, Module.Basis.equivFun_symm_apply]
    exact hl.sub continuous_const
  have hf3c : Continuous f3 := by
    have h : (fun t => Algebra.norm K (p + q * (Φ t - e))) = fun t =>
        (Algebra.leftMulMatrix B (p - q * e) + Algebra.leftMulMatrix B q *
          Algebra.leftMulMatrix B (Φ t)).det := by
      funext t
      rw [Algebra.norm_eq_matrix_det B, ← map_mul, ← map_add]
      congr 2
      ring
    have : Continuous fun t => Algebra.norm K (p + q * (Φ t - e)) := by
      rw [h]
      exact (continuous_const.add (continuous_const.matrix_mul hM)).matrix_det
    exact this.sub continuous_const
  set t₀ : ι → K := fun i => B.repr e i with ht₀
  have hΦ₀ : Φ t₀ = e := by simp only [hΦ, ht₀]; exact B.sum_repr e
  have hball' : ∀ x₀ : K, Valued.v x₀ ≠ 0 → {z : K | Valued.v z ≤ Valued.v x₀} ∈ 𝓝 (0 : K) := by
    intro x₀ hx₀
    have hl : {y : K | Valued.v y = Valued.v x₀} ∈ 𝓝 x₀ := Valued.locally_const hx₀
    have hc : ContinuousAt (fun z : K => z + x₀) 0 := (continuous_id.add continuous_const).continuousAt
    have h' := hc.preimage_mem_nhds (by simpa using hl)
    filter_upwards [h'] with z hz
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
    calc Valued.v z = Valued.v ((z + x₀) - x₀) := by rw [add_sub_cancel_right]
      _ ≤ max (Valued.v (z + x₀)) (Valued.v x₀) := Valuation.map_sub _ _ _
      _ = Valued.v x₀ := by rw [hz, max_self]
  have hva : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have hx₀ : Valued.v ((algebraMap E K π) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hva, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : ∀ γ, γ = WithZero.exp (-(n : ℤ)) ∨ γ = 1 → {z : K | Valued.v z ≤ γ} ∈ 𝓝 (0 : K) := by
    rintro γ (rfl | rfl)
    · rw [← hx₀]
      exact hball' _ (by rw [hx₀]; exact WithZero.exp_ne_zero)
    · have := hball' 1 (by simp)
      simpa using this
  have h1 : ∀ᶠ t in 𝓝 t₀, ∀ i, Valued.v (f1 t i) ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun t => f1 t i) t₀ := ((continuous_apply i).comp hf1c).continuousAt
    have h0 : f1 t₀ i = 0 := by simp [hf1, hΦ₀, he]
    exact hc.preimage_mem_nhds (by rw [h0]; exact hball 1 (Or.inr rfl))
  have h2 : ∀ᶠ t in 𝓝 t₀, Valued.v (f2 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f2 t₀ = 0 := by simp [hf2, hΦ₀, hψ]
    exact hf2c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have h3 : ∀ᶠ t in 𝓝 t₀, Valued.v (f3 t) ≤ WithZero.exp (-(n : ℤ)) := by
    have h0 : f3 t₀ = 0 := by simp [hf3, hΦ₀]
    exact hf3c.continuousAt.preimage_mem_nhds (by rw [h0]; exact hball _ (Or.inl rfl))
  have hd : DenseRange (Pi.map fun _ : ι => (algebraMap E K : E → K)) :=
    DenseRange.piMap fun _ => w.denseRange_algebraMap E
  obtain ⟨c, hc1, hc2, hc3⟩ := hd.mem_nhds (h1.and (h2.and h3))
  set ε : E' := ∑ i, c i • b i with hε
  have hΦc : Φ (Pi.map (fun _ : ι => (algebraMap E K : E → K)) c) = (1 : K) ⊗ₜ ε := by
    simp only [hΦ, Pi.map_apply, hε]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.tmul_smul, algebraMap_smul]
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro i
    have h := hc1 i
    simp only [hf1, hΦc] at h
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub,
      hB, Algebra.TensorProduct.basis_repr_tmul] at h
    simp only [one_smul, Finsupp.mapRange_apply] at h
    rw [← hva]
    exact h
  · have h := hc2
    simpa only [hf2, hΦc] using h
  · have h := hc3
    simpa only [hf3, hΦc] using h
end GlobalTheory
