-- Prove2me | solution 1 for GlobalTheory.Mem.PartialZeta.partial_zeta_continuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:55.561836+00:00
-- url     : https://prove2.me/submissions/9cb8c3f9-934f-437f-b891-5b64a79f5638

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_normSq_eq
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_finite_units
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_im_ne_zero
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_abs_im_eq
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_lattice_bij
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_gen_bij
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_hasSum_cnt
import Theorems.Thm_GlobalTheory_T_lattice_epstein_zeta_continuation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.PartialZeta
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ D : RayData K M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : D.G, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = ρ ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → LSeriesSummable (D.cnt c) s ∧ Z s = (s - 1) * LSeries (D.cnt c) s := by
  intro K _ _ _ h2 M hM2 D
  classical
  have hrk : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, h2]
  have hNnorm : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton,
      show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) (M : ℤ) by simp, Algebra.norm_algebraMap, hrk]
    simp [Int.natAbs_pow]
  have hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_top] at this
    nlinarith
  have hN0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_bot] at this
    nlinarith
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk
  let φ : K →+* ℂ := Classical.choice inferInstance
  let ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K)
  haveI : Finite (𝓞 K)ˣ := finite_units h2
  let U := {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}
  haveI : Fintype U := Fintype.ofFinite _
  have hw : 0 < Fintype.card U := Fintype.card_pos_iff.2 ⟨⟨1, by simp⟩⟩
  set ib := |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| with hib
  have hib0 : 0 < ib := abs_pos.2 (im_ne_zero φ b)
  refine ⟨Real.pi / (Fintype.card U * (M : ℝ) ^ 2 * ib), by positivity, fun c => ?_⟩
  obtain ⟨B, hBc, hB0, hcB⟩ := D.cls_surj c⁻¹
  obtain ⟨x₀, hx₀B, z, hz, hxz⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hBc))
  have hx₀1 : x₀ - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
    have : x₀ - 1 = -z := by rw [← hxz]; ring
    rw [this]; exact (Ideal.neg_mem_iff _).2 hz
  have hNB0 : Ideal.span {(M : 𝓞 K)} * B ≠ ⊥ := mul_ne_zero hN0 hB0
  let e : Module.Basis (Fin 2) ℤ ↥(Ideal.span {(M : 𝓞 K)} * B) := Ideal.selfBasis b _ hNB0
  obtain ⟨fL, hfL⟩ := lattice_bij (Ideal.span {(M : 𝓞 K)}) B hBc e x₀ hx₀B hx₀1
  obtain ⟨fG, hfG⟩ := gen_bij hM D c B hBc hB0 hcB
  have hBn0 : Ideal.absNorm B ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hIm := abs_im_eq φ b (Ideal.span {(M : 𝓞 K)} * B) e
  rw [map_mul, hNnorm] at hIm
  have him : (starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hIm
    have : (0 : ℝ) < ((M ^ 2 * Ideal.absNorm B : ℕ) : ℝ) * ib := by
      have : 0 < M ^ 2 * Ideal.absNorm B := by positivity
      positivity
    linarith
  have hψL : ∀ p : ℤ × ℤ, ψ (fL p : 𝓞 K) =
      φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) + p.2 * φ ((e 1 : 𝓞 K) : K) := by
    intro p
    rw [hfL p]
    simp [ψ, map_add, map_mul, map_intCast]
  have hnz : ∀ m n : ℤ, φ (x₀ : K) + m * φ ((e 0 : 𝓞 K) : K) + n * φ ((e 1 : 𝓞 K) : K) ≠ 0 := by
    intro m n h0
    have hx := (fL (m, n)).2.2
    have hzero : (fL (m, n) : 𝓞 K) = 0 := by
      have := hψL (m, n)
      rw [h0] at this
      have hinj : Function.Injective ψ :=
        φ.injective.comp (IsFractionRing.injective (𝓞 K) K)
      exact hinj (by rw [this, map_zero])
    rw [hzero, zero_sub] at hx
    apply hM
    rw [Ideal.eq_top_iff_one]
    simpa using (Ideal.neg_mem_iff _).2 hx
  obtain ⟨Z0, hZd, hZ1, hZm1, hZs⟩ := GlobalTheory.T.lattice_epstein_zeta_continuation _ _ _ him hnz
  have hBc0 : (Ideal.absNorm B : ℂ) ≠ 0 := by exact_mod_cast hBn0
  have hwc : (Fintype.card U : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  refine ⟨fun s => (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s, ?_, ?_, ?_, ?_⟩
  · exact ((differentiable_id.const_cpow (Or.inl hBc0)).div_const _).mul hZd
  · simp only [Complex.cpow_one]
    rw [hZ1, hIm]
    push_cast
    field_simp
    rw [← hib]
    exact div_self (by exact_mod_cast hib0.ne')
  · simp [hZm1]
  · intro s hs
    obtain ⟨hsum, hZeq⟩ := hZs s hs
    set S := ∑' p : ℤ × ℤ, ((‖φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) +
      p.2 * φ ((e 1 : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) with hS
    let G : {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} → ℂ := fun x =>
      ((‖ψ (x : 𝓞 K)‖ ^ 2 : ℝ) : ℂ) ^ (-s)
    have hG : HasSum G S := by
      rw [← fL.hasSum_iff]
      convert hsum.hasSum using 1
      funext p
      simp only [Function.comp_apply, G, hψL p]
    have hGG := fG.hasSum_iff.2 hG
    have hterm : ∀ p, (G ∘ fG) p = (Ideal.absNorm p.1.1 : ℂ) ^ (-s) *
        (Ideal.absNorm B : ℂ) ^ (-s) := by
      intro p
      simp only [Function.comp_apply, G]
      have hn := normSq_eq h2 φ (fG p : 𝓞 K)
      rw [hfG p, map_mul] at hn
      show ((‖φ ((fG p : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) = _
      rw [hn]
      push_cast
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast (Ideal.absNorm B),
        ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    have hfib := hGG.prod_fiberwise (fun I => hasSum_fintype (fun u : U => (G ∘ fG) (I, u)))
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfib
    have hcnt : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧
        D.cls I = c} => (Ideal.absNorm I.1 : ℂ) ^ (-s))
        ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U * S) := by
      have hBs : (Ideal.absNorm B : ℂ) ^ s ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; tauto
      refine (hfib.mul_left ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U)).congr_fun (fun I => ?_)
      rw [Complex.cpow_neg (Ideal.absNorm B : ℂ)]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have hL := hasSum_cnt hM D c s _ hcnt
    refine ⟨hL.LSeriesSummable, ?_⟩
    rw [hL.LSeries_eq]
    show (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s = _
    rw [hZeq]
    ring
end GlobalTheory.Mem.PartialZeta
