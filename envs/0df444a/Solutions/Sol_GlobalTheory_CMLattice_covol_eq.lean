-- Prove2me | solution 1 for GlobalTheory.CMLattice.covol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:46.225594+00:00
-- url     : https://prove2.me/submissions/c892f222-0d2e-45d3-be1e-76b30ffed9ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Theorems.Thm_GlobalTheory_CMLattice_im_mul_conj_eq_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMLattice
theorem _root_.solution (σ : K →+* ℂ) (b : Basis (Fin 2) ℤ (𝓞 K)) (L : PeriodPair)
    (I : FractionalIdeal (𝓞 K)⁰ K) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ z, z ∈ L.lattice ↔ ∃ x ∈ I, z = c * σ x) :
    |(L.ω₁ * starRingEnd ℂ L.ω₂).im| = ‖c‖ ^ 2 * (FractionalIdeal.absNorm I : ℚ) *
      |(σ (b 0 : K) * starRingEnd ℂ (σ (b 1 : K))).im| := by
  obtain ⟨u0, hu0, e0⟩ := (h L.ω₁).1 L.ω₁_mem_lattice
  obtain ⟨u1, hu1, e1⟩ := (h L.ω₂).1 L.ω₂_mem_lattice
  let w : Fin 2 → (I : Submodule (𝓞 K) K) := ![⟨u0, hu0⟩, ⟨u1, hu1⟩]
  have hli : LinearIndependent ℤ w := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hK : (s : K) * u0 + t * u1 = 0 := by
      have := congrArg Subtype.val hst
      simpa [zsmul_eq_mul] using this
    have h' : (s : ℝ) • L.ω₁ + (t : ℝ) • L.ω₂ = 0 := by
      rw [e0, e1, Complex.real_smul, Complex.real_smul]
      have := congrArg (fun y => c * σ y) hK
      simp only [map_add, map_mul, map_intCast, map_zero, mul_zero] at this
      push_cast
      linear_combination this
    have := LinearIndependent.pair_iff.1 L.indep s t h'
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range w) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.1 ((h (c * σ x)).2 ⟨x, hx, rfl⟩)
    have hxK : x = p * u0 + q * u1 := by
      apply σ.injective
      apply mul_left_cancel₀ hc
      rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← hpq, e0, e1]
      ring
    have hx' : (⟨x, hx⟩ : (I : Submodule (𝓞 K) K)) = p • w 0 + q • w 1 := by
      ext
      simp [w, hxK, zsmul_eq_mul]
    rw [hx']
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bI : Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K) := Basis.mk hli hsp
  have hdet := FractionalIdeal.abs_det_basis_change b I bI
  have hcomp : ((↑) ∘ bI : Fin 2 → K) = ![u0, u1] := by
    ext i
    fin_cases i <;> simp [bI, w]
  rw [hcomp] at hdet
  have him := im_mul_conj_eq_det σ (b.localizationLocalization ℚ ℤ⁰ K) ![u0, u1]
  simp only [Basis.localizationLocalization_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at him
  have hsq : (c * σ u0 * starRingEnd ℂ (c * σ u1)).im = ‖c‖ ^ 2 * (σ u0 * starRingEnd ℂ (σ u1)).im := by
    rw [map_mul, show c * σ u0 * (starRingEnd ℂ c * starRingEnd ℂ (σ u1)) =
      (c * starRingEnd ℂ c) * (σ u0 * starRingEnd ℂ (σ u1)) by ring, Complex.mul_conj,
      Complex.im_ofReal_mul, Complex.normSq_eq_norm_sq]
  rw [e0, e1, hsq, abs_mul, abs_of_nonneg (by positivity), him, abs_mul, ← Rat.cast_abs, hdet]
  simp only [RingOfIntegers.coe_eq_algebraMap]
  ring
end GlobalTheory.CMLattice
