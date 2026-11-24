-- Prove2me | solution 1 for GlobalTheory.Koecher.exists_siegel_fourierCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:43.741352+00:00
-- url     : https://prove2.me/submissions/d576ebe9-27e1-40c8-9248-47a5dabe3b4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Theorems.Thm_GlobalTheory_Koecher_exists_tube_fourierCoeff
import Theorems.Thm_GlobalTheory_Koecher_exists_bound_of_unit_periods
import Theorems.Thm_GlobalTheory_convex_phDom
import Theorems.Thm_GlobalTheory_isOpen_phDom
import Theorems.Thm_GlobalTheory_isSymm_phSym


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.Koecher
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
namespace GlobalTheory.Koecher
theorem _root_.solution {g N : ℕ} (hN : 1 ≤ N) {F : Matrix (Fin g) (Fin g) ℂ → ℂ}
    (hF : IsHoloSiegel g F)
    (hper : ∀ B : Matrix (Fin g) (Fin g) ℤ, B.IsSymm → ∀ τ ∈ SiegelH (Fin g),
        F (τ + (N : ℂ) • B.map (Int.cast : ℤ → ℂ)) = F τ) :
    (∀ Y : Matrix (Fin g) (Fin g) ℝ, Y.PosDef → ∃ M : ℝ, ∀ τ : Matrix (Fin g) (Fin g) ℂ,
      τ.IsSymm → τ.map Complex.im = Y → ‖F τ‖ ≤ M) ∧
    ∃ a : (Fin g × Fin g → ℤ) → ℝ, (∀ m, 0 ≤ a m) ∧
      (∀ Y : Matrix (Fin g) (Fin g) ℝ, ((N : ℝ) • (Y + Yᵀ)).PosDef → ∀ M : ℝ,
        (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → τ.map Complex.im = (N : ℝ) • (Y + Yᵀ) →
          ‖F τ‖ ≤ M) →
        ∀ m, a m * Real.exp (-(2 * π * ∑ q, (m q : ℝ) * Y q.1 q.2)) ≤ M) ∧
      (∀ τ ∈ SiegelH (Fin g), ∀ b : (Fin g × Fin g → ℤ) → ℝ, Summable b →
        (∀ m, a m * Real.exp (-(π / N * ∑ q, (m q : ℝ) * (τ q.1 q.2).im)) ≤ b m) →
          ‖F τ‖ ≤ ∑' m, b m) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  let ψ : (Fin g × Fin g → ℂ) →ₗ[ℝ] (Fin g → Fin g → ℂ) :=
    { toFun := fun z i j => 2 * N * z (i, j)
      map_add' := fun z w => by funext i j; simp [mul_add]
      map_smul' := fun c z => by funext i j; simp; ring }
  have hψ : Differentiable ℂ ψ := by
    change Differentiable ℂ fun (z : Fin g × Fin g → ℂ) i j => 2 * N * z (i, j)
    fun_prop
  set Φ : (Fin g × Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun z => phSym (Matrix.of (ψ z))
    with hΦ
  have hΦa : ∀ z i j, Φ z i j = N * (z (i, j) + z (j, i)) := fun z i j => by
    simp [hΦ, phSym, ψ]; ring
  have hΦs : ∀ z, (Φ z).IsSymm := fun z => isSymm_phSym _
  have hΦim : ∀ z (t : Fin g × Fin g → ℝ),
      (Φ ((fun q => (t q : ℂ)) + z)).map Complex.im = (Φ z).map Complex.im := fun z t => by
    ext i j; simp [hΦa]
  have hU : IsOpen (ψ ⁻¹' phDom g) := (isOpen_phDom g).preimage hψ.continuous
  have hU' : IsPreconnected (ψ ⁻¹' phDom g) :=
    ((convex_phDom g).linear_preimage ψ).isPreconnected
  have hmem : ∀ z, z ∈ ψ ⁻¹' phDom g ↔ Φ z ∈ SiegelH (Fin g) := fun z => Iff.rfl
  have htube : ∀ z ∈ ψ ⁻¹' phDom g, ∀ t : Fin g × Fin g → ℝ,
      (fun q => (t q : ℂ)) + z ∈ ψ ⁻¹' phDom g := fun z hz t =>
    (hmem _).2 ⟨hΦs _, by rw [hΦim]; exact ((hmem _).1 hz).2⟩
  have hf : DifferentiableOn ℂ (fun z => F (Φ z)) (ψ ⁻¹' phDom g) :=
    DifferentiableOn.comp (g := fun x : Fin g → Fin g → ℂ => F (phSym (Matrix.of x))) (f := ψ)
      hF hψ.differentiableOn fun z hz => hz
  have hp : ∀ z ∈ ψ ⁻¹' phDom g, ∀ q, F (Φ (z + Pi.single q 1)) = F (Φ z) := fun z hz q => by
    rw [← hper (Matrix.of (fun i j => (Pi.single q 1 : Fin g × Fin g → ℤ) (i, j) +
      (Pi.single q 1 : Fin g × Fin g → ℤ) (j, i))) (by ext i j; simp [add_comm]) _ ((hmem _).1 hz)]
    congr 1
    ext i j
    simp [hΦa, Pi.single_apply]
    ring
  have hsym : ∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm →
      Φ (fun q => τ q.1 q.2 / (2 * N)) = τ := fun τ hτ => by
    ext i j
    rw [hΦa, hτ.apply i j]
    field_simp
    ring
  refine ⟨fun Y hY => ?_, ?_⟩
  · set z : Fin g × Fin g → ℂ := fun q => I * Y q.1 q.2 / (2 * N) with hz
    have hYs : ∀ i j, Y j i = Y i j := fun i j => by simpa using hY.1.apply i j
    have hzU : z ∈ ψ ⁻¹' phDom g := by
      refine (hmem _).2 ⟨hΦs _, ?_⟩
      convert hY using 1
      ext i j
      have : Φ z i j = I * Y i j := by
        rw [hΦa]; simp only [hz, hYs i j]; field_simp; ring
      simp [this]
    obtain ⟨M, hM⟩ := exists_bound_of_unit_periods
      (A := fun x : Fin g × Fin g → ℝ => F (Φ ((fun i => (x i : ℂ)) + z)))
      (hf.continuousOn.comp_continuous (by fun_prop) fun x => htube z hzU x) (fun i x => by
        rw [← hp _ (htube z hzU x) i]
        congr 2
        funext j
        by_cases hij : j = i
        · subst hij; simp; ring
        · simp [hij])
    refine ⟨M, fun τ hτ hτY => ?_⟩
    have h := hM fun q => (τ q.1 q.2).re / (2 * N)
    rw [← hsym τ hτ]
    convert h using 4
    funext q
    simp only [Pi.add_apply, hz, ← hτY, Matrix.map_apply]
    push_cast
    rw [← add_div, mul_comm I, Complex.re_add_im]
  · obtain ⟨a, ha0, ha1, ha2⟩ := exists_tube_fourierCoeff hU hU' htube hf hp
    refine ⟨a, ha0, fun Y hY M hM m => ?_, fun τ hτ b hb hle => ?_⟩
    · set z : Fin g × Fin g → ℂ := fun q => I * Y q.1 q.2 with hz
      have him : (Φ z).map Complex.im = (N : ℝ) • (Y + Yᵀ) := by
        ext i j; simp [hΦa, hz]
      have := ha1 z ((hmem _).2 ⟨hΦs _, by rwa [him]⟩) M
        (fun t => hM _ (hΦs _) (by rw [hΦim, him])) m
      simpa [hz] using this
    · have := ha2 (fun q => τ q.1 q.2 / (2 * N)) ((hmem _).2 (by rwa [hsym τ hτ.1])) b hb
        fun m => by
          convert hle m using 4
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          have : (τ q.1 q.2 / (2 * N)).im = (τ q.1 q.2).im / (2 * N) := by
            rw [show (2 * N : ℂ) = ((2 * N : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_im]
          rw [this]
          field_simp
      rwa [hsym τ hτ.1] at this
end GlobalTheory.Koecher
