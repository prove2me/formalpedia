-- Prove2me | solution 1 for GlobalTheory.HermSign.signature_of_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:26.267109+00:00
-- url     : https://prove2.me/submissions/9f7c3b63-30bf-42cd-8653-e6e8f53adc81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_exists_diag_of_complexStructure
import Theorems.Thm_GlobalTheory_HermSign_gram_eq
import Theorems.Thm_GlobalTheory_HermSign_exists_complexStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : FD.cc ξ = -ξ)
    (hm : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) :
    (0 < (τ ξ).im → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q =
      Matrix.diagonal fun a : Fin r => ((FD.sgn D.q (a : ℕ) : ℝ) : ℂ))) ∧
    ((τ ξ).im < 0 → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q =
      Matrix.diagonal fun a : Fin r => ((FD.sgn D.p (a : ℕ) : ℝ) : ℂ))) := by
  obtain ⟨-, hspan, hherm, -, hEF⟩ := hm
  obtain ⟨hr, M, hM, hinv, hpos, htr⟩ := exists_complexStructure D (hostType H) φ ξ Gm hspan hEF
    (fun _ => Iff.rfl) ⟨τ, hτ⟩
  have hG : (Gm.map τ).IsHermitian := by
    ext a b
    rw [conjTranspose_apply, map_apply, map_apply, ← hherm b a, FD.cc,
      IsCMField.complexEmbedding_complexConj]
    rfl
  have hre : τ ξ = ((τ ξ).im : ℂ) * Complex.I := by
    have h := congrArg τ hξ
    rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
    have := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at this
    apply Complex.ext <;> simp
    linarith
  dsimp only at hinv hpos
  rw [hre] at hinv hpos
  have fin : ∀ m : ℕ, (∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧
      Nᴴ * Gm.map τ * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ)) →
      ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q =
        Matrix.diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
    rintro m ⟨N, hN, h⟩
    refine ⟨N.map conj, ?_, by rw [gram_eq, h]⟩
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hN
  refine ⟨fun hs => fin _ ?_, fun hs => fin _ ?_⟩
  · refine exists_diag_of_complexStructure (n := D.p) (by omega) _ M hG _ 1 (by norm_num)
      (by simpa using hs) hM hinv hpos ?_
    rw [htr]; push_cast
    linear_combination ((D.p : ℂ) - D.q) * Complex.I_mul_I
  · refine exists_diag_of_complexStructure (n := D.q) hr _ M hG _ (-1) (by norm_num)
      (by simpa using hs) hM hinv hpos ?_
    rw [htr]; push_cast
    linear_combination (-((D.p : ℂ) - D.q)) * Complex.I_mul_I
end GlobalTheory.HermSign
