-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.exists_functional_det_map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:53:55.009799+00:00
-- url     : https://prove2.me/submissions/4585c53f-d467-406a-89fb-3d8616be6987

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntertwiningBijectiveOfFieldBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution [Infinite K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (hM : M.det ≠ 0) : ∃ ℓ : F →ₗ[K] K, (M.map ℓ).det ≠ 0 := by
  classical
  let e := Module.Basis.ofVectorSpace K F
  let φ : F →ₗ[K] MvPolynomial (Module.Basis.ofVectorSpaceIndex K F) K := e.constr K MvPolynomial.X
  by_contra h
  push Not at h
  have hP : (M.map φ).det = 0 := by
    refine MvPolynomial.funext fun c => ?_
    have hc : ∀ x, MvPolynomial.aeval c (φ x) = e.constr K c x := fun x =>
      LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval c).toLinearMap ∘ₗ φ) (f₂ := e.constr K c)
        (fun i => by simp [φ])) x
    rw [map_zero, ← h (e.constr K c), RingHom.map_det]
    congr 1
    ext i j
    exact hc _
  have hc : ∀ x, MvPolynomial.aeval e (φ x) = x := fun x =>
    LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval e).toLinearMap ∘ₗ φ) (f₂ := LinearMap.id)
      (fun i => by simp [φ])) x
  apply hM
  have := congrArg (MvPolynomial.aeval (R := K) e) hP
  rw [map_zero, AlgHom.map_det] at this
  rw [← this]
  congr 1
  ext i j
  exact (hc _).symm
end GlobalTheory.FieldBaseChange
