-- Prove2me | solution 1 for GlobalTheory.BorelAlg.Equivariant.numer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:22.7538+00:00
-- url     : https://prove2.me/submissions/797696fc-6e54-4185-9b37-8b8a1984312d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_GlobalTheory_BorelAlg_eval_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
variable [Fintype ι]
variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]
namespace GlobalTheory.BorelAlg
namespace Equivariant
theorem _root_.solution {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f)
    {P : MvPolynomial (Lt m) L} {N : ℕ}
    (hP : f * algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N) = algebraMap _ S P)
    {T : Type} [Field T] (c : L →+* T) (x y b : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T)
    (hx : ∀ τ, (x τ).det ≠ 0) (hy : ∀ τ, (y τ).det ≠ 0) (hb : ∀ τ i j, i < j → b τ i j = 0)
    (hxy : ∀ τ, y τ = b τ * x τ) :
    eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) P * (∏ τ, (x τ).det) ^ N =
      (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) *
        eval₂Hom c (fun p : Lt m => x p.1 p.2.1 p.2.2) P * (∏ τ, (y τ).det) ^ N := by
  have hu : ∀ z : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T, (∀ τ, (z τ).det ≠ 0) →
      IsUnit (eval₂Hom c (fun p : Lt m => z p.1 p.2.1 p.2.2) (∏ τ, (gen m L τ).det)) := by
    intro z hz
    rw [map_prod, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro τ _
    rw [eval_det]; exact hz τ
  let φ : S →+* T := IsLocalization.Away.lift _ (hu x hx)
  let ψ : S →+* T := IsLocalization.Away.lift _ (hu y hy)
  have hφ : ∀ q, φ (algebraMap _ S q) = eval₂Hom c (fun p : Lt m => x p.1 p.2.1 p.2.2) q :=
    fun q => IsLocalization.Away.lift_eq _ _ q
  have hψ : ∀ q, ψ (algebraMap _ S q) = eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) q :=
    fun q => IsLocalization.Away.lift_eq _ _ q
  have key := hf T φ ψ b (fun g => by rw [hφ, hψ]; simp) hb (fun τ i k => by
    simp only [hφ, hψ, eval₂Hom_X']
    rw [hxy, Matrix.mul_apply])
  have h1 := congrArg φ hP
  have h2 := congrArg ψ hP
  rw [map_mul, hφ, hφ, map_pow, map_prod] at h1
  rw [map_mul, hψ, hψ, map_pow, map_prod] at h2
  simp only [eval_det] at h1 h2
  rw [← h1, ← h2, key]
  ring
end Equivariant
end GlobalTheory.BorelAlg
