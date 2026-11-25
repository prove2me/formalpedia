-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.exists_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:45.843546+00:00
-- url     : https://prove2.me/submissions/e5238b4d-1f10-4d7b-8beb-b0afa18a9815

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MapMemChartIdealOfAevalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
open MvPolynomial ReciprocityTheory.AnForm.R
variable {σ : Type}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
theorem _root_.solution (s : σ → σ) (G₀ : MvPolynomial σ ℤ) :
    ∃ H m : MvPolynomial σ ℤ, ∀ (T : Type) [CommRing T] (f : MvPolynomial σ ℤ →+* T) (w : σ → T),
      (∀ q, IsUnit (f (X (s q)))) → (∀ q, f (X q) = f (X (s q)) * w q) →
      IsUnit (f m) ∧ eval₂Hom (Int.castRingHom T) w G₀ * f m = f H := by
  classical
  let M : Submonoid (MvPolynomial σ ℤ) :=
    Submonoid.closure (Set.range fun q => (X (s q) : MvPolynomial σ ℤ))
  let B := Localization M
  have hs : ∀ q, (X (s q) : MvPolynomial σ ℤ) ∈ M := fun q => Submonoid.subset_closure ⟨q, rfl⟩
  let ψ : MvPolynomial σ ℤ →+* B := eval₂Hom (Int.castRingHom B)
    (fun q => IsLocalization.mk' B (X q : MvPolynomial σ ℤ) ⟨X (s q), hs q⟩)
  obtain ⟨⟨H, m⟩, hHm⟩ := IsLocalization.surj M (ψ G₀)
  refine ⟨H, m, fun T _ f w hu hw => ?_⟩
  have hM : ∀ y : M, IsUnit (f y) := by
    rintro ⟨y, hy⟩
    induction hy using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact hu q
    | one => simp
    | mul a b _ _ ha hb => simpa using ha.mul hb
  let L : B →+* T := IsLocalization.lift hM
  have hL : ∀ r, L (algebraMap _ B r) = f r := IsLocalization.lift_eq hM
  have hcomp : L.comp ψ = eval₂Hom (Int.castRingHom T) w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · intro q
      simp only [RingHom.comp_apply, ψ, eval₂Hom_X']
      exact (IsLocalization.lift_mk'_spec _ _ _ _).2 (hw q)
  refine ⟨hM m, ?_⟩
  have h := congrArg L hHm
  rw [map_mul, hL, hL] at h
  rw [← h, ← hcomp]
  rfl
end GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
