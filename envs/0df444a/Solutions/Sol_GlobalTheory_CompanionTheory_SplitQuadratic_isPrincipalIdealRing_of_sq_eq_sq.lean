-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:52.599025+00:00
-- url     : https://prove2.me/submissions/1dca0152-e608-4517-a8ca-058c77391422

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitQuadraticOrderPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitQuadratic
namespace GlobalTheory.CompanionTheory.SplitQuadratic
theorem _root_.solution :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
      (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) →
      (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ ι δ e hδ hspan _ he h2
  obtain ⟨e', he'⟩ := he.exists_right_inv
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hee' : ι e * ι e' = 1 := by rw [← map_mul, he', map_one]
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι hh
    rwa [map_mul, map_one, map_ofNat] at this
  have hδ' : δ * δ = ι e * ι e := by rw [hδ, map_mul]

  have hu2 : (ι e' * δ) * (ι e' * δ) = 1 := by
    linear_combination (ι e' * ι e') * hδ' + (ι e * ι e' + 1) * hee'

  set ε₁ : O := ι h * (1 + ι e' * δ) with hε₁
  set ε₂ : O := ι h * (1 - ι e' * δ) with hε₂
  have h11 : ε₁ * ε₁ = ε₁ := by
    rw [hε₁]
    linear_combination (ι h * (1 + ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h22 : ε₂ * ε₂ = ε₂ := by
    rw [hε₂]
    linear_combination (ι h * (1 - ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h12 : ε₁ * ε₂ = 0 := by
    rw [hε₁, hε₂]
    linear_combination (-(ι h * ι h)) * hu2
  have hsum : ε₁ + ε₂ = 1 := by
    rw [hε₁, hε₂]
    linear_combination h2'

  let φ : R × R →+* O :=
    { toFun := fun x => ι x.1 * ε₁ + ι x.2 * ε₂
      map_one' := by
        simp only [Prod.fst_one, Prod.snd_one, map_one, one_mul]
        exact hsum
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(ι x.1 * ι y.1)) * h11 + (-(ι x.2 * ι y.2)) * h22 +
          (-(ι x.1 * ι y.2 + ι x.2 * ι y.1)) * h12
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring }
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p, q, rfl⟩ := hspan y
    refine ⟨(p + q * e, p - q * e), ?_⟩
    show ι (p + q * e) * ε₁ + ι (p - q * e) * ε₂ = ι p + ι q * δ
    rw [hε₁, hε₂]
    simp only [map_add, map_sub, map_mul]
    linear_combination (ι p + ι q * ι e * ι e' * δ) * h2' + (ι q * δ) * hee'
  exact IsPrincipalIdealRing.of_surjective φ hsurj
end GlobalTheory.CompanionTheory.SplitQuadratic
