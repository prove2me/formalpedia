-- Prove2me | solution 1 for GlobalTheory.HostModel.sq_sub_smul_derivation_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:18.396808+00:00
-- url     : https://prove2.me/submissions/59aa8f55-d7ae-4f95-af69-f732b2873678

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HostModel
theorem _root_.solution {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module A M] [Module B M] (D : Derivation A B M) (σ : B →+* B) (hσ : ∀ b, σ (σ b) = b)
    (hfix : ∀ b, σ b = b → b ∈ Set.range (algebraMap A B)) (w b : B) : (w - σ w) ^ 2 • D b = 0 := by
  have h0 : ∀ x, σ x = x → D x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := hfix x hx
    exact D.map_algebraMap a
  have h1 : ∀ x, D (σ x) = -D x := fun x => by
    have h := h0 (x + σ x) (by rw [map_add, hσ, add_comm])
    rw [map_add] at h
    exact eq_neg_of_add_eq_zero_right h
  have h2 : ∀ x, (x - σ x) • D x = 0 := fun x => by
    have h := h0 (σ x * x) (by rw [map_mul, hσ, mul_comm])
    rw [D.leibniz, h1, smul_neg, ← sub_eq_add_neg, ← sub_smul] at h
    rw [← neg_sub, neg_smul, h, neg_zero]
  have h3 : (w - σ w) • D b + (b - σ b) • D w = 0 := by
    have h := h2 (w + b)
    have e : w + b - σ (w + b) = (w - σ w) + (b - σ b) := by rw [map_add]; ring
    rw [e, map_add, add_smul, smul_add, smul_add, h2, h2, zero_add, add_zero] at h
    exact h
  have h4 := congrArg (fun m => (w - σ w) • m) h3
  simp only [smul_add, smul_zero] at h4
  rw [smul_comm (w - σ w) (b - σ b), h2, smul_zero, add_zero, ← mul_smul, ← sq] at h4
  exact h4
end GlobalTheory.HostModel
