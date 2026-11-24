-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:04.509024+00:00
-- url     : https://prove2.me/submissions/9d736827-fcd1-4f7d-81f4-2126695c4854

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {A : Type*} [CommRing A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.ThetaRational
theorem _root_.solution (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (a : A)
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (q : MvPolynomial (Fin n) ℂ)
    (hp : ∀ r : Polynomial (MvPolynomial (Fin n) ℂ), r.eval₂ j.toRingHom a = 0 → p ∣ r)
    (hq : ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin n) ℂ), j q * b = r.eval₂ j.toRingHom a)
    (w : (Fin n → ℂ) × ℂ) (hw : MvPolynomial.eval w.1 q ≠ 0)
    (hw' : (p.map (MvPolynomial.eval w.1)).eval w.2 = 0) :
    ∃ χ : A →ₐ[ℂ] ℂ, (∀ i, χ (j (MvPolynomial.X i)) = w.1 i) ∧ χ a = w.2 := by
  choose R hR using hq
  set ρ := Polynomial.eval₂RingHom (MvPolynomial.eval w.1) w.2 with hρ
  set ψ := Polynomial.eval₂RingHom j.toRingHom a with hψ
  have hR' : ∀ b, ψ (R b) = j q * b := fun b => (hR b).symm
  have hψq : ψ (Polynomial.C q) = j q := by simp [hψ]
  have hρq : ρ (Polynomial.C q) = MvPolynomial.eval w.1 q := by simp [hρ]
  have hρp : ρ p = 0 := by rw [Polynomial.eval_map] at hw'; exact hw'
  have key : ∀ r r', ψ r = ψ r' → ρ r = ρ r' := by
    intro r r' h
    have h1 : ψ (r - r') = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨s, hs⟩ := hp _ h1
    rw [← sub_eq_zero, ← map_sub, hs, map_mul, hρp, zero_mul]
  have key2 : ∀ r, ρ (R (ψ r)) / MvPolynomial.eval w.1 q = ρ r := by
    intro r
    rw [div_eq_iff hw, key (R (ψ r)) (r * Polynomial.C q) (by rw [hR', map_mul, hψq, mul_comm]),
      map_mul, hρq]
  let χ : A →ₐ[ℂ] ℂ :=
    { toFun := fun b => ρ (R b) / MvPolynomial.eval w.1 q
      map_one' := by simpa using key2 1
      map_zero' := by simpa using key2 0
      map_add' := fun b b' => by
        rw [← add_div, ← map_add, key (R (b + b')) (R b + R b') (by
          rw [map_add, hR', hR', hR', mul_add])]
      map_mul' := fun b b' => by
        have := key (Polynomial.C q * R (b * b')) (R b * R b') (by
          rw [map_mul, map_mul, hR', hR', hR', hψq]; ring)
        rw [map_mul, map_mul, hρq] at this
        field_simp
        rw [← this, mul_comm]
      commutes' := fun c => by
        have h1 : ψ (Polynomial.C (MvPolynomial.C c)) = algebraMap ℂ A c := by
          rw [hψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
          exact j.commutes c
        rw [← h1, key2]
        simp [hρ] }
  refine ⟨χ, fun i => ?_, ?_⟩
  · have h1 : ψ (Polynomial.C (MvPolynomial.X i)) = j (MvPolynomial.X i) := by simp [hψ]
    change ρ (R _) / _ = _
    rw [← h1, key2]
    simp [hρ]
  · have h1 : ψ Polynomial.X = a := by simp [hψ]
    change ρ (R _) / _ = _
    rw [← h1, key2]
    simp [hρ]
end GlobalTheory.ThetaRational
