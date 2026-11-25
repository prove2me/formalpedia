-- Prove2me | solution 1 for GlobalTheory.PeriodConn.entry_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:04:38.851943+00:00
-- url     : https://prove2.me/submissions/8753c50b-8f40-44c9-9918-472ababb0955

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix
open GlobalTheory GlobalTheory.PeriodConn
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
namespace GlobalTheory.PeriodConn
namespace _root_.GlobalTheory.PeriodConn
theorem _root_.solution {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P P' : D.La →+ (Fin g → ℂ)}
    (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P') {A : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ x, P' x = A.mulVec (P x)) (i j : Fin g) (hij : ty i ≠ ty j) : A i j = 0 := by
  obtain ⟨hlin, -, -, hspan, -⟩ := hP
  have hlin' := hP'.1
  have key : ∀ a : 𝓞 E, A i j * ((ty j) (a : E) - (ty i) (a : E)) = 0 := by
    intro a
    set d : Fin g → ℂ := fun k => (ty k) (a : E) - (ty i) (a : E) with hd
    let φ : (Fin g → ℂ) →ₗ[ℝ] ℂ :=
      ((LinearMap.proj i).comp (A.mulVecLin.comp (Matrix.diagonal d).mulVecLin)).restrictScalars ℝ
    have hφ : φ = 0 := by
      refine LinearMap.ext_on_range hspan fun x => ?_
      have h1 := hlin' a x i
      rw [h (a • x), h x] at h1
      have hvec : Matrix.diagonal d *ᵥ P x = P (a • x) - (ty i) (a : E) • P x := by
        funext k
        simp [Matrix.mulVec_diagonal, hd, hlin, sub_mul]
      simp only [φ, LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Matrix.mulVecLin_apply, LinearMap.zero_apply, hvec, Matrix.mulVec_sub,
        Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, sub_self]
    have := LinearMap.congr_fun hφ (Pi.single j 1)
    simpa [φ, hd, Matrix.mulVec_single, Matrix.mulVec, dotProduct, Matrix.diagonal,
      Pi.single_apply] using this
  by_contra hA
  apply hij
  refine (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_).symm
  ext a
  have := key a
  simp only [RingHom.comp_apply]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hA))
end _root_.GlobalTheory.PeriodConn
end GlobalTheory.PeriodConn
