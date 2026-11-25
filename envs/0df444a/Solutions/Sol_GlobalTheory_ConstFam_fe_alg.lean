-- Prove2me | solution 1 for GlobalTheory.ConstFam.fe_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:06.39496+00:00
-- url     : https://prove2.me/submissions/a377511c-1b9a-4a1f-933e-49e4e344bab1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
namespace GlobalTheory.ConstFam
theorem _root_.solution {U : Type} [CommGroup U] (j : ℕ) (n₁ n₂ n₃ : ℤ) {u u' x ψ₁ ψ₂ ψ₃ ρ χ₁ χ₂ χ₃ ρ₀ o m a s t : U}
    (v₁ : χ₁ * χ₂⁻¹ * χ₃⁻¹ * ρ₀⁻¹ * (χ₂ ^ j * ρ₀ ^ j) =
      o ^ ((j : ℤ) - 1) * t * t⁻¹ * o * (m ^ ((j : ℤ) - 1) * s * a⁻¹ * o)⁻¹ * u')
    (v₂ : u = ψ₁ * ψ₂⁻¹ * ψ₃⁻¹ * ρ⁻¹ * (ψ₂ ^ j * ρ ^ j)) (q₁ : ψ₁ = s * (x ^ (n₁ + n₂ + n₃) * χ₁))
    (q₂ : ψ₂ = m * (x ^ n₁ * χ₂)) (q₃ : ψ₃ = a * (x ^ n₂ * χ₃)) (q₄ : ρ₀ = o * ρ) :
    u = x ^ (j * n₁ + n₃) * u' := by
  apply Additive.ofMul.injective
  have b₁ := congrArg Additive.ofMul v₁
  have b₂ := congrArg Additive.ofMul v₂
  have c₁ := congrArg Additive.ofMul q₁
  have c₂ := congrArg Additive.ofMul q₂
  have c₃ := congrArg Additive.ofMul q₃
  have c₄ := congrArg Additive.ofMul q₄
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow] at b₁ b₂ c₁ c₂ c₃ c₄ ⊢
  linear_combination (norm := module) b₂ + b₁ + c₁ + ((j : ℤ) - 1) • c₂ - c₃ - ((j : ℤ) - 1) • c₄
end GlobalTheory.ConstFam
