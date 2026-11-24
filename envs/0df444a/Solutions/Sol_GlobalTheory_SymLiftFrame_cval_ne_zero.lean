-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.cval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:58.835387+00:00
-- url     : https://prove2.me/submissions/5203d5fb-399e-4c88-b66a-f6009bc060b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_mem_chart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
section Values
variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
private theorem valAt'_mul_moduli {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f f' : Γ(Z, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  unfold valAt'
  split_ifs with h
  · unfold valAt
    rw [map_mul, map_mul]
  · rw [zero_mul]
private theorem valAt'_one_moduli {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valAt' x U 1 = 1 := by
  unfold valAt'
  rw [dif_pos h]
  unfold valAt
  rw [map_one, map_one]
variable {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ
end Values
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}
end GlobalTheory.SymLiftFrame
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
variable {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y) : cval t r J ≠ 0 := by
  intro h0
  have h1 := valAt'_mul_moduli r ((L.LinComb φ ε).U fun k => J (r ≫ φ k))
    ((t.s fun k => J (r ≫ φ k))⁻¹).val (t.s fun k => J (r ≫ φ k)).val
  rw [Units.inv_mul] at h1
  have h2 : valAt' r ((L.LinComb φ ε).U fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val = 0 := h0
  rw [h2, mul_zero] at h1
  exact one_ne_zero ((valAt'_one_moduli r _ (mem_chart hJ φ r)).symm.trans h1)
end GlobalTheory.SymLiftFrame
