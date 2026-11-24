-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.cval_powGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:00:01.024689+00:00
-- url     : https://prove2.me/submissions/2ab70676-dd38-4877-a840-94cb4259ca88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_mem_chart
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_pull
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
private theorem valAt'_presheaf_map_homOfLE {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Z, U)) :
    valAt' x V (Z.presheaf.map (homOfLE hVU).op f) = valAt' x U f := by
  unfold valAt'
  rw [dif_pos h, dif_pos (h.trans fun p hp => hVU hp)]
  unfold valAt
  congr 1
  rw [← Scheme.Hom.map_appLE x h (homOfLE hVU).op]
  rfl
private theorem valAt'_finset_prod {Z : Scheme.{0}} {I : Type} (x : Sp ℂ ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset I) (f : I → Γ(Z, U)) :
    valAt' x U (∏ i ∈ s, f i) = ∏ i ∈ s, valAt' x U (f i) := by
  unfold valAt'
  simp only [dif_pos h]
  unfold valAt
  rw [map_prod, map_prod]
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
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
include hJ
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution {k : ℤ} (θ : ThetaGrp A L k T) (n : ℕ) (r : Sp ℂ ⟶ (T ⊗ A).left) :
    cval (powGen A L k θ n) r J =
      ∏ i ∈ Finset.range n, cval (L := L) θ.φ (r ≫ (translT A (θ.pt ^ i)).left) J := by
  rw [← Fin.prod_univ_eq_prod_range]
  unfold powGen
  conv_lhs => unfold cval
  dsimp only
  rw [Units.coe_prod]
  refine (valAt'_finset_prod r _ (mem_chart hJ _ r) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  unfold res
  refine (valAt'_presheaf_map_homOfLE r _ (mem_chart hJ _ r) _).trans ?_
  exact cval_pull hJ θ.φ (translT A (θ.pt ^ (i : ℕ))).left r
end GlobalTheory.SymLiftFrame
