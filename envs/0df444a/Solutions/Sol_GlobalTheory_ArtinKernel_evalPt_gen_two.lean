-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.evalPt_gen_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:48.408014+00:00
-- url     : https://prove2.me/submissions/6ba9b21d-f052-4b25-8a3c-8d365ee58965

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_congr
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_appLE
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
section Points
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}
private theorem evalPt_res_eq_evalPt (x : Sp R ⟶ Y) {U V : Y.Opens} (e : V ≤ U) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(Y, U)ˣ) : evalPt x V hV (res e s).val = evalPt x U hU s.val :=
  evalPt_res x e hU hV s.val
private theorem units_map_evalPt_res_pullU_eq_comp (x : Sp R ⟶ Y) (ψ : Y ⟶ X) {U₀ U₁ : X.Opens} {V : Y.Opens}
    (e : V ≤ ψ ⁻¹ᵁ U₀ ⊓ ψ ⁻¹ᵁ U₁) (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, U₀ ⊓ U₁)ˣ) :
    Units.map (evalPt x V hV).toMonoidHom (res e (pullU ψ (U₀ ⊓ U₁) s)) =
      Units.map (evalPt (x ≫ ψ) (U₀ ⊓ U₁) (hV.trans (x.preimage_mono e))).toMonoidHom s := by
  ext
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact evalPt_appLE x ψ _ rfl (U₀ ⊓ U₁) V e hV _ s.val
private theorem mul_eq_mul_of_eq_mul_zpow_neg_one {M : Type} [CommGroup M] {c c' t₀ t₁ : M}
    (h : c = t₀ * t₁ ^ (-1 : ℤ) * c') : c * t₁ = t₀ * c' := by
  rw [h, _root_.zpow_neg_one, mul_right_comm, inv_mul_cancel_right]
end Points
section Family
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable [Module.Finite ℂ R]
end Family
end GlobalTheory.ArtinKernel
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (L : LB X) (φ₀ φ₁ : Y ⟶ X)
    (c : LB.Gen (LB.LinComb L (K := Fin 2) ![φ₀, φ₁] ![1, -1])) (hc : c.IsGen)
    (x : Sp R ⟶ Y) (y₀ y₁ : Sp R ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁)
    (j j' : Fin 2 → L.ι) (a : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j) (b : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j')
    (a₀ : ⊤ ≤ y₀ ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j' 0))) (a₁ : ⊤ ≤ y₁ ⁻¹ᵁ (L.U (j 1) ⊓ L.U (j' 1))) :
    evalPt x _ a (c.s j).val * evalPt y₁ _ a₁ (L.g (j 1) (j' 1)).val =
      evalPt y₀ _ a₀ (L.g (j 0) (j' 0)).val * evalPt x _ b (c.s j').val := by
  have hab : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L ![φ₀, φ₁] j ⊓ LB.wchart L ![φ₀, φ₁] j') :=
    GlobalTheory.ThetaGroupFrame.top_le_inf x a b
  have hh := congrArg
    (Units.map (evalPt x (LB.wchart L ![φ₀, φ₁] j ⊓ LB.wchart L ![φ₀, φ₁] j') hab).toMonoidHom) (hc j j')
  unfold LB.LinComb at hh
  simp only [map_mul, map_prod, map_zpow, units_map_evalPt_res_pullU_eq_comp] at hh
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zpow_one] at hh
  have hv := congrArg Units.val (mul_eq_mul_of_eq_mul_zpow_neg_one hh)
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hv
  rw [evalPt_res_eq_evalPt x _ a hab, evalPt_res_eq_evalPt x _ b hab, evalPt_congr h₀ _ _ a₀,
    evalPt_congr h₁ _ _ a₁] at hv
  exact hv
end GlobalTheory.ArtinKernel
