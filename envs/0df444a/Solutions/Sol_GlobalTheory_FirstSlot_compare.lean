-- Prove2me | solution 1 for GlobalTheory.FirstSlot.compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:40.720614+00:00
-- url     : https://prove2.me/submissions/ecd98e58-b236-4835-9531-51562226b2b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionFirstVariable
import Theorems.Thm_GlobalTheory_FirstSlot_cT_add
import Theorems.Thm_GlobalTheory_FirstSlot_kapV_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
open GlobalTheory.FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.FirstSlot
theorem _root_.solution (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (a b mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (x : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : ∀ χ, sval (s₀ 0) (lift ρ (x * cT D T χ)).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J =
      C * (sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (a + mu)) (cT D T (b + mu)) x).val *
        ((val (D.psi (a + mu)) κ.left z J).val * (val (D.psi (b + mu)) κ.left z J).val) =
      C * (U * (cubV D.cub z J (cT D T a) (cT D T b) (x * cT D T mu)).val * (val (D.psi a) κ.left z J).val *
        (val (D.psi b) κ.left z J).val) := by
  have e₁ := (hA T ρ x 1 z J hJ).1 (a + mu) (b + mu) (a + b + 2 • mu) (a - b) (by rw [two_smul]; abel) (by abel)
  have e₂ := (hA T ρ (x * cT D T mu) 1 z J hJ).1 a b (a + b) (a - b) rfl rfl
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one x, hP _ T ρ κ _ z J hJ, hP (b + mu) T ρ κ _ z J hJ] at e₁
  rw [kapV_one D _ _ hJ, inv_one, _root_.mul_one (x * cT D T mu), hP _ T ρ κ _ z J hJ, hP b T ρ κ _ z J hJ,
    _root_.mul_assoc x, _root_.mul_assoc x, ← cT_add, ← cT_add, add_comm mu a, add_comm mu b] at e₂
  have e₃ : ∑ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J * sval (s' i (a - b)) (lift ρ 1).left z J =
      C * U * ∑ i, sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * sval (s' i (a - b)) (lift ρ 1).left z J := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]; ring
  rw [e₁, e₂] at e₃
  have hne : gs (𝟙 _) z ⊤ (scal T.hom r) * ((val D.sym (1 : T ⟶ D.P.A).left z J)⁻¹ * rigV D z J ^ 2).val *
      (rigV D z J).val * (rigV D z J).val * sval (s₀ 0) (lift ρ (x * cT D T (a + mu))).left z J *
      sval (s₀ 0) (lift ρ (x * cT D T (b + mu))).left z J ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hr (Units.ne_zero _)) (Units.ne_zero _))
      (Units.ne_zero _)) (h0 _)) (h0 _)
  refine mul_left_cancel₀ hne ?_
  simp only [Units.val_mul] at e₃ ⊢
  linear_combination e₃
end GlobalTheory.FirstSlot
