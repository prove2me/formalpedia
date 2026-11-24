-- Prove2me | solution 1 for GlobalTheory.KaUnique.jac_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:14.26692+00:00
-- url     : https://prove2.me/submissions/97caa46a-6758-47fa-94db-f8b27ac931b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Theorems.Thm_GlobalTheory_KaUnique_valT_comp
import Theorems.Thm_GlobalTheory_KaUnique_trU_val
import Theorems.Thm_GlobalTheory_KaUnique_valT_sec
import Theorems.Thm_GlobalTheory_KaUnique_fst_translate
import Theorems.Thm_GlobalTheory_KaUnique_top_le_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
variable {T T' : Type} [CommRing T] [CommRing T'] {X : Scheme.{0}}
variable {R : Type} [CommRing R]
namespace GlobalTheory.KaUnique
theorem _root_.solution (x : KeyIn R) {n : ℕ} (s : Fin x.P.g → RR x n) (z : Pt x) (c c' : x.P.L.ι)
    (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c')
    (h0 : ∀ i, valT (T := R) z.left (x.P.L.U c') ((s i).f c') = 0) :
    jac x s z c = (trU (T := R) z.left x.P.L c c' h h').val ^ (x.P.g * n) * jac x s z c' := by
  unfold jac
  rw [mul_comm x.P.g n, pow_mul]
  have hd : ∀ (a : R) (M : Matrix (Fin x.P.g) (Fin x.P.g) R), a ^ x.P.g * M.det = (a • M).det := fun a M => by
    rw [Matrix.det_smul, Fintype.card_fin]
  rw [hd]
  congr 1
  ext i k
  have hk := top_le_translate x z k h
  have hk' := top_le_translate x z k h'
  have e1 : (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v k).left (x.P.L.U c') ((s i).f c')).fst = 0 := by
    have := valT_comp (TrivSqZeroExt.fstHom R R R).toRingHom _ _ hk' ((s i).f c')
    erw [fst_translate x z k, h0 i] at this
    exact this.symm
  have e2 : ((trU (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v k).left x.P.L c c' hk hk').val).fst =
      (trU (T := R) z.left x.P.L c c' h h').val := by
    have := valT_comp (TrivSqZeroExt.fstHom R R R).toRingHom _ (x.P.L.U c ⊓ x.P.L.U c')
      (fun _ hp => ⟨hk hp, hk' hp⟩) (x.P.L.g c c').val
    erw [fst_translate x z k] at this
    rw [trU_val, trU_val]
    exact this.symm
  rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply]
  erw [valT_sec _ x.P.L c c' hk hk' n (s i)]
  rw [TrivSqZeroExt.snd_mul]
  erw [e1]
  rw [TrivSqZeroExt.fst_pow, e2]
  simp
end GlobalTheory.KaUnique
