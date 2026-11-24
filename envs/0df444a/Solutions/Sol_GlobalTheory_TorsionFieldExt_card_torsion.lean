-- Prove2me | solution 1 for GlobalTheory.TorsionFieldExt.card_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:05.15074+00:00
-- url     : https://prove2.me/submissions/ac4bd704-e35f-4f2c-a97f-c7c3401e0992

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointsFieldExtension

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionFieldExt
variable {S : Scheme.{0}}
namespace GlobalTheory.TorsionFieldExt
theorem _root_.solution (hL : Out.Laws) (P : Out.PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) {n : ℕ}
    (hn : (n : K) ≠ 0) : Nat.card {y : Over.mk x ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g) := by
  have hn' : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hL.polBaseChange S _ x P
  have c := (hL.mulN _ P' n hn').2.2.2.2 K (𝟙 _) hn
  let Φ : (Over.mk (𝟙 (Sp K)) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ x) ⟶ P.A) :=
    MonoidHom.mk' (fun y => Out.toBase hg.w y) (hmul _)
  have hΦ : Function.Bijective Φ :=
    ⟨fun a b e => Over.OverMorphism.ext
      (hg.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z =>
      ⟨Over.homMk (hg.lift z.left (𝟙 _) (Over.w z)) (hg.lift_snd _ _ _), Over.OverMorphism.ext (hg.lift_fst _ _ _)⟩⟩
  have e : Nat.card {y : Over.mk (𝟙 (Sp K)) ⟶ P'.A // y ^ n = 1} =
      Nat.card {y : Over.mk (𝟙 _ ≫ x) ⟶ P.A // y ^ n = 1} :=
    Nat.card_congr ((Equiv.ofBijective Φ hΦ).subtypeEquiv fun y => by
      show _ ↔ Φ y ^ n = 1
      rw [← map_pow, map_eq_one_iff Φ hΦ.1])
  rw [Category.id_comp] at e
  rw [← e, ← hdim]
  exact c
end GlobalTheory.TorsionFieldExt
