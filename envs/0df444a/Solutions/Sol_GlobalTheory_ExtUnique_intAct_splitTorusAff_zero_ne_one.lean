-- Prove2me | solution 1 for GlobalTheory.ExtUnique.intAct_splitTorusAff_zero_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:59.248804+00:00
-- url     : https://prove2.me/submissions/2c2ffaf1-f8b8-4565-af95-9c2e48aa83ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
namespace GlobalTheory.ExtUnique
theorem _root_.solution (R : CommRingCat.{0}) [Nontrivial R] (X : Type) [AddCommGroup X]
    [Nontrivial X] : (intAct (splitTorusAff R X)).act 0 ≠ (intAct (splitTorusAff R X)).act 1 := by
  intro h
  rw [(intAct _).one] at h
  change (𝟙 _ : splitTorusAff R X ⟶ _) ^ (0 : ℤ) = _ at h
  rw [zpow_zero, Hom.one_def] at h
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ (η[splitTorusAff R X]).left =
      𝟙 (Spec (torusRing R X)) := congrArg (fun z => z.left) h
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := torusRing R X) (S := R) (η[splitTorusAff R X]).left
  rw [← hψ] at h₁
  have h₂ : ψ ≫ CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)) = 𝟙 (torusRing R X) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_id]; exact h₁)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have h₃ : algebraMap R (AddMonoidAlgebra R X) (ψ (AddMonoidAlgebra.single x 1)) = AddMonoidAlgebra.single x 1 :=
    congrArg (fun z => z.hom (AddMonoidAlgebra.single x 1)) h₂
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply] at h₃
  have h₄ := congrArg (fun z : AddMonoidAlgebra R X => z.coeff x) h₃
  simp [hx] at h₄
end GlobalTheory.ExtUnique
