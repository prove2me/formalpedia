-- Prove2me | solution 1 for GlobalTheory.HkFactor.exists_unique_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:08.733028+00:00
-- url     : https://prove2.me/submissions/c4043bb9-2b5c-41de-9920-ecb0d5aecda6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueFactorThroughEtaleIsogenyReduced
import Theorems.Thm_GlobalTheory_HkFactor_ext_of_geometricPoints
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_of_flat_surjective
import Theorems.Thm_GlobalTheory_FlatQuotient_exists_desc
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
open GlobalTheory GlobalTheory.HkFactor
namespace GlobalTheory.HkFactor
theorem _root_.solution : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  intro S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H

  let T : Over S := pullback ψ η[B]
  let i : T ⟶ A := pullback.fst ψ η[B]
  have hker : IsPullback i (toUnit T) ψ η[B] := by
    have hp := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit T)] at hp

  have : IsReduced T.left := by
    have hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left := hker.map (Over.forget S)
    have : Etale (toUnit T).left := MorphismProperty.of_isPullback hp het
    have : IsReduced (𝟙_ (Over S)).left := by dsimp; infer_instance
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left
  have := hsep

  have hf : i ≫ g = toUnit T ≫ η[B'] := by
    apply Over.OverMorphism.ext
    refine ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_
    intro k _ _ x
    let xo : Over.mk (x ≫ T.hom) ⟶ T := Over.homMk x
    have e1 : (xo ≫ i) ≫ ψ = 1 := by
      rw [Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    have e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B']) := by
      rw [← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc,
        toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    simpa only [xo, Over.comp_left, Over.homMk_left] using congrArg CommaMorphism.left e3
  have := hψ; have := hg; have := hfin; have := het; have := hsurj
  obtain ⟨β, hβ, hψβ⟩ := FlatQuotient.exists_desc ψ i g hker hf
  have : Epi ψ := FlatQuotient.epi_of_flat_surjective ψ
  exact ⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩
end GlobalTheory.HkFactor
