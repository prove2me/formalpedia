-- Prove2me | solution 1 for GlobalTheory.TorusAlg.snd_pull_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:18:41.016291+00:00
-- url     : https://prove2.me/submissions/2c47901c-5a0e-49da-bc25-bec500cfc242

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
open Out Out.Inh
namespace GlobalTheory.TorusAlg
theorem _root_.solution (φ : Sp (DualNumber ℂ) ⟶ Sp ℂ) (hφ : φ = spMap (algebraMap ℂ (DualNumber ℂ)))
    (U : (Sp ℂ).Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (f : Γ(Sp ℂ, U)) :
    TrivSqZeroExt.snd (show DualNumber ℂ from
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((φ.appLE U ⊤ h).hom f)) = 0 := by
  have hU : U = ⊤ := top_unique fun x _ => by
    obtain ⟨y⟩ : Nonempty (Sp (DualNumber ℂ)) := inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber ℂ)))
    have hy : φ y ∈ U := h (show y ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rwa [show x = φ y from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
  subst hU hφ
  have e : (spMap (algebraMap ℂ (DualNumber ℂ))).appLE ⊤ ⊤ h = (spMap (algebraMap ℂ (DualNumber ℂ))).appTop :=
    Scheme.Hom.appLE_eq_app _
  have n := congrArg (fun k => k.hom f) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))))
  rw [e]
  exact (congrArg (TrivSqZeroExt.snd (R := ℂ) (M := ℂ)) n).trans rfl
end GlobalTheory.TorusAlg
