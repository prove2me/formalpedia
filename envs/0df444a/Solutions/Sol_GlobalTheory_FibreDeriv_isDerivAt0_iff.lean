-- Prove2me | solution 1 for GlobalTheory.FibreDeriv.isDerivAt0_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:19.044112+00:00
-- url     : https://prove2.me/submissions/252df0b1-243c-4232-8279-71b91f2156d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Theorems.Thm_GlobalTheory_FibreDeriv_fst_jet
import Theorems.Thm_GlobalTheory_FibreDeriv_snd_jet
import Theorems.Thm_GlobalTheory_FibreDeriv_fst_evEps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
namespace GlobalTheory.FibreDeriv
theorem _root_.solution (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 e w v ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 ∧
      ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), evEps v U h f = jet w (fun z => valAt' (e z) U f) := by
  refine and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_
  refine ⟨fun H => TrivSqZeroExt.ext ?_ ?_, fun H => ?_⟩
  · rw [fst_jet, fst_evEps v _ h0]
  · rw [snd_jet]; exact H
  · rw [← snd_jet, ← H]; rfl
end GlobalTheory.FibreDeriv
