-- Prove2me | solution 1 for GlobalTheory.KS.PtDual.exists_ptDer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:28.486035+00:00
-- url     : https://prove2.me/submissions/7f6856bf-729d-4066-905e-92f8c97dd7dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Theorems.Thm_GlobalTheory_KS_PtDual_ev_res
import Theorems.Thm_GlobalTheory_KS_PtDual_le_preimage_iff
import Theorems.Thm_GlobalTheory_KS_PtDual_fst_ev
import Theorems.Thm_GlobalTheory_top_le_preimage_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.PtDual
variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
open Classical
namespace GlobalTheory.KS.PtDual
theorem _root_.solution {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) :
    ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  have H : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ⊤ ≤ v ⁻¹ᵁ W := fun W h => (le_preimage_iff v _).2 (hv ▸ h)
  refine ⟨fun W f => if h : ⊤ ≤ v ⁻¹ᵁ W then (ev v W h f).snd else 0, ⟨?_, ?_, ?_⟩, fun W h f => ?_⟩
  · intro W h f f'
    simp only [dif_pos (H W h), map_add, TrivSqZeroExt.snd_add]
  · intro W h f f'
    simp only [dif_pos (H W h), map_mul, DualNumber.snd_mul, fst_ev hv]
    ring
  · intro W W' e h f
    have k := H W (top_le_preimage_mono y e h)
    simp only [dif_pos (H W' h), dif_pos k, ev_res v e k]
  · simp only [dif_pos h]
end GlobalTheory.KS.PtDual
