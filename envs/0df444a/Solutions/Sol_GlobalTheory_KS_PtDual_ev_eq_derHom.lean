-- Prove2me | solution 1 for GlobalTheory.KS.PtDual.ev_eq_derHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:57.371195+00:00
-- url     : https://prove2.me/submissions/18dabe9b-3e42-4510-b11b-8111e15d62da

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
import Theorems.Thm_GlobalTheory_KS_PtDual_snd_derHom
import Theorems.Thm_GlobalTheory_KS_PtDual_derHom_res
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem


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
namespace GlobalTheory.KS.PtDual
theorem _root_.solution {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : pt0 ≫ v = y) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : ev v U h = derHom hδ U h') (W : X.Opens) (k : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : (ev v W k f).snd = δ W f := by
  have k' : ⊤ ≤ y ⁻¹ᵁ W := hv ▸ (le_preimage_iff v W).1 k
  obtain ⟨g, hg, hy⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (top_le_preimage_iff_mem y W).1 k'⟩
    ((top_le_preimage_iff_mem y U).1 h')
  have l' : ⊤ ≤ y ⁻¹ᵁ X.basicOpen g := (top_le_preimage_iff_mem y _).2 hy
  have l : ⊤ ≤ v ⁻¹ᵁ X.basicOpen g := (le_preimage_iff v _).2 (hv ▸ l')
  have := hU.isLocalization_basicOpen g
  have e' : ev v _ l = derHom hδ _ l' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
    refine (ev_res v (X.basicOpen_le g) h l a).trans ?_
    rw [e]
    exact (derHom_res hδ (X.basicOpen_le g) h' l' a).symm
  rw [← ev_res v hg k l, e', derHom_res hδ hg k' l', snd_derHom]
end GlobalTheory.KS.PtDual
