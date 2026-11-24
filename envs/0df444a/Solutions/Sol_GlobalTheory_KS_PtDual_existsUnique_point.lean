-- Prove2me | solution 1 for GlobalTheory.KS.PtDual.existsUnique_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:46.740221+00:00
-- url     : https://prove2.me/submissions/a33f923c-ec60-4953-8a63-35c76fda131b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Theorems.Thm_GlobalTheory_KS_PtDual_ev_ext
import Theorems.Thm_GlobalTheory_KS_PtDual_exists_ev
import Theorems.Thm_GlobalTheory_KS_PtDual_ev_comp
import Theorems.Thm_GlobalTheory_KS_PtDual_le_preimage_iff
import Theorems.Thm_GlobalTheory_KS_PtDual_fst_ev
import Theorems.Thm_GlobalTheory_KS_PtDual_fst_derHom
import Theorems.Thm_GlobalTheory_KS_PtDual_snd_derHom
import Theorems.Thm_GlobalTheory_KS_PtDual_exists_affine
import Theorems.Thm_GlobalTheory_KS_PtDual_ev_eq_derHom
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAtHom_eb5802171cfc


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
theorem _root_.solution {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) :
    ∃! v : Sp (DualNumber ℂ) ⟶ X, pt0 ≫ v = y ∧
      ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  obtain ⟨U, hU, h'⟩ := exists_affine y
  obtain ⟨v, h, e⟩ := exists_ev hU (derHom hδ U h')
  have hv : pt0 ≫ v = y := by
    refine ev_ext hU ((le_preimage_iff v U).1 h) h' (RingHom.ext fun f => ?_)
    rw [ev_comp _ v U h, e]
    exact (fst_derHom hδ U h' f).trans (valAt'_eq_valAtHom y h' f)
  refine ⟨v, ⟨hv, ev_eq_derHom hδ hv hU h h' e⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  have k : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff w _).2 (hw ▸ h')
  refine ev_ext hU k h (RingHom.ext fun f => ?_)
  rw [e]
  ext
  · rw [fst_ev hw, fst_derHom]
  · rw [hw', snd_derHom]
end GlobalTheory.KS.PtDual
