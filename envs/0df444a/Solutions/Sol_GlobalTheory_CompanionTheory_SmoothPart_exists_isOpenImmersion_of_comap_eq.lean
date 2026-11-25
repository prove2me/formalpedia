-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothPart.exists_isOpenImmersion_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:59.381968+00:00
-- url     : https://prove2.me/submissions/ce612040-92a8-4a0a-b690-25703faac7fc

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_isIso_inclusion_of_eq
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothPart
namespace GlobalTheory.CompanionTheory.SmoothPart
theorem _root_.solution {X : Scheme.{0}} (I J : X.IdealSheafData) (O : X.Opens)
    (hO : (I.support : Set X) ⊆ O) (e : I.comap O.ι = J.comap O.ι) :
    ∃ h : I.subscheme ⟶ J.subscheme, IsOpenImmersion h ∧ h ≫ J.subschemeι = I.subschemeι := by
  have hsurj : Function.Surjective (pullback.snd O.ι I.subschemeι) := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    ext y
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    apply hO
    rw [← I.range_subschemeι]
    exact Set.mem_range_self y
  have : Epi (pullback.snd O.ι I.subschemeι).base := (TopCat.epi_iff_surjective _).2 hsurj
  have : IsIso (pullback.snd O.ι I.subschemeι) := IsOpenImmersion.isIso _
  have hincl : IsIso (Scheme.IdealSheafData.inclusion e.ge) := isIso_inclusion_of_eq _ e.symm
  refine ⟨inv (pullback.snd O.ι I.subschemeι) ≫ (I.comapIso O.ι).inv ≫
    Scheme.IdealSheafData.inclusion e.ge ≫ (J.comapIso O.ι).hom ≫ pullback.snd _ _,
    inferInstance, ?_⟩
  simp only [Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    Scheme.IdealSheafData.inclusion_subschemeι_assoc,
    Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc, pullback.condition,
    IsIso.inv_hom_id_assoc]
end GlobalTheory.CompanionTheory.SmoothPart
