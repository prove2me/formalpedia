-- Prove2me | solution 1 for ModularCurve.IgusaScheme.flat_igusaTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7aa5a34e-b87e-525d-8884-429c80483846

import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlg XFin XInf ιFin ιInf isOpenImmersion_ιFin isOpenImmersion_ιInf igusaTo ιFin_igusaTo ιInf_igusaTo mem_range_ιFin_or_mem_range_ιInf"
p2m_open "ModularCurve.IgusaScheme ModularCurve"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

omit [NeZero N] [Fact ℓ.Prime] in

theorem f1_algebraMap_injective :
    Function.Injective
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N)) := by
  rw [IsScalarTower.algebraMap_eq ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N),
    RingHom.coe_comp]
  exact (algebraMap ℚ ↥(modularFunctionFieldFull N)).injective.comp Subtype.val_injective

scoped instance f1_isTorsionFree_field :
    Module.IsTorsionFree ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (f1_algebraMap_injective N ℓ)

scoped instance f1_isPrincipalIdealRing : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt ℓ) :=
  GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ

scoped instance f1_flat_chartAlg (S : Set ↥(modularFunctionFieldFull N)) :
    Module.Flat ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlg N ℓ S) := by
  haveI : Module.IsTorsionFree ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlg N ℓ S) := inferInstance
  infer_instance

theorem f1_flat_specMap (S : Set ↥(modularFunctionFieldFull N)) :
    Flat (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlg N ℓ S)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

def f1_openCover : (ModularCurve.IgusaScheme N ℓ).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => bif b then XFin N ℓ else XInf N ℓ)
    (fun b => match b with
      | true => ιFin N ℓ
      | false => ιInf N ℓ)
    (fun x => by
      rcases mem_range_ιFin_or_mem_range_ιInf N ℓ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (fun b => by
      cases b
      · exact isOpenImmersion_ιInf N ℓ
      · exact isOpenImmersion_ιFin N ℓ)

theorem f1_flat_igusaTo : Flat (igusaTo N ℓ) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (f1_openCover N ℓ) fun b => ?_
  cases b
  · show Flat (ιInf N ℓ ≫ igusaTo N ℓ)
    rw [ιInf_igusaTo]
    exact f1_flat_specMap N ℓ _
  · show Flat (ιFin N ℓ ≫ igusaTo N ℓ)
    rw [ιFin_igusaTo]
    exact f1_flat_specMap N ℓ _

end ModularCurve.IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve.IgusaScheme"

open AlgebraicGeometry _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.ModularCurve.IgusaScheme in
theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] : Flat (igusaTo N ℓ) :=
  ModularCurve.IgusaScheme.f1_flat_igusaTo N ℓ

end S_ModularCurve_IgusaScheme_flat_igusaTo
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo (solution)
