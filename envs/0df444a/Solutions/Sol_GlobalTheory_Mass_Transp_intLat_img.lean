-- Prove2me | solution 1 for GlobalTheory.Mass.Transp.intLat_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:29:19.74781+00:00
-- url     : https://prove2.me/submissions/a14df394-e16d-43f6-9025-b4e43b6a8bff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
import Theorems.Thm_GlobalTheory_Mass_Transp_mem_img
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.Transp
section General
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
omit [StarRing K] in
private lemma isLattice_img_of_isLattice (e : V ≃ₗ[K] V') (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (_root_.GlobalTheory.Mass.Transp.img e L) := by
  refine ⟨hL.fg.map _, ?_⟩
  rw [_root_.GlobalTheory.Mass.Transp.img, Submodule.map_coe, LinearMap.coe_restrictScalars,
    Submodule.span_image (e : V →ₗ[K] V'), hL.span_eq_top, Submodule.map_top]
  exact LinearEquiv.range e
end General
end GlobalTheory.Mass.Transp
end

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Transp
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open NumberField Matrix
open scoped ENNReal Classical
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace GlobalTheory.Mass.Transp
namespace _root_.GlobalTheory.Mass.Transp
theorem _root_.solution (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule R V)
    (hL : _root_.GlobalTheory.Mass.IsIntLat h L) : _root_.GlobalTheory.Mass.IsIntLat h' (_root_.GlobalTheory.Mass.Transp.img e L) := by
  unfold _root_.GlobalTheory.Mass.IsIntLat _root_.Formalism.HermitianLatticesTheory.IsIntegralLat at *
  refine ⟨isLattice_img_of_isLattice e L hL.1, fun x hx y hy => ?_⟩
  rw [_root_.GlobalTheory.Mass.Transp.mem_img] at hx hy
  rw [← _root_.GlobalTheory.Mass.Transp.symm_isom e he]
  exact hL.2 _ hx _ hy
end _root_.GlobalTheory.Mass.Transp
end GlobalTheory.Mass.Transp
