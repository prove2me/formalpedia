-- Prove2me | solution 1 for GlobalTheory.Mass.Transp.dual_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:05.523794+00:00
-- url     : https://prove2.me/submissions/6d3f46b8-491e-4d02-9a73-26cc8e27293a

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
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
private lemma mem_dual_iff_hermitian_lattices (L : Submodule R V) (x : V) :
    x ∈ _root_.Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  unfold _root_.Formalism.HermitianLatticesTheory.dual _root_.Formalism.E.hdual
  simp [Submodule.mem_iInf]
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
theorem _root_.solution (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule R V) :
    _root_.Formalism.HermitianLatticesTheory.dual h' (_root_.GlobalTheory.Mass.Transp.img e L) = _root_.GlobalTheory.Mass.Transp.img e (_root_.Formalism.HermitianLatticesTheory.dual h L) := by
  ext y
  rw [mem_dual_iff_hermitian_lattices, _root_.GlobalTheory.Mass.Transp.mem_img, mem_dual_iff_hermitian_lattices]
  constructor
  · intro hy x hx
    rw [← he, LinearEquiv.apply_symm_apply]
    exact hy (e x) ((_root_.GlobalTheory.Mass.Transp.mem_img e L _).2 (by simpa using hx))
  · intro hy z hz
    rw [_root_.GlobalTheory.Mass.Transp.mem_img] at hz
    have := hy _ hz
    rwa [_root_.GlobalTheory.Mass.Transp.symm_isom e he] at this
end _root_.GlobalTheory.Mass.Transp
end GlobalTheory.Mass.Transp
