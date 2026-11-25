-- Prove2me | solution 1 for GlobalTheory.Mass.Transp.genus_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:45.455205+00:00
-- url     : https://prove2.me/submissions/aa921f8b-08d6-4747-a868-c618f57a90cb

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
open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
omit [StarRing K] in
private lemma img_trans_eq_img_img (e₁ : V ≃ₗ[K] V') (e₂ : V' ≃ₗ[K] V'') (L : Submodule R V) :
    _root_.GlobalTheory.Mass.Transp.img (e₁.trans e₂) L =
      _root_.GlobalTheory.Mass.Transp.img e₂ (_root_.GlobalTheory.Mass.Transp.img e₁ L) := by
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.mem_img]
open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} in
private lemma mem_genus_iff_isLattice_and_locally_isom (L M : Submodule R V) : M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L ↔ Submodule.IsLattice K M ∧
    ∀ p : Ideal R, p.IsMaximal → ∃ g ∈ _root_.Formalism.HermitianLatticesTheory.isom h,
      _root_.GlobalTheory.Mass.Transp.img g (_root_.Formalism.HermitianLatticesTheory.loc (K := K) p L) = _root_.Formalism.HermitianLatticesTheory.loc (K := K) p M := Iff.rfl
open NumberField Matrix in
open scoped ENNReal Classical in
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V''] in
private lemma loc_img_eq_img_loc (e : V ≃ₗ[K] V') (p : Ideal R) (L : Submodule R V) :
    _root_.Formalism.HermitianLatticesTheory.loc (K := K) p (_root_.GlobalTheory.Mass.Transp.img e L) =
      _root_.GlobalTheory.Mass.Transp.img e (_root_.Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
  have hsmul : ∀ (s : R) (y : V'), e.symm (s • y) = s • e.symm y :=
    fun s y => LinearMap.map_smul_of_tower e.symm.toLinearMap s y
  ext y
  rw [_root_.GlobalTheory.Mass.Transp.mem_img]
  unfold _root_.Formalism.HermitianLatticesTheory.loc _root_.Formalism.HermitianLatticesTheory.locS
  show (∃ s ∈ _, s • y ∈ _) ↔ (∃ s ∈ _, s • e.symm y ∈ _)
  simp only [_root_.GlobalTheory.Mass.Transp.mem_img, hsmul]
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
theorem _root_.solution (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L M : Submodule R V)
    (hM : M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L) : _root_.GlobalTheory.Mass.Transp.img e M ∈ _root_.Formalism.HermitianLatticesTheory.genus h' (_root_.GlobalTheory.Mass.Transp.img e L) := by
  rw [mem_genus_iff_isLattice_and_locally_isom] at hM ⊢
  refine ⟨isLattice_img_of_isLattice e M hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, heq⟩ := hM.2 p hp
  refine ⟨(_root_.GlobalTheory.Mass.Transp.conj e he ⟨g, hg⟩ : _root_.Formalism.HermitianLatticesTheory.isom h'), SetLike.coe_mem _, ?_⟩
  rw [loc_img_eq_img_loc, loc_img_eq_img_loc, ← heq, ← img_trans_eq_img_img, ← img_trans_eq_img_img]
  congr 1
  ext x
  simp [_root_.GlobalTheory.Mass.Transp.conj]
end _root_.GlobalTheory.Mass.Transp
end GlobalTheory.Mass.Transp
