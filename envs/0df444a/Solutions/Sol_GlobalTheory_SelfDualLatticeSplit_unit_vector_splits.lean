-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeSplit.unit_vector_splits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:42:53.03021+00:00
-- url     : https://prove2.me/submissions/2fcc6616-05d7-473a-a921-2b7e32e265ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_hR_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
namespace GlobalTheory.SelfDualLatticeSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma selfDualLatticeSplit_proj_eq_sub_smul (x : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
    (b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) (y : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y =
      y - (b * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y) • x := by
  simp [_root_.GlobalTheory.SelfDualLatticeSplit.proj, _root_.GlobalTheory.SelfDualLatticeSplit.formAt]
open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma hR_selfDualLatticeSplit_proj_eq_zero (x : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
    (b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) (hb : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x x * b = 1)
    (y : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x (_root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y) = 0 := by
  rw [selfDualLatticeSplit_proj_eq_sub_smul, sub_eq_add_neg, _root_.GlobalTheory.SelfDualLatticeSplit.hR_add_right, ← neg_smul,
    _root_.GlobalTheory.SelfDualLatticeCompare.hR_smul_right]
  linear_combination (-(_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y)) * hb
open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma form_smul_add_left_lemma_3 (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
    (x p y : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J (c • x + p) y =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ c * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y +
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J p y := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR _root_.Formalism.UG.hform _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR
  simp [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
end GlobalTheory.SelfDualLatticeSplit
end
end

set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.SelfDualLatticeSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.SelfDualLatticeSplit
namespace _root_.GlobalTheory.SelfDualLatticeSplit
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
      ∀ (v : HeightOneSpectrum (𝓞 F))
        (L : Submodule (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) (Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)),
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLat σ J v L → ∀ x ∈ L,
          (∃ b ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x x * b = 1) →
          L = Submodule.span (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) {x} ⊔
              _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x ∧
            _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLatIn σ J v (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perp σ J v x)
              (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x) := by
  intro F E _ _ _ _ _ σ _ M J _ v L hL x hx hbex
  obtain ⟨b, hbO, hb⟩ := hbex
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLatIn at hL
  obtain ⟨hFG, hspan, hdual⟩ := hL
  have hperp : ∀ y, y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x ↔
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y = 0 ∧ y ∈ L := fun y ↦ Iff.rfl
  have hxy : ∀ y ∈ L, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v :=
    fun y hy ↦ ((hdual y).1 hy).2 x hx
  have hsmul : ∀ y ∈ L, (b * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y) • x ∈ L := fun y hy ↦
    L.smul_mem (⟨_, mul_mem hbO (hxy y hy)⟩ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) hx
  have hprojL : ∀ y ∈ L, _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y ∈
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x := fun y hy ↦ by
    refine (hperp _).2 ⟨hR_selfDualLatticeSplit_proj_eq_zero σ J v x b hb y, ?_⟩
    rw [selfDualLatticeSplit_proj_eq_sub_smul]
    exact L.sub_mem hy (hsmul y hy)
  have hdecomp : ∀ y, y = (b * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y) • x +
      _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y := fun y ↦ by
    rw [selfDualLatticeSplit_proj_eq_sub_smul]
    abel
  have hfix : ∀ y, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y = 0 →
      _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y = y := fun y hy ↦ by
    rw [selfDualLatticeSplit_proj_eq_sub_smul, hy, mul_zero, zero_smul, sub_zero]
  refine ⟨le_antisymm (fun y hy ↦ ?_) (sup_le ?_ (fun y hy ↦ ((hperp y).1 hy).2)), ?_, ?_, ?_⟩
  · rw [hdecomp y]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hprojL y hy))
    exact Submodule.smul_mem _ (⟨_, mul_mem hbO (hxy y hy)⟩ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v)
      (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx
  · have heq : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x =
        L.map ((_root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b).restrictScalars
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v)) := by
      ext y
      constructor
      · intro hy
        exact ⟨y, ((hperp y).1 hy).2, hfix y ((hperp y).1 hy).1⟩
      · rintro ⟨z, hz, rfl⟩
        exact hprojL z hz
    rw [heq]
    exact hFG.map _
  · refine le_antisymm (Submodule.span_le.2 fun y hy ↦ ((hperp y).1 hy).1) (fun y hy ↦ ?_)
    have hy' : _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y ∈
        Submodule.span (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
          (_root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b '' (L : Set _)) := by
      rw [← Submodule.map_span, hspan]
      exact ⟨y, trivial, rfl⟩
    rw [hfix y hy] at hy'
    refine Submodule.span_mono ?_ hy'
    rintro _ ⟨z, hz, rfl⟩
    exact hprojL z hz
  · intro y
    constructor
    · intro hy
      exact ⟨((hperp y).1 hy).1, fun z hz ↦ ((hdual y).1 ((hperp y).1 hy).2).2 z ((hperp z).1 hz).2⟩
    · rintro ⟨hy0, hz⟩
      refine (hperp y).2 ⟨hy0, (hdual y).2 ⟨trivial, fun z hzL ↦ ?_⟩⟩
      have hy0' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y = 0 := hy0
      rw [hdecomp z, form_smul_add_left_lemma_3, hy0', mul_zero, zero_add]
      exact hz _ (hprojL z hzL)
end _root_.GlobalTheory.SelfDualLatticeSplit
end GlobalTheory.SelfDualLatticeSplit
