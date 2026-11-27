-- Prove2me | solution 1 for GlobalTheory.homology_of_free_complex_of_isFiniteLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:08.850095+00:00
-- url     : https://prove2.me/submissions/ec1eaf4d-f008-4aa0-921c-9d2eff75d2e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_of_isZero_left
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_length_ext_of_isFiniteLength
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_free
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_residue
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_acyclicityLemma_depth_differentialCokernels_finiteLength
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_length_ext_opcycles
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_length_ext_zero_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open FiniteLengthComplex
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g →
      ∀ C : CochainComplex (ModuleCat.{0} O) ℕ,
        (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, g < i → IsZero (C.X i)) →
        (∀ i, IsFiniteLength O (C.homology i)) →
        Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O]
          IsLocalRing.ResidueField O) →
        (∀ i, i ≠ g → IsZero (C.homology i)) ∧ Module.length O (C.homology g) = 1 := by
  intro O _ _ g hg C hF hZ hH ⟨e⟩
  have hk := subsingleton_ext_residue g hg
  have hlt : ∀ i < g, IsZero (C.homology i) := fun i hi =>
    (acyclicityLemma_depth_differentialCokernels_finiteLength C g (fun j n hn => by
      have := (hF j).1
      have := (hF j).2
      exact subsingleton_ext_free _ n (hk n hn.ne) _) hH i).2 hi
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hi with h | h
    · exact hlt i h
    · exact IsZero.of_mono (C.homologyι i) (IsZero.of_epi (C.pOpcycles i) (hZ i h))
  have hres : Module.length O (IsLocalRing.ResidueField O) = 1 := by
    have : IsSimpleModule O (IsLocalRing.ResidueField O) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal O, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have h0 := (length_ext_zero_quot C).trans (e.length_eq.trans hres)
  have h1 : Module.length O (Abelian.Ext.{0} (C.opcycles g) (ModuleCat.of O O) g) = 1 := by
    cases g with
    | zero =>
      rw [← h0]
      refine (Submodule.quotEquivOfEqBot _ ?_).length_eq.symm
      rw [LinearMap.range_eq_bot]
      ext x
      have := subsingleton_ext_of_isZero_left (hZ 1 one_pos) (ModuleCat.of O O) 0
      rw [Subsingleton.elim x 0]
      simp
    | succ j =>
      rw [length_ext_opcycles C _ (fun i => by
        have := (hF i).1
        infer_instance) j hlt, h0]
  have := C.isIso_homologyι g (g + 1) (by simp) ((hZ _ (by omega)).eq_zero_of_tgt _)
  rw [(extCongrLeft (asIso (C.homologyι g)) _ g).length_eq] at h1
  have h2 : 1 = Module.length O (C.homology g) * Module.length O (Abelian.Ext.{0}
      (ModuleCat.of O (O ⧸ maximalIdeal O)) (ModuleCat.of O O) g) :=
    h1.symm.trans (length_ext_of_isFiniteLength _ g hk _ (hH g))
  generalize Module.length O (C.homology g) = a at h2 ⊢
  generalize Module.length O (Abelian.Ext.{0} (ModuleCat.of O (O ⧸ maximalIdeal O))
    (ModuleCat.of O O) g) = b at h2
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h2
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h2
  refine le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr ha)
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * b := by gcongr; exact Order.one_le_iff_ne_zero.mpr hb
    _ = 1 := h2.symm
end GlobalTheory
