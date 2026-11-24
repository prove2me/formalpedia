-- Prove2me | solution 1 for GlobalTheory.DenseBasis.existsUnique_section_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:23.831776+00:00
-- url     : https://prove2.me/submissions/b8f36237-7006-43e9-b998-801484b3ccf8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfDense
import Theorems.Thm_GlobalTheory_DenseBasis_isOpenImmersion_section
import Theorems.Thm_GlobalTheory_DenseBasis_comp_section_eq_iff
import Theorems.Thm_GlobalTheory_DenseBasis_exists_lift

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseBasis
variable {Z S : Scheme.{0}}
namespace GlobalTheory.DenseBasis
theorem _root_.solution (p : Z ⟶ S) [IsFinite p] [Etale p] {I : Type} [Finite I]
    (σ : I → (S ⟶ Z)) (hσ : ∀ i, σ i ≫ p = 𝟙 S) (D : Set S) (hD : Dense D)
    (h : ∀ t ∈ D, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (.of K) ⟶ S),
      t ∈ Set.range x ∧ ∀ y : Spec (.of K) ⟶ Z, y ≫ p = x → ∃! i, x ≫ σ i = y)
    (K : Type) [Field K] (x : Spec (.of K) ⟶ S) (y : Spec (.of K) ⟶ Z) (hy : y ≫ p = x) :
    ∃! i, x ≫ σ i = y := by
  have hO : ∀ i, IsOpenImmersion (σ i) := fun i => isOpenImmersion_section p (σ i) (hσ i)
  have hCl : ∀ i, IsClosedImmersion (σ i) := fun i => by
    have : IsClosedImmersion (σ i ≫ p) := by rw [hσ i]; infer_instance
    exact IsClosedImmersion.of_comp (σ i) p
  have hp : ∀ i s, p (σ i s) = s := fun i s => by
    rw [← Scheme.Hom.comp_apply, hσ i]; rfl

  have hdisj : ∀ i j s s', σ i s = σ j s' → i = j := by
    intro i j s s' hss
    have hE : IsOpen ((σ i).base ⁻¹' Set.range (σ j)) :=
      (σ j).isOpenEmbedding.isOpen_range.preimage (σ i).continuous
    obtain ⟨t, htE, htD⟩ := hD.inter_open_nonempty _ hE ⟨s, s', hss.symm⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h t htD
    obtain ⟨t', ht'⟩ := htE
    have hsec : ((x' ≫ σ i) ≫ p) ≫ σ j = x' ≫ σ i := by
      rw [comp_section_eq_iff p (σ j) (hσ j)]
      exact ⟨t', by rw [Scheme.Hom.comp_apply, hw']; exact ht'⟩
    simp only [Category.assoc] at hsec
    rw [reassoc_of% (hσ i)] at hsec
    have hl : (x' ≫ σ i) ≫ p = x' := by rw [Category.assoc, hσ i, Category.comp_id]
    exact (hu _ hl).unique rfl hsec

  have hcov : ∀ z : Z, ∃ i, z ∈ Set.range (σ i) := by
    by_contra hne
    push Not at hne
    set C : Set Z := (⋃ i, Set.range (σ i))ᶜ with hCdef
    have hCo : IsOpen C :=
      (isClosed_iUnion_of_finite fun i => (σ i).isClosedEmbedding.isClosed_range).isOpen_compl
    obtain ⟨z₀, hz₀⟩ := hne
    have hz₀C : z₀ ∈ C := by simpa [hCdef] using hz₀
    obtain ⟨t, ⟨z, hzC, rfl⟩, htD⟩ :=
      hD.inter_open_nonempty _ (p.isOpenMap C hCo) ⟨p z₀, z₀, hz₀C, rfl⟩
    obtain ⟨K', _, _, x', ⟨w', hw'⟩, hu⟩ := h (p z) htD
    obtain ⟨y', hy'p, hy'w⟩ := exists_lift p x' w' z hw'.symm
    obtain ⟨i, hi, -⟩ := hu y' hy'p
    apply hzC
    rw [Set.mem_iUnion]
    exact ⟨i, x' w', by rw [← hy'w, ← hi, Scheme.Hom.comp_apply]⟩
  let w : Spec (.of K) := default
  obtain ⟨i, hi⟩ := hcov (y w)
  have hyi : (y ≫ p) ≫ σ i = y := (comp_section_eq_iff p (σ i) (hσ i) y w).2 hi
  rw [hy] at hyi
  refine ⟨i, hyi, fun j hj => ?_⟩
  obtain ⟨s, hs⟩ := hi
  refine hdisj j i (x w) s ?_
  rw [hs, ← hj, Scheme.Hom.comp_apply]
end GlobalTheory.DenseBasis
