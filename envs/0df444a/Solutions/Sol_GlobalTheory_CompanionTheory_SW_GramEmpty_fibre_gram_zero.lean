-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:37.990833+00:00
-- url     : https://prove2.me/submissions/e14c4c6e-3302-4822-b32f-983ff1368b15

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankZeroGramFiberMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramEmpty_fibre_eq_dirac_of_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.SW.GramEmpty
namespace GlobalTheory.CompanionTheory.SW.GramEmpty
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ d b lam _ m hm S
  obtain ⟨-, h2, -⟩ := hm
  haveI : Subsingleton (HermR R σ 0) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : IsEmpty {p : Fin 0 × Fin 0 // p.1 < p.2} := ⟨fun p => p.1.1.elim0⟩
  have hU : {X : Fin 0 → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = Set.univ := by
    ext X
    simp
  have hμ : coordW R b lam 0 M Set.univ = 1 := by
    unfold coordW
    rw [Measure.pi_of_empty]
    simp
  have hν : coordHerm R σ b lam 0 Set.univ = 1 := by
    unfold coordHerm
    rw [Measure.comap_apply _ (Function.injective_of_subsingleton _)
      (fun s _ => Subsingleton.measurableSet) _ MeasurableSet.univ]
    have : (Set.univ : Set ((Fin 0 → R) × ({p : Fin 0 × Fin 0 // p.1 < p.2} → R ⊗[F] E))) =
        Set.univ ×ˢ Set.univ := by simp
    rw [Set.image_univ_of_surjective, this, Measure.prod_prod, Measure.pi_of_empty, Measure.pi_of_empty]
    · simp
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  refine fibre_eq_dirac_of_unique _ _ m _ hμ hν (fun φ hφ => ?_) S
  have := h2 φ hφ
  rw [hU, Measure.restrict_univ] at this
  exact this
end GlobalTheory.CompanionTheory.SW.GramEmpty
