-- Prove2me | solution 1 for GlobalTheory.exists_basicOpen_fibres_preirreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:27.195889+00:00
-- url     : https://prove2.me/submissions/be5b568c-ab45-47db-bfa7-1839d1489ef9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleFibreStandardEtaleSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleTensorLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmooth
import Theorems.Thm_GlobalTheory_T_preirreducible_fibre_standardEtale_spreads
import Theorems.Thm_GlobalTheory_T_preirreducible_tensor_localization_away
import Theorems.Thm_GlobalTheory_T_range_comap_includeRight_eq_comap_eq_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B →
    ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) →
    PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) →
    ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧
      (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧
      ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) →
        IsPreirreducible {r : PrimeSpectrum B |
          r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  intro A B _ _ _ hsm q Ω _ _ _ hq hΩ
  obtain ⟨b, hbq, n, _, hST, hSE⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q.asIdeal)
  have hΩb := GlobalTheory.T.preirreducible_tensor_localization_away A B b Ω hΩ
  obtain ⟨a, I, haΩ, hIΩ, hall⟩ := GlobalTheory.T.preirreducible_fibre_standardEtale_spreads A (Localization.Away b) n hSE Ω hΩb
  have memq : ∀ x : A, algebraMap A B x ∈ q.asIdeal ↔ algebraMap A Ω x = 0 := by
    intro x
    have := congrArg (x ∈ ·) hq
    simpa [Ideal.mem_comap, RingHom.mem_ker] using this
  refine ⟨b, a, I, hbq, fun h => haΩ ((memq a).1 h), fun c hc => (memq c).2 (hIΩ c hc), ?_⟩
  intro t hat hIt
  let k := AlgebraicClosure t.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap A k) = t.asIdeal := by
    rw [IsScalarTower.algebraMap_eq A t.asIdeal.ResidueField k, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap t.asIdeal.ResidueField k).injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  have hmem : ∀ x : A, algebraMap A k x = 0 ↔ x ∈ t.asIdeal := by
    intro x; rw [← RingHom.mem_ker, hker]
  have hk := hall k (fun h => hat ((hmem a).1 h)) (fun c hc => (hmem c).2 (hIt c hc))
  have himg := (PreirreducibleSpace.isPreirreducible_univ (X := PrimeSpectrum (k ⊗[A] Localization.Away b))).image
    (PrimeSpectrum.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away b →ₐ[A] k ⊗[A] Localization.Away b).toRingHom.comp
        (algebraMap B (Localization.Away b))))
    (PrimeSpectrum.continuous_comap _).continuousOn
  convert himg using 1
  rw [Set.image_univ, PrimeSpectrum.comap_comp, Set.range_comp,
    GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker, hker]
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hr, hbr⟩
    have : r ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]; exact hbr
    obtain ⟨r', rfl⟩ := this
    refine ⟨r', ?_, rfl⟩
    rw [← hr, IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
    rfl
  · rintro ⟨r', hr', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hr', IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
      rfl
    · have : PrimeSpectrum.comap (algebraMap B (Localization.Away b)) r' ∈
          Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨r', rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this
end GlobalTheory
