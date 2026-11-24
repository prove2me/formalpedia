-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ResDeg.card_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:28.958207+00:00
-- url     : https://prove2.me/submissions/d19ac4bd-9afc-47b4-8cc2-a412eb8275e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
import Theorems.Thm_GlobalTheory_UnitLemma_ResDeg_odd_of_involution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ResDeg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing
variable {K : UQ}
namespace GlobalTheory.UnitLemma.ResDeg
theorem _root_.solution (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) :
    ∃ d : ℕ, Odd d ∧
      Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) := by
  classical
  haveI := hl
  haveI : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
    Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  haveI : Finite (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) :=
    Module.finite_of_finite (ResidueField K.O)
  letI : Fintype (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) := Fintype.ofFinite _
  set τ := ResidueField.mapEquiv (sigmaAdj B hu hi)
  have hτ : ∀ z, τ (τ z) = z := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    simp only [τ, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (B.σ_σ r)
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  refine ⟨Module.finrank (ResidueField K.O) (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))),
    odd_of_involution (algebraMap (ResidueField K.O) _) K.q _ ?_ ?_ τ hτ (residue K.O x) (residue K.O y) ?_ ?_, ?_⟩
  · rw [← K.card_res, Nat.card_eq_fintype_card]
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]
  · show ResidueField.map _ (residue _ (algebraMap K.O _ x)) = residue _ (algebraMap K.O _ y)
    rw [ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hxy, ← IsScalarTower.algebraMap_apply]
  · intro h
    exact hne (Ideal.Quotient.eq.1 h)
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]
end GlobalTheory.UnitLemma.ResDeg
