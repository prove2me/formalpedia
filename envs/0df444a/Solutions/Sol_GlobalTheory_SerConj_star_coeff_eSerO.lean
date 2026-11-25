-- Prove2me | solution 1 for GlobalTheory.SerConj.star_coeff_eSerO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:52:24.168908+00:00
-- url     : https://prove2.me/submissions/715ccc2d-6912-4141-b555-a8c3aad878e4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_GlobalTheory_SerConj_simple_bc
import Theorems.Thm_GlobalTheory_SerConj_normRev_normRev
import Theorems.Thm_GlobalTheory_SerConj_hasLabelO_conj
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_galoisConjCentralIdempotent
import Theorems.Thm_Formalism_L2_NT_IsTeich_map_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
namespace GlobalTheory.SerConj
theorem _root_.solution : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x,
      star ((Formalism.L2.NT.eSerO O r f).coeff x) =
        (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := by
  intro g _ Cv O hO r f hm h0 x
  classical
  let S : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) ≃+ MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
    MonoidAlgebra.mapAddEquiv _ (starRingAut : ℂ ≃+* ℂ).toAddEquiv
  have hS : ∀ z y, (S z).coeff y = star (z.coeff y) := fun z y => MonoidAlgebra.coeff_mapAddEquiv _ _ _
  have hSS : ∀ z, S (S z) = z := fun z => by
    ext y
    rw [hS, hS, star_star]
  have hz : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), zIdem (bc starRingAut τ) = S (zIdem τ) := fun τ => by
    ext y
    rw [hS]
    exact (galoisConjCentralIdempotent _ starRingAut τ y).symm
  rw [← hS]
  congr 2
  unfold Formalism.L2.NT.eSerO
  rw [S.map_finsum]
  refine finsum_eq_of_bijective S S.bijective fun z => ?_
  have hiff : (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) ↔
      ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = S z ∧
        HasLabelO O τ (C (f.coeff 0)⁻¹ * f.reverse) := by
    constructor
    · rintro ⟨τ, h1, h2, h3⟩
      exact ⟨_, simple_bc _ h1, by rw [hz, h2], hasLabelO_conj O hO h3⟩
    · rintro ⟨τ, h1, h2, h3⟩
      have h4 := hasLabelO_conj O hO h3
      rw [normRev_normRev hm h0] at h4
      exact ⟨_, simple_bc _ h1, by rw [hz, h2, hSS], h4⟩
  rw [finsum_eq_if, finsum_eq_if, ← hiff]
  split_ifs
  · rfl
  · exact map_zero S
end GlobalTheory.SerConj
