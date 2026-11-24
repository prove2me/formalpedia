-- Prove2me | solution 1 for GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:38.546863+00:00
-- url     : https://prove2.me/submissions/aaeff0c8-efea-4eb7-b826-d4c1520157d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinatesDifferentials
import Theorems.Thm_GlobalTheory_EtaleCoordJacobian_exists_basis_of_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory GlobalTheory.EtaleCoordRank
open KaehlerDifferential TensorProduct
namespace GlobalTheory.EtaleCoordRank
theorem _root_.solution : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  intro R B K _ _ _ _ _ d t h
  have key : ∃ b : Module.Basis (Fin d) B Ω[B⁄R], ∀ i, b i = D R B (t i) := by
    letI : Algebra (MvPolynomial (Fin d) R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin d) R) B :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R B r = MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.C r)
        simp
    haveI : Algebra.Etale (MvPolynomial (Fin d) R) B := h
    obtain ⟨⟨b, hb⟩, _⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B (Fin d)
    refine ⟨b, fun i => ?_⟩
    rw [hb]
    congr 1
    change MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.X i) = t i
    simp
  obtain ⟨b, hb⟩ := key
  let b' : Module.Basis (Fin d) K (K ⊗[B] Ω[B⁄R]) := b.baseChange K
  refine ⟨by rw [Module.finrank_eq_card_basis b', Fintype.card_fin], ?_⟩
  intro ι e u ht
  have hli : LinearIndependent K (fun i => b' (e i)) := b'.linearIndependent.comp e e.injective
  have hfun : (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) =
      (fun i => Units.map (algebraMap B K : B →* K) (u i)) • (fun i => b' (e i)) := by
    funext i
    simp only [Pi.smul_apply', Units.smul_def, Units.coe_map, MonoidHom.coe_coe, b',
      Module.Basis.baseChange_apply, hb]
    rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, ← algebraMap_smul K (u i : B),
      ← algebraMap_smul K (t (e i)), ht, zero_smul, add_zero]
  rw [hfun]
  exact hli.units_smul _
end GlobalTheory.EtaleCoordRank
