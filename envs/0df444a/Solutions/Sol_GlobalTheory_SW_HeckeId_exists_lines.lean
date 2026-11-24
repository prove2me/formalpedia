-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.exists_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:22.669797+00:00
-- url     : https://prove2.me/submissions/8315e82d-3eda-46a0-ad7a-181d5965593f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_card_proj_mem
import Theorems.Thm_GlobalTheory_SW_HeckeId_card_ker_dual
import Theorems.Thm_GlobalTheory_SW_HeckeId_card_hyp_le
import Theorems.Thm_GlobalTheory_SW_HeckeId_one_tmul_eq_zero
import Theorems.Thm_GlobalTheory_SW_Hyper_finrank_fibre
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
attribute [local instance] Ideal.Quotient.field
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] : ∃ (A : ℕ) (e : Fin A → M),
    A * (Nat.card (O ⧸ P) - 1) = Nat.card (O ⧸ P) ^ Module.finrank O M - 1 ∧
    (∀ i, e i ∉ (P • ⊤ : Submodule O M)) ∧
    ∀ (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L]
      (u : M →ₗ[O] L),
      (Nat.card {i // u (e i) ∈ (P • ⊤ : Submodule O L)} * (Nat.card (O ⧸ P) - 1) + 1) *
          Nat.card (O ⧸ P) ^ Module.finrank O L =
        ({N ∈ Hyp P L | LinearMap.range u ≤ N}.ncard * (Nat.card (O ⧸ P) - 1) + 1) *
          Nat.card (O ⧸ P) ^ Module.finrank O M := by
  have : Finite ((O ⧸ P) ⊗[O] M) := Module.finite_of_finite (O ⧸ P)
  have hs : ∀ v : (O ⧸ P) ⊗[O] M, ∃ x : M, (1 : O ⧸ P) ⊗ₜ[O] x = v :=
    TensorProduct.mk_surjective O M (O ⧸ P) Ideal.Quotient.mk_surjective
  choose l hl using hs
  let ε := Finite.equivFin (ℙ (O ⧸ P) ((O ⧸ P) ⊗[O] M))
  refine ⟨_, fun i => l (ε.symm i).rep, ?_, fun i => ?_, fun L _ _ _ _ u => ?_⟩
  · rw [← Projectivization.card, ← Hyper.finrank_fibre O M (O ⧸ P),
      Module.natCard_eq_pow_finrank (K := O ⧸ P)]
  · rw [← one_tmul_eq_zero, hl]
    exact Projectivization.rep_nonzero _
  · let e := LinearMap.liftBaseChangeEquiv (R := O) (M := L) (N := O ⧸ P) (O ⧸ P)
    have : Module.Finite (O ⧸ P) (L →ₗ[O] O ⧸ P) := Module.Finite.equiv e.symm
    have : Finite (L →ₗ[O] O ⧸ P) := Module.finite_of_finite (O ⧸ P)
    let g := u.baseChange (O ⧸ P)
    rw [card_hyp_le P ((LinearMap.ker g.dualMap).comap e.toLinearMap), ← Hyper.finrank_fibre O M (O ⧸ P),
      ← Hyper.finrank_fibre O L (O ⧸ P),
      Nat.card_congr (e.ofSubmodule' (LinearMap.ker g.dualMap)).toEquiv, ← card_ker_dual,
      ← card_proj_mem]
    · congr 3
      refine Nat.card_congr (ε.symm.subtypeEquiv fun i => ?_)
      rw [← one_tmul_eq_zero, LinearMap.mem_ker]
      conv_rhs => rw [← hl (ε.symm i).rep]
      rfl
    · intro f
      rw [LinearMap.range_le_ker_iff]
      change (e f) ∘ₗ g = 0 ↔ _
      constructor
      · intro h
        ext x
        simpa [e, g] using LinearMap.congr_fun h (1 ⊗ₜ x)
      · intro h
        refine LinearMap.ext fun v => ?_
        rw [← hl v]
        simpa [e, g] using LinearMap.congr_fun h (l v)
end GlobalTheory.SW.HeckeId
