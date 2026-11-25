-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.X_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:09:43.691388+00:00
-- url     : https://prove2.me/submissions/b47a9923-1181-44d9-9726-bdea4572d2e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (B : InvAlg K) (y : B.A) (hy : y ≠ 0) (h : ∀ z, Algebra.trace K.E B.A (y * z) = 0) (x : B.A) :
    ¬ (B.X x).Nonempty := by
  rintro ⟨L, hL⟩
  obtain ⟨⟨hfg, -⟩, -, hdual⟩ := hL
  have hmem : ∀ s : B.A, y * s ∈ L := fun s => (hdual _).2 fun z _ => by
    have h0 : B.herm x (y * s) z = 0 := by
      unfold InvAlg.herm
      rw [show x * (y * s) * B.σ z = y * (x * s * B.σ z) by ring]
      exact h _
    rw [h0]
    exact zero_mem _
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K.E hy
  have htop : (⊤ : Submodule K.O K.E) ≤ L.map ((φ : B.A →ₗ[K.E] K.E).restrictScalars K.O) := by
    intro e _
    refine Submodule.mem_map.2 ⟨y * algebraMap K.E B.A e, hmem _, ?_⟩
    rw [LinearMap.restrictScalars_apply, mul_comm, ← Algebra.smul_def, map_smul, hφ, smul_eq_mul, mul_one]
  have : Module.Finite K.O K.E := ⟨by rw [← top_le_iff.1 htop]; exact hfg.map _⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hp0 : algebraMap K.O K.E p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 hp.ne_zero
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.IsIntegral.isIntegral (R := K.O) (algebraMap K.O K.E p)⁻¹)
  apply hp.not_isUnit
  have hpr : p * r = 1 :=
    IsFractionRing.injective K.O K.E (by rw [map_mul, hr, map_one, mul_inv_cancel₀ hp0])
  exact ⟨⟨p, r, hpr, by rw [mul_comm, hpr]⟩, rfl⟩
end GlobalTheory.UnitLemma.LieEnd
