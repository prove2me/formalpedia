-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.card_hyp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:39.883454+00:00
-- url     : https://prove2.me/submissions/cf97e483-b01b-40ef-bcea-3ae28b45afeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_card_proj_mem
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_smul_mem
import Theorems.Thm_GlobalTheory_SW_Hyper_surj_of_ne
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
theorem _root_.solution (P : Ideal O) [hP : P.IsMaximal] [Finite (M →ₗ[O] O ⧸ P)]
    (K : Submodule (O ⧸ P) (M →ₗ[O] O ⧸ P)) (U : Submodule O M)
    (hK : ∀ f, f ∈ K ↔ U ≤ LinearMap.ker f) :
    {N ∈ Hyp P M | U ≤ N}.ncard * (Nat.card (O ⧸ P) - 1) + 1 = Nat.card K := by
  rw [← card_proj_mem _ _ K]
  congr 2
  symm
  refine Nat.card_eq_of_bijective
    (fun p => ⟨LinearMap.ker p.1.rep, ⟨_, p.1.rep_nonzero, rfl⟩, (hK _).1 p.2⟩) ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    have h : LinearMap.ker p.rep = LinearMap.ker p'.rep := congrArg Subtype.val h
    refine Subtype.ext ?_
    change p = p'
    rw [← p.mk_rep, ← p'.mk_rep, Projectivization.mk_eq_mk_iff']
    obtain ⟨v, hv⟩ := Hyper.surj_of_ne P _ p'.rep_nonzero
    refine ⟨p.rep v, LinearMap.ext fun x => ?_⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (p'.rep x)
    have h1 : x - c • v ∈ LinearMap.ker p'.rep := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hv, ← hc, Algebra.smul_def, mul_one]
      exact sub_self _
    rw [← h, LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h1
    rw [h1, LinearMap.smul_apply, ← hc, Algebra.smul_def c, smul_eq_mul, mul_comm]; rfl
  · rintro ⟨_, ⟨f, hf, rfl⟩, hU⟩
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (O ⧸ P) f hf
    refine ⟨⟨Projectivization.mk _ f hf, ha ▸ K.smul_mem (a : O ⧸ P) ((hK f).2 hU)⟩, Subtype.ext ?_⟩
    ext x
    simp only [← ha, LinearMap.mem_ker]
    simp [Units.smul_def]
end GlobalTheory.SW.HeckeId
