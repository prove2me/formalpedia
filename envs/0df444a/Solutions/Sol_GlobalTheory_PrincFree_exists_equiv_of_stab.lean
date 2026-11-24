-- Prove2me | solution 1 for GlobalTheory.PrincFree.exists_equiv_of_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:32:50.465798+00:00
-- url     : https://prove2.me/submissions/e912af9d-0745-4cdb-a325-1b4f0f9a88f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalGroupActsFreelyOnFlags

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.PrincFree
namespace GlobalTheory.PrincFree
theorem _root_.solution {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    {r : ℕ} (φ : L →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ LinearMap.range φ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ LinearMap.range φ) :
    ∃ g : L ≃ₗ[𝓞 E] L, ∀ a, φ (g a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  choose f hf using fun a : L => (hγ (φ a)).1 (LinearMap.mem_range_self φ a)
  let g : L →ₗ[𝓞 E] L :=
    { toFun := f
      map_add' := fun a b => hφ (by rw [map_add, hf, hf, hf, map_add, Matrix.mulVec_add])
      map_smul' := fun c a => hφ (by
        rw [RingHom.id_apply, map_smul, hf, hf, map_smul, Matrix.mulVec_smul]) }
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective g ⟨fun a b hab => hφ ?_, fun b => ?_⟩, hf⟩
  · have h : f a = f b := hab
    rw [← hli (φ a), ← hli (φ b), ← hf, ← hf, h]
  · obtain ⟨a, ha⟩ := (hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ b)).2
      (by rw [hri]; exact LinearMap.mem_range_self φ b)
    exact ⟨a, hφ (by rw [← hri (φ b), ← ha]; exact hf a)⟩
end GlobalTheory.PrincFree
