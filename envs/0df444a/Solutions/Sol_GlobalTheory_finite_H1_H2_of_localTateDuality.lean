-- Prove2me | solution 1 for GlobalTheory.finite_H1_H2_of_localTateDuality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:42.897922+00:00
-- url     : https://prove2.me/submissions/24fd4e1d-eea3-428a-9c31-fe52535a3ca3

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmodStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteH1H2Local
import Theorems.Thm_GlobalTheory_T_finite_of_bijective_pairing_zmod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.GaloisCohomology ReciprocityTheory.Gal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hC, -, h11, h11f, h20⟩ := hT l K hK r M rho hr hrho
  obtain ⟨e⟩ := hC
  haveI hCfin : Finite (H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  have hAB := GlobalTheory.T.finite_of_bijective_pairing_zmod (l ^ r) _ _ _ _ ⟨e⟩ h11 h11f
  refine ⟨hAB.2, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K)))) :=
    Subtype.finite
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  exact Finite.of_injective _ h20.1
end GlobalTheory
