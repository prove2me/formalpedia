-- Prove2me | solution 1 for GlobalTheory.CompleteJoin.exists_normal_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:23.643546+00:00
-- url     : https://prove2.me/submissions/fa2fa343-89e5-467b-8ea4-0c8c77aa5f7e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedCharStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompleteNormalSubringJoin
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.CompleteJoin
variable {C : Type} [NormedField C] [IsUltrametricDist C]
omit [IsUltrametricDist C]
namespace GlobalTheory.CompleteJoin
theorem _root_.solution (S : Subring C)
    (h : Module.Finite S (integralClosure S (FractionRing S))) :
    ∃ (S' : Subring C) (ψ : S →+* S'), ψ.Finite ∧ (∀ a, (ψ a : C) = a) ∧ IsIntegrallyClosed S' := by
  let j : FractionRing S →ₐ[S] C :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId S C) Subtype.val_injective
  let e := (integralClosure S (FractionRing S)).equivMapOfInjective j j.injective
  haveI : IsFractionRing (integralClosure S (FractionRing S)) (FractionRing S) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing S) (FractionRing S)
  haveI : IsIntegrallyClosed (integralClosure S (FractionRing S)) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S)).2 inferInstance
  exact ⟨((integralClosure S (FractionRing S)).map j).toSubring,
    algebraMap S ((integralClosure S (FractionRing S)).map j),
    (RingHom.finite_algebraMap (B := (integralClosure S (FractionRing S)).map j)).2
      (Module.Finite.equiv e.toLinearEquiv), fun _ => rfl,
    IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
end GlobalTheory.CompleteJoin
