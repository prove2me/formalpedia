-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.unramFin_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:05:26.4788+00:00
-- url     : https://prove2.me/submissions/8d09226b-d2cc-4d4a-8b38-b5758f326fb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_sub_conj_notMem
import Theorems.Thm_GlobalTheory_CMVal_Model_zeta_prim
import Theorems.Thm_Formalism_L2_Pj_unramBridge_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
attribute [local instance] FractionRing.liftAlgebra
namespace GlobalTheory.CMVal.Model
theorem _root_.solution : UnramFin K := by
  have hu := Formalism.L2.Pj.unramBridge_holds K (fun P hP => ⟨_, sub_conj_notMem zeta_prim hP.ne_top⟩)
  have hsep : Algebra.IsSeparable (FractionRing (OF K)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have := hM.isPrime
  exact (not_dvd_differentIdeal_iff (A := OF K) (P := M)).2 inferInstance (Ideal.dvd_iff_le.2 hle)
end GlobalTheory.CMVal.Model
