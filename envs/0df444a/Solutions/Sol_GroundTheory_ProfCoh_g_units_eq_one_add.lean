-- Prove2me | solution 1 for GroundTheory.ProfCoh.g_units_eq_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:34.857305+00:00
-- url     : https://prove2.me/submissions/5a444254-36cd-429a-85b2-08c50efd4306

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_uliftInt
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_uliftInt
import Theorems.Thm_GroundTheory_ProfCoh_ordHom_surjective
import Theorems.Thm_GroundTheory_ProfCoh_ordHom_exact
import Theorems.Thm_GroundTheory_ProfCoh_ordHom_smul
import Theorems.Thm_GroundTheory_ProfCoh_unitsIncl_toAdditive_smul
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_integerUnits
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_add
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_of_trivial_int
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
variable {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
namespace GroundTheory.ProfCoh
theorem _root_.solution [Finite (ModN (Additive 𝒪[F]ˣ) l)] :
    d.g (Additive Fˣ) = d.one + d.g (Additive 𝒪[F]ˣ) := by
  let := trivialIntAction.{u} (F ≃ₐ[E] F)
  have := finite_torsN_integerUnits (F := F) l
  have := finite_modN_uliftInt.{u} l
  have := finite_torsN_uliftInt.{u} l
  have hinj : Function.Injective (unitsIncl F).toAdditive :=
    fun _ _ h ↦ Additive.toMul.injective (unitsIncl_injective (Additive.ofMul.injective h))
  rw [d.g_add (unitsIncl F).toAdditive (ordHom F) unitsIncl_toAdditive_smul
      (fun σ x ↦ ordHom_smul σ x) hinj ordHom_exact ordHom_surjective,
    d.g_of_trivial_int (ULift.{u} ℤ) (fun _ _ ↦ rfl) AddEquiv.ulift, add_comm]
end GroundTheory.ProfCoh
