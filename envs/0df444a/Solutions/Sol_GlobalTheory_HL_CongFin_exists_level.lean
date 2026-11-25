-- Prove2me | solution 1 for GlobalTheory.HL.CongFin.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:32:01.446415+00:00
-- url     : https://prove2.me/submissions/6cf89c1a-39c6-4d3a-b93a-de6c09eb4f1c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Theorems.Thm_GlobalTheory_HL_CongFin_exists_pow_smul_mem
import Theorems.Thm_GlobalTheory_PowSmulMem_exists_pow_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CongFin
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}
namespace GlobalTheory.HL.CongFin
theorem _root_.solution {p : E} (hp : p ∈ O) (hu : IsUnit p) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ Λ' : Submodule O V) (hΛ : Λ.FG) (hs : Submodule.span E (Λ : Set V) = ⊤)
    (hΛ' : Λ'.FG) (hs' : Submodule.span E (Λ' : Set V) = ⊤) (N : ℕ) :
    ∃ N' : ℕ, ∀ g : V ≃ₗ[E] V, (∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p ^ N' • w) →
      ∀ v ∈ Λ', ∃ w ∈ Λ', g v - v = p ^ N • w := by
  obtain ⟨a, ha⟩ := exists_pow_smul_mem hp hdiv Λ Λ' hΛ hs'
  obtain ⟨b, hb⟩ := exists_pow_smul_mem hp hdiv Λ' Λ hΛ' hs
  refine ⟨b + (N + a), fun g hg v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := hg _ (hb v hv)
  refine ⟨p ^ a • w, ha w hw, ?_⟩
  rw [map_smul, ← smul_sub, pow_add, mul_smul, pow_add, mul_smul] at e
  exact (hu.pow b).smul_left_cancel.1 e
end GlobalTheory.HL.CongFin
