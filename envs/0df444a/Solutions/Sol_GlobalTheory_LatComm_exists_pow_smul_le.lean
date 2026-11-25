-- Prove2me | solution 1 for GlobalTheory.LatComm.exists_pow_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:30:48.404815+00:00
-- url     : https://prove2.me/submissions/64a25d72-2e8e-4201-83a9-485ec5314615

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitia
import Theorems.Thm_GlobalTheory_LatComm_exists_pow_smul_mem

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
open GlobalTheory GlobalTheory.LatComm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.LatComm
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (hΛ' : Λ'.FG) :
    ∃ j : ℕ, ∀ v ∈ Λ', p ^ j • v ∈ Λ := by
  obtain ⟨s, rfl⟩ := hΛ'
  choose f hf using exists_pow_smul_mem L hϖ p hp hΛ
  refine ⟨s.sup f, fun v hv => ?_⟩
  have : Submodule.span L.O (s : Set (Fin n → E)) ≤
      Λ.comap (LinearMap.lsmul L.O (Fin n → E) (p ^ s.sup f)) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hx)
    show p ^ s.sup f • x ∈ Λ
    rw [hk, pow_add, mul_smul]
    exact Λ.smul_mem _ (hf x)
  exact this hv
end GlobalTheory.LatComm
