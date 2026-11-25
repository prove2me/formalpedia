-- Prove2me | solution 1 for GlobalTheory.HL.GlobalOrbits.smul_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:40.449776+00:00
-- url     : https://prove2.me/submissions/b5bf2a3f-131a-4330-9b56-f627705ba7eb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUniqueGlobalLatticeOfLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStabStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalHermitianFramesTermsOrbitsLocal
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlobalOrbits
namespace GlobalTheory.HL.GlobalOrbits
theorem _root_.solution {F' E' : Type} [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [CommRing E']
    [Algebra F' E'] [TopologicalSpace E'] (L : LocE F' E') {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E')
    (Λ : Submodule L.O (Fin n → E')) (hΛ : IsSD L Hm Λ) (u : (Fin n → E') ≃ₗ[E'] (Fin n → E'))
    (hu : u ∈ isomG L Hm) (hle : ∀ x ∈ Λ, u x ∈ Λ) : u • Λ = Λ := by
  have hu' : ∀ x y, hf L Hm (u x) (u y) = hf L Hm x y := hu
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    exact hle x hx
  · intro hy
    have h1 : u.symm y ∈ Λ := by
      refine (hΛ.2 _).1 fun x hx => ?_
      have := hu' x (u.symm y)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact (hΛ.2 y).2 hy (u x) (hle x hx)
    have h2 : y = u • u.symm y := by simp
    rw [h2]
    exact Submodule.smul_mem_pointwise_smul _ _ _ h1
end GlobalTheory.HL.GlobalOrbits
