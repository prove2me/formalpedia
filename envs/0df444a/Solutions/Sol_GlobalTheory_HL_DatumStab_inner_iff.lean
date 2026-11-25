-- Prove2me | solution 1 for GlobalTheory.HL.DatumStab.inner_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:05.314798+00:00
-- url     : https://prove2.me/submissions/e8cef170-de91-44a4-b5d9-60793f3fd437

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers
import Theorems.Thm_GlobalTheory_HL_DatumStab_mem_smul_iff
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.DatumStab
theorem _root_.solution (S : Frames L r k) {g : Fin (r + 1) → S.V} {A Λ₀ : Submodule L.O S.V} {n : S.GLV}
    (hn : n ∈ S.Nof g)
    (hA : ∀ x, x ∈ A ↔ ∃ y ∈ Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) (x : S.V) :
    x ∈ A ↔ ∃ y ∈ n • Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  rw [hA]
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, by simpa [mem_smul_iff] using hy, (h1 y).2 hp, ?_⟩
    have := Submodule.add_mem _ (h2 y hp) hx
    simpa using this
  · rintro ⟨y, hy, hp, hx⟩
    rw [mem_smul_iff] at hy
    have hp' : n.symm y ∈ perp L S.Hm (S.spanTo g r) := (h1 _).1 (by simpa using hp)
    refine ⟨_, hy, hp', ?_⟩
    have := Submodule.sub_mem _ hx (h2 _ hp')
    simpa using this
end GlobalTheory.HL.DatumStab
