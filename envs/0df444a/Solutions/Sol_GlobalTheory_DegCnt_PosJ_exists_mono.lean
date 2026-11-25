-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.exists_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:39.872795+00:00
-- url     : https://prove2.me/submissions/7d465ee8-8a4f-4e2a-bc13-1e2921cba398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_BlockStab_exists_monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
variable (N : NF H r)
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution : ∃ (σ : Fin N.j → Fin N.j) (β : Fin N.j → ℕ) (c : Fin N.j → K),
    (∀ a, σ (σ a) = a) ∧ (∀ a b, a ≤ b → β a ≤ β b) ∧ (∀ a b, β a = β b → a < b → σ b < σ a) ∧
    (∀ a b : Fin N.j, sameBlock N.w.blocks a b = true → β a = β b) ∧ (∀ a, c a ≠ 0) ∧
    ∀ a b, H.B (ej N.F N.j_le a) (ej N.F' N.j_le b) = if b = σ a then c a else 0 := by
  obtain ⟨σ, β, t, h⟩ := BlockStab.exists_monomial N.w.blocks
  rw [N.w.size] at h
  let σ' : Fin N.j → Fin N.j := fun a => ⟨σ a, (h a a.2).1⟩
  refine ⟨σ', fun a => β a, fun a => (t (β a) : K) * ((N.sgn (σ' a) : ℤ) : K),
    fun a => Fin.ext (h a a.2).2.1, fun a b hab => ((h a a.2).2.2.2 b b.2).2.1 hab, fun a b hab hl => ?_,
    fun a b hab => ((h a a.2).2.2.2 b b.2).1.1 hab, fun a => ?_, fun a b => ?_⟩
  · have h1 := ((h a a.2).2.2.2 b b.2).2.2.1 hab
    have h2 : (a : ℕ) < b := hl
    show σ b < σ a
    omega
  · rcases Int.units_eq_one_or (N.sgn (σ' a)) with h | h <;> simp [h]
  · rw [ej, ej, N.pair, Pt.mat, ((h a a.2).2.2.2 b b.2).2.2.2]
    by_cases h2 : b = σ' a
    · subst h2; simp [σ']
    · have h3 : ¬ (b : ℕ) = σ a := fun h => h2 (Fin.ext h)
      simp [h2, h3]
end GlobalTheory.DegCnt.PosJ
