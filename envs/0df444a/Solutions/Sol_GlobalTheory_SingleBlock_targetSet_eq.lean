-- Prove2me | solution 1 for GlobalTheory.SingleBlock.targetSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:18.021122+00:00
-- url     : https://prove2.me/submissions/c8ebf512-4395-455a-97cf-26926c54209b

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_le_range_of_le_GLint
import Theorems.Thm_GlobalTheory_SingleBlock_residue_eq_iff
import Theorems.Thm_GlobalTheory_SingleBlock_mem_blockPar_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)} (hP : P ≤ GLint 𝒪[F] r) :
    targetSet t 𝒪[F] (ϖ : F) P =
      (((blockPar t (residueImage P)).comap
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (IsLocalRing.residue 𝒪[F]))).map
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (𝒪[F]).subtype) :
          Subgroup (GL (Fin r ⊕ Fin t) F)) := by
  ext h
  constructor
  · rintro ⟨⟨h0, rfl⟩, ⟨p, hp, e1⟩, e2⟩
    obtain ⟨p0, rfl⟩ := le_range_of_le_GLint hP hp
    have hp0 : GeneralLinearGroup.map (n := Fin r) (IsLocalRing.residue 𝒪[F]) p0 ∈
        residueImage P := Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 hp)
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2
      ((mem_blockPar_iff _ _).2 ⟨⟨_, hp0, ?_⟩, ?_⟩))
    · ext i j
      exact (residue_eq_iff hϖ _ _).2 (e1 i j)
    · ext i j
      have := (residue_eq_iff hϖ (h0.val (Sum.inr i) (Sum.inl j)) 0).2
        (by rw [ZeroMemClass.coe_zero, sub_zero]; exact e2 i j)
      rw [map_zero] at this
      exact this
  · rintro ⟨h0, hh, rfl⟩
    obtain ⟨⟨pb, hpb, e1⟩, e2⟩ := (mem_blockPar_iff _ _).1 (Subgroup.mem_comap.1 hh)
    obtain ⟨p0, hp, rfl⟩ := Subgroup.mem_map.1 hpb
    refine ⟨⟨h0, rfl⟩, ⟨_, Subgroup.mem_comap.1 hp, fun i j => ?_⟩, fun i j => ?_⟩
    · exact (residue_eq_iff hϖ _ _).1 (congrFun (congrFun e1 i) j)
    · have := (residue_eq_iff hϖ ((h0 : Matrix _ _ 𝒪[F]) (Sum.inr i) (Sum.inl j)) 0).1
        (by rw [map_zero]; exact congrFun (congrFun e2 i) j)
      rw [ZeroMemClass.coe_zero, sub_zero] at this
      exact this
end GlobalTheory.SingleBlock
