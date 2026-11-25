-- Prove2me | solution 1 for GlobalTheory.SingleBlock.comap_congSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:17.160954+00:00
-- url     : https://prove2.me/submissions/07478601-bca2-414a-84e8-9dd13e3f802f

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_unif_ne_zero
import Theorems.Thm_GlobalTheory_SingleBlock_residue_eq_iff
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_one_coe
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : Irreducible ϖ) :
    (congSub 𝒪[F] (ϖ : F) r).comap (GeneralLinearGroup.map (n := Fin r) (𝒪[F]).subtype) =
      (GeneralLinearGroup.map (n := Fin r) (IsLocalRing.residue 𝒪[F])).ker := by
  ext g
  have key : ∀ i j, IsLocalRing.residue 𝒪[F] ((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j) =
      (1 : Matrix (Fin r) (Fin r) 𝓀[F]) i j ↔
      (ϖ : F)⁻¹ * ((((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j : 𝒪[F]) : F) -
        (1 : Matrix (Fin r) (Fin r) F) i j) ∈ 𝒪[F] := by
    intro i j
    have e : (1 : Matrix (Fin r) (Fin r) 𝓀[F]) i j =
        IsLocalRing.residue 𝒪[F] ((1 : Matrix (Fin r) (Fin r) 𝒪[F]) i j) := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [e, residue_eq_iff hϖ, GLRed.one_coe]
    constructor
    · rintro ⟨o, ho, e⟩
      rwa [e, inv_mul_cancel_left₀ (unif_ne_zero hϖ)]
    · intro h
      exact ⟨_, h, by rw [mul_inv_cancel_left₀ (unif_ne_zero hϖ)]⟩
  rw [Subgroup.mem_comap, MonoidHom.mem_ker]
  constructor
  · intro h
    exact Units.ext (Matrix.ext fun i j => (key i j).2 (h.2 i j))
  · intro h
    refine ⟨⟨fun i j => ((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2, fun i j => ?_⟩,
      fun i j => (key i j).1 ?_⟩
    · rw [← map_inv]
      exact (((g⁻¹ : GL (Fin r) 𝒪[F]) : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2
    · exact congrArg (fun x : GL (Fin r) 𝓀[F] => (x : Matrix (Fin r) (Fin r) 𝓀[F]) i j) h
end GlobalTheory.SingleBlock
