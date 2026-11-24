-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.red_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:22:07.863952+00:00
-- url     : https://prove2.me/submissions/17e3c19d-85a3-496c-9877-940d5ca48ba3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DiagVol.RowIdx
theorem _root_.solution (x : KO k ι) (r s : ι) (h : x.1.val r s ∈ 𝒪[k]) :
    (red x).val r s = IsLocalRing.residue 𝒪[k] ⟨x.1.val r s, h⟩ := by
  set u := (MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).symm x with hu
  have h1 : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u = x.1 := by
    have := congrArg Subtype.val ((MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).apply_symm_apply x)
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  have h2' : ((u.val r s : 𝒪[k]) : k) = x.1.val r s := by rw [← h1]; rfl
  have h2 : u.val r s = ⟨x.1.val r s, h⟩ := Subtype.ext h2'
  show IsLocalRing.residue 𝒪[k] (u.val r s) = _
  rw [h2]
end GlobalTheory.DiagVol.RowIdx
