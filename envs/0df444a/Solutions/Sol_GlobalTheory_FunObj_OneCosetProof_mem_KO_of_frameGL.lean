-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.mem_KO_of_frameGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:48:27.241572+00:00
-- url     : https://prove2.me/submissions/fdfbb5e5-6985-45f8-aa52-5d2b8476d388

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution {a c b : ℕ} (h : a + c = b) {g : GL (Fin b) k} (hg : frameGL h g ∈ KO k _) :
    g ∈ KO k _ := by
  obtain ⟨y, hy⟩ := hg
  refine ⟨Units.map (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (frame h)).toMonoidHom y, ?_⟩
  ext i j
  have := congrArg (fun u : GL (Fin a ⊕ Fin c) k => u.val ((frame h).symm i) ((frame h).symm j)) hy
  simpa [frameGL, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply] using this
end GlobalTheory.FunObj.OneCosetProof
