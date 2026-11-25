-- Prove2me | solution 1 for GlobalTheory.SmoothForms.center_eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:50.448432+00:00
-- url     : https://prove2.me/submissions/3a6a51ad-d26c-492d-beb2-14395cf5eb29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracketStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Theorems.Thm_GlobalTheory_SmoothForms_gelf_adjoin_comm
import Theorems.Thm_GlobalTheory_SmoothForms_central_of_filt
import Theorems.Thm_GlobalTheory_SmoothForms_exists_filt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}
namespace GlobalTheory.SmoothForms
theorem _root_.solution (hE : Formalism.REAL.GlRel E)
    (hgen : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) = ⊤) :
    Subalgebra.center ℂ A = Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  refine le_antisymm (fun z hz => ?_) fun c hc => ?_
  · obtain ⟨d, hd⟩ := exists_filt (E := E) (z := z) (hgen ▸ Algebra.mem_top)
    exact central_of_filt hE d z hd fun a b => Subalgebra.mem_center_iff.1 hz _
  · refine Subalgebra.mem_center_iff.2 fun b => ?_
    have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) ≤ Subalgebra.centralizer ℂ {c} := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩ _ rfl
      exact (gelf_adjoin_comm hE hc p.1 p.2).symm
    exact (this (hgen ▸ Algebra.mem_top : b ∈ _) _ rfl).symm
end GlobalTheory.SmoothForms
