-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.exists_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:22.68069+00:00
-- url     : https://prove2.me/submissions/12d48aaa-a363-49c5-9423-e7c387809172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hs : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) {S : Set V}
    (hS : S.Finite) : ∃ (d : ℕ) (b : Fin d → V), (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ v ∈ S, ∃ c : Fin d → ℂ, v = ∑ i, c i • b i := by
  letI : InnerProductSpace.Core ℂ V := core B hs hp
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  haveI : FiniteDimensional ℂ (Submodule.span ℂ S) := FiniteDimensional.span_of_finite ℂ hS
  let b := stdOrthonormalBasis ℂ (Submodule.span ℂ S)
  refine ⟨_, fun i => b i, fun i j => ?_, fun v hv => ⟨b.repr ⟨v, Submodule.subset_span hv⟩, ?_⟩⟩
  · exact (orthonormal_iff_ite.1 b.orthonormal j i).trans (by simp only [eq_comm])
  · simpa using (congrArg Subtype.val (b.sum_repr ⟨v, Submodule.subset_span hv⟩)).symm
end GlobalTheory.SmGL.UnitInd
