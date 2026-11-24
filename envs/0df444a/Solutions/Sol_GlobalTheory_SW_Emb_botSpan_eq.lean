-- Prove2me | solution 1 for GlobalTheory.SW.Emb.botSpan_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:37.103134+00:00
-- url     : https://prove2.me/submissions/2c80036e-2992-44c5-a1f5-c6f9bc887767

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_TransComp_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Emb
theorem _root_.solution (h : M2 E (N + 1)) (h0 : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1)
    (h1 : ∀ a, h (Sum.inr a) (Sum.inl 0) = 0) :
    botSpan h = (E ∙ Pi.single (Sum.inr 0) 1) ⊔
      (botSpan (h.submatrix (up N) (up N))).map (extV E N) := by
  have key : ∀ b : Fin N, extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) =
      h (Sum.inr b.succ) - h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 := by
    intro b
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp [extV, h1, Pi.single_apply]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    show h (Sum.inr a) ∈ _
    induction a using Fin.cases with
    | zero => rw [h0]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    | succ b =>
      have e : h (Sum.inr b.succ) = h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 +
          extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) := by rw [key]; abel
      rw [e]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, rfl⟩)))
  · refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, ← h0]
      exact Submodule.subset_span ⟨0, rfl⟩
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, rfl⟩
      show extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) ∈ botSpan h
      rw [key]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨b.succ, rfl⟩) (Submodule.smul_mem _ _ ?_)
      rw [← h0]
      exact Submodule.subset_span ⟨0, rfl⟩
end GlobalTheory.SW.Emb
