-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:38.850333+00:00
-- url     : https://prove2.me/submissions/b37f43c7-40f1-437f-bd10-c252aff59975

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_solve_alg
import Theorems.Thm_GlobalTheory_Cyc_TateS_est

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {ζ : PadicComplex l} (hζ : IsPrimitiveRoot ζ l)
    {x : PadicComplex l} (hx : x ∈ Xj K j) : ∃ y ∈ Xj K j, act g y - y = (ζ - 1) * x := by
  have hp : l.Prime := Fact.out
  have hζ1 : 0 < ‖ζ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 (hζ.ne_one hp.one_lt))
  have hcl : IsClosed (Xj K j : Set (PadicComplex l)) := AddSubgroup.isClosed_topologicalClosure _
  haveI : CompleteSpace ↥(Xj K j) := hcl.completeSpace_coe
  let f : ↥(Xj K j) → PadicComplex l := fun y => act g y - y
  have hanti : AntilipschitzWith (Real.toNNReal (l / ‖ζ - 1‖)) f := by
    refine AntilipschitzWith.of_le_mul_dist fun a b => ?_
    have h := est hact hχ K hj hg hζ (sub_mem a.2 b.2)
    rw [Real.coe_toNNReal _ (by positivity), Subtype.dist_eq, dist_eq_norm, dist_eq_norm,
      div_mul_eq_mul_div, le_div_iff₀ hζ1, mul_comm]
    have e : f a - f b = act g ((a : PadicComplex l) - b) - ((a : PadicComplex l) - b) := by
      simp only [f, map_sub]
      ring
    rw [e]
    exact h
  have huc : UniformContinuous f :=
    ((AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).uniformContinuous.comp
      uniformContinuous_subtype_val).sub uniformContinuous_subtype_val
  have hr := (hanti.isClosed_range huc).preimage (continuous_const_mul (ζ - 1))
  have hsub : (Xalg K j : Set (PadicComplex l)) ⊆ (fun b => (ζ - 1) * b) ⁻¹' Set.range f := by
    intro d hd
    obtain ⟨y, hy, -, h⟩ := solve_alg hact hχ K hj hg hζ hd
    exact ⟨⟨y, hy⟩, h⟩
  obtain ⟨y, hy⟩ := closure_minimal hsub hr hx
  exact ⟨y, y.2, hy⟩
end GlobalTheory.Cyc.TateS
