-- Prove2me | solution 1 for GlobalTheory.RowVal.valOf_eq_hRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:05:41.743364+00:00
-- url     : https://prove2.me/submissions/69ad0661-9b20-48db-83d6-caf9a09bd5fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdmissibleRowsValueEqRowGauge
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_exp
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_mul
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_prod
import Theorems.Thm_GlobalTheory_RowValueCheck_agree_rowCopy
import Theorems.Thm_GlobalTheory_RowValueCheck_valOf_eq
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mul
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowVal
open GlobalTheory.RowValueCheck
namespace GlobalTheory.RowVal
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  intro C _ V d _ I _ κ _ X H N P kind hk gr
  classical
  rw [valOf_eq]
  set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS
  have key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf (X.rowData H).hL (kind ρ)) X.hRow := by
    intro ρ μ hμ
    rcases hr : kind ρ with _ | ⟨g, a, a'⟩
    · obtain ⟨g, hg⟩ := hk.2 ρ hr
      have h1 : ∀ w, μ w ≠ 0 → w.1 = g := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hg ν hν w hν'
      show (0 : C) = _
      refine (H.axes μ ?_).symm
      have hg2 : g = 0 ∨ g = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g
      rcases hg2 with rfl | rfl
      · exact Or.inl fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
      · exact Or.inr fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
    · obtain ⟨-, -, hl⟩ := hk.1 ρ g a a' hr
      have h1 : ∀ w, μ w ≠ 0 → X.OnLf g a a' w := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hl ν hν w hν'
      exact if_pos fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
  have hA := Agree.prod (S := S) Finset.univ (fun ρ =>
    Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl)
      (agree_rowCopy S ρ _ _ (key ρ)).exp)
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]
end GlobalTheory.RowVal
