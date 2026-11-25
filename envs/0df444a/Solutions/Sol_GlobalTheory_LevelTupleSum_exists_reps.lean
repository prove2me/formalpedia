-- Prove2me | solution 1 for GlobalTheory.LevelTupleSum.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:23.692393+00:00
-- url     : https://prove2.me/submissions/d5cecced-a157-40e6-8365-2b1f4e58ce72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelTupleSumEqRational
import Theorems.Thm_GlobalTheory_LevelTupleSum_Gen_of_sub
import Theorems.Thm_GlobalTheory_LevelTupleSum_exists_finite_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.LevelTupleSum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]
namespace GlobalTheory.LevelTupleSum
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ 𝒯 : Finset (Fin r → Fin r → E), (∀ t ∈ 𝒯, Gen Λ t) ∧
      ∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ Λ := by
  obtain ⟨S, hS, hres⟩ := exists_finite_res Λ hΛ
  let ρ : (Fin r → E) → (Fin r → E) := fun v => (Submodule.Quotient.mk (p := Λ) v).out
  have hρ : ∀ v, v - ρ v ∈ Λ := fun v => (Submodule.Quotient.eq Λ).1 (Submodule.Quotient.mk_out _).symm
  have hρe : ∀ v w, v - w ∈ Λ → ρ v = ρ w := fun v w h => by
    simp only [ρ, (Submodule.Quotient.eq Λ).2 h]
  have hfin : {t : Fin r → Fin r → E | Gen Λ t ∧ ∀ j, ρ (t j) = t j}.Finite := by
    refine (Set.Finite.pi' fun _ : Fin r => hS.image ρ).subset ?_
    rintro t ⟨hg, ht⟩ j
    obtain ⟨s, hs, h⟩ := hres _ (hg.1 j)
    exact ⟨s, hs, by rw [← hρe _ _ h, ht]⟩
  refine ⟨hfin.toFinset, fun t ht => (hfin.mem_toFinset.1 ht).1, fun t ht => ⟨fun j => ρ (t j),
    ⟨hfin.mem_toFinset.2 ⟨ht.of_sub fun j => hρ _, fun j => (hρe _ _ (hρ _)).symm⟩, fun j => hρ _⟩, ?_⟩⟩
  rintro t' ⟨h1, h2⟩
  funext j
  rw [hρe _ _ (h2 j), (hfin.mem_toFinset.1 h1).2 j]
end GlobalTheory.LevelTupleSum
