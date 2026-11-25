-- Prove2me | solution 1 for GlobalTheory.ChartCmp.JetDim.card_le_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:20.826007+00:00
-- url     : https://prove2.me/submissions/bed19697-e401-4232-8107-2709cfc1ca7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
import Theorems.Thm_GlobalTheory_ChartCmp_JetDim_tanAll_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JetDim
variable {V : Type} [CommRing V]
namespace GlobalTheory.ChartCmp.JetDim
theorem _root_.solution [Nontrivial V] {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ]
    (ψ : Jet V κ' 1 →ₐ[V] Jet V κ 1) (hψ : Function.Surjective ψ) : Fintype.card κ ≤ Fintype.card κ' := by
  let φ : MvPolynomial κ' V →ₐ[V] TrivSqZeroExt V (κ → V) :=
    ((tanAll κ).comp ψ).comp (Ideal.Quotient.mkₐ V _)
  let v : κ' → κ → V := fun j => (φ (MvPolynomial.X j)).snd
  have hmem : ∀ p, (φ p).snd ∈ Submodule.span V (Set.range v) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.algHom_C, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      exact zero_mem _
    | add p q hp hq =>
      rw [map_add, TrivSqZeroExt.snd_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) (Submodule.smul_mem _ _ hp)
  have htop : Submodule.span V (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun V κ).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := hψ (Ideal.Quotient.mk _ (MvPolynomial.X i))
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : (φ p).snd = Pi.basisFun V κ i := by
      show (tanAll κ (ψ (Ideal.Quotient.mk _ p))).snd = _
      rw [ha, tanAll_X, TrivSqZeroExt.snd_inr, Pi.basisFun_apply]
    rw [← this]
    exact hmem p
  have h := finrank_range_le_card (R := V) v
  rw [Set.finrank, htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  exact h
end GlobalTheory.ChartCmp.JetDim
