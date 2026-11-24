-- Prove2me | solution 1 for GlobalTheory.QNorm.norm_form_mem_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:40.940077+00:00
-- url     : https://prove2.me/submissions/f925a917-9123-4c78-b77c-e3ae149d6452

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne
import Theorems.Thm_GlobalTheory_QNorm_NormOpen_eventually_isSquare_finite
import Theorems.Thm_GlobalTheory_QNorm_NormOpen_eventually_isSquare_infinite
import Theorems.Thm_GlobalTheory_QNorm_NormOpen_eventually_integral
import Theorems.Thm_GlobalTheory_QNorm_NormOpen_continuous_eval
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_exists_integral_sq_sub_mul_sq_of_unit
import Theorems.Thm_GlobalTheory_QNorm_finite_valuation_ne_one
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
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
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
open NumberField IsDedekindDomain
open scoped Topology
open GlobalTheory GlobalTheory.QNorm
open NormOpen
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → {a : (AdeleRing (𝓞 F) F)ˣ | ∃ x y : AdeleRing (𝓞 F) F, (a : AdeleRing (𝓞 F) F) = x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
  intro F _ _ δ hδ
  set S : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v.valuation F (2 : F) ≠ 1} ∪ {v | v.valuation F δ ≠ 1} with hS
  have hSfin : S.Finite := by
    have h2 := finite_valuation_ne_one F (Units.mk0 (2 : F) two_ne_zero)
    have hd := finite_valuation_ne_one F (Units.mk0 δ hδ)
    simp only [Units.val_mk0] at h2 hd
    exact h2.union hd
  set U : Set (AdeleRing (𝓞 F) F) := {b | (∀ w, IsSquare (b.1 w)) ∧
    ((∀ v, b.2 v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ S, IsSquare (b.2 v))} with hU_def
  have hU : U ∈ 𝓝 (1 : AdeleRing (𝓞 F) F) := by
    have h1 : ∀ᶠ b in 𝓝 (1 : InfiniteAdeleRing F), ∀ w, IsSquare (b w) := by
      have h : ∀ᶠ b in 𝓝 (1 : (w : InfinitePlace F) → w.Completion), ∀ w, IsSquare (b w) := by
        rw [nhds_pi]
        exact Filter.eventually_pi fun w => NormOpen.eventually_isSquare_infinite w
      exact h
    have h2 : ∀ᶠ b in 𝓝 (1 : FiniteAdeleRing (𝓞 F) F), ∀ v ∈ S, IsSquare (b v) := by
      refine (Filter.eventually_all_finite hSfin).2 fun v _ => ?_
      exact ((NormOpen.continuous_eval v).tendsto 1).eventually (NormOpen.eventually_isSquare_finite v)
    have h3 : ∀ᶠ z in 𝓝 ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)),
        (∀ w, IsSquare (z.1 w)) ∧ ((∀ v, z.2 v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ S, IsSquare (z.2 v)) :=
      h1.prod_nhds (NormOpen.eventually_integral.and h2)
    exact h3
  have hV : ∀ᶠ a : (AdeleRing (𝓞 F) F)ˣ in 𝓝 1,
      (a : AdeleRing (𝓞 F) F) ∈ U ∧ ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ U := by
    have hc1 : Filter.Tendsto (fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F))
        (𝓝 1) (𝓝 1) := by
      simpa using Units.continuous_val.tendsto (1 : (AdeleRing (𝓞 F) F)ˣ)
    have hc2 : Filter.Tendsto
        (fun a : (AdeleRing (𝓞 F) F)ˣ => ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        (𝓝 1) (𝓝 1) := by
      simpa using Units.continuous_coe_inv.tendsto (1 : (AdeleRing (𝓞 F) F)ˣ)
    exact (hc1.eventually hU).and (hc2.eventually hU)
  filter_upwards [hV] with a ha
  obtain ⟨⟨hAinf, hAint, hAS⟩, ⟨-, hBint, -⟩⟩ := ha
  set A : AdeleRing (𝓞 F) F := (a : AdeleRing (𝓞 F) F) with hA_def
  set B : AdeleRing (𝓞 F) F := ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) with hB_def
  have hAB : A * B = 1 := a.mul_inv
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ p : v.adicCompletion F × v.adicCompletion F,
      A.2 v = p.1 ^ 2 - (algebraMap F (AdeleRing (𝓞 F) F) δ).2 v * p.2 ^ 2 ∧
      (v ∉ S → p.1 ∈ v.adicCompletionIntegers F ∧ p.2 ∈ v.adicCompletionIntegers F) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hAS v hv
      exact ⟨(r, 0), by rw [hr]; ring, fun h => absurd hv h⟩
    · have hv2 : v.valuation F (2 : F) = 1 := by
        by_contra h; exact hv (Or.inl h)
      have hvδ : v.valuation F δ = 1 := by
        by_contra h; exact hv (Or.inr h)
      have h2eq : ((2 : F) : v.adicCompletion F) = 2 := by
        rw [show (2 : F) = 1 + 1 from one_add_one_eq_two.symm,
          show (2 : v.adicCompletion F) = 1 + 1 from one_add_one_eq_two.symm,
          HeightOneSpectrum.adicCompletion.coe_add, HeightOneSpectrum.adicCompletion.coe_one]
      have h2 : Valued.v (2 : v.adicCompletion F) = 1 := by
        rw [← h2eq, HeightOneSpectrum.adicCompletion.valued_coe, hv2]
      have hδv : Valued.v ((algebraMap F (AdeleRing (𝓞 F) F) δ).2 v) = 1 := by
        change Valued.v ((δ : F) : v.adicCompletion F) = 1
        rw [HeightOneSpectrum.adicCompletion.valued_coe, hvδ]
      have hprod : A.2 v * B.2 v = 1 := by
        have := congrArg (fun z : AdeleRing (𝓞 F) F => z.2 v) hAB
        exact this
      have hAle : Valued.v (A.2 v) ≤ 1 := hAint v
      have hBle : Valued.v (B.2 v) ≤ 1 := hBint v
      have hAv : Valued.v (A.2 v) = 1 := by
        have hmul : Valued.v (A.2 v) * Valued.v (B.2 v) = 1 := by
          rw [← map_mul, hprod, map_one]
        refine le_antisymm hAle ?_
        calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (A.2 v) * Valued.v (B.2 v) := hmul.symm
          _ ≤ Valued.v (A.2 v) * 1 := by gcongr
          _ = Valued.v (A.2 v) := mul_one _
      obtain ⟨x, hx, y, hy, hxy⟩ :=
        exists_integral_sq_sub_mul_sq_of_unit F v _ (A.2 v) h2 hδv hAv
      exact ⟨(x, y), hxy, fun _ => ⟨hx, hy⟩⟩
  choose p hp using hloc
  choose r hr using hAinf
  have hx : ∀ᶠ v in Filter.cofinite, (p v).1 ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_cofinite.2 (hSfin.subset fun v hv => ?_)
    by_contra h
    exact hv ((hp v).2 h).1
  have hy : ∀ᶠ v in Filter.cofinite, (p v).2 ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_cofinite.2 (hSfin.subset fun v hv => ?_)
    by_contra h
    exact hv ((hp v).2 h).2
  let X : AdeleRing (𝓞 F) F :=
    ((fun w => r w : InfiniteAdeleRing F), RestrictedProduct.mk (fun v => (p v).1) hx)
  let Y : AdeleRing (𝓞 F) F :=
    ((0 : InfiniteAdeleRing F), RestrictedProduct.mk (fun v => (p v).2) hy)
  refine ⟨X, Y, ?_⟩
  refine Prod.ext ?_ ?_
  · funext w
    change A.1 w = r w ^ 2 - (algebraMap F (AdeleRing (𝓞 F) F) δ).1 w * (0 : w.Completion) ^ 2
    rw [hr w]
    ring
  · refine RestrictedProduct.ext _ _ fun v => ?_
    change A.2 v = (p v).1 ^ 2 - (algebraMap F (AdeleRing (𝓞 F) F) δ).2 v * (p v).2 ^ 2
    exact (hp v).1
end GlobalTheory.QNorm
