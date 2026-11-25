-- Prove2me | solution 1 for GlobalTheory.WirtChain.ExpSum.deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:56.505339+00:00
-- url     : https://prove2.me/submissions/a5ec5666-e1ee-45a8-b126-ab7f6fbfadb9

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
import Theorems.Thm_P2M_GlobalTheory_WirtChain_contDiffOn_wirtWord__3aa88b37ccd1
import Theorems.Thm_P2M_GlobalTheory_WirtChain_fderiv_eq_sum_wirt__25170e863539
import Theorems.Thm_GlobalTheory_WirtChain_ExpSum_const_mul
import Theorems.Thm_GlobalTheory_WirtChain_ExpSum_sum
import Theorems.Thm_GlobalTheory_WirtChain_ExpSum_smooth
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.WirtChain
open Complex
variable {Φ I : Type} [Fintype Φ] [Fintype I]
variable {U : Set (I → ℂ)} {G : ℂ → (Φ → ℂ) → ℂ} {t : (I → ℂ) → Φ → ℂ} {l : (I → ℂ) → ℂ}
namespace GlobalTheory.WirtChain
namespace ExpSum
theorem _root_.solution {D : Set ℂ} {V : Set (Φ → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (v : I → ℂ) :
    ∃ F', ExpSum U G t l F' ∧ ∀ σ ∈ D, ∀ z ∈ U, fderiv ℝ (F σ) z v = F' σ z := by
  have hdt := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 ht).2
  have hdl := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hl).2
  have hdtv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ t z v) U := hdt.clm_apply contDiffOn_const
  have hdlv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ l z v) U := hdl.clm_apply contDiffOn_const
  induction hF with
  | zero => exact ⟨fun _ _ => 0, ExpSum.zero, fun σ _ z _ => by simp⟩
  | @add F₁ F₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨F₁', h₁', e₁⟩ := ih₁
    obtain ⟨F₂', h₂', e₂⟩ := ih₂
    refine ⟨fun σ z => F₁' σ z + F₂' σ z, ExpSum.add h₁' h₂', fun σ hσ z hz => ?_⟩
    have d₁ := ((h₁.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    have d₂ := ((h₂.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    show fderiv ℝ (fun y => F₁ σ y + F₂ σ y) z v = F₁' σ z + F₂' σ z
    have hsum : HasFDerivAt (fun y => F₁ σ y + F₂ σ y) _ z := d₁.hasFDerivAt.add d₂.hasFDerivAt
    rw [hsum.fderiv, ContinuousLinearMap.add_apply, e₁ σ hσ z hz, e₂ σ hσ z hz]
  | term n β w hβ =>
    have hdb := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hβ).2
    have hdbv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ β z v) U := hdb.clm_apply contDiffOn_const
    refine ⟨fun σ z => (σ ^ n * fderiv ℝ β z v * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z) +
        σ ^ (n + 1) * (-(β z * fderiv ℝ l z v)) * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)) +
        ∑ τ : Φ, (σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirtWord ((τ, false) :: w) (G σ) (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) *
            wirtWord ((τ, true) :: w) (G σ) (t z)), ?_, ?_⟩
    · refine ExpSum.add (ExpSum.add (ExpSum.term n _ w hdbv) (ExpSum.term (n + 1) _ w (hβ.mul hdlv).neg))
        (ExpSum.sum Finset.univ _ fun τ _ => ExpSum.add (ExpSum.term n _ _ (hβ.mul (contDiffOn_pi.1 hdtv τ)))
          (ExpSum.term n _ _ (hβ.mul ?_)))
      have := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.1 hdtv τ)
      simpa [Function.comp_def] using this
    · intro σ hσ z hz
      have hzn := hU.mem_nhds hz
      set W := wirtWord w (G σ) with hWdef
      have hWs : ContDiffOn ℝ ∞ W V := contDiffOn_wirtWord' hV (hGs σ hσ) w
      have hb' : HasFDerivAt β (fderiv ℝ β z) z :=
        ((hβ.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hl' : HasFDerivAt l (fderiv ℝ l z) z :=
        ((hl.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have ht' : HasFDerivAt t (fderiv ℝ t z) z :=
        ((ht.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hW' : HasFDerivAt W (fderiv ℝ W (t z)) (t z) :=
        ((hWs.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hmaps hz))).hasFDerivAt
      have hE := (hl'.const_mul (-σ)).cexp
      have hWt := hW'.comp z ht'
      have hall := ((hb'.const_mul (σ ^ n)).mul hE).mul hWt
      have hall' : HasFDerivAt (fun y => σ ^ n * β y * Complex.exp (-σ * l y) * W (t y)) _ z := hall
      rw [hall'.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.comp_apply, Function.comp_apply, Pi.mul_apply]
      rw [fderiv_eq_sum_wirt' W (t z) (fderiv ℝ t z v)]
      simp only [wirtWord_cons]
      rw [← hWdef]
      have hs : ∀ τ : Φ, σ ^ n * β z * Complex.exp (-σ * l z) * (fderiv ℝ t z v τ * wirt τ false W (t z) +
          (starRingEnd ℂ) (fderiv ℝ t z v τ) * wirt τ true W (t z)) =
          σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirt τ false W (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) * wirt τ true W (t z) :=
        fun τ => by ring
      rw [Finset.mul_sum]
      simp only [hs]
      ring
end ExpSum
end GlobalTheory.WirtChain
