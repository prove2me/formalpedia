-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.chi_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:13.696022+00:00
-- url     : https://prove2.me/submissions/cae16a67-1af5-4308-b884-e270bae49168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_norm_ne_zero_of_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_norm_mul_sigma
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_twist_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eS_idem
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_sigma_eS
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_mul_eq_zero_of_idem
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_sum_mul_sum_diag
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) {y : B.A} (hy : B.Plus y) :
    chi B e S y = K.eta (Algebra.norm K.E y) := by
  have he := h.1.toOrthogonalIdempotents
  have hcomp := h.1.complete
  choose f hf using h.2
  set E := eS B e S with hEdef
  have hE : E * E = E := eS_idem B he S
  have hσE : B.σ E = E := sigma_eS B h S
  have hfe : ∀ i ∈ Sᶜ, f i * e i = f i := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, hid.eq, (h2 hiS).1, add_zero]
  have hge : ∀ i ∈ Sᶜ, B.σ (f i) * e i = B.σ (f i) := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, mul_comm (B.σ (f i)) (f i), (h2 hiS).1, zero_add, ← map_mul, hid.eq]
  set F := ∑ i ∈ Sᶜ, f i with hFdef
  set G := ∑ i ∈ Sᶜ, B.σ (f i) with hGdef
  have hGσ : G = B.σ F := by rw [hGdef, hFdef, map_sum]
  have hFF : F * F = F := by
    rw [hFdef, sum_mul_sum_diag B he _ f f hfe hfe]; exact Finset.sum_congr rfl fun i _ => (hf i).1.eq
  have hFG : F * G = 0 := by
    rw [hFdef, hGdef, sum_mul_sum_diag B he _ f _ hfe hge]
    exact Finset.sum_eq_zero fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).1
  have hGG : G * G = G := by rw [hGσ, ← map_mul, hFF]
  have hFE : F * E = 0 := by
    rw [hFdef, hEdef, eS, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
      mul_eq_zero_of_idem B he (fun hij => Finset.mem_compl.1 hi (by rw [hij]; exact hj)) (hfe i hi) (he.idem j).eq
  have hGE : G * E = 0 := by rw [hGσ, ← hσE, ← map_mul, hFE, map_zero]
  have hFGsum : F + G = 1 - E := by
    have h1 : F + G = ∑ i ∈ Sᶜ, e i := by
      rw [hFdef, hGdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).2.symm
    rw [h1, ← hcomp, ← Finset.sum_add_sum_compl S e, hEdef, eS]; ring
  set w := y * F + G + E with hwdef
  have hσw : B.σ w = y * G + F + E := by
    rw [hwdef, map_add, map_add, map_mul, hy.2, hσE, hGσ, B.σ_σ]
  have hw : w * B.σ w = y * (1 - E) + E := by
    rw [hσw, ← hFGsum]
    linear_combination (y ^ 2 + 1) * hFG + y * hFF + (y + 1) * hFE + y * hGG + (y + 1) * hGE + hE
  have hE' : (1 - E) * (1 - E) = 1 - E := by linear_combination hE
  have hwwU : IsUnit (w * B.σ w) := by
    have := twist_isUnit B hE' hy.1
    rwa [sub_sub_cancel, ← hw] at this
  have hwU : IsUnit w := isUnit_of_mul_isUnit_left hwwU
  have hsplit : y = (y * E + (1 - E)) * (w * B.σ w) := by
    rw [hw]; linear_combination (y ^ 2 - 2 * y + 1) * hE
  unfold chi
  rw [← hEdef]
  conv_rhs => rw [hsplit]
  rw [map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy.1)) (norm_ne_zero_of_isUnit B hwwU),
    eta_norm_mul_sigma B hwU, mul_one]
end GlobalTheory.UnitLemma.Desc
