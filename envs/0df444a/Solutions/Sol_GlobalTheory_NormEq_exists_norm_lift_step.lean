-- Prove2me | solution 1 for GlobalTheory.NormEq.exists_norm_lift_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:13.905181+00:00
-- url     : https://prove2.me/submissions/94d4639f-e02c-41e8-9dc2-d3934bf125a5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFiltration
import Theorems.Thm_GlobalTheory_NormEq_isUnit_of_sub_one_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.NormEq
namespace GlobalTheory.NormEq
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  intro L _ _ σ ϖ q h P m hm x hx hxm
  obtain ⟨x₀, hx₀, hv⟩ := h.2.2.2.2.1
  have hve : Valued.v (x₀ - σ x₀) = 1 := by rw [← Valuation.map_neg, neg_sub]; exact hv
  have he : x₀ - σ x₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hve; exact zero_ne_one hve
  have hcO : x₀ * (x₀ - σ x₀)⁻¹ ∈ intL L := by
    change Valued.v (x₀ * (x₀ - σ x₀)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, hve, inv_one, mul_one]; exact hx₀
  let cO : intL L := ⟨_, hcO⟩
  have hcs : cO + sigO σ h.2.1 cO = 1 := by
    apply Subtype.ext
    change x₀ * (x₀ - σ x₀)⁻¹ + σ (x₀ * (x₀ - σ x₀)⁻¹) = 1
    have e2 : σ x₀ - x₀ = -(x₀ - σ x₀) := by ring
    rw [map_mul, map_inv₀, map_sub, h.1, e2, inv_neg]
    field_simp
    ring
  set ι := algebraMap (intL L) (GlobalTheory.UTr.Alg P) with hι
  set πA := ι (piO h) with hπA
  have hconjπ : GlobalTheory.UTr.conj P πA = πA := by
    rw [hπA, GlobalTheory.UTr.conj_algebraMap]; congr 1; exact Subtype.ext h.2.2.1
  have hconjc : GlobalTheory.UTr.conj P (ι cO) + ι cO = 1 := by
    have := congrArg ι hcs
    rw [map_add, map_one] at this
    rw [hι, GlobalTheory.UTr.conj_algebraMap]; rw [← this]; ring
  have h1 : (x : GlobalTheory.UTr.Alg P) - 1 ∈ Ideal.span {πA ^ m} := hxm
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hxc : GlobalTheory.UTr.conj P (x : GlobalTheory.UTr.Alg P) = x := GlobalTheory.UTr.mem_plus.1 hx
  have hca : πA ^ m * GlobalTheory.UTr.conj P a = πA ^ m * a := by
    have := congrArg (GlobalTheory.UTr.conj P) ha
    rw [map_mul, map_pow, hconjπ, map_sub, map_one, hxc] at this
    rw [mul_comm, this, ← ha, mul_comm]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hu1 : (1 + πA ^ (k + 1) * (ι cO * a)) - 1 ∈ GlobalTheory.NormEq.piPow h P (k + 1) := by
    rw [add_sub_cancel_left]; exact Ideal.mem_span_singleton'.2 ⟨ι cO * a, mul_comm _ _⟩
  refine ⟨(GlobalTheory.NormEq.isUnit_of_sub_one_mem h P hm hu1).unit, hu1, ?_⟩
  change (x : GlobalTheory.UTr.Alg P) - (1 + πA ^ (k + 1) * (ι cO * a)) *
    GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) ∈ Ideal.span {πA ^ (k + 1 + 1)}
  have e1 : GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) =
      1 + πA ^ (k + 1) * (GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a) := by
    rw [map_add, map_one, map_mul, map_pow, hconjπ, map_mul]
  rw [e1, Ideal.mem_span_singleton']
  refine ⟨-(πA ^ k * ι cO * a * GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a), ?_⟩
  linear_combination ha + GlobalTheory.UTr.conj P (ι cO) * hca + πA ^ (k + 1) * a * hconjc
end GlobalTheory.NormEq
