-- Prove2me | solution 1 for GlobalTheory.MinorFrame.RatProj.exists_rat_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:26.645929+00:00
-- url     : https://prove2.me/submissions/212188be-84b9-4b93-b14c-d90ec3741c77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsRationalFockProjectionMaximalMinors
import Theorems.Thm_GlobalTheory_MinorFrame_RatProj_fockQL_apply
import Theorems.Thm_GlobalTheory_MinorFrame_RatProj_fockS_map
import Theorems.Thm_GlobalTheory_MinorFrame_RatProj_eq_zero_of_fockQ_self
import Theorems.Thm_GlobalTheory_MinorFrame_RatProj_map_prodMinorsQ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RatProj
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame.RatProj
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  intro ι _ a d n k
  let PQ : Tup ι a d n → MvPolynomial (Var ι d a) ℚ := fun T => prodMinorsQ T
  let W := Submodule.span ℚ (Set.range PQ)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range PQ)
  let ψ : W →ₗ[ℚ] Module.Dual ℚ W := (fockQL (σ := Var ι d a)).flip.compl₁₂ W.subtype W.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h1 : ψ w w = 0 := by rw [LinearMap.mem_ker.mp hw]; rfl
    have h2 : fockQ (w : MvPolynomial (Var ι d a) ℚ) w = 0 := h1
    exact Subtype.ext (eq_zero_of_fockQ_self h2)
  have hsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w₀, hw₀⟩ := hsurj ((fockQL.flip (monomial k (1 : ℚ))).comp W.subtype)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 w₀.2
  let e : Fin (Fintype.card (Tup ι a d n)) ≃ Tup ι a d n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Tup ι a d n), fun p => c (e p), fun p => e p, fun T => ?_⟩
  have hsum : (∑ p, ((c (e p) : ℚ) : ℂ) • prodMinors (e p)) =
      map (algebraMap ℚ ℂ) (w₀ : MvPolynomial (Var ι d a) ℚ) := by
    rw [e.sum_comp (fun T => ((c T : ℚ) : ℂ) • prodMinors T), ← hc, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [PQ]
    rw [smul_eq_C_mul (prodMinorsQ T) (c T), map_mul, map_C, map_prodMinorsQ, smul_eq_C_mul]
    simp
  have hmon : (monomial k (1 : ℂ)) = map (algebraMap ℚ ℂ) (monomial k (1 : ℚ)) := by simp [map_monomial]
  rw [hsum, ← map_prodMinorsQ T, hmon, ← map_sub, fockS_map, ← fockQL_apply, map_sub]
  have h3 := LinearMap.congr_fun hw₀ ⟨PQ T, Submodule.subset_span ⟨T, rfl⟩⟩
  have h4 : fockQL (PQ T) (w₀ : MvPolynomial (Var ι d a) ℚ) = fockQL (PQ T) (monomial k 1) := h3
  simp only [PQ] at h4
  rw [h4, sub_self, Rat.cast_zero]
end GlobalTheory.MinorFrame.RatProj
