-- Prove2me | solution 1 for GlobalTheory.Chow.elimIdeal_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:18.165646+00:00
-- url     : https://prove2.me/submissions/c97d02f8-aa03-4539-a7fc-d69688fe9178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_Chow_exists_ringKrullDim_eq_and_trdeg_eq
import Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint_eq_zero_iff
import Theorems.Thm_GlobalTheory_Chow_aeval_smul_eq_zero
import Theorems.Thm_GlobalTheory_Chow_genericPoint_ne_zero
import Theorems.Thm_GlobalTheory_Chow_map_mem_span_linForm
import Theorems.Thm_GlobalTheory_Chow_mem_elimIdeal_iff_of_generic
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ β : Type} [Fintype σ] [Fintype β]
namespace GlobalTheory.Chow
theorem _root_.solution {p : Ideal (MvPolynomial σ K)} [hP : p.IsPrime]
    (hp : p.IsHomogeneous (homogeneousSubmodule σ K)) (hX : ∃ j, X j ∉ p)
    (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) ≤ (Fintype.card β : ℕ)) : elimIdeal β p ≠ ⊥ := by
  classical
  intro hE
  have hne := genericPoint_ne_zero hX
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hne
  replace hj₀ : genericPoint p j₀ ≠ 0 := hj₀
  let F := FractionRing (MvPolynomial σ K ⧸ p)
  let y : σ → F := fun j => (genericPoint p j₀)⁻¹ * genericPoint p j
  let q : Ideal (MvPolynomial σ K) := RingHom.ker (aeval y : MvPolynomial σ K →ₐ[K] F)
  have hq : q.IsPrime := RingHom.ker_isPrime _
  have hle : p ≤ q :=
    aeval_smul_eq_zero hp (fun g => (aeval_genericPoint_eq_zero_iff p g).2) _
  have h1q : X j₀ - 1 ∈ q := by simp [q, y, RingHom.mem_ker, hj₀]
  have h1p : X j₀ - 1 ∉ p := by
    intro h
    have := homogeneousComponent_mem_of_mem hp h 0
    rw [homogeneousComponent_zero] at this
    simp only [coeff_sub, coeff_zero_X, coeff_zero_one, zero_sub, map_neg, map_one,
      neg_mem_iff] at this
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
  let B := MvPolynomial σ K ⧸ q
  obtain ⟨s, hs, hs'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K B
  have hlt := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk p (X j₀ - 1))
    (mem_nonZeroDivisors_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.1 h1p))
    (Ideal.Quotient.eq_zero_iff_mem.2 h1q)
  have hsβ : s + 1 ≤ Fintype.card β := by
    have := hlt.trans hdim
    rw [hs] at this
    exact_mod_cast this
  let u : σ → B := fun j => Ideal.Quotient.mk q (X j)
  have hu : IsUnit (u j₀) := by
    have : u j₀ = 1 := Ideal.Quotient.eq.2 h1q
    rw [this]; exact isUnit_one
  let χ : MvPolynomial (β × σ) K →ₐ[K]
      MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ j₀} B :=
    ((linFormElim u hu Set.univ).restrictScalars K).comp (mapAlgHom (Algebra.ofId K B))
  have hχ : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : map (algebraMap K B) f ∈ Ideal.span (Set.range (linForm u : β → _)) := by
      rw [← Set.image_univ, ← ker_linFormElim u hu]
      exact hf
    let ι : B →ₐ[K] F := Ideal.kerLiftAlg (aeval y : MvPolynomial σ K →ₐ[K] F)
    have h2 := map_mem_span_linForm ι.toRingHom h1
    have h3 : ι.toRingHom.comp (algebraMap K B) = algebraMap K F := RingHom.ext ι.commutes
    rw [map_map, h3] at h2
    rw [← Ideal.mem_bot, ← hE,
      mem_elimIdeal_iff_of_generic (aeval_genericPoint_eq_zero_iff p) hne]
    refine Ideal.span_le.2 ?_ h2
    rintro _ ⟨i, rfl⟩
    have h4 (j) : ι.toRingHom (u j) = (genericPoint p j₀)⁻¹ * genericPoint p j := by
      exact (Ideal.kerLiftAlg_mk _ _).trans (aeval_X _ _)
    have : linForm (fun j => ι.toRingHom (u j)) i =
        C (genericPoint p j₀)⁻¹ * linForm (genericPoint p) i := by
      simp only [linForm, h4, Finset.mul_sum, C_mul, mul_assoc]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have h5 := trdeg_le_of_injective χ hχ
  rw [← trdeg_add_eq K B (A := MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ j₀} B), hs',
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_natCast] at h5
  have h6 : Fintype.card (β × σ) ≤
      s + Fintype.card {v : β × σ // v ∉ elimIndices Set.univ j₀} := by exact_mod_cast h5
  have h7 : Fintype.card β ≤ Fintype.card {v : β × σ // v ∈ elimIndices Set.univ j₀} :=
    Fintype.card_le_of_injective (fun i => ⟨(i, j₀), trivial, rfl⟩)
      fun a b h => congrArg (fun v => v.1.1) h
  have h8 := Fintype.card_subtype_compl fun v : β × σ => v ∈ elimIndices Set.univ j₀
  have h9 := Fintype.card_subtype_le fun v : β × σ => v ∈ elimIndices Set.univ j₀
  omega
end GlobalTheory.Chow
