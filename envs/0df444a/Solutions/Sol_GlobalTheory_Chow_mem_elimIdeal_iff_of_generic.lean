-- Prove2me | solution 1 for GlobalTheory.Chow.mem_elimIdeal_iff_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:27:46.596799+00:00
-- url     : https://prove2.me/submissions/ea73c93c-8e1e-4b2d-bf8c-f6cf61fe943c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_C_mem_incidenceIdeal
import Theorems.Thm_GlobalTheory_Chow_incidenceIdeal_le
import Theorems.Thm_GlobalTheory_Chow_mem_elimIdeal_iff_forall
import Theorems.Thm_GlobalTheory_Chow_exists_pow_mul_sub_rename_mem
import Theorems.Thm_GlobalTheory_Chow_map_linForm
import Theorems.Thm_GlobalTheory_Chow_map_mem_span_linForm
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
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]
namespace GlobalTheory.Chow
theorem _root_.solution {F : Type*} [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p) (hne : ξ ≠ 0)
    {f : MvPolynomial (β × σ) K} :
    f ∈ elimIdeal β p ↔
      map (algebraMap K F) f ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
  let φ : MvPolynomial σ K →+* F := (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom
  have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
  have hφj (j) : φ (X j) = ξ j := congrFun hφ j
  have hC : φ.comp C = algebraMap K F := by ext; simp [φ]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have hle : incidenceIdeal β p ≤
        (Ideal.span (Set.range (linForm ξ : β → _))).comap (map φ) := by
      refine incidenceIdeal_le.2 ⟨fun g hg => ?_, fun i => ?_⟩
      · have : φ g = 0 := (hξ g).2 hg
        simp [Ideal.mem_comap, this]
      · rw [Ideal.mem_comap, genericForm, map_linForm, hφ]
        exact Ideal.subset_span ⟨i, rfl⟩
    have := hle (hm j)
    rw [Ideal.mem_comap, map_mul, map_map, hC, map_C, map_pow, hφj] at this
    exact (Ideal.mul_unit_mem_iff_mem _ ((pow_ne_zero m hj).isUnit.map C)).1 this
  · intro hf
    refine mem_elimIdeal_iff_forall.2 fun j => ?_
    by_cases hj : ξ j = 0
    · exact ⟨1, Ideal.mul_mem_left _ _ (C_mem_incidenceIdeal (by
        rw [pow_one, ← hξ, aeval_X, hj]))⟩
    obtain ⟨m, g, hg⟩ := exists_pow_mul_sub_rename_mem (X : σ → MvPolynomial σ K) j (map C f)
    refine ⟨m, ?_⟩
    have h1 := map_mem_span_linForm φ hg
    rw [hφ, map_sub, map_mul, map_map, hC, map_rename] at h1
    have h2 : rename Subtype.val (map φ g) ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right (map φ (C (X j ^ m))) _ hf) h1
      rwa [sub_sub_cancel] at this
    rw [← Set.image_univ, ← ker_linFormElim ξ (Ne.isUnit hj), RingHom.mem_ker,
      linFormElim_rename, ← RingHom.mem_ker, MvPolynomial.ker_map] at h2
    have hker : RingHom.ker φ = p := Ideal.ext fun g => hξ g
    rw [hker] at h2
    have h3 : rename Subtype.val g ∈ p.map (C : _ →+* MvPolynomial (β × σ) (MvPolynomial σ K)) := by
      rw [← Ideal.mem_comap (f := (rename Subtype.val : _ →ₐ[MvPolynomial σ K] _))]
      refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) h2
      simpa [Ideal.mem_comap] using Ideal.mem_map_of_mem _ ha
    have := Ideal.add_mem _ (Ideal.mem_sup_right (S := p.map C) hg) (Ideal.mem_sup_left h3)
    rwa [sub_add_cancel] at this
end GlobalTheory.Chow
