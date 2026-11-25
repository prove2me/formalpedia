-- Prove2me | solution 1 for GlobalTheory.Chow.isPrincipal_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:36:35.993604+00:00
-- url     : https://prove2.me/submissions/cf363333-65ac-40d9-b88b-a50a94be3167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_Chow_isPrincipal_of_forall_rename_mem
import Theorems.Thm_GlobalTheory_Chow_injective_of_eval
import Theorems.Thm_GlobalTheory_Chow_algebraicIndependent_div
import Theorems.Thm_GlobalTheory_Chow_exists_algebraicIndependent_genericPoint
import Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_rename
import Theorems.Thm_GlobalTheory_Chow_aeval_eq_zero_of_mem_elimIdeal
import Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint_eq_zero_iff
import Theorems.Thm_GlobalTheory_Chow_isPrime_elimIdeal
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
theorem _root_.solution [Nonempty β] {p : Ideal (MvPolynomial σ K)} [p.IsPrime]
    (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) = (Fintype.card β : ℕ)) :
    (elimIdeal β p).IsPrincipal := by
  classical
  obtain ⟨κ, hκ⟩ := exists_algebraicIndependent_genericPoint hdim
  obtain ⟨i₀⟩ := ‹Nonempty β›
  let F := FractionRing (MvPolynomial σ K ⧸ p)
  let ξ : σ → F := genericPoint p
  let j₀ := κ i₀
  have h0 : ξ j₀ ≠ 0 := hκ.ne_zero i₀
  have hκ0 (i : β) (hi : i ≠ i₀) : κ i ≠ j₀ := fun h => hi (hκ.injective (congrArg ξ h))
  have : (elimIdeal β p).IsPrime := isPrime_elimIdeal ⟨j₀, fun h =>
    h0 (by rw [← aeval_genericPoint_eq_zero_iff, aeval_X] at h; exact h)⟩
  let V := β × {j : σ // j ≠ j₀}
  let W := {i : β // i ≠ i₀}
  let δ : Option (V ⊕ W) → β × σ := fun o =>
    o.elim (i₀, j₀) (Sum.elim (fun v => (v.1, v.2.1)) fun i => (i.1, j₀))
  have hδ : Function.Bijective δ := by
    constructor
    · rintro (_ | ⟨i, j, hj⟩ | ⟨i, hi⟩) (_ | ⟨i', j', hj'⟩ | ⟨i', hi'⟩) h <;>
        simp only [δ, Option.elim, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h <;>
        first | rfl | (obtain ⟨rfl, h⟩ := h; first | contradiction | (subst h; first | rfl | contradiction) | rfl)
    · rintro ⟨i, j⟩
      by_cases hj : j = j₀
      · by_cases hi : i = i₀
        · exact ⟨none, by simp [δ, hi, hj]⟩
        · exact ⟨some (.inr ⟨i, hi⟩), by simp [δ, hj]⟩
      · exact ⟨some (.inl (i, ⟨j, hj⟩)), rfl⟩
  refine isPrincipal_of_forall_rename_mem (Equiv.ofBijective δ hδ).symm _ fun g hg => ?_
  let s : β → MvPolynomial V F := fun i => -∑ k : {j : σ // j ≠ j₀}, X (i, k) * C (ξ k / ξ j₀)
  let t : β × σ → MvPolynomial V F := fun v => if h : v.2 = j₀ then s v.1 else X (v.1, ⟨v.2, h⟩)
  have ht (i : β) : ∑ j, t (i, j) * C (ξ j) = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      Finset.sum_subtype (p := fun l => l ≠ j₀) (F := inferInstance) _ (by simp)]
    simp only [t, s, dif_pos, neg_mul, Finset.sum_mul, mul_assoc, ← C_mul, div_mul_cancel₀ _ h0]
    rw [neg_add_eq_zero]
    exact Finset.sum_congr rfl fun k _ => by rw [dif_neg k.2]
  have hz : aeval t (rename (fun v => δ (some v)) g) = 0 := by
    refine aeval_eq_zero_of_mem_elimIdeal (ξ := fun j => C (ξ j)) (fun a ha => ?_)
      (fun h => h0 (C_eq_zero.1 (congrFun h j₀))) ht hg
    have := aeval_algebraMap_apply (MvPolynomial V F) ξ a
    rw [(aeval_genericPoint_eq_zero_iff p a).2 ha, map_zero] at this
    exact this
  let ψ : MvPolynomial V (MvPolynomial W K) →+* MvPolynomial V F :=
    eval₂Hom (aeval (fun i : W => s i.1) : MvPolynomial W K →ₐ[K] _).toRingHom X
  have hψ : ψ (sumAlgEquiv K V W g) = aeval t (rename (fun v => δ (some v)) g) := by
    have : ψ.comp (sumAlgEquiv K V W).toRingEquiv.toRingHom =
        ((aeval t).comp (rename (fun v => δ (some v))) : _ →ₐ[K] _).toRingHom := by
      refine ringHom_ext (fun a => ?_) ?_
      · simp [ψ]
      · rintro (⟨i, j, hj⟩ | i) <;> simp [ψ, δ, t, *]
    exact DFunLike.congr_fun this g
  have hinj : Function.Injective ψ := by
    refine injective_of_eval ψ (fun v => by simp [ψ])
      (fun v => if v.2.1 = κ v.1 then -1 else 0) (fun v => if v.2.1 = κ v.1 then -1 else 0)
      (fun v => by split_ifs <;> simp) fun r hr => ?_
    refine algebraicIndependent_iff.1 (algebraicIndependent_div hκ i₀) r ?_
    rw [← hr]
    have : (aeval (fun i : W => ξ (κ i) / ξ j₀) : MvPolynomial W K →ₐ[K] F).toRingHom =
        (eval fun v : V => if v.2.1 = κ v.1 then (-1 : F) else 0).comp (ψ.comp C) := by
      refine ringHom_ext (fun a => by simp [ψ]) fun i => ?_
      have : ∑ k : {j : σ // j ≠ j₀}, (if k.1 = κ i then (-1 : F) else 0) * (ξ k / ξ j₀) =
          -(ξ (κ i) / ξ j₀) := by
        rw [Finset.sum_eq_single ⟨κ i, hκ0 i i.2⟩]
        · rw [if_pos rfl]
          ring
        · intro k _ hk
          rw [if_neg fun h => hk (Subtype.ext h), zero_mul]
        · simp
      simp only [ψ, s, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply,
        eval₂Hom_C, map_neg, map_sum, map_mul, eval_X, eval_C, this]
      ring
    exact DFunLike.congr_fun this r
  rw [← hψ, map_eq_zero_iff ψ hinj, map_eq_zero_iff _ (AlgEquiv.injective _)] at hz
  exact hz
end GlobalTheory.Chow
