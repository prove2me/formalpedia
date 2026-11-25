-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.span_algebraMap_eq_map_ptIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:25.5138+00:00
-- url     : https://prove2.me/submissions/096f05fa-ca4e-46f3-b3a4-d90e148475c6

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SpanEqTopOfForallDotEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_span_eq_top_of_forall_dot_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_ptI_le_of_span_grad_eq_top
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_C
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_add
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_lin
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_mul
import Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_isLocalRing_isNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing
variable {m : ℕ}
private theorem gradP_eq_eval_pderiv (t : Fin m → ℂ) (a : MvPolynomial (Fin m) ℂ) (j : Fin m) :
    gradP t a j = eval t (pderiv j a) := by
  induction a using MvPolynomial.induction_on
  next c =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, pderiv_C, map_zero, Pi.zero_apply]
  next p q hp hq =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, Pi.add_apply, hp, hq, map_add, map_add]
  next p i hp =>
    have hX : gradP t (X i) = Pi.single i 1 := by
      have h2 : (X i : MvPolynomial (Fin m) ℂ) = (X i - C (t i)) + C (t i) := by ring
      rw [h2, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin,
        ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, add_zero]
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_mul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, hp, hX, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
      map_mul, eval_X]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution (e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : Fin e → MvPolynomial (Fin m) ℂ) (hI : ∀ h ∈ I, eval t h = 0) (hr : ∀ l, eval t (r l) = 0)
    (hv : ∀ v : Fin m → ℂ, (∀ h ∈ I, ∑ j, v j * eval t (pderiv j h) = 0) →
      (∀ l, ∑ j, v j * eval t (pderiv j (r l)) = 0) → v = 0) :
    Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) := by
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  have hpt : ptI t = ptIdeal t := by
    ext a
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    unfold ptIdeal
    rw [RingHom.mem_ker]
  have hmemPt : ∀ a, eval t a = 0 → a ∈ ptIdeal t := fun a ha => by
    rw [← hpt, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    exact ha
  have hφ : ∀ a, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)
        (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t) a) := fun a => rfl
  have hI0 : ∀ a ∈ I, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a = 0 := by
    intro a ha
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  set N : Ideal (locRing I t) := Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l))
    with hN
  set M : Ideal (locRing I t) := Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) with hM
  have hNM : N ≤ M := by
    rw [hN, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact Ideal.mem_map_of_mem _ (hmemPt _ (hr l))
  have key : ptI t ≤ Ideal.comap (algebraMap _ (locRing I t)) (N ⊔ M ^ 2) := by
    refine ptI_le_of_span_grad_eq_top t _ ?_ ((I : Set (MvPolynomial (Fin m) ℂ)) ∪ Set.range r)
      ?_ ?_ ?_
    · intro a ha
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_right
      rw [hM, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (by rw [← hpt]; exact ha)
    · rintro a (ha | ⟨l, rfl⟩)
      · rw [SetLike.mem_coe, Ideal.mem_comap, hI0 a ha]
        exact Submodule.zero_mem _
      · rw [SetLike.mem_coe, Ideal.mem_comap]
        exact Ideal.mem_sup_left (Ideal.subset_span ⟨l, rfl⟩)
    · rintro a (ha | ⟨l, rfl⟩)
      · exact hI a ha
      · exact hr l
    · apply span_eq_top_of_forall_dot_eq_zero
      intro v hvS
      apply hv v
      · intro h hh
        have h3 := hvS _ ⟨h, Or.inl hh, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
      · intro l
        have h3 := hvS _ ⟨r l, Or.inr ⟨l, rfl⟩, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
  have hMle : M ≤ N ⊔ M ^ 2 := Ideal.map_le_iff_le_comap.mpr (hpt.symm.le.trans key)
  haveI := hloc
  haveI := hnoeth
  have hMtop : M ≠ ⊤ := by
    haveI : (ptIdeal t).IsPrime := ptIdeal_isPrime t
    intro htop
    have hmax : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) =
        IsLocalRing.maximalIdeal (Localization.AtPrime (ptIdeal t)) :=
      Localization.AtPrime.map_eq_maximalIdeal
    have hMeq : M = Ideal.map
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
        (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t)) := by
      rw [hM, Ideal.map_map]
      exact congrArg (fun f => Ideal.map f (ptIdeal t)) (RingHom.ext fun a => rfl)
    have hc := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
      Ideal.Quotient.mk_surjective (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t))
    rw [← hMeq, htop, Ideal.comap_top] at hc
    have hb : Ideal.comap
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)) ⊥ ≤
        Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
      exact Ideal.map_mono (fun a ha => hmemPt a (hI a ha)) hx
    rw [sup_eq_left.mpr hb, hmax] at hc
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (ptIdeal t))).ne_top hc.symm
  have hMj : M ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hMtop
  have hle : M ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian M) hMj ?_
    rw [Ideal.smul_eq_mul, ← pow_two]
    exact hMle
  exact le_antisymm hNM hle
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
