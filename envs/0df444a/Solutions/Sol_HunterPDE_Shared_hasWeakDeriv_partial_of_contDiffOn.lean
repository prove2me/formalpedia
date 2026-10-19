-- Prove2me | solution 1 for HunterPDE.Shared.hasWeakDeriv_partial_of_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:22:52.786518+00:00
-- url     : https://prove2.me/submissions/ebbb3faf-a380-4dfe-9e90-1cd06f9137f1

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ 1 f Ω) (i : Fin n) :
    HasWeakDeriv Ω (Pi.single i 1) f (partialDeriv f i) := by
  have hc : ContinuousOn (partialDeriv f i) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  refine ⟨hf.continuousOn.locallyIntegrableOn hΩ.measurableSet,
    hc.locallyIntegrableOn hΩ.measurableSet, ?_⟩
  intro φ hφ
  have hd : Continuous (partialDeriv φ i) :=
    ((hφ.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  have hs : tsupport (partialDeriv φ i) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2
  have hp (g ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContinuousOn g Ω)
      (hψ : Continuous ψ) (hk : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω) :
      Integrable (fun x => g x * ψ x) := by
    have hh : Continuous (fun x => g x * ψ x) :=
      (hg.mul hψ.continuousOn).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans hsψ)
    exact hh.integrable_of_hasCompactSupport hk.mul_left
  have hfg := hp f φ hf.continuousOn hφ.1.continuous hφ.2.1 hφ.2.2
  have hdfg := hp (partialDeriv f i) φ hc hφ.1.continuous hφ.2.1 hφ.2.2
  have hfdg := hp f (partialDeriv φ i) hf.continuousOn hd
    (hφ.2.1.fderiv_apply ℝ _) hs
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (v := EuclideanSpace.single i 1) hdfg hfdg hfg
    (fun x hx => (hf.differentiableOn (by simp) x (hφ.2.2 hx)).differentiableAt
      (hΩ.mem_nhds (hφ.2.2 hx)))
    (fun x _ => hφ.1.differentiable (by simp) x)
  have he (g ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hsψ : tsupport ψ ⊆ Ω) :
      (∫ x in Ω, g x * ψ x) = ∫ x, g x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), mul_zero]
  have hl (l : List (Fin n)) (hl : l.Nodup) :
      l.flatMap (fun j => List.replicate ((Pi.single i 1 : Fin n → ℕ) j) j) =
        if i ∈ l then [i] else [] := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha := (List.nodup_cons.mp hl).1
      have hh := ih (List.nodup_cons.mp hl).2
      by_cases h : a = i
      · subst a; simp [List.flatMap_cons, hh, ha]
      · simp [List.flatMap_cons, hh, h, Ne.symm h]
  have hm : multiDeriv φ (Pi.single i 1) = partialDeriv φ i := by
    unfold multiDeriv multiIndexList
    rw [hl (List.finRange n) (List.nodup_finRange n)]
    simp [iteratedPartial]
  rw [hm, he _ _ hφ.2.2, he _ _ hs]
  simpa [partialDeriv, Finset.sum_pi_single] using congrArg Neg.neg hibp.symm
