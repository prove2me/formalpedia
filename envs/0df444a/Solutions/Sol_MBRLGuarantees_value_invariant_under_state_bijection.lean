-- Prove2me | solution 1 for MBRLGuarantees.value_invariant_under_state_bijection
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:39:08.018803+00:00
-- url     : https://prove2.me/submissions/24bc4d83-d9c8-4bfc-ab7b-5642c7291a50

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace MBRLGuarantees

lemma vi_sk {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (m : S × A → S) (hm : Measurable m) (p : S → A) (hp : Measurable p) :
    stateKernel (Kernel.deterministic p hp) (Kernel.deterministic m hm) =
      Kernel.deterministic (fun s => m (s, p s)) (hm.comp (measurable_id.prodMk hp)) := by
  ext s B hB
  rw [stateKernel, Kernel.snd_apply' _ _ hB, Kernel.compProd_apply (measurable_snd hB),
    Kernel.deterministic_apply, lintegral_dirac']
  · rw [Kernel.deterministic_apply, Kernel.deterministic_apply]
    rfl
  · show Measurable fun b => (Kernel.deterministic m hm (s, b)) B
    exact (Kernel.measurable_coe _ hB).comp measurable_prodMk_left

lemma vi_iter {S : Type*} [MeasurableSpace S] (f : S → S) (hf : Measurable f) (t : ℕ) :
    iterKernel (Kernel.deterministic f hf) t = Kernel.deterministic (f^[t]) (hf.iterate t) := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [iterKernel, ih, Kernel.deterministic_comp_deterministic]
    ext x : 1
    rw [Kernel.deterministic_apply, Kernel.deterministic_apply, Function.iterate_succ']

lemma vi_er {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (R : S × A → ℝ) (hRm : Measurable R) (p : S → A) (hp : Measurable p) (s : S) :
    expReward R (Kernel.deterministic p hp) s = R (s, p s) := by
  unfold expReward
  rw [Kernel.deterministic_apply]
  exact integral_dirac' (fun a => R (s, a)) _ (hRm.comp measurable_prodMk_left).stronglyMeasurable

lemma vi_term {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (R : S × A → ℝ) (hRm : Measurable R) (m : S × A → S) (hm : Measurable m)
    (p : S → A) (hp : Measurable p) (t : ℕ) (s : S) :
    ∫ s', expReward R (Kernel.deterministic p hp) s'
        ∂(iterKernel (stateKernel (Kernel.deterministic p hp) (Kernel.deterministic m hm)) t s) =
      R ((fun x => m (x, p x))^[t] s, p ((fun x => m (x, p x))^[t] s)) := by
  rw [vi_sk, vi_iter, Kernel.deterministic_apply]
  have e : (fun s' => expReward R (Kernel.deterministic p hp) s') = fun s' => R (s', p s') :=
    funext fun s' => vi_er R hRm p hp s'
  rw [e]
  exact integral_dirac' (fun s' => R (s', p s')) _
    (hRm.comp (measurable_id.prodMk hp)).stronglyMeasurable

theorem value_invariant_under_state_bijection {S S' A : Type*} [MeasurableSpace S]
    [MeasurableSpace S'] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (T : S ≃ᵐ S') (m : S × A → S) (hm : Measurable m) (p : S → A) (hp : Measurable p)
    (mT : S' × A → S') (hmT : Measurable mT) (hmT_eq : ∀ x, mT x = T (m (T.symm x.1, x.2)))
    (pT : S' → A) (hpT : Measurable pT) (hpT_eq : ∀ x, pT x = p (T.symm x)) (s : S) :
    stateValue γ (fun x : S' × A => R (T.symm x.1, x.2)) (Kernel.deterministic pT hpT)
        (Kernel.deterministic mT hmT) (T s) =
      stateValue γ R (Kernel.deterministic p hp) (Kernel.deterministic m hm) s := by
  have hR' : Measurable (fun x : S' × A => R (T.symm x.1, x.2)) :=
    hRm.comp ((T.symm.measurable.comp measurable_fst).prodMk measurable_snd)
  unfold stateValue
  congr 1
  funext t
  rw [vi_term _ hR', vi_term _ hRm]
  congr 2
  have key : ∀ n : ℕ, (fun x => mT (x, pT x))^[n] (T s) = T ((fun x => m (x, p x))^[n] s) := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hmT_eq, hpT_eq]
      simp
  rw [key, hpT_eq]
  simp

end MBRLGuarantees

open MBRLGuarantees in
theorem solution {S S' A : Type*} [MeasurableSpace S]
    [MeasurableSpace S'] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (T : S ≃ᵐ S') (m : S × A → S) (hm : Measurable m) (p : S → A) (hp : Measurable p)
    (mT : S' × A → S') (hmT : Measurable mT) (hmT_eq : ∀ x, mT x = T (m (T.symm x.1, x.2)))
    (pT : S' → A) (hpT : Measurable pT) (hpT_eq : ∀ x, pT x = p (T.symm x)) (s : S) :
    stateValue γ (fun x : S' × A => R (T.symm x.1, x.2)) (Kernel.deterministic pT hpT)
        (Kernel.deterministic mT hmT) (T s) =
      stateValue γ R (Kernel.deterministic p hp) (Kernel.deterministic m hm) s :=
  MBRLGuarantees.value_invariant_under_state_bijection γ hγ0 hγ1 R hRm hRb T m hm p hp mT hmT
    hmT_eq pT hpT hpT_eq s
