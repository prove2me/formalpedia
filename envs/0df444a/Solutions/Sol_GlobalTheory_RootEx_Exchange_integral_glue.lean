-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.integral_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:48.585855+00:00
-- url     : https://prove2.me/submissions/9e3a5644-2f1c-430e-94bc-24cf47bb9557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_wittExtendByZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [T2Space k]
  [SecondCountableTopology k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]
omit [T2Space k]
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution {I B : Type} [Fintype B] (P Q : I → Prop) [Fintype {i // P i}] [Fintype {i // Q i}]
    (j : B → I) (hj : Function.Injective j) (hPj : ∀ b, ¬ P (j b)) (hQ : ∀ i, Q i ↔ P i ∨ ∃ b, j b = i)
    (g : (B → k) → I → k) (hg1 : ∀ u b, g u (j b) = u b) (hg2 : ∀ u i, (∀ b, j b ≠ i) → g u i = 0)
    (f : (I → k) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∫ u : B → k, (∫ e, f (ext0 P e + g u) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) =
      ∫ e, f (ext0 Q e) ∂(Measure.pi fun _ => ν) := by
  classical
  let s : {i // P i} ⊕ B → {i // Q i} :=
    Sum.elim (fun i => ⟨i.1, (hQ _).2 (Or.inl i.2)⟩) (fun b => ⟨j b, (hQ _).2 (Or.inr ⟨b, rfl⟩)⟩)
  have hs : Function.Bijective s := by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [s, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · rw [Subtype.ext h]
      · exact absurd (h ▸ a.2) (hPj b)
      · exact absurd (h ▸ b.2) (hPj a)
      · rw [hj h]
    · rintro ⟨i, hi⟩
      rcases (hQ i).1 hi with h | ⟨b, rfl⟩
      · exact ⟨Sum.inl ⟨i, h⟩, rfl⟩
      · exact ⟨Sum.inr b, rfl⟩
  let σ := Equiv.ofBijective s hs
  have h1 := measurePreserving_piCongrLeft (α := fun _ : {i // Q i} => k) (fun _ => ν) σ
  have h2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // P i} ⊕ B => k) (fun _ => ν)
  have h3 := h1.comp h2
  have hint : Integrable (fun e => f (ext0 Q e)) (Measure.pi fun _ => ν) := by
    refine (hf.comp (continuous_wittExtendByZero Q)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (K := (fun (y : I → k) (i : {i // Q i}) => y i.1) '' tsupport f)
      (hc.isCompact.image (by fun_prop)) fun e he => ?_
    by_contra h
    refine he ⟨_, subset_tsupport _ h, ?_⟩
    funext i
    simp [ext0, i.2]
  have key : ∀ z : ({i // P i} → k) × (B → k), ext0 P z.1 + g z.2 =
      ext0 Q ((MeasurableEquiv.piCongrLeft (fun _ : {i // Q i} => k) σ ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // P i} ⊕ B => k)).symm) z) := by
    intro z
    funext i
    by_cases hq : Q i
    · obtain ⟨t, ht⟩ := σ.surjective ⟨i, hq⟩
      have hi : i = (σ t).1 := by rw [ht]
      simp only [ext0, hq, dite_true, Pi.add_apply, Function.comp, ← ht]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      rcases t with t | t
      · have hi' : i = t.1 := hi
        subst hi'
        have : g z.2 t.1 = 0 := hg2 _ _ fun b hb => hPj b (hb ▸ t.2)
        simp [this, t.2, MeasurableEquiv.sumPiEquivProdPi]
      · have hi' : i = j t := hi
        subst hi'
        simp [hg1, hPj, MeasurableEquiv.sumPiEquivProdPi]
    · have hp : ¬ P i := fun h => hq ((hQ i).2 (Or.inl h))
      have : g z.2 i = 0 := hg2 _ _ fun b hb => hq ((hQ i).2 (Or.inr ⟨b, hb⟩))
      simp [ext0, hq, hp, this]
  have hint2 := h3.integrable_comp_of_integrable hint
  rw [← h3.map_eq, integral_map (f := fun e => f (ext0 Q e)) h3.measurable.aemeasurable
    (hf.comp (continuous_wittExtendByZero Q)).aestronglyMeasurable]
  have := integral_prod_symm _ hint2
  simp only [Function.comp] at this key ⊢
  rw [this]
  simp only [← key]
end GlobalTheory.RootEx.Exchange
