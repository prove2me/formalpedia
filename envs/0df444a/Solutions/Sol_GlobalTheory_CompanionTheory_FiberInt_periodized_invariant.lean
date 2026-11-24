-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FiberInt.periodized_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:18.305469+00:00
-- url     : https://prove2.me/submissions/aee93e0c-f553-4b42-8b46-4279d1c4136b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence
import Theorems.Thm_GlobalTheory_CompanionTheory_FiberInt_lintegral_periodized

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FiberInt
variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']
namespace GlobalTheory.CompanionTheory.FiberInt
theorem _root_.solution {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} [lam.IsAddHaarMeasure] {𝓖 : Set A}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) :
    (periodized π Γ' lam 𝓖).IsAddLeftInvariant := by
  constructor
  intro c
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_const_add c),
    lintegral_periodized hπ lam 𝓖 (f := fun y => f (c + y)) (hf.comp (measurable_const_add c)),
    lintegral_periodized hπ lam 𝓖 hf]
  have key : ∀ x : A, ∑' γ : Γ', f (c + ((γ : A') + π x)) = ∑' γ : Γ', f ((γ : A') + π (s c + x)) := by
    intro x
    refine tsum_congr fun γ => ?_
    rw [map_add, hs]
    congr 1
    abel
  simp_rw [key]
  have hemb : MeasurableEmbedding (fun x : A => s c + x) :=
    (MeasurableEquiv.addLeft (s c)).measurableEmbedding
  rw [(measurePreserving_add_left lam (s c)).setLIntegral_comp_emb hemb
    (fun x => ∑' γ : Γ', f ((γ : A') + π x)) 𝓖]
  have hG' : IsAddFundamentalDomain Γ ((fun x : A => s c + x) '' 𝓖) lam := hG.vadd_of_comm (s c)
  refine hG'.setLIntegral_eq hG _ ?_
  intro g x
  show ∑' γ : Γ', f ((γ : A') + π ((g : A) + x)) = ∑' γ : Γ', f ((γ : A') + π x)
  rw [← (Equiv.addRight (⟨π g, hΓ g g.2⟩ : Γ')).tsum_eq (fun γ : Γ' => f ((γ : A') + π x))]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_addRight, AddSubgroup.coe_add, map_add, add_assoc]
end GlobalTheory.CompanionTheory.FiberInt
