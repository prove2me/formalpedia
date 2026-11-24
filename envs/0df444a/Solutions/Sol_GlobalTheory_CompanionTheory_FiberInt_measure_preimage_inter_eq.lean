-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FiberInt.measure_preimage_inter_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:01:37.764378+00:00
-- url     : https://prove2.me/submissions/f99510ba-3d95-4f12-b20c-3472630c7dfc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSplitExactSequence
import Theorems.Thm_GlobalTheory_CompanionTheory_FiberInt_periodized_invariant

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
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} {lam' : Measure A'} [lam.IsAddHaarMeasure]
    [lam'.IsAddHaarMeasure] {𝓖 : Set A} {𝓖' : Set A'}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (hG' : IsAddFundamentalDomain Γ' 𝓖' lam') (h1' : lam' 𝓖' = 1)
    {S : Set A'} (hS : MeasurableSet S) (hinv : ∀ γ ∈ Γ', ∀ x, γ + x ∈ S ↔ x ∈ S) :
    lam (π ⁻¹' S ∩ 𝓖) = lam' (S ∩ 𝓖') := by
  obtain ⟨P, hPdef⟩ : ∃ P, P = periodized π Γ' lam 𝓖 := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = Measure.map π (lam.restrict 𝓖) := ⟨_, rfl⟩
  have hPsum : P = Measure.sum fun γ : Γ' => ν.map ((γ : A') + ·) := by rw [hPdef, hνdef]; rfl
  have : P.IsAddLeftInvariant := by rw [hPdef]; exact periodized_invariant hπ hs hΓ hG
  have : SFinite P := by rw [hPdef]; infer_instance
  have : lam'.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam'
  have : lam'.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular lam'
  obtain ⟨M, hMdef⟩ : ∃ M, M = toMeasurable lam' 𝓖' := ⟨_, rfl⟩
  have hMm : MeasurableSet M := by rw [hMdef]; exact measurableSet_toMeasurable lam' 𝓖'
  have hMae : M =ᵐ[lam'] 𝓖' := by rw [hMdef]; exact hG'.nullMeasurableSet.toMeasurable_ae_eq
  have hM1 : lam' M = 1 := by rw [hMdef, measure_toMeasurable, h1']
  have hne : lam' ≠ 0 := fun h => by simp [h] at h1'
  have hPac : P ≪ lam' := absolutelyContinuous_of_isAddLeftInvariant P lam' hne
  have hνP : ν ≤ P := by
    have h0 := Measure.le_sum (fun γ : Γ' => Measure.map (fun y : A' => (γ : A') + y) ν) 0
    simp only [AddSubgroup.coe_zero, zero_add, Measure.map_id'] at h0
    rw [hPsum]
    exact h0
  have hνac : ν ≪ lam' := by
    intro t ht
    exact le_antisymm ((Measure.le_iff'.1 hνP t).trans (hPac ht).le) zero_le
  have claim : ∀ T : Set A', MeasurableSet T → (∀ γ ∈ Γ', ∀ x, γ + x ∈ T ↔ x ∈ T) →
      lam (π ⁻¹' T ∩ 𝓖) = P (T ∩ M) := by
    intro T hT hTinv
    have e1 : lam (π ⁻¹' T ∩ 𝓖) = ν T := by
      rw [hνdef, Measure.map_apply hπ hT, Measure.restrict_apply (hπ hT)]
    rw [e1, hG'.measure_eq_tsum_of_ac hνac T, hPsum, Measure.sum_apply _ (hT.inter hMm)]
    conv_lhs => rw [← (Equiv.neg Γ').tsum_eq]
    refine tsum_congr fun γ => ?_
    rw [Measure.map_apply (measurable_const_add _) (hT.inter hMm)]
    have hpre : (fun x => (γ : A') + x) ⁻¹' (T ∩ M) = T ∩ (fun x => (γ : A') + x) ⁻¹' M := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, hTinv γ γ.2 x]
    have hset : (fun x => (γ : A') + x) ⁻¹' 𝓖' = (Equiv.neg Γ') γ +ᵥ 𝓖' := by
      ext x
      rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
      simp [AddSubgroup.vadd_def]
    have hae : (fun x => (γ : A') + x) ⁻¹' M =ᵐ[lam'] (fun x => (γ : A') + x) ⁻¹' 𝓖' :=
      (measurePreserving_add_left lam' (γ : A')).quasiMeasurePreserving.preimage_ae_eq hMae
    rw [hpre, ← hset]
    exact measure_congr ((ae_eq_refl T).inter (hνac.ae_eq hae).symm)
  have hPt : ∀ t, MeasurableSet t → P t = P M * lam' t := by
    intro t ht
    have h := measure_add_lintegral_eq lam' P hMm (t.indicator 1) (measurable_one.indicator ht)
    rw [hM1, one_mul, lintegral_indicator_one ht] at h
    rw [h]
    have hc : ∀ x : A', P ((fun z => z + x) ⁻¹' M) = P M := fun x => by
      simp_rw [add_comm _ x]
      exact measure_preimage_add P x M
    simp_rw [hc]
    rw [lintegral_const_mul (P M) (f := fun x => t.indicator 1 (-x))
      ((measurable_one.indicator ht).comp measurable_neg),
      lintegral_neg_eq_self (t.indicator 1), lintegral_indicator_one ht]
  have hU := claim Set.univ MeasurableSet.univ (fun _ _ _ => by simp)
  rw [Set.preimage_univ, Set.univ_inter, h1, Set.univ_inter] at hU
  rw [claim S hS hinv, hPt _ (hS.inter hMm), ← hU, one_mul]
  exact measure_congr ((ae_eq_refl S).inter hMae)
end GlobalTheory.CompanionTheory.FiberInt
