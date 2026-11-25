-- Prove2me | solution 1 for GlobalTheory.mem_of_wild_of_pow_mem_open_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:19:43.284942+00:00
-- url     : https://prove2.me/submissions/592a4c7a-b044-4968-8d3e-34d739ea9291

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ValuationPowApplyDivSubOneLt
import Theorems.Thm_GlobalTheory_valuation_pow_apply_div_sub_one_lt
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open GlobalTheory
open NumberField IsDedekindDomain
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ (H : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)), H.Normal → IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∀ (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) (n : ℕ), ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → σ ^ n ∈ H → σ ∈ H := by
  intro E Ω _ _ _ _ _ A v hA H _ hH σ n hn hσ hpow
  change Ω ≃ₐ[E] Ω at σ
  have hv : A.valuation (n : Ω) = 1 := by
    have h1 : ¬ A.valuation (n : Ω) < 1 := by
      intro h
      apply hn
      rw [← hA]
      simpa using h
    have h2 : A.valuation (n : Ω) ≤ 1 := by
      simpa using A.valuation_le_one (n : A)
    exact le_antisymm h2 (not_lt.1 h1)
  have hn0 : (n : Ω) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨s, hsdef⟩ : ∃ s : Ω → Ω, ∀ z, s z = ∑ i ∈ Finset.range n, (σ ^ i) z :=
    ⟨_, fun _ => rfl⟩
  have hs : ∀ z, (σ ^ n) z = z → σ (s z) = s z := by
    intro z hz
    have e1 := Finset.sum_range_succ (fun i => (σ ^ i) z) n
    have e2 := Finset.sum_range_succ' (fun i => (σ ^ i) z) n
    simp only [hz, pow_zero, AlgEquiv.one_apply] at e1 e2
    rw [hsdef, map_sum]
    have e3 : ∑ i ∈ Finset.range n, σ ((σ ^ i) z) = ∑ i ∈ Finset.range n, (σ ^ (i + 1)) z :=
      Finset.sum_congr rfl fun i _ => by rw [pow_succ', AlgEquiv.mul_apply]
    rw [e3]
    exact add_right_cancel (e2.symm.trans e1)
  have hk : ∀ w, σ w = w → ∀ k : ℕ, (σ ^ k) w = w := by
    intro w hw k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hw]
  have hne : ∀ z, z ≠ 0 → s z ≠ 0 := by
    intro z hz h0
    have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero
        (fun i _ => _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ z hz i)
    have e : ∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1) = s z / z - n := by
      simp [hsdef, Finset.sum_sub_distrib, Finset.sum_div]
    rw [e, h0, zero_div, zero_sub, Valuation.map_neg, hv] at hlt
    exact lt_irrefl _ hlt
  have hfix : ∀ y : Ω, (σ ^ n) y = y → σ y = y := by
    intro y hy
    have hsy := hs y hy
    have h1 : ∀ i, (σ ^ i) ((n : Ω) * y - s y) = n * (σ ^ i) y - s y := fun i => by
      rw [map_sub, map_mul, map_natCast, hk (s y) hsy i]
    have hsz : s ((n : Ω) * y - s y) = 0 := by
      rw [hsdef, Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← hsdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have hz : (n : Ω) * y - s y = 0 := by
      by_contra h
      exact hne _ h hsz
    have hy' : s y = n * y := (sub_eq_zero.1 hz).symm
    have e := congrArg σ hy'
    rw [hsy, map_mul, map_natCast, hy'] at e
    exact (mul_left_cancel₀ hn0 e).symm
  haveI : IsGalois E Ω := inferInstance
  have hcl : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := H.isClosed_of_isOpen hH
  have hH' := InfiniteGalois.fixingSubgroup_fixedField (⟨H, hcl⟩ : ClosedSubgroup (Ω ≃ₐ[E] Ω))
  have hmem : σ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply hfix
    exact (IntermediateField.mem_fixedField_iff H y).1 hy _ hpow
  rw [hH'] at hmem
  exact hmem
end _root_.GlobalTheory
end GlobalTheory
