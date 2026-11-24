-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.integrate_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:42.370259+00:00
-- url     : https://prove2.me/submissions/95953155-9e61-4245-8fb3-dc3bd11620ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_integrable_red
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_red_insert
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_exists_subgroup
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_exists_representatives
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_integral_cosets
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_indicator_mem
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_red_shift
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_red_indicator
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_red_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.IntLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β E (insert e I) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ M _ _ L w β E I e heE hK hInt
  by_cases heI : e ∈ I
  · rwa [Finset.insert_eq_of_mem heI]
  intro Φ hΦ
  obtain ⟨U, hUo, hUc, hU⟩ := exists_subgroup k ψ hψ R Q Φ.1 Φ.2 e (w (Matrix.single e.1 e.2 1))
  obtain ⟨S, hSd, hS⟩ := exists_representatives k R Q Φ.1 Φ.2 U hUo e
  have hsh : ∀ x (u : k), u ∈ U → red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x :=
    fun x u hu => red_shift k ψ ν R Q w β E I e heE heI Φ.1 u (hU u hu).2 (hU u hu).1 x
  have hlin : ∀ (f : k → Matrix R Q k → ℂ), (∀ a, f a ∈ SB (Matrix R Q k)) → ∀ x,
      red ψ ν w β E I (∑ a ∈ S, f a) x = ∑ a ∈ S, red ψ ν w β E I (f a) x := by
    intro f hf x
    unfold red
    simp only [Finset.sum_apply, Finset.sum_mul]
    exact integral_finset_sum S fun a _ => integrable_red k ψ ν hψ hν R Q w β E I (f a) (hf a) x
  have hsum : ∀ x, ∑ a ∈ S, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 (a - x e.1 e.2)) = 0 := by
    intro x
    have h0 : red ψ ν w β E (insert e I) Φ.1 x = 0 := congrFun hΦ x
    rw [red_insert k ψ ν hψ hν R Q w β E I e heE heI Φ.1 x
      (integrable_red k ψ ν hψ hν R Q w β E (insert e I) Φ.1 Φ.2 x)] at h0
    rw [integral_cosets k ν hν U hUo hUc S hSd
      (fun s => red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 (s - x e.1 e.2))) ?_ ?_] at h0
    · have h1 : ν (U : Set k) ≠ 0 := hUo.measure_ne_zero ν ⟨0, U.zero_mem⟩
      have h2 : ν (U : Set k) ≠ ⊤ := hUc.measure_lt_top.ne
      have hpos : ((ν (U : Set k)).toReal : ℂ) ≠ 0 := by
        exact_mod_cast (ENNReal.toReal_pos h1 h2).ne'
      exact (mul_eq_zero.1 h0).resolve_left hpos
    · intro s u hu
      rw [show s + u - x e.1 e.2 = (s - x e.1 e.2) + u by ring, Matrix.single_add, ← add_assoc]
      exact hsh _ u hu
    · intro s hs
      obtain ⟨t, ht, hte⟩ := red_support k ψ ν R Q w β E I e heE heI Φ.1 _ hs
      obtain ⟨a, ha, hta⟩ := hS t ht
      refine ⟨a, ha, ?_⟩
      have hxe : (x + Matrix.single e.1 e.2 (s - x e.1 e.2)) e.1 e.2 = s := by
        rw [Matrix.add_apply, Matrix.single_apply_same, add_sub_cancel]
      rw [hte, hxe] at hta
      exact hta
  let Φc : k → SB (Matrix R Q k) := fun a =>
    ⟨Set.indicator {t : Matrix R Q k | t e.1 e.2 - a ∈ U} Φ.1, indicator_mem k R Q Φ.1 Φ.2 U hUo e a⟩
  have hcov : ∑ a ∈ S, Φc a = Φ := by
    apply Subtype.ext
    funext t
    rw [Submodule.coe_sum, Finset.sum_apply]
    by_cases ht : Φ.1 t = 0
    · rw [ht]
      exact Finset.sum_eq_zero fun a _ => Set.indicator_apply_eq_zero.mpr fun _ => ht
    · obtain ⟨a, ha, hta⟩ := hS t ht
      rw [Finset.sum_eq_single a]
      · exact Set.indicator_of_mem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hta Φ.1
      · intro b hb hba
        refine Set.indicator_of_notMem (s := {t : Matrix R Q k | t e.1 e.2 - b ∈ U}) ?_ Φ.1
        intro htb
        have hm := U.sub_mem hta htb
        rw [sub_sub_sub_cancel_left] at hm
        exact hba (hSd b hb a ha hm)
      · intro ha'
        exact absurd ha ha'
  choose Φ' hΦ'L hΦ'r using fun a => hInt a (Φc a)
  have hred' : ∀ a x, red ψ ν w β E I (Φ' a).1 x =
      Set.indicator {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)}
        (fun z => red ψ ν w β E I Φ.1 (z + Matrix.single e.1 e.2 (a - z e.1 e.2))) x := by
    intro a x
    rw [hΦ'r a x]
    have h8 := red_indicator k ψ ν R Q w β E I e heE heI Φ.1 {s : k | s - a ∈ U} (x + Matrix.single e.1 e.2 a)
    have hxe : (x + Matrix.single e.1 e.2 a) e.1 e.2 - a = x e.1 e.2 := by
      simp [Matrix.add_apply, Matrix.single_apply]
    change red ψ ν w β E I (Set.indicator {t : Matrix R Q k | t e.1 e.2 ∈ {s : k | s - a ∈ U}} Φ.1) _ = _
    rw [h8]
    by_cases hx : x e.1 e.2 ∈ U
    · rw [Set.indicator_of_mem (show (x + Matrix.single e.1 e.2 a) ∈ {z : Matrix R Q k | z e.1 e.2 ∈ {s : k | s - a ∈ U}} by
          show (x + Matrix.single e.1 e.2 a) e.1 e.2 - a ∈ U
          rw [hxe]; exact hx),
        Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
      rw [← hsh (x + Matrix.single e.1 e.2 (a - x e.1 e.2)) (x e.1 e.2) hx, add_assoc, ← Matrix.single_add,
        sub_add_cancel]
    · rw [Set.indicator_of_notMem (show (x + Matrix.single e.1 e.2 a) ∉ {z : Matrix R Q k | z e.1 e.2 ∈ {s : k | s - a ∈ U}} by
          show ¬ ((x + Matrix.single e.1 e.2 a) e.1 e.2 - a ∈ U)
          rw [hxe]; exact hx),
        Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
  have hΞ : red ψ ν w β E I (∑ a ∈ S, Φ' a).1 = 0 := by
    funext x
    rw [Submodule.coe_sum, hlin (fun a => (Φ' a).1) (fun a => (Φ' a).2) x]
    simp only [hred']
    by_cases hx : x e.1 e.2 ∈ U
    · simp only [Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
      exact hsum x
    · simp only [Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx),
        Finset.sum_const_zero, Pi.zero_apply]
  have hL := hK (∑ a ∈ S, Φ' a) hΞ
  rw [← hcov, map_sum]
  rw [map_sum] at hL
  rw [← hL]
  exact Finset.sum_congr rfl fun a _ => (hΦ'L a).symm
end GlobalTheory.PartRed.IntEntry
