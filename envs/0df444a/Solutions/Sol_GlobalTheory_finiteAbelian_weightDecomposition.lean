-- Prove2me | solution 1 for GlobalTheory.finiteAbelian_weightDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:48:54.13523+00:00
-- url     : https://prove2.me/submissions/451cade3-ffa9-4312-a20d-f99f7b78fa5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_mem_weightSpace_iff
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_comm_avg
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_apply_avg
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_of_weight
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_of_weight_ne
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_sum_avg
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_baseChange_avg_of_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
open GlobalTheory
open FiniteAbelianWeights
namespace GlobalTheory
theorem _root_.solution :
    ∀ (o : Type) [CommRing o] [IsDomain o] (N : ℕ) (ζ : o), 0 < N → IsUnit (N : o) →
    IsPrimitiveRoot ζ N → ∀ (T : Type) [CommGroup T] [Finite T], (∀ t : T, t ^ N = 1) →
    ∀ (M : Type) [AddCommGroup M] [Module o M] (ρ : Representation o T M)
      [DecidableEq (T →* oˣ)],
      Finite (T →* oˣ) ∧
      DirectSum.IsInternal
        (fun c : T →* oˣ => ⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id)) ∧
      (∀ (T' : Subgroup T) (c' : T' →* oˣ),
        (⨅ t : T', LinearMap.ker (ρ t - (c' t : o) • LinearMap.id)) =
          ⨆ c : {c : T →* oˣ // c.comp T'.subtype = c'},
            ⨅ t, LinearMap.ker (ρ t - (c.1 t : o) • LinearMap.id)) ∧
      ∀ (A : Type) [CommRing A] [Algebra o A] (c : T →* oˣ),
        (⨅ t, LinearMap.ker ((ρ t).baseChange A - (algebraMap o A (c t)) • LinearMap.id)) =
          (⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id)).baseChange A := by
  intro o _ _ N ζ hN hNu hζ T _ _ hT M _ _ ρ _
  classical
  haveI : NeZero N := ⟨hN.ne'⟩

  have hunit : ∀ (G : Type) [CommGroup G] [Fintype G], (∀ g : G, g ^ N = 1) →
      ∃ u : o, u * (Fintype.card G : o) = 1 := by
    intro G _ _ hG
    have h1 := card_dvd_exponent_pow_rank' G hG
    rw [Nat.card_eq_fintype_card] at h1
    have h2 : (Fintype.card G : o) ∣ (N : o) ^ Group.rank G := by
      exact_mod_cast Nat.cast_dvd_cast (α := o) h1
    exact (isUnit_of_dvd_unit h2 (hNu.pow _)).exists_left_inv
  haveI : HasEnoughRootsOfUnity o N := ⟨⟨ζ, hζ⟩, inferInstance⟩
  haveI : HasEnoughRootsOfUnity o (Monoid.exponent T) :=
    HasEnoughRootsOfUnity.of_dvd o (Monoid.exponent_dvd_of_forall_pow_eq_one hT)
  have hfin : Finite (T →* oˣ) :=
    Finite.of_equiv T (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity T o).some.toEquiv.symm
  haveI := Fintype.ofFinite T
  haveI := Fintype.ofFinite (T →* oˣ)
  obtain ⟨u, hu⟩ := hunit T hT
  have hmem : ∀ (c : T →* oˣ) (x : M),
      avg ρ u c x ∈ ⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id) := fun c x =>
    (mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).2 fun t => apply_avg ρ u c t x
  refine ⟨hfin, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro c
      rw [Submodule.disjoint_def]
      intro x hx hx'
      have hle : (⨆ d, ⨆ (_ : d ≠ c), ⨅ t, LinearMap.ker (ρ t - (d t : o) • LinearMap.id)) ≤
          LinearMap.ker (avg ρ u c) := by
        refine iSup₂_le fun d hd y hy => ?_
        exact avg_of_weight_ne ρ u c d hd y
          ((mem_weightSpace_iff (fun t => ρ t) (fun t => (d t : o)) _).1 hy)
      have h0 : avg ρ u c x = 0 := hle hx'
      rwa [avg_of_weight ρ u hu c x
        ((mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hx)] at h0
    · rw [eq_top_iff]
      intro x _
      rw [← sum_avg ρ u hu x]
      exact Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hmem c x)
  · intro T' c'
    apply le_antisymm
    · intro x hx
      have hx' := (mem_weightSpace_iff (fun t : T' => ρ t) (fun t => (c' t : o)) _).1 hx
      rw [← sum_avg ρ u hu x]
      refine Submodule.sum_mem _ fun c _ => ?_
      by_cases hc : c.comp T'.subtype = c'
      · exact Submodule.mem_iSup_of_mem
          (⟨c, hc⟩ : {c : T →* oˣ // c.comp T'.subtype = c'}) (hmem c x)
      · haveI := Fintype.ofFinite T'
        obtain ⟨v, hv⟩ := hunit T' fun g => Subtype.ext (by simpa using hT g)
        let ρ' : Representation o T' M := ρ.comp T'.subtype
        have h1 : avg ρ' v c' (avg ρ u c x) = avg ρ u c x :=
          avg_of_weight ρ' v hv c' _ fun t => by
            change ρ t (avg ρ u c x) = _
            rw [comm_avg, hx' t, map_smul]
        have h2 : avg ρ' v c' (avg ρ u c x) = 0 :=
          avg_of_weight_ne ρ' v c' (c.comp T'.subtype) hc _ fun t => apply_avg ρ u c t x
        rw [← h1, h2]
        exact Submodule.zero_mem _
    · refine iSup_le fun c x hx => ?_
      obtain ⟨c, rfl⟩ := c
      have hx' := (mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hx
      exact (mem_weightSpace_iff (fun t : T' => ρ t)
        (fun t => (c.comp T'.subtype t : o)) _).2 fun t => hx' t
  · intro A _ _ c
    apply le_antisymm
    · intro x hx
      have hx' := (mem_weightSpace_iff (fun t => (ρ t).baseChange A)
        (fun t => algebraMap o A (c t)) _).1 hx
      rw [← baseChange_avg_of_weight ρ u hu A c x hx']
      clear hx hx'
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a m =>
        rw [LinearMap.baseChange_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem a (hmem c m)
      | add y z hy hz =>
        rw [map_add]
        exact Submodule.add_mem _ hy hz
    · rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      have hm' := (mem_weightSpace_iff (fun t => ρ t) (fun t => (c t : o)) _).1 hm
      refine (mem_weightSpace_iff (fun t => (ρ t).baseChange A)
        (fun t => algebraMap o A (c t)) _).2 fun t => ?_
      simp only [TensorProduct.mk_apply, LinearMap.baseChange_tmul, hm', algebraMap_smul,
        TensorProduct.tmul_smul]
end GlobalTheory
