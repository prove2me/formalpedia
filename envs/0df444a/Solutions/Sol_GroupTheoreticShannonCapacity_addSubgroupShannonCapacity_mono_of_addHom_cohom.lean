-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_mono_of_addHom_cohom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:12.517994+00:00
-- url     : https://prove2.me/submissions/da6fe736-ff2c-4c30-b8f2-398a946a3aad

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {G H : Type*}
    [AddGroup G] [Fintype G] [AddGroup H] [Fintype H]
    (Γ_G : SimpleGraph G) (Γ_H : SimpleGraph H)
    (f : G →+ H) (hf_inj : Function.Injective f)
    (hf_cohom : ∀ u v, u ≠ v → ¬Γ_G.Adj u v → f u ≠ f v ∧ ¬Γ_H.Adj (f u) (f v)) :
    addSubgroupShannonCapacity Γ_H ≥ addSubgroupShannonCapacity Γ_G := by
  -- Extend f to strong powers pointwise
  simp only [addSubgroupShannonCapacity]
  apply ciSup_le
  intro n
  -- f^n : (Fin (n+1) → G) → (Fin (n+1) → H) is also an injective hom and cohomomorphism
  let f_pow : (Fin (n + 1) → G) →+ (Fin (n + 1) → H) := {
    toFun := fun x => fun i => f (x i)
    map_zero' := by funext i; simp
    map_add' := by intro x y; funext i; simp [Pi.add_apply]
  }
  have hf_pow_inj : Function.Injective f_pow := by
    intro x y hxy
    funext i
    exact hf_inj (congrFun hxy i)
  have hf_pow_cohom : ∀ u v : Fin (n + 1) → G, u ≠ v →
      ¬(strongPower Γ_G (n + 1)).Adj u v →
      f_pow u ≠ f_pow v ∧ ¬(strongPower Γ_H (n + 1)).Adj (f_pow u) (f_pow v) := by
    intro u v huv hnadj
    constructor
    · exact fun h => huv (hf_pow_inj h)
    · simp only [strongPower] at hnadj ⊢
      push_neg at hnadj
      obtain ⟨i, hi_ne, hi_nadj⟩ := hnadj huv
      intro ⟨_, hadj_all⟩
      have hcohom_i := hf_cohom (u i) (v i) hi_ne hi_nadj
      cases hadj_all i with
      | inl heq => exact hcohom_i.1 heq
      | inr hadj => exact hcohom_i.2 hadj
  -- Show the supremum for H dominates term n of G
  have hbdd : BddAbove (Set.range fun m =>
      (addSubgroupIndependenceNumber (strongPower Γ_H (m + 1)) : ℝ) ^ (1 / (m + 1 : ℝ))) := by
    use (Fintype.card H : ℝ)
    intro x ⟨m, hm⟩
    rw [← hm]
    have hindep_le : (addSubgroupIndependenceNumber (strongPower Γ_H (m + 1)) : ℝ) ≤
        (Fintype.card (Fin (m + 1) → H) : ℝ) := by
      simp only [addSubgroupIndependenceNumber]
      have hnat : sSup { k | ∃ K : AddSubgroup (Fin (m + 1) → H),
          (strongPower Γ_H (m + 1)).IsIndepSet (K : Set _) ∧ Nat.card ↥K = k } ≤
          Fintype.card (Fin (m + 1) → H) := by
        apply csSup_le
        · use 1, ⊥
          exact ⟨fun u hu v hv huv => by
            simp only [SetLike.mem_coe, AddSubgroup.mem_bot] at hu hv
            exact (huv (hv ▸ hu)).elim, AddSubgroup.card_bot⟩
        · intro x ⟨K, _, hcard⟩
          rw [← hcard]; haveI : Fintype K := Fintype.ofFinite K
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      exact_mod_cast hnat
    have hcard_eq : Fintype.card (Fin (m + 1) → H) = (Fintype.card H) ^ (m + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    have hcard_pos : (0 : ℝ) ≤ Fintype.card H := by positivity
    calc (addSubgroupIndependenceNumber (strongPower Γ_H (m + 1)) : ℝ) ^ (1 / (m + 1 : ℝ))
        ≤ (Fintype.card (Fin (m + 1) → H) : ℝ) ^ (1 / (m + 1 : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity) hindep_le (by positivity)
      _ = ((Fintype.card H : ℝ) ^ (m + 1 : ℕ)) ^ (1 / (m + 1 : ℝ)) := by rw [hcard_eq]; norm_cast
      _ = (Fintype.card H : ℝ) ^ ((m + 1 : ℕ) * (1 / (m + 1 : ℝ))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hcard_pos]
      _ = (Fintype.card H : ℝ) ^ (1 : ℝ) := by congr 1; push_cast; field_simp
      _ = Fintype.card H := Real.rpow_one _
  apply le_ciSup_of_le hbdd n
  apply Real.rpow_le_rpow (by positivity)
  · -- addSubgroupIndependenceNumber transfers
    have hnat_ineq : addSubgroupIndependenceNumber (strongPower Γ_G (n + 1)) ≤
        addSubgroupIndependenceNumber (strongPower Γ_H (n + 1)) := by
      simp only [addSubgroupIndependenceNumber]
      apply csSup_le
      · use 1, ⊥
        exact ⟨fun u hu v hv huv => by
          simp only [SetLike.mem_coe, AddSubgroup.mem_bot] at hu hv
          exact (huv (hv ▸ hu)).elim, AddSubgroup.card_bot⟩
      · intro k ⟨K, hK_indep, hK_card⟩
        let K' := AddSubgroup.map f_pow K
        have hK'_indep : (strongPower Γ_H (n + 1)).IsIndepSet (K' : Set _) := by
          apply (SimpleGraph.isIndepSet_iff _).2
          intro u hu v hv huv
          simp only [K', AddSubgroup.coe_map, Set.mem_image] at hu hv
          obtain ⟨u', hu'K, hu'eq⟩ := hu
          obtain ⟨v', hv'K, hv'eq⟩ := hv
          rw [← hu'eq, ← hv'eq]
          have huv' : u' ≠ v' := fun heq => huv (hu'eq ▸ hv'eq ▸ heq ▸ rfl)
          have hpair := (SimpleGraph.isIndepSet_iff _).1 hK_indep
          have hnadj' : ¬(strongPower Γ_G (n + 1)).Adj u' v' :=
            hpair (by simpa using hu'K) (by simpa using hv'K) huv'
          exact (hf_pow_cohom u' v' huv' hnadj').2
        have hK'_card : Nat.card K' = Nat.card K := AddSubgroup.card_map_of_injective hf_pow_inj
        rw [← hK_card, ← hK'_card]
        apply le_csSup
        · use Fintype.card (Fin (n + 1) → H)
          intro x ⟨L, _, hLcard⟩
          rw [← hLcard]; haveI : Fintype L := Fintype.ofFinite L
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        · exact ⟨K', hK'_indep, rfl⟩
    exact_mod_cast hnat_ineq
  · positivity
end GroupTheoreticShannonCapacity
