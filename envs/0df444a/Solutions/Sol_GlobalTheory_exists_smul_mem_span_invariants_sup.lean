-- Prove2me | solution 1 for GlobalTheory.exists_smul_mem_span_invariants_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:36.051136+00:00
-- url     : https://prove2.me/submissions/76d7b008-c255-4dc4-a1e3-e6dbabf7bc59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulMemSpanInvariantsSup
import Theorems.Thm_GlobalTheory_exists_sum_smul_separating_inertia


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B] (N : Type)
      [AddCommGroup N] [Module B N] [DistribMulAction Γ N],
      (∀ (g : Γ) (b : B) (x : N), g • (b • x) = (g • b) • (g • x)) → ∀ q : Ideal B, q.IsPrime →
      (Nat.card (q.inertia Γ) : B) ∉ q →
      (∀ g ∈ q.inertia Γ, ∀ x : N, g • x - x ∈ q • (⊤ : Submodule B N)) →
      ∀ x : N, ∃ s : B, s ∉ q ∧
        s • x ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} ⊔ q • (⊤ : Submodule B N) := by
  intro Γ _ _ B _ _ N _ _ _ hsemi q hq hcard htriv x
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨n, c, d, s, hs, hsep⟩ := exists_sum_smul_separating_inertia Γ B q hq

  refine ⟨(Nat.card (q.inertia Γ) : B) * s, fun h => (hq.mem_or_mem h).elim hcard hs, ?_⟩

  have hinv : ∀ j, (∑ g : Γ, g • (c j • x)) ∈ {y : N | ∀ g : Γ, g • y = y} := by
    intro j h
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  obtain ⟨z, hzdef⟩ : ∃ z : N, z = ∑ j, d j • ∑ g : Γ, g • (c j • x) := ⟨_, rfl⟩
  have hz : z ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} := by
    rw [hzdef]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hinv j)))
  have hz' : z = ∑ g : Γ, (∑ j, d j * g • c j) • (g • x) := by
    rw [hzdef]
    simp only [Finset.smul_sum, hsemi, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : Nat.card (q.inertia Γ) = (Finset.univ.filter (fun g : Γ => g ∈ q.inertia Γ)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hsumI : ((Nat.card (q.inertia Γ) : B) * s) • x
      = ∑ g : Γ, if g ∈ q.inertia Γ then s • x else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, hc, ← Nat.cast_smul_eq_nsmul B, smul_smul]

  have hdiff : z - ((Nat.card (q.inertia Γ) : B) * s) • x ∈ q • (⊤ : Submodule B N) := by
    rw [hz', hsumI, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    by_cases hg : g ∈ q.inertia Γ
    · rw [if_pos hg]
      have e : (∑ j, d j * g • c j) • (g • x) - s • x
          = ((∑ j, d j * g • c j) - s) • (g • x) + s • (g • x - x) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul ((hsep g).1 hg) Submodule.mem_top)
        (Submodule.smul_mem _ s (htriv g hg x))
    · rw [if_neg hg, sub_zero]
      exact Submodule.smul_mem_smul ((hsep g).2 hg) Submodule.mem_top
  have key := Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hdiff)
  rwa [sub_sub_cancel] at key
end GlobalTheory
