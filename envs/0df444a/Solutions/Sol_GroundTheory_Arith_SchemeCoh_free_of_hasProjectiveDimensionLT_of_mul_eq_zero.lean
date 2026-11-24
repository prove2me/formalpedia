-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.free_of_hasProjectiveDimensionLT_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:20.091804+00:00
-- url     : https://prove2.me/submissions/43ec1ee9-b397-458d-acda-b465261d946b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_zero_of_forall_smul_eq_zero_of_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R]
    {s : R} (hs : s ≠ 0) (hms : ∀ a ∈ maximalIdeal R, a * s = 0) (k : ℕ) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) : Module.Free R M := by
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM
    exact Module.free_of_flat_of_isLocalRing
  | succ k ih =>
    classical
    have hfg : (⊤ : Submodule R M).FG := Module.Finite.fg_top
    obtain ⟨t, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
    let π : (t → R) →ₗ[R] M := Fintype.linearCombination R (fun j : t ↦ (j : M))
    have hπ : Function.Surjective π := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hspan]
      exact Submodule.span_mono (fun y hy ↦ ⟨⟨y, hy⟩, rfl⟩)

    have hker : ∀ v ∈ LinearMap.ker π, ∀ i, v i ∈ maximalIdeal R := by
      intro v hv i
      by_contra hvi
      have hu : IsUnit (v i) := (IsLocalRing.notMem_maximalIdeal.mp hvi)
      have hsum : ∑ j, v j • (j : M) = 0 := by
        rw [LinearMap.mem_ker] at hv
        simpa [π, Fintype.linearCombination_apply] using hv
      rw [Fintype.sum_eq_add_sum_compl i] at hsum
      have hmem : (i : M) ∈ Submodule.span R ((t.erase i : Finset M) : Set M) := by
        have h1 : v i • (i : M) = -∑ j ∈ ({i}ᶜ : Finset t), v j • (j : M) :=
          eq_neg_of_add_eq_zero_left hsum
        have h2 : ∑ j ∈ ({i}ᶜ : Finset t), v j • (j : M) ∈
            Submodule.span R ((t.erase i : Finset M) : Set M) := by
          refine Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
          exact ⟨j.2, fun h ↦ hj (Subtype.ext h)⟩
        have h3 : (i : M) = ((hu.unit⁻¹ : Rˣ) : R) • (v i • (i : M)) := by
          rw [smul_smul, IsUnit.val_inv_mul, one_smul]
        have h4 : ((hu.unit⁻¹ : Rˣ) : R) • (v i • (i : M)) ∈
            Submodule.span R ((t.erase i : Finset M) : Set M) := by
          rw [h1]
          exact Submodule.smul_mem _ _ (Submodule.neg_mem _ h2)
        rwa [← h3] at h4
      have htop : Submodule.span R ((t.erase i : Finset M) : Set M) = ⊤ := by
        rw [eq_top_iff, ← hspan, Submodule.span_le]
        intro y hy
        by_cases hyi : y = i
        · rw [hyi]; exact hmem
        · exact Submodule.subset_span (by simp [hyi, hy])
      have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
        (Finset.finite_toSet (t.erase i))
      rw [htop, Set.ncard_coe_finset, Finset.card_erase_of_mem i.2, hcard] at hle
      have hpos : 0 < (⊤ : Submodule R M).spanFinrank := by
        rw [← hcard]; exact Finset.card_pos.mpr ⟨i, i.2⟩
      omega

    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker π)) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp hM
    have hKfree := ih (LinearMap.ker π) hK
    have hKzero : Subsingleton (LinearMap.ker π) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact hs (eq_zero_of_forall_smul_eq_zero_of_free (M := LinearMap.ker π) fun v ↦
        Subtype.ext (funext fun i ↦ by
          simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero,
            Pi.zero_apply]
          rw [mul_comm]; exact hms _ (hker v v.2 i)))
    have hinj : Function.Injective π := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.eq_bot_of_subsingleton
    exact Module.Free.of_equiv (LinearEquiv.ofBijective π ⟨hinj, hπ⟩)
end GroundTheory.Arith.SchemeCoh
