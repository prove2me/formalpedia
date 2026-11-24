-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.sub_fixedProj_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:40.133577+00:00
-- url     : https://prove2.me/submissions/22f8eba9-a84f-480d-ba25-f28c3500038c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (u : V) :
    u - (fixedProj ρ hρ hKc hKo u : V) ∈
      Submodule.span ℂ (range fun k : K => ρ k u - u) := by
  classical
  obtain ⟨N, hNo, hNK, hNu, hnorm, hfin⟩ :=
    exists_normal_subgroup hKc hKo (U := (stabilizerOf ρ u : Set G))
      ((hρ u).mem_nhds (one_mem _))
  let _ : Fintype (K ⧸ N.subgroupOf K) := Fintype.ofFinite _
  have hu : u ∈ fixedVectors ρ N := fun n hn => hNu hn
  set c : ℂ := (Fintype.card (K ⧸ N.subgroupOf K) : ℂ)
  have hc : c ≠ 0 := by
    simp only [c, ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  set w : V := c⁻¹ • cosetSum ρ K N u
  have hw : w ∈ fixedVectors ρ K :=
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hu)
  have hdiff : u - w = -(c⁻¹ • ∑ q : K ⧸ N.subgroupOf K,
      (ρ ((Quotient.out q : K) : G) u - u)) := by
    rw [Finset.sum_sub_distrib, ← cosetSum_apply, Finset.sum_const, Finset.card_univ,
      smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    simp [w]
  have hspan : u - w ∈ Submodule.span ℂ (range fun k : K => ρ k u - u) := by
    rw [hdiff]
    refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_))
    exact Submodule.subset_span ⟨Quotient.out q, rfl⟩
  have hle : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer ρ K := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact sub_mem_coinvariantsKer k.2 u
  have heq : fixedProj ρ hρ hKc hKo u = ⟨w, hw⟩ :=
    (fixedProj_eq_iff hρ hKc hKo).2 (hle hspan)
  rw [heq]
  exact hspan
end GroundTheory.Automorphic.RestrictedTensor
