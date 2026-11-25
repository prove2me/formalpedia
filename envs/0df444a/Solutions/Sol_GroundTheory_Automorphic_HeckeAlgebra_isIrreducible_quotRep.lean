-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.isIrreducible_quotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:20.198729+00:00
-- url     : https://prove2.me/submissions/beabb30c-97f3-4388-8b85-1a6cbbc19b57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_mem_subrep
import Theorems.Thm_P2M_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_corner__idem_mul_c76622439763
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isSmooth_quotRep
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_coe_smul_fixedVectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
open GroundTheory.Automorphic.HeckeAlgebra
open HeckeAlgebraLevel
variable (I : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo))
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution (hI : IsCoatom I) : (quotRep hKc hKo I).IsIrreducible := by
  have hne : (toFixedQuot hKc hKo I 1 : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) ≠ 0 := by
    intro h0
    apply hI.1
    rw [Ideal.eq_top_iff_one, ← ker_toFixedQuot hKc hKo I, LinearMap.mem_ker]
    exact Subtype.ext h0
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun X => ?_ }
  · have : (toFixedQuot hKc hKo I 1 : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) ∈
        (⊤ : Subrepresentation (quotRep hKc hKo I)) := Submodule.mem_top
    rw [← h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · by_cases hX : ∃ y ∈ X, y ∈ fixedVectors (quotRep hKc hKo I) K ∧ y ≠ 0
    · right
      obtain ⟨y, hyX, hyK, hy0⟩ := hX
      obtain ⟨h₀, hh₀⟩ := toFixedQuot_surjective hKc hKo I ⟨y, hyK⟩
      let I' : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) :=
        { carrier := {h | (toFixedQuot hKc hKo I h : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) ∈ X}
          add_mem' := fun {a b} ha hb => by
            simp only [mem_setOf_eq, map_add, Submodule.coe_add]
            exact X.toSubmodule.add_mem ha hb
          zero_mem' := by
            simp only [mem_setOf_eq, map_zero, ZeroMemClass.coe_zero]
            exact X.toSubmodule.zero_mem
          smul_mem' := fun a h hh => by
            simp only [mem_setOf_eq, map_smul, coe_smul_fixedVectors]
            exact heckeAct_mem_subrep X (a : HeckeAlgebra μ).mem (isSmooth_quotRep hKc hKo I _) hh }
      have hII' : I < I' := by
        refine lt_of_le_of_ne (fun h hh => ?_) fun heq => ?_
        · show _ ∈ X
          have : toFixedQuot hKc hKo I h = 0 := by rwa [← LinearMap.mem_ker, ker_toFixedQuot]
          rw [this]
          exact X.toSubmodule.zero_mem
        · have : h₀ ∈ I' := show _ ∈ X by rw [hh₀]; exact hyX
          rw [← heq, ← ker_toFixedQuot hKc hKo I, LinearMap.mem_ker, hh₀] at this
          exact hy0 (congrArg Subtype.val this)
      have h1 : (1 : HeckeAlgebraLevel μ K hKc hKo) ∈ I' := by
        rw [hI.2 I' hII']
        trivial
      rw [eq_top_iff]
      intro z _
      obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective z
      rw [← mkQ_mul_idem hKc hKo I φ, ← heckeAct_quotRep]
      exact heckeAct_mem_subrep X φ.mem (isSmooth_quotRep hKc hKo I _) h1
    · left
      push_neg at hX
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective z
      show _ ∈ (⊥ : Submodule ℂ _)
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      intro g
      have hmem : heckeAct μ (quotRep hKc hKo I) (idem μ hKc hKo)
          (quotRep hKc hKo I g ((heckeKernel hKc hKo I).mkQ φ)) = 0 :=
        hX _ (heckeAct_mem_subrep X (idem μ hKc hKo).mem (isSmooth_quotRep hKc hKo I _)
          (X.apply_mem_toSubmodule g hz))
          (heckeAct_idem_mem hKc hKo (isSmooth_quotRep hKc hKo I _))
      rw [quotRep_mkQ, heckeAct_quotRep, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
      have := hmem 1
      rwa [map_one, Module.End.one_apply, cornerₗ_idem_mul] at this
end GroundTheory.Automorphic.HeckeAlgebra
