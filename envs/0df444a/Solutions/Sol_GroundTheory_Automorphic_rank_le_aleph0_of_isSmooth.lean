-- Prove2me | solution 1 for GroundTheory.Automorphic.rank_le_aleph0_of_isSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:22.731393+00:00
-- url     : https://prove2.me/submissions/f983f1f5-2575-4df7-bfe8-6802fd9bb023

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Theorems.Thm_GroundTheory_Automorphic_exists_ne_zero_of_isIrreducible

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
open Polynomial Cardinal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Module.rank ℂ V ≤ ℵ₀ := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have hstable : ∀ g : G, Submodule.span ℂ (Set.range fun h : G => ρ h v) ≤
      (Submodule.span ℂ (Set.range fun h : G => ρ h v)).comap (ρ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  let W : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun h : G => ρ h v), fun g _ hx => hstable g hx⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left fun h => hv (by
    have hvW : v ∈ W.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at hvW
    exact (Submodule.mem_bot ℂ).1 hvW)
  have hspan : Submodule.span ℂ (Set.range fun h : G => ρ h v) = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW
  have hsub : Set.range (fun h : G => ρ h v) ⊆ Set.range (fun d : D => ρ (d : G) v) := by
    rintro _ ⟨g, rfl⟩
    have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G)) :=
      (hρ v).preimage (by fun_prop)
    obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU ⟨g, by simp⟩
    refine ⟨⟨d, hdD⟩, ?_⟩
    have hd : ρ (g⁻¹ * d) v = v := hdU
    change ρ d v = ρ g v
    conv_rhs => rw [← hd]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have htop : Submodule.span ℂ (Set.range fun d : D => ρ (d : G) v) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono hsub
  have : Countable D := hDc.to_subtype
  have : Countable (Set.range fun d : D => ρ (d : G) v) := (Set.countable_range _).to_subtype
  calc Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun d : D => ρ (d : G) v)) := by rw [htop]
    _ ≤ #(Set.range fun d : D => ρ (d : G) v) := rank_span_le _
    _ ≤ ℵ₀ := Cardinal.mk_le_aleph0
end GroundTheory.Automorphic
