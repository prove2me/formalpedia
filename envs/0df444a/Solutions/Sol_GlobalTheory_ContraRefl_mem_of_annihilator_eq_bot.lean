-- Prove2me | solution 1 for GlobalTheory.ContraRefl.mem_of_annihilator_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:13.530465+00:00
-- url     : https://prove2.me/submissions/bc276866-6b80-419f-ae07-f56550a98b62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_contra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.ContraRefl
theorem _root_.solution
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (U : Subrepresentation (contra π))
    (hA : ∀ v : V, (∀ u ∈ U.toSubmodule, (u : Module.Dual ℂ V) v = 0) → v = 0)
    (l : smoothPart π.dual) : l ∈ U.toSubmodule := by
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra π l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra π) K := mem_fix.2 fun h hh => hKs hh
  haveI := hπ.2 K ho hc
  let S : Submodule ℂ (Module.Dual ℂ (fixed π K)) :=
    (U.toSubmodule.comap (fixed (contra π) K).subtype).map (res π K)
  by_cases hS : S = ⊤
  · have hmem : res π K ⟨l, hlK⟩ ∈ S := hS ▸ Submodule.mem_top
    obtain ⟨u, hu, he⟩ := hmem
    have := res_injective hπ.1 hc he
    rw [show l = ((⟨l, hlK⟩ : fixed (contra π) K) : smoothPart π.dual) from rfl, ← this]
    exact hu
  · exfalso
    obtain ⟨φ, hφ, hφS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hS)
      inferInstance
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ (fixed π K)).surjective φ
    have hv0 : v ≠ 0 := fun h => hφ (by rw [h, map_zero])
    apply hv0
    refine Subtype.ext (hA v fun u hu => ?_)
    have hUs : IsSmooth U.toRepresentation := fun x => by
      have : {g : G | U.toRepresentation g x = x} = {g : G | contra π g x.1 = x.1} := by
        ext g; exact Subtype.ext_iff
      rw [this]; exact isSmooth_contra π x.1
    let f : U.toSubmodule →ₗ[ℂ] ℂ :=
      Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype ∘ₗ U.toSubmodule.subtype
    obtain ⟨y, hy, hfy⟩ := IwahoriOnto.exists_fixed_map_eq hUs hc f ⟨u, hu⟩ fun h hh => by
      show ((contra π h u : smoothPart π.dual) : Module.Dual ℂ V) v = (u : Module.Dual ℂ V) v
      rw [contra_apply, mem_fix.1 v.2 _ (inv_mem hh)]
    have hyK : (y : smoothPart π.dual) ∈ fixed (contra π) K :=
      mem_fix.2 fun h hh => congrArg Subtype.val (mem_fix.1 hy h hh)
    have h1 : res π K ⟨y, hyK⟩ ∈ S := ⟨⟨y, hyK⟩, y.2, rfl⟩
    have h2 : Module.evalEquiv ℂ (fixed π K) v (res π K ⟨y, hyK⟩) = 0 := by
      have := Submodule.mem_map_of_mem (f := (Module.evalEquiv ℂ (fixed π K) v)) h1
      rw [hφS] at this
      exact (Submodule.mem_bot ℂ).1 this
    show f ⟨u, hu⟩ = 0
    rw [← hfy]
    exact h2
end GlobalTheory.ContraRefl
