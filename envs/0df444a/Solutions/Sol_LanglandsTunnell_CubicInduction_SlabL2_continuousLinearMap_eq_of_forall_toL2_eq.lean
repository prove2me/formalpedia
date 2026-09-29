-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.continuousLinearMap_eq_of_forall_toL2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/faf4df4c-e005-55da-ac48-ca427cb27b25

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuousLinearMap_eq_of_forall_toL2_eq

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    (T T' : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] E)
    (_h : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
      T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ =
        T' ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩) :
    T = T' := by

  have hcl : IsClosed {x : ↥(cuspidalSubspace ω a b Φ₀) | T x = T' x} := isClosed_eq T.continuous T'.continuous

  have hspan : ∀ (v : Carrier a b Φ₀) (hv : v ∈ Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀)),
      T ⟨v, Submodule.le_topologicalClosure _ hv⟩ = T' ⟨v, Submodule.le_topologicalClosure _ hv⟩ := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨f, hf, rfl⟩ := hv
      exact _h (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) hf
    | zero =>
      have e : (⟨0, Submodule.le_topologicalClosure _ (Submodule.zero_mem _)⟩ : ↥(cuspidalSubspace ω a b Φ₀)) = 0 :=
        rfl
      rw [e, map_zero, map_zero]
    | add u v hu hv ihu ihv =>
      have e : (⟨u + v, Submodule.le_topologicalClosure _ (Submodule.add_mem _ hu hv)⟩ :
          ↥(cuspidalSubspace ω a b Φ₀)) =
          ⟨u, Submodule.le_topologicalClosure _ hu⟩ + ⟨v, Submodule.le_topologicalClosure _ hv⟩ := rfl
      rw [e, map_add, map_add, ihu, ihv]
    | smul c v hv ih =>
      have e : (⟨c • v, Submodule.le_topologicalClosure _ (Submodule.smul_mem _ c hv)⟩ :
          ↥(cuspidalSubspace ω a b Φ₀)) = c • ⟨v, Submodule.le_topologicalClosure _ hv⟩ := rfl
      rw [e, map_smul, map_smul, ih]

  ext x
  have hsub : ((Subtype.val : ↥(cuspidalSubspace ω a b Φ₀) → Carrier a b Φ₀) ⁻¹'
      (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀) : Set (Carrier a b Φ₀))) ⊆
      {x : ↥(cuspidalSubspace ω a b Φ₀) | T x = T' x} := by
    intro y hy
    exact hspan y.1 hy
  have hx : x ∈ closure ((Subtype.val : ↥(cuspidalSubspace ω a b Φ₀) → Carrier a b Φ₀) ⁻¹'
      (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀) : Set (Carrier a b Φ₀))) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    show (x : Carrier a b Φ₀) ∈ closure ((Subtype.val : ↥(cuspidalSubspace ω a b Φ₀) → Carrier a b Φ₀) ''
      ((Subtype.val : ↥(cuspidalSubspace ω a b Φ₀) → Carrier a b Φ₀) ⁻¹'
        (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀) : Set (Carrier a b Φ₀))))
    have himg : (Subtype.val : ↥(cuspidalSubspace ω a b Φ₀) → Carrier a b Φ₀) ''
        ((Subtype.val : ↥(cuspidalSubspace ω a b Φ₀) → Carrier a b Φ₀) ⁻¹'
          (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀) : Set (Carrier a b Φ₀))) =
        (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀) : Set (Carrier a b Φ₀)) := by
      apply Set.image_preimage_eq_of_subset
      intro v hv
      exact ⟨⟨v, Submodule.le_topologicalClosure _ hv⟩, rfl⟩
    rw [himg, ← Submodule.topologicalClosure_coe]
    exact x.2
  exact hcl.closure_subset (closure_mono hsub hx)

end S_LanglandsTunnell_CubicInduction_SlabL2_continuousLinearMap_eq_of_forall_toL2_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_continuousLinearMap_eq_of_forall_toL2_eq (solution)
