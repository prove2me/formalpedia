-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.sup_orthIn_eq_top_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:19.264719+00:00
-- url     : https://prove2.me/submissions/ddafde1e-ea24-42e0-827a-6f1bf29c731a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement
import Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_sup_orthIn_eq_top
import Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_exists_apply_eq_zero_inner_eq
import Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_apply_aeval_comm

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
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}
namespace GroundTheory.Automorphic.PeterssonComplement
theorem _root_.solution (U : Submodule ℂ V) (hι : Function.Injective ι)
    {T : Module.End ℂ V} (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y)))
    (hUT : ∀ u ∈ U, T u ∈ U)
    (h : ∀ v : V, ∃ V₀ : Submodule ℂ V, v ∈ V₀ ∧ (∀ z ∈ V₀, T z ∈ V₀) ∧
      (∀ x ∈ V₀, ∃ p : ℝ[X], aeval T (p.map (algebraMap ℝ ℂ)) x = 0 ∧
        FiniteDimensional ℂ (V₀ ⊓ LinearMap.ker (aeval T (p.map (algebraMap ℝ ℂ))) : Submodule ℂ V)) ∧
      ∀ u ∈ U, ∃ e ∈ U ⊓ V₀, ∀ w ∈ V₀, inner ℂ (ι u) (ι w) = inner ℂ (ι e) (ι w)) :
    U ⊔ orthIn ι U = ⊤ := by
  refine sup_orthIn_eq_top U fun v => ?_
  obtain ⟨V₀, hv, hV₀T, hfin, havg⟩ := h v
  obtain ⟨p, hpv, hpfin⟩ := hfin v hv
  refine ⟨V₀ ⊓ LinearMap.ker (aeval T (p.map (algebraMap ℝ ℂ))), hpfin, ⟨hv, hpv⟩, fun u hu => ?_⟩
  obtain ⟨e, ⟨heU, heV₀⟩, he⟩ := havg u hu
  obtain ⟨q, hqe, hqfin⟩ := hfin e heV₀
  set Z : Submodule ℂ V := U ⊓ (V₀ ⊓ LinearMap.ker (aeval T (q.map (algebraMap ℝ ℂ)))) with hZ
  have : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le (inf_le_right : Z ≤ _)
  have hZT : ∀ z ∈ Z, T z ∈ Z := by
    rintro z ⟨hzU, hzV₀, hzk⟩
    refine ⟨hUT z hzU, hV₀T z hzV₀, ?_⟩
    show T z ∈ LinearMap.ker _
    rw [LinearMap.mem_ker, ← apply_aeval_comm, LinearMap.mem_ker.1 (hzk : z ∈ LinearMap.ker _), map_zero]
  obtain ⟨m, ⟨hmU, hmV₀, -⟩, hmk, hm⟩ :=
    exists_apply_eq_zero_inner_eq hι hT p Z hZT (⟨heU, heV₀, hqe⟩ : e ∈ Z)
  exact ⟨m, ⟨hmU, hmV₀, hmk⟩, fun w ⟨hwV₀, hwk⟩ => (he w hwV₀).trans (hm w hwk)⟩
end GroundTheory.Automorphic.PeterssonComplement
