-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.finrank_sq_le_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:09:38.368803+00:00
-- url     : https://prove2.me/submissions/deaf7c5c-e205-4af9-bd54-0abab14e5068

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BurnsideSurjOfIrred
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SimpleOfCommutativeStatement
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl
namespace GlobalTheory.CompanionTheory.RgFl
theorem _root_.solution {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (hρ : Function.Surjective ρ) {d l : ℕ}
    (x y : Fin d → A) (a : Fin l → A)
    (hs : Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} = ⊤) :
    Module.finrank ℂ V ^ 2 ≤
      d ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) := by
  classical
  set B := Algebra.adjoin ℂ (Set.range fun i => ρ (a i)) with hB
  have hmap : ∀ c ∈ Algebra.adjoin ℂ (Set.range a), ρ c ∈ B := by
    intro c hc
    have e : B = (Algebra.adjoin ℂ (Set.range a)).map ρ := by
      rw [hB, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [e]
    exact ⟨c, hc, rfl⟩
  let G : Fin d × Fin d → (B →ₗ[ℂ] Module.End ℂ V) := fun p =>
    (LinearMap.mulLeft ℂ (ρ (x p.1))) ∘ₗ (LinearMap.mulRight ℂ (ρ (y p.2))) ∘ₗ B.val.toLinearMap
  let F : (Fin d × Fin d → B) →ₗ[ℂ] Module.End ℂ V :=
    ∑ p : Fin d × Fin d, G p ∘ₗ LinearMap.proj p
  have hFs : ∀ (p : Fin d × Fin d) (b : B), F (Pi.single p b) = ρ (x p.1) * b * ρ (y p.2) := by
    intro p b
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single p]
    · simp [G, mul_assoc]
    · intro q _ hq
      simp [Pi.single_eq_of_ne hq]
    · simp
  have hF : LinearMap.range F = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨g, rfl⟩ := hρ f
    have hg : g ∈ Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} := by
      rw [hs]; exact Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, j, c, hc, rfl⟩ := hz
      exact ⟨Pi.single (i, j) ⟨ρ c, hmap c hc⟩, by simp [hFs]⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul t u _ hu => simpa using Submodule.smul_mem _ t hu
  have h1 : Module.finrank ℂ (Module.End ℂ V) ≤ Module.finrank ℂ (Fin d × Fin d → B) := by
    have := LinearMap.finrank_range_le F
    rwa [hF, finrank_top] at this
  have h2 : Module.finrank ℂ (Module.End ℂ V) = Module.finrank ℂ V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have h3 : Module.finrank ℂ (Fin d × Fin d → B) = d ^ 2 * Module.finrank ℂ B := by
    rw [Module.finrank_pi_fintype]
    simp [sq]
  rw [h2, h3] at h1
  exact h1
end GlobalTheory.CompanionTheory.RgFl
