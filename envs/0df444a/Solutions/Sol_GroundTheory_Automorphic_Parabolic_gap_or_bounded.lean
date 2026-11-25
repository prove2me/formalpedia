-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.gap_or_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:49.278619+00:00
-- url     : https://prove2.me/submissions/97e321b8-a616-49a4-a2d3-5362a32b8114

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (μ : Fin n → ℤ) {C : ℤ} (hC : 0 < C) :
    (∃ θ : ℤ, ∃ b : α, (∃ j, β j = b ∧ θ ≤ μ j) ∧ (∃ k, β k = b ∧ μ k < θ) ∧
      ∀ k, β k = b → μ k < θ → μ k + C ≤ θ) ∨
    (∀ i j, β i = β j → μ i < μ j + n * C) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  push_neg at hB
  obtain ⟨i, j, hij, hbig⟩ := hB
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun k => β k = β j) μ
    ⟨j, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ hmin
  have hj₀j : μ j₀ ≤ μ j := hmin j rfl
  have hk : ∀ t : Fin n, ∃ k, β k = β j ∧ μ k < μ j₀ + ((t : ℕ) + 1 : ℤ) * C ∧
      μ j₀ + ((t : ℕ) + 1 : ℤ) * C < μ k + C := by
    intro t
    by_contra hne
    push_neg at hne
    apply hA
    refine ⟨μ j₀ + ((t : ℕ) + 1 : ℤ) * C, β j, ⟨i, hij, ?_⟩, ⟨j₀, hj₀, ?_⟩, fun k hk hlt => hne k hk hlt⟩
    · have ht : ((t : ℕ) + 1 : ℤ) ≤ n := by have := t.2; omega
      nlinarith
    · nlinarith
  choose k hkb hk1 hk2 using hk
  have hinj : Function.Injective k := by
    intro s t hst
    have h1 := hk1 s
    have h2 := hk2 s
    have h3 := hk1 t
    have h4 := hk2 t
    rw [hst] at h1 h2
    have hs : ((s : ℕ) : ℤ) < (t : ℕ) + 1 := by
      by_contra h
      push_neg at h
      nlinarith
    have ht : ((t : ℕ) : ℤ) < (s : ℕ) + 1 := by
      by_contra h
      push_neg at h
      nlinarith
    exact Fin.ext (by omega)
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hinj) j₀
  have h1 := hk2 t
  rw [ht] at h1
  have : (0 : ℤ) ≤ ((t : ℕ) : ℤ) * C := by positivity
  nlinarith
end GroundTheory.Automorphic.Parabolic
