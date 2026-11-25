-- Prove2me | solution 1 for GlobalTheory.ev_starProjection_eigenspace_eq_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:42.309311+00:00
-- url     : https://prove2.me/submissions/4b363a45-e7cd-4c8b-9231-8d9f60a38635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open Module
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (t : ℕ) (m : Fin t → ℂ) (s : ℂ) (Om : Module.End ℂ Y) (ev : Y →ₗ[ℂ] V) (K : ℂ → (Y →ₗ[ℂ] V)) (q : ℂ → ℂ) (y : Y) (v : V) (l : Fin t), Function.Injective m → Om.IsSymmetric → (∀ (lam : ℂ) (x : Y), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + s) → (∀ (u : ℂ) (x : Y), K u ((u - s) • x + Om x) = (∏ j, (u + m j)) • ev x) → Continuous q → (∀ u, K u y = q u • v) → ev ((Module.End.eigenspace Om (m l + s)).starProjection y) = (q (-m l) / ∏ j ∈ Finset.univ.erase l, (m j - m l)) • v := by
  intro Y _ _ _ V _ _ t m s Om ev K q y v l hm hOm hspec hK hq hKy
  set P : Fin t → Y → Y := fun j x => (Module.End.eigenspace Om (m j + s)).starProjection x with hP
  set c : Fin t → ℂ → ℂ := fun j u => ∏ k ∈ Finset.univ.erase j, (u + m k) with hc
  have key : ∀ x : Y, ∀ u : ℂ, (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x) := by
    intro x u
    have hx : x ∈ ⨆ μ, Module.End.eigenspace Om μ := by
      rw [Submodule.orthogonal_eq_bot_iff.mp hOm.orthogonalComplement_iSup_eigenspaces_eq_bot]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun μ => Module.End.eigenspace Om μ) (motive := fun x => (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x)) hx ?_ ?_ ?_
    · intro μ x hxμ
      by_cases hx0 : x = 0
      · subst hx0; simp [hP]
      have hOmx : Om x = μ • x := Module.End.mem_eigenspace_iff.mp hxμ
      obtain ⟨i, rfl⟩ := hspec μ x hx0 hOmx
      have hPx : ∀ j, P j x = if j = i then x else 0 := by
        intro j
        split_ifs with hji
        · subst hji; exact Submodule.starProjection_eq_self_iff.mpr hxμ
        · have hne : m j + s ≠ m i + s := fun h => hji (hm (add_right_cancel h))
          have hortho := hOm.orthogonalFamily_eigenspaces.isOrtho hne
          exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (hortho.symm hxμ)
      have hsum : ∑ j, c j u • ev (P j x) = c i u • ev x := by
        rw [Finset.sum_eq_single i (fun j _ hji => by rw [hPx, if_neg hji, map_zero, smul_zero]) (by simp), hPx, if_pos rfl]
      have hKx : (u + m i) • K u x = (∏ k, (u + m k)) • ev x := by
        rw [← hK u x, hOmx, ← map_smul]
        congr 1
        rw [← add_smul]; congr 1; ring
      have hprod : ∏ k, (u + m k) = c i u * (u + m i) := by
        simp only [hc]; exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      rw [hsum, smul_comm (∏ k, (u + m k)) (c i u), ← hKx, hprod, mul_smul]
    · simp [hP]
    · intro x₁ x₂ h₁ h₂
      simp only [hP] at h₁ h₂ ⊢
      simp only [map_add, smul_add, Finset.sum_add_distrib, h₁, h₂]
  have hgen : ∀ u, ∏ k, (u + m k) ≠ 0 → q u • v = ∑ j, c j u • ev (P j y) := by
    intro u hu
    rw [← hKy]
    exact smul_right_injective V hu (key y u)
  have hdense : Dense {u : ℂ | ∏ k, (u + m k) ≠ 0} := by
    have hfin : {u : ℂ | ∏ k, (u + m k) = 0}.Countable := by
      apply Set.Finite.countable
      apply (Set.finite_range (fun k => -m k)).subset
      intro u hu
      simp only [Set.mem_setOf_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hu
      obtain ⟨k, hk⟩ := hu
      exact ⟨k, by linear_combination -hk⟩
    simpa [Set.compl_setOf] using hfin.dense_compl ℝ
  have hcont : Continuous fun u => ∑ j, c j u • ev (P j y) := by
    simp only [hc]; fun_prop
  have hf : Continuous fun u => q u • v := hq.smul continuous_const
  have hl := congrFun (Continuous.ext_on hdense hf hcont hgen) (-m l)
  rw [Finset.sum_eq_single l (fun j _ hjl => by
    simp only [hc]
    rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ l⟩) (by ring), zero_smul]) (by simp)] at hl
  have hcl : c l (-m l) = ∏ j ∈ Finset.univ.erase l, (m j - m l) :=
    Finset.prod_congr rfl (fun k _ => by ring)
  have hD : ∏ j ∈ Finset.univ.erase l, (m j - m l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (hm.ne (Finset.ne_of_mem_erase hj)))
  rw [hcl] at hl
  change ev (P l y) = _
  rw [div_eq_inv_mul, mul_smul, hl, smul_smul, inv_mul_cancel₀ hD, one_smul]
end _root_.GlobalTheory
end GlobalTheory
