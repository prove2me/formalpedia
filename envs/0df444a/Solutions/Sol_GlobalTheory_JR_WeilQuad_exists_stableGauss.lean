-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.exists_stableGauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:51.253969+00:00
-- url     : https://prove2.me/submissions/b2e091da-a5ce-4c33-8068-829cffb5415b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsStableQuadraticGaussIntegral
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussStable_NL_add
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussStable_NL_zero
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussStable_formL_symm_nondeg
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussStable_integral_indicator_char
import Theorems.Thm_GlobalTheory_JR_EtMeas_continuous_NL
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_formL_apply
import Theorems.Thm_GlobalTheory_JR_WeilQuad_isLocallyConstant_of_stdChar
import Theorems.Thm_GlobalTheory_JR_exists_small_dual_lattices


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory.JR.WeilQuad.GaussStable
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  intro F E _ _ _ _ hU A ψ x μ ω h u
  classical
  obtain ⟨-, -, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  set β := EtMeas.formL A ((u * x : A.Kˣ) : A.K) with hβ
  set f : A.L → ℂ := fun y => A.psiK ψ ((u : A.K) * x * A.NL y) with hf
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hin : Continuous fun y : A.L => Algebra.trace F A.K ((u : A.K) * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hflc : IsLocallyConstant f := (isLocallyConstant_of_stdChar hψ).comp_continuous hin
  have hfc : Continuous f := hflc.continuous
  have hkey : ∀ y m, f (y + m) = f y * ψ (β m y) * f m := by
    intro y m
    simp only [hf, hβ, EtMeas.formL_apply, Units.val_mul, NL_add A, Et.psiK, mul_add, map_add,
      AddChar.map_add_eq_mul]
  have hf0 : f 0 = 1 := by simp [hf, NL_zero A, Et.psiK]
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.L β
    (formL_symm_nondeg A (u * x)).1 (formL_symm_nondeg A (u * x)).2
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, -⟩ :=
    hsmall {y | f y = 1} ((hflc.isOpen_fiber 1).mem_nhds hf0)
  have hfM : ∀ m ∈ M, f m = 1 := fun m hm => hMU hm
  have hMpos : μ.real (M : Set A.L) ≠ 0 :=
    (ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hMc.measure_lt_top.ne).ne'
  refine ⟨∫ y in (N : Set A.L), f y ∂μ, M ⊔ N, AddSubgroup.isOpen_mono le_sup_left hMo, ?_, ?_⟩
  · refine (hMc.add hNc).of_isClosed_subset
      (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hMo)) ?_
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hz
    exact Set.add_mem_add ha hb
  intro Λ hΛo hΛc hle
  have hMΛ : M ≤ Λ := le_sup_left.trans hle
  have hNΛ : N ≤ Λ := le_sup_right.trans hle
  set iM : A.L → ℂ := (M : Set A.L).indicator (fun _ => 1) with hiM
  set iΛ : A.L → ℂ := (Λ : Set A.L).indicator (fun _ => 1) with hiΛ
  have hiMc : Continuous iM :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hMo, hMo⟩ continuous_const
  have hiΛc : Continuous iΛ :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hΛo, hΛo⟩ continuous_const
  let g : A.L → A.L → ℂ := fun m y => iM m * (iΛ y * f (y + m))
  have hgc : Continuous (Function.uncurry g) :=
    (hiMc.comp continuous_fst).mul ((hiΛc.comp continuous_snd).mul (hfc.comp (continuous_snd.add continuous_fst)))
  have hgs : HasCompactSupport (Function.uncurry g) := by
    refine HasCompactSupport.intro (hMc.prod hΛc) ?_
    rintro ⟨m, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : iM m = 0 := by rw [hiM, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
    · have : iΛ y = 0 := by rw [hiΛ, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
  have hswap := integral_integral_swap_of_hasCompactSupport hgc hgs (μ := μ) (ν := μ)
  have hA : ∀ m, ∫ y, g m y ∂μ = iM m * ∫ y in (Λ : Set A.L), f y ∂μ := by
    intro m
    by_cases hm : m ∈ M
    · have e : ∀ y, iΛ y * f (y + m) = (Λ : Set A.L).indicator f (y + m) := by
        intro y
        by_cases hy : y ∈ Λ
        · rw [hiΛ, Set.indicator_of_mem (by exact hy), Set.indicator_of_mem (by exact Λ.add_mem hy (hMΛ hm)), one_mul]
        · have h2 : y + m ∉ Λ := fun h' => hy (by simpa using Λ.sub_mem h' (hMΛ hm))
          rw [hiΛ, Set.indicator_of_notMem (by exact hy), Set.indicator_of_notMem (by exact h2), zero_mul]
      simp only [g]
      rw [integral_const_mul]
      congr 1
      simp_rw [e]
      rw [integral_add_right_eq_self (μ := μ) ((Λ : Set A.L).indicator f) m,
        integral_indicator hΛo.measurableSet]
    · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
      simp [g, h1]
  have hB : ∀ y, ∫ m, g m y ∂μ = (N : Set A.L).indicator (fun y => (μ.real (M : Set A.L) : ℂ) * f y) y := by
    intro y
    have e : ∀ m, g m y = iΛ y * f y * (M : Set A.L).indicator (fun m => ψ (β m y)) m := by
      intro m
      by_cases hm : m ∈ M
      · have h1 : iM m = 1 := by rw [hiM, Set.indicator_of_mem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = ψ (β m y) :=
          Set.indicator_of_mem (by exact hm) _
        simp only [g]
        rw [h1, h2, hkey, hfM m hm]; ring
      · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = 0 :=
          Set.indicator_of_notMem (by exact hm) _
        simp only [g]
        rw [h1, h2]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_indicator_char μ M hMo (fun m => ψ (β m y))
      (fun a b => by simp [map_add, AddChar.map_add_eq_mul])]
    by_cases hy : y ∈ N
    · rw [if_pos ((hN y).1 hy), Set.indicator_of_mem (by exact hy), hiΛ, Set.indicator_of_mem (by exact hNΛ hy)]
      ring
    · rw [if_neg (fun h' => hy ((hN y).2 h')), Set.indicator_of_notMem (by exact hy), mul_zero]
  have h1 : ∫ m, ∫ y, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (Λ : Set A.L), f y ∂μ := by
    simp_rw [hA]
    rw [integral_mul_const, hiM, integral_indicator_const _ hMo.measurableSet]
    simp
  have h2 : ∫ y, ∫ m, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (N : Set A.L), f y ∂μ := by
    simp_rw [hB]
    rw [integral_indicator hNo.measurableSet, integral_const_mul]
  have hmain := h1.symm.trans (hswap.trans h2)
  unfold gaussInt
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hMpos) hmain
end GlobalTheory.JR.WeilQuad
