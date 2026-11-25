-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:40.716491+00:00
-- url     : https://prove2.me/submissions/f7d58464-eba8-436f-b394-8291d2eb7566

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_one_mem_unip
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_sum_char
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_rankMap_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_mem_unip
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_off
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_blkGL_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_blkGL_extHom_self
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_blkGL_extHom_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.TyFin.CuspVan
theorem _root_.solution {s s' : ℕ} (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hcusp : ∀ c, IsCuspidal K (lam c))
    (c : Fin s) (i₀ j₀ : ι) (hi : b i₀ = c) (hj : b j₀ = c) (hβ : β i₀ ≠ β j₀)
    (H : Subgroup (GL ι K)) [DecidablePred (· ∈ H)] (F : GL ι K → ℂ) (hH : H ≤ parab K b)
    (hF : ∀ u ∈ unip K β, (∀ i j, b i ≠ b j → (u : Matrix ι ι K) i j = 0) →
      u ∈ H ∧ ∀ h ∈ H, F (h * u) = F h) :
    ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
  set βc : {i // b i = c} → Fin s' := fun i => β i.1 with hβc
  have ht : 2 ≤ (Finset.univ.image βc).card :=
    Finset.one_lt_card.mpr ⟨βc ⟨i₀, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      βc ⟨j₀, hj⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hβ⟩
  have key : ∀ Y : Finset (GL {i // b i = c} K), (∀ v ∈ Y, v ∈ unip K (rankMap βc)) → 1 ∈ Y →
      (∀ g, ∑ v ∈ Y, (lam c).character (g * v) = 0) →
      ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
    intro Y hY h1 hY0
    set A : GL ι K → ℂ := fun h => ∏ c' ∈ Finset.univ.erase c, (lam c').character (blkGL b c' h)
      with hA
    set G : GL ι K → GL {i // b i = c} K → ℂ := fun h v =>
      if h ∈ H then F h * ((lam c).character (blkGL b c h * v) * A h) else 0 with hG
    set T : GL ι K → ℂ := fun h =>
      if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0 with hT
    have step : ∀ v ∈ Y, ∑ h, T h = ∑ h, G h v := by
      intro v hv
      obtain ⟨heH, hFe⟩ := hF (extHom b c v) (extHom_mem_unip b c β (hY v hv)) (extHom_off b c v)
      have hep : extHom b c v ∈ parab K b := hH heH
      refine (Equiv.sum_comp (Equiv.mulRight (extHom b c v)) T).symm.trans ?_
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [Equiv.coe_mulRight, hT, hG]
      by_cases hh : h ∈ H
      · rw [if_pos (mul_mem hh heH), if_pos hh, hFe h hh, hcFun,
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
          blkGL_mul b c (hH hh) hep, blkGL_extHom_self b c v hep]
        congr 2
        refine Finset.prod_congr rfl fun c' hc' => ?_
        rw [blkGL_mul b c' (hH hh) hep, blkGL_extHom_ne b (Finset.ne_of_mem_erase hc') v hep, mul_one]
      · rw [if_neg hh, if_neg (fun h' => hh (by simpa using mul_mem h' (inv_mem heH)))]
    have hcard : (Y.card : ℂ) * ∑ h, T h = 0 := by
      calc (Y.card : ℂ) * ∑ h, T h = ∑ _v ∈ Y, ∑ h, T h := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ v ∈ Y, ∑ h, G h v := Finset.sum_congr rfl step
        _ = ∑ h, ∑ v ∈ Y, G h v := Finset.sum_comm
        _ = 0 := by
            refine Finset.sum_eq_zero fun h _ => ?_
            by_cases hh : h ∈ H
            · simp only [hG, if_pos hh]
              rw [← Finset.mul_sum, ← Finset.sum_mul, hY0, zero_mul, mul_zero]
            · simp only [hG, if_neg hh, Finset.sum_const_zero]
    have hne : (Y.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h1)
    exact (mul_eq_zero.mp hcard).resolve_left hne
  classical
  exact key _ (fun v hv => (Finset.mem_filter.mp hv).2)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem_unip _⟩)
    (sum_char (rankMap βc) (rankMap_surj βc) ht (lam c) (hcusp c))
end GlobalTheory.CompanionTheory.TyFin.CuspVan
