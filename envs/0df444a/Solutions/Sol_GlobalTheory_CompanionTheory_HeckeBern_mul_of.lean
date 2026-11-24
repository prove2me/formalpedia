-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.mul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:13:58.562881+00:00
-- url     : https://prove2.me/submissions/7c098e32-1ee1-49f8-a7bf-587640759b59

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_lam_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_eps_lam
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_hk_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_lam_out_dd
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_hk_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_fixed_eq_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_q_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_T_dd
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_augmentation_of_hecke_operator
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_ext_dd
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
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
variable (T : G → Hk K) (hp : IsHeckePair K)
variable (h1 : ∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) →
    (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) =
      ∑ y ∈ S, Finsupp.single y (1 : ℂ))
  (h3 : ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0)
include h1
include h3
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution {g h u : G} (H : ∀ k ∈ K, ∃ a ∈ K, ∃ b ∈ K, h * k * g = a * u * b) :
    T g * T h = (q hp g * q hp h / q hp u) • T u := by
  have hw : (T g * T h).1 (dd K) =
      ∑ y ∈ (hp h).toFinset, lam K (Quotient.out y) ((T g).1 (dd K)) := by
    show (T g).1 ((T h).1 (dd K)) = _
    rw [T_dd T hp h1 h, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← lam_out_dd, hk_comm]
  have key : ∀ y ∈ (hp h).toFinset, ∀ z ∈ (hp g).toFinset,
      (Quotient.out y) • z ∈ (hp u).toFinset := by
    intro y hy z hz
    obtain ⟨k1, rfl⟩ := (hp h).mem_toFinset.1 hy
    obtain ⟨k3, rfl⟩ := (hp g).mem_toFinset.1 hz
    set y0 : G ⧸ K := k1 • (h : G ⧸ K) with hy0
    have hout : ((Quotient.out y0 : G) : G ⧸ K) = ((k1 * h : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq']; rfl
    have hk2 : ((k1 : G) * h)⁻¹ * Quotient.out y0 ∈ K := QuotientGroup.eq.1 hout.symm
    obtain ⟨a, ha, b, hb, hab⟩ := H _ (K.mul_mem hk2 k3.2)
    rw [(hp u).mem_toFinset]
    refine ⟨⟨(k1 : G) * a, K.mul_mem k1.2 ha⟩, ?_⟩
    show (((k1 : G) * a * u : G) : G ⧸ K) = (Quotient.out y0 * ((k3 : G) * g) : G)
    rw [QuotientGroup.eq]
    have e : Quotient.out y0 * ((k3 : G) * g) = (k1 : G) * (h * ((((k1 : G) * h)⁻¹ * Quotient.out y0) * k3) * g) := by
      group
    rw [e, hab]
    have e2 : ((k1 : G) * a * u)⁻¹ * ((k1 : G) * (a * u * b)) = b := by group
    rw [e2]; exact hb
  have hsupp : ∀ y, y ∉ (hp u).toFinset → ((T g * T h).1 (dd K)) y = 0 := by
    classical
    intro y hy
    rw [hw, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [T_dd T hp h1 g, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [lam_single, Finsupp.single_apply, if_neg]
    intro e
    exact hy (e ▸ key x hx z hz)
  have hfix := fixed_eq_smul ((T g * T h).1 (dd K)) (fun k hk => hk_fixed (T g * T h) hk) u
    (hp u).toFinset (by simp) hsupp
  set c : ℂ := ((T g * T h).1 (dd K)) (u : G ⧸ K) with hc
  have heq : T g * T h = c • T u := by
    apply ext_dd T h1 h3
    rw [hfix, ← T_dd T hp h1 u]
    rfl
  have hq : c * q hp u = q hp g * q hp h := by
    have e1 : eps K ((T g * T h).1 (dd K)) = c * q hp u := by
      rw [hfix, map_smul, ← T_dd T hp h1 u, augmentation_of_hecke_operator T hp h1, smul_eq_mul]
    have e2 : eps K ((T g * T h).1 (dd K)) = q hp g * q hp h := by
      rw [hw, map_sum]
      simp only [eps_lam, augmentation_of_hecke_operator T hp h1]
      simp [q, mul_comm]
    rw [← e1, e2]
  rw [heq, eq_div_of_mul_eq (q_ne hp u) hq]
end GlobalTheory.CompanionTheory.HeckeBern
