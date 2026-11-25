-- Prove2me | solution 1 for GlobalTheory.Mass.Hyperplane.exists_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:23.337674+00:00
-- url     : https://prove2.me/submissions/a694d5a2-b8d4-4d6f-8aea-cf637834eda9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
import Theorems.Thm_GlobalTheory_Mass_Hyperplane_exists_refl
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.Hyperplane
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (h x y) = h y x) (A : Subring K)
    (I : AddSubgroup K) (Λ : AddSubgroup V) (hA : ∀ a ∈ A, star a ∈ A) (hI : ∀ a ∈ A, ∀ x ∈ I, a * x ∈ I)
    (hU : ∀ a ∈ A, a ∉ I → star a ∉ I → a⁻¹ ∈ A) (e : K) (heA : e ∈ A) (he : e ∈ I) (he' : 1 - star e ∈ I)
    (hΛ : ∀ a ∈ A, ∀ x ∈ Λ, a • x ∈ Λ) (hh : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ A) (u u' w : V) (hu : u ∈ Λ)
    (hu' : u' ∈ Λ) (hw : w ∈ Λ) (h1 : h u w ∉ I) (h2 : h u' w ∉ I) :
    ∃ g ∈ isom h, (∀ x ∈ Λ, g x ∈ Λ) ∧ (∀ x ∈ Λ, g.symm x ∈ Λ) ∧ ∀ x ∈ Λ, h u' (g x) - h u x ∈ I := by
  have hI' : ∀ a ∈ A, ∀ x ∈ I, x * a ∈ I := fun a ha x hx => mul_comm a x ▸ hI a ha x hx
  have one : (1 : K) ∉ I := fun H => h1 (by simpa using hI _ (hh u hu w hw) 1 H)
  have hd : e + star e ∉ I := fun H => one (by
    have := I.add_mem (I.sub_mem H he) he'
    simpa using this)
  have hd0 : e + star e ≠ 0 := fun H => hd (H ▸ I.zero_mem)
  have hds : star (e + star e) = e + star e := by rw [star_add, star_star, add_comm]
  have hdi : (e + star e)⁻¹ ∈ A := hU _ (A.add_mem heA (hA e heA)) hd (by rw [hds]; exact hd)
  obtain ⟨θ, hθA, hθI, hθ⟩ : ∃ θ ∈ A, θ ∈ I ∧ star θ = 1 - θ := by
    refine ⟨e * (e + star e)⁻¹, A.mul_mem heA hdi, hI' _ hdi _ he, ?_⟩
    rw [star_mul', star_inv₀, hds]
    field_simp
    ring
  have hθ' : 1 - θ ∈ A := A.sub_mem A.one_mem hθA
  set v : V := θ • (u - u') + (1 - θ) • w with hv
  have hvΛ : v ∈ Λ := Λ.add_mem (hΛ _ hθA _ (Λ.sub_mem hu hu')) (hΛ _ hθ' _ hw)
  have l1 : ∀ x ∈ Λ, h v x - (h u x - h u' x) ∈ I := by
    intro x hx
    have : h v x - (h u x - h u' x) = θ * (h w x - (h u x - h u' x)) := by
      simp only [hv, map_add, map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hθ, map_one]
      ring
    rw [this]
    exact hI' _ (A.sub_mem (hh _ hw _ hx) (A.sub_mem (hh _ hu _ hx) (hh _ hu' _ hx))) _ hθI
  have l2 : ∀ x ∈ Λ, h x v - h x w ∈ I := by
    intro x hx
    have : h x v - h x w = θ * (h x (u - u') - h x w) := by
      simp only [hv, map_add, map_smul, smul_eq_mul]
      ring
    rw [this]
    exact hI' _ (A.sub_mem (hh _ hx _ (Λ.sub_mem hu hu')) (hh _ hx _ hw)) _ hθI
  set n := h v v with hn
  set γ := h u' v with hγ
  have hnA : n ∈ A := hh _ hvΛ _ hvΛ
  have hγA : γ ∈ A := hh _ hu' _ hvΛ
  have hns : star n = n := hs v v
  set b := (1 - θ) * (-γ) + θ * (n + star γ) with hb
  have hbs : star b = θ * (-star γ) + (1 - θ) * (n + γ) := by
    simp only [hb, star_add, star_mul', star_sub, star_neg, star_one, star_star, hθ, hns]
    ring
  have hbA : b ∈ A := A.add_mem (A.mul_mem hθ' (A.neg_mem hγA)) (A.mul_mem hθA (A.add_mem hnA (hA _ hγA)))
  have hbγ : b + γ ∈ I := by
    have : b + γ = θ * (γ + n + star γ) := by rw [hb]; ring
    rw [this]
    exact hI' _ (A.add_mem (A.add_mem hγA hnA) (hA _ hγA)) _ hθI
  have hbI : b ∉ I := fun H => h2 (by
    have := I.sub_mem (I.sub_mem hbγ H) (l2 _ hu')
    simpa [hγ] using this)
  have hbI' : star b ∉ I := fun H => h1 (by
    have h3 : θ * (γ + n + star γ) ∈ I := hI' _ (A.add_mem (A.add_mem hγA hnA) (hA _ hγA)) _ hθI
    have := I.sub_mem (I.sub_mem (I.add_mem H h3) (l1 _ hvΛ)) (l2 _ hu)
    convert this using 1
    rw [hbs]
    ring)
  have hb0 : b ≠ 0 := fun H => hbI (H ▸ I.zero_mem)
  have hb0' : star b ≠ 0 := fun H => hbI' (H ▸ I.zero_mem)
  have haA : b⁻¹ ∈ A := hU b hbA hbI hbI'
  obtain ⟨g, hg, g1, g2⟩ := exists_refl h hs v b⁻¹ (by
    have : h v v = b + star b := by rw [hbs, hb, ← hn]; ring
    rw [this, star_inv₀]
    field_simp
    ring)
  refine ⟨g, hg, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [g1]
    exact Λ.sub_mem hx (hΛ _ (A.mul_mem haA (hh _ hvΛ _ hx)) _ hvΛ)
  · rw [g2]
    exact Λ.sub_mem hx (hΛ _ (A.mul_mem (hA _ haA) (hh _ hvΛ _ hx)) _ hvΛ)
  · have : h u' (g x) - h u x = (h v x - (h u x - h u' x)) - (b⁻¹ * h v x) * (b + γ) := by
      rw [g1, map_sub, map_smul, smul_eq_mul, ← hγ]
      field_simp
      ring
    rw [this]
    exact I.sub_mem (l1 x hx) (hI _ (A.mul_mem haA (hh _ hvΛ _ hx)) _ hbγ)
end GlobalTheory.Mass.Hyperplane
