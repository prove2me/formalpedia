-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.restrict_isMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:16.733381+00:00
-- url     : https://prove2.me/submissions/d5b7d0ac-eaaa-4550-a24f-d7af9fd9fbc8

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_smul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_absorb
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_bdd
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_decomp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_coef_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_norm_form
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_coef_int
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_restrict_isLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V] {s : L →+* L} {h : V → V → L} {δ : L} {e f : V}
variable {U : Submodule L V}
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution (hS : StSandwich) [ProperSpace L] [FiniteDimensional L V] (hs : IsInv s)
    (hδ : IsDelta s δ) (hh : IsHerm s h) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) {Λ : AddSubgroup V} (hΛ : IsMax h Λ)
    (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ) :
    IsMax (fun x y : U => h x y) (Λ.comap U.subtype.toAddMonoidHom) := by
  have hδ0 := hδ.1
  have hlatU := restrict_isLat hS hh hδ0 he hf hef hU hΛ.1
  refine ⟨hlatU, fun x hx => hΛ.2.1 _ hx, fun N hN hNint hle => ?_⟩
  set P := prU hh hδ0 he hf hef hU with hP
  have hPv : ∀ x, ((P x : U) : V) = pr hh δ e f x := fun _ => rfl
  set M := bigLat (ca hh δ f) (cb hh δ e) P N with hM
  have hΛM : Λ ≤ M := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := coef_int hs hδ0 hh hΛ.1 hpair heΛ hfΛ hx
    exact ⟨h1, h2, hle h3⟩
  obtain ⟨c, hc0, hc1, hc⟩ := lat_bdd hN hlatU (LinearMap.id : U →ₗ[L] U)
  have hMlat : IsLat L M := by
    refine hS L V Λ M c hΛ.1 hc0 (fun x hx => ?_) (fun x => ?_) (fun a ha x hx => ?_)
    · obtain ⟨h1, h2, h3⟩ := hx
      have h4 : c • pr hh δ e f x ∈ Λ := hc _ h3
      rw [decomp hh δ e f x, smul_add, smul_add]
      exact Λ.add_mem (Λ.add_mem (lat_smul_mem hΛ.1 hc1 (lat_smul_mem hΛ.1 h1 heΛ))
        (lat_smul_mem hΛ.1 hc1 (lat_smul_mem hΛ.1 h2 hfΛ))) h4
    · obtain ⟨a, ha0, -, ha⟩ := lat_absorb hΛ.1 (fun _ : Unit => x)
      exact ⟨a, ha0, hΛM (ha ())⟩
    · obtain ⟨h1, h2, h3⟩ := hx
      refine ⟨?_, ?_, ?_⟩
      · rw [map_smul, smul_eq_mul, norm_mul]
        exact mul_le_one₀ ha (norm_nonneg _) h1
      · rw [map_smul, smul_eq_mul, norm_mul]
        exact mul_le_one₀ ha (norm_nonneg _) h2
      · rw [map_smul]
        exact lat_smul_mem hN ha h3
  have hMint : ∀ x ∈ M, ‖h x x‖ ≤ 1 := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨o1, o2⟩ := pr_orth hh hδ0 he hf hef x
    have hq := norm_form hs hh he hf hef (ca hh δ f x) (cb hh δ e x) o1 o2
    rw [← decomp hh δ e f x] at hq
    rw [hq]
    have ht : ‖δ * (s (ca hh δ f x) * cb hh δ e x) + s (δ * (s (ca hh δ f x) * cb hh δ e x))‖ ≤ 1 :=
      ((hδ.2.1 δ).2 le_rfl) _ (by
        rw [norm_mul, hs.2.1]
        exact mul_le_one₀ h1 (norm_nonneg _) h2)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ht (hNint _ h3))
  have hMeq : M = Λ := hΛ.2.2 M hMlat hMint hΛM
  refine le_antisymm (fun x hx => ?_) hle
  have hx' := (hU x).1 x.2
  obtain ⟨c1, c2, c3⟩ := coef_eq hh hδ0 he hf hef 0 0 hx'.1 hx'.2
  simp only [zero_smul, zero_add] at c1 c2 c3
  have hxM : (x : V) ∈ M := by
    refine ⟨by simp [c1], by simp [c2], ?_⟩
    have : P (x : V) = x := Subtype.ext c3
    rwa [this]
  rw [hMeq] at hxM
  exact hxM
end GlobalTheory.CompanionTheory.RgSplit
