-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.mem_map_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:44.341474+00:00
-- url     : https://prove2.me/submissions/97e55890-507f-4d51-9757-0b5b7ccfc3eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_of_mul_mem_map
import Theorems.Thm_GlobalTheory_ProperFunctions_map_mem_map_of_comp_eq
import Theorems.Thm_GlobalTheory_ProperFunctions_appLE_comp_appLE_of_section
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_compatible
import Theorems.Thm_GlobalTheory_ProperFunctions_exists_ker_fromSpecResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {p : X ⟶ S} [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    (hq : ∀ s : S, Function.Surjective (p.fiberToSpecResidueField s).appTop)
    {e : S ⟶ X} (he : e ≫ p = 𝟙 S) (I : Ideal Γ(S, ⊤))
    (h : ∀ U : X.affineOpens, Γ(X, U.1))
    (hc : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      X.presheaf.map (homOfLE hVU).op (h U) - h V ∈
        I.map (p.appLE ⊤ V.1 (le_preimage_top p _)).hom)
    (hv : ∀ (U : X.affineOpens) (W : S.affineOpens) (hW : W.1 ≤ e ⁻¹ᵁ U.1),
      e.appLE U.1 W.1 hW (h U) ∈ I.map
        (Scheme.Hom.appLE (𝟙 S) ⊤ W.1 (le_preimage_top _ _)).hom)
    (U : X.affineOpens) :
    h U ∈ I.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom := by
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  induction I using IsNoetherian.induction generalizing h U with
  | hgt I IH =>
  by_cases hI : I = ⊤
  · simp [hI, Ideal.map_top]
  have : Nontrivial (Γ(S, ⊤) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨𝔭, h𝔭⟩ := associatedPrimes.nonempty Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)
  obtain ⟨h𝔭, a, ha⟩ := isAssociatedPrime_iff.mp h𝔭
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha' : ∀ r, r ∈ 𝔭 ↔ r * a ∈ I := by
    intro r
    rw [ha, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem,
      map_mul]
    rfl
  have haI : a ∉ I := fun h ↦ h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr ((ha' 1).mpr (by simpa)))
  have hlt : I < I ⊔ Ideal.span {a} := by
    refine lt_of_le_of_ne le_sup_left fun h ↦ haI ?_
    rw [h]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have h1 := IH _ hlt h (fun U V hVU ↦ Ideal.map_mono le_sup_left (hc U V hVU))
    (fun U W hW ↦ Ideal.map_mono le_sup_left (hv U W hW))
  have h2 : ∀ U : X.affineOpens, ∃ k : Γ(X, U.1),
      h U - p.appLE ⊤ U.1 (le_preimage_top p _) a * k ∈
        Ideal.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom I := by
    intro U
    have := h1 U
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at this
    obtain ⟨y, hy, z, hz, hyz⟩ := this
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨k, ?_⟩
    rw [← hyz, mul_comm k]
    simpa using hy
  choose k hk using h2
  obtain ⟨s, hs⟩ := exists_ker_fromSpecResidueField 𝔭 h𝔭
  have h3 := mem_map_ker_of_compatible (f := S.fromSpecResidueField s) (g := p.fiberι s)
    (q := p.fiberToSpecResidueField s) (.of_hasPullback _ _) default (hq s) he k ?_ ?_ U
  · rw [hs] at h3
    have h4 : p.appLE ⊤ U.1 (le_preimage_top p _) a * k U ∈
        Ideal.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom I := by
      have : Ideal.span {a} * 𝔭 ≤ I := Ideal.span_singleton_mul_le_iff.mpr fun r hr ↦ by
        rw [mul_comm]; exact (ha' r).mp hr
      refine Ideal.map_mono this ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self a)) h3
    simpa using Ideal.add_mem _ (hk U) h4
  · intro U V hVU
    rw [hs]
    refine mem_map_of_mul_mem_map _ (p.flat_appLE (isAffineOpen_top S) V.2 _) I 𝔭 a
      (fun r ↦ (ha' r).mpr) _ ?_
    have e1 : p.appLE ⊤ U.1 (le_preimage_top p _) ≫ X.presheaf.map (homOfLE hVU).op =
        p.appLE ⊤ V.1 (le_preimage_top p _) := Scheme.Hom.appLE_map _ _ _
    have h4 := map_mem_map_of_comp_eq e1 (hk U)
    rw [map_sub, map_mul, ← CommRingCat.comp_apply _ _ a, e1] at h4
    convert Ideal.add_mem _ (Ideal.sub_mem _ (hc U V hVU) h4) (hk V) using 1
    ring
  · intro U W hW
    rw [hs]
    refine mem_map_of_mul_mem_map _ (Scheme.Hom.flat_appLE (𝟙 S) (isAffineOpen_top S) W.2 _) I 𝔭 a
      (fun r ↦ (ha' r).mpr) _ ?_
    have e1 := appLE_comp_appLE_of_section he U.1 W.1 hW
    have h4 := map_mem_map_of_comp_eq e1 (hk U)
    rw [map_sub, map_mul, ← CommRingCat.comp_apply _ _ a, e1] at h4
    convert Ideal.sub_mem _ (hv U W hW) h4 using 1
    ring
end GlobalTheory.ProperFunctions
