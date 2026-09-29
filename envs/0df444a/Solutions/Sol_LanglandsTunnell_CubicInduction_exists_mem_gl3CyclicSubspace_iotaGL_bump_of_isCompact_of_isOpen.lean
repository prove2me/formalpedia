-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/af111972-fb02-59ab-a666-f7c1074e3332

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn mem_gl3PsiWhittakerFnSpace_iff gl3AmbientRightTranslate gl3AmbientRightTranslate_apply rightTranslate_mem_gl3PsiWhittakerFnSpace gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace iotaGL iotaGL_unipotentGL2 LocalGL3 exists_mem_gl3CyclicSubspace_iotaGL_bump"
namespace Kirillov
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section CosetSum

variable {G : Type*} [Group G] (K : Subgroup G)

private theorem apply_eq_of_mk_eq_of_rightInvariant (φ : G → ℂ) (hφ : ∀ k ∈ K, ∀ x, φ (x * k) = φ x) {x y : G}
    (hxy : (x : G ⧸ K) = y) : φ x = φ y := by
  have hK : x⁻¹ * y ∈ K := QuotientGroup.eq.mp hxy
  rw [← hφ _ hK x, mul_inv_cancel_left]

private theorem out_mk_one_mem : ((1 : G) : G ⧸ K).out ∈ K := by
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' ((1 : G) : G ⧸ K)).symm
  rwa [inv_one, one_mul] at h

private theorem sum_apply_mul_out [Fintype (G ⧸ K)] (φ : G → ℂ) (hφ : ∀ k ∈ K, ∀ x, φ (x * k) = φ x) (a : G) :
    ∑ q : G ⧸ K, φ (a * q.out) = ∑ q : G ⧸ K, φ q.out := by
  have h₁ : ∀ q : G ⧸ K, φ (a * q.out) = φ (a • q).out := fun q =>
    apply_eq_of_mk_eq_of_rightInvariant K φ hφ
      ((MulAction.Quotient.mk_smul_out K a q).trans (QuotientGroup.out_eq' (a • q)).symm)
  calc ∑ q : G ⧸ K, φ (a * q.out) = ∑ q : G ⧸ K, φ (a • q).out := Finset.sum_congr rfl fun q _ => h₁ q
    _ = ∑ q : G ⧸ K, φ q.out :=
        Fintype.sum_bijective _ (MulAction.bijective (β := G ⧸ K) a) _ _ fun _ => rfl

private theorem sum_ne_zero_of_forall_eq_zero_or_eq_one {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (h01 : ∀ i, f i = 0 ∨ f i = 1) {i₀ : ι} (hi₀ : f i₀ = 1) : ∑ i, f i ≠ 0 := by
  classical
  have hsum : ∑ i, f i = ((Finset.univ.filter fun i => f i ≠ 0).card : ℂ) := by
    rw [← Finset.sum_filter_ne_zero]
    rw [Finset.sum_congr rfl fun i hi => (h01 i).resolve_left (Finset.mem_filter.mp hi).2, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  rw [hsum]
  exact_mod_cast Finset.card_ne_zero_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, by rw [hi₀]; exact one_ne_zero⟩)

end CosetSum

section PrescribedCell

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isGL3PsiWhittakerFn_of_mem_span {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W V : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (hV : V ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ V := by
  refine (mem_gl3PsiWhittakerFnSpace_iff ψ V).mp (Submodule.span_le.mpr ?_ hV)
  rintro _ ⟨g, rfl⟩
  exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ g ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)

private theorem exists_bump_of_isCompact {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (t₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (U₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (hU₁ : IsCompact (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hψU₁ : ∀ x : v.adicCompletion ℚ, t₀⁻¹ * unipotentGL2 x * t₀ ∈ U₁ → ψ x = 1)
    (hsmall : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
      U ≤ U₁ ∧ ∃ W' ∈ gl3CyclicSubspace W,
        (∀ k ∈ U, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
          ∃ x : v.adicCompletion ℚ, ∃ k ∈ U, h = unipotentGL2 x * t₀ * k) ∧
        W' (iotaGL t₀) = 1) :
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ U₁, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ U₁, h = unipotentGL2 x * t₀ * k) ∧
      W' (iotaGL t₀) = 1 := by
  obtain ⟨U, hUo, hUle, W', hW'mem, hinv, hsupp, ht₀⟩ := hsmall
  have hW'law : IsGL3PsiWhittakerFn ψ W' := isGL3PsiWhittakerFn_of_mem_span v hW hW'mem

  haveI : CompactSpace U₁ := isCompact_iff_compactSpace.mp hU₁
  have hKo : IsOpen ((U.subgroupOf U₁ : Subgroup U₁) : Set U₁) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  haveI : Finite (U₁ ⧸ U.subgroupOf U₁) := Subgroup.quotient_finite_of_isOpen _ hKo
  haveI : Fintype (U₁ ⧸ U.subgroupOf U₁) := Fintype.ofFinite _

  set F : LocalGL3 v → ℂ :=
    ∑ q : U₁ ⧸ U.subgroupOf U₁, gl3AmbientRightTranslate (R := ℂ) (iotaGL (q.out : GL (Fin 2) (v.adicCompletion ℚ))) W'
    with hF
  have hFmem : F ∈ gl3CyclicSubspace W :=
    Submodule.sum_mem _ fun q _ => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hW'mem
  have hFiota : ∀ h : GL (Fin 2) (v.adicCompletion ℚ),
      F (iotaGL h) = ∑ q : U₁ ⧸ U.subgroupOf U₁, W' (iotaGL (h * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) := by
    intro h
    simp only [hF, Finset.sum_apply, gl3AmbientRightTranslate_apply, map_mul]

  have hφ : ∀ h : GL (Fin 2) (v.adicCompletion ℚ), ∀ k ∈ U.subgroupOf U₁, ∀ x : U₁,
      W' (iotaGL (h * ((x * k : U₁) : GL (Fin 2) (v.adicCompletion ℚ)))) =
        W' (iotaGL (h * (x : GL (Fin 2) (v.adicCompletion ℚ)))) := by
    intro h k hk x
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact hinv _ (Subgroup.mem_subgroupOf.mp hk) _

  have h01 : ∀ q : U₁ ⧸ U.subgroupOf U₁,
      W' (iotaGL (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) = 0 ∨
        W' (iotaGL (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) = 1 := by
    intro q
    by_cases hz : W' (iotaGL (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)))) = 0
    · exact Or.inl hz
    right
    obtain ⟨x, u, hu, hxu⟩ := hsupp _ hz
    have hn : unipotentGL2 x = t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)) * u⁻¹ * t₀⁻¹ :=
      eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq hxu.symm)
    have hψx : ψ x = 1 := by
      apply hψU₁
      rw [hn]
      have hgrp : t₀⁻¹ * (t₀ * (q.out : GL (Fin 2) (v.adicCompletion ℚ)) * u⁻¹ * t₀⁻¹) * t₀ =
          (q.out : GL (Fin 2) (v.adicCompletion ℚ)) * u⁻¹ := by group
      rw [hgrp]
      exact U₁.mul_mem q.out.2 (U₁.inv_mem (hUle hu))
    rw [hxu, hinv u hu, map_mul, iotaGL_unipotentGL2, hW'law x 0 0, add_zero, ht₀, hψx, mul_one]
  have hone : W' (iotaGL (t₀ * ((((1 : U₁) : U₁ ⧸ U.subgroupOf U₁).out : U₁) : GL (Fin 2) (v.adicCompletion ℚ)))) =
      1 := by
    rw [hinv _ (Subgroup.mem_subgroupOf.mp (out_mk_one_mem (U.subgroupOf U₁))), ht₀]
  have hc : F (iotaGL t₀) ≠ 0 := by
    rw [hFiota]
    exact sum_ne_zero_of_forall_eq_zero_or_eq_one _ h01 hone
  refine ⟨(F (iotaGL t₀))⁻¹ • F, Submodule.smul_mem _ _ hFmem, ?_, ?_, ?_⟩
  ·
    intro k hk h
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [hFiota, hFiota]
    have := sum_apply_mul_out (U.subgroupOf U₁)
      (fun x : U₁ => W' (iotaGL (h * (x : GL (Fin 2) (v.adicCompletion ℚ))))) (hφ h) ⟨k, hk⟩
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  ·
    intro h hne
    simp only [Pi.smul_apply, smul_eq_mul] at hne
    have hne' := right_ne_zero_of_mul hne
    rw [hFiota] at hne'
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    obtain ⟨x, u, hu, hxu⟩ := hsupp _ hq
    refine ⟨x, u * (q.out : GL (Fin 2) (v.adicCompletion ℚ))⁻¹, U₁.mul_mem (hUle hu) (U₁.inv_mem q.out.2), ?_⟩
    rw [eq_mul_inv_of_mul_eq hxu, mul_assoc]
  ·
    simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hc

end PrescribedCell

end LanglandsTunnell.CubicInduction.Kirillov

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₁ : IsCompact (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hU₁' : IsOpen (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hψU₁ : ∀ x : v.adicCompletion ℚ, t₀⁻¹ * unipotentGL2 x * t₀ ∈ U₁ → ψ x = 1) :
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ U₁, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ U₁, h = unipotentGL2 x * t₀ * k) ∧
      W' (iotaGL t₀) = 1 :=
  LanglandsTunnell.CubicInduction.Kirillov.exists_bump_of_isCompact v hW t₀ U₁ hU₁ hψU₁
    (LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump v ψ hψ W hW hsm hne t₀ U₁ hU₁')

end

end S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen (solution)
