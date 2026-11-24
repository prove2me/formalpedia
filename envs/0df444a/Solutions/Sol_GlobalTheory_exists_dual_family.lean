-- Prove2me | solution 1 for GlobalTheory.exists_dual_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:13:48.818351+00:00
-- url     : https://prove2.me/submissions/0d45a2b6-e85c-413c-b55e-8710b0904429

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_symm
import Theorems.Thm_GlobalTheory_DualFamily_isIntegral_cc
import Theorems.Thm_GlobalTheory_DualFamily_exists_herm_eq
import Theorems.Thm_GlobalTheory_DualFamily_span_eq_top
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace DualFamily
end DualFamily
open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in
private lemma exists_linearForm_extend_of_span_eq_univ {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (g : Λ →ₗ[𝓞 E] 𝓞 E) :
    ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y : Λ, φ y = g y := by
  obtain ⟨t, htΛ, hts, hli⟩ := exists_linearIndependent E (Λ : Set (Fin n → E))
  let b : Module.Basis t E (Fin n → E) :=
    Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hts, hspan]))
  have hb : ∀ i, b i ∈ Λ := fun i => by rw [Module.Basis.mk_apply]; exact htΛ i.2
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  refine ⟨b.constr E fun i => ((g ⟨b i, hb i⟩ : 𝓞 E) : E), fun y => ?_⟩
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ (b.repr y)
  have hd' : ∀ i, ∃ x : 𝓞 E, algebraMap (𝓞 E) E x = (d : 𝓞 E) • b.repr y i :=
    fun i => hd i (Finset.mem_univ _)
  choose a ha using hd'
  have hdy : (d : 𝓞 E) • y = ∑ i, a i • (⟨b i, hb i⟩ : Λ) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_sum]
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul E (a i), ha i, smul_assoc]
  have hg := congrArg (fun z => ((g z : 𝓞 E) : E)) hdy
  simp only [map_smul, map_sum, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul] at hg
  simp only [RingOfIntegers.coe_eq_algebraMap]
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  apply mul_left_cancel₀ hd0
  rw [hg]
  conv_lhs => rw [← b.sum_repr (y : Fin n → E)]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, ha i, smul_eq_mul, Algebra.smul_def]
  ring
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ ∃ (m : ℕ) (v w : Fin m → Fin n → E),
      (∀ i, v i ∈ Λ) ∧ (∀ i, w i ∈ Λ) ∧ ∀ u : Fin n → E, u = ∑ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u (w i) • v i := by
  have hspan := _root_.GlobalTheory.DualFamily.span_eq_top Λ hfg hdual
  refine ⟨hspan, ?_⟩
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have := Module.finitePresentation_of_finite (𝓞 E) Λ
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hext : ∀ j : Fin m, ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y (hy : y ∈ Λ), φ y = σ ⟨y, hy⟩ j :=
    fun j => (exists_linearForm_extend_of_span_eq_univ Λ hspan ((LinearMap.proj j).comp σ)).imp
      fun φ h y hy => h ⟨y, hy⟩
  choose φ hφ using hext
  choose w hw using fun j => _root_.GlobalTheory.DualFamily.exists_herm_eq (φ j)
  let v : Fin m → Fin n → E := fun j => (π fun k => if j = k then 1 else 0 : Λ)
  refine ⟨m, v, w, fun j => (π _).2, fun j => hdual _ fun y hy => ?_, fun u => ?_⟩
  · rw [_root_.GlobalTheory.DualFamily.herm_one_symm, ← hw, hφ j y hy]
    exact _root_.GlobalTheory.DualFamily.isIntegral_cc (RingOfIntegers.isIntegral_coe _)
  · have hL : (∑ j, (φ j).smulRight (v j)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun y hy => ?_
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have hy' : y = ((π (σ ⟨y, hy⟩) : Λ) : Fin n → E) := by
        rw [← LinearMap.comp_apply, hσ]
        rfl
      conv_rhs => rw [hy', π.pi_apply_eq_sum_univ]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hφ j y hy, RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    have hu := congrArg (fun L : (Fin n → E) →ₗ[E] (Fin n → E) => L u) hL
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply, hw] at hu
    exact hu.symm
end _root_.GlobalTheory
end GlobalTheory
