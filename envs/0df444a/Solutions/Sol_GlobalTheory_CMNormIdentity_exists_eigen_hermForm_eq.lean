-- Prove2me | solution 1 for GlobalTheory.CMNormIdentity.exists_eigen_hermForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:35:33.148826+00:00
-- url     : https://prove2.me/submissions/5fccd1d3-5c07-4a05-b4cc-63abd9a357a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingSmul
import Theorems.Thm_GlobalTheory_CMNormIdentity_isDiff_of_isLieComb
import Theorems.Thm_GlobalTheory_CMNormIdentity_lift_unique
import Theorems.Thm_GlobalTheory_CMNormIdentity_exists_eigen_components
import Theorems.Thm_GlobalTheory_CMNormIdentity_eq_zero_of_sum_embedding_smul
import Theorems.Thm_GlobalTheory_CMNormIdentity_quadratic_eq_zero
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_right
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_right
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_conj
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_eigen
import Theorems.Thm_GlobalTheory_HomLinear_exists_linear_of_isMonHom
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_hermForm_pull_eq_of_lbIso_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CMNormIdentity
namespace GlobalTheory.CMNormIdentity
theorem _root_.solution :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (P₀ P : Out.PolAV (Sp ℂ)), P₀.g = 1 →
  ∀ (u₀ : HolUnif P₀.A P₀.L P₀.g) (u : HolUnif P.A P.L P.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u₀.IsAH H₀ χ₀ → u.IsAH Hm χ →
  (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
  ∀ (act : OAct (𝓞 E) P.A) (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (h : L → L → E) (ρ : ℂ) (φ : L → (P₀.A ⟶ P.A))
    (v₀ : epsR ℂ ⟶ P₀.A) (w₀ : Fin P₀.g → ℂ) (m : ℕ) (e : Fin m → L) (nn : L → ℕ),
  ρ ^ 2 = -(H.d : ℂ) → (∀ a b c, h (a + b) c = h a c + h b c) → (∀ (s : 𝓞 E) a c, h (s • a) c = s * h a c) →
  (∀ a b, h b a = IsCMField.complexConj E (h a b)) →
  (∀ a, (nn a : ℂ) = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a a)) →
  (∀ a, IsMonHom (φ a)) → (∀ a b, φ (a + b) = φ a * φ b) → (∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ act.act s) →
  IsTangent v₀ → u₀.IsDiff w₀ v₀ → (∀ a, IsLieComb ![ρ] ![v₀ ≫ φ a] (v₀ ≫ φ a ≫ act.act H.rt)) →
  Submodule.span ℤ (Set.range e) = ⊤ →
  (∀ a, ((∃ i, a = e i) ∨ ∃ i j, a = e i + e j) →
    ∃ N : ℕ, 1 ≤ N ∧ LBIso (lbPow (P.L.pull (φ a).left) N) (lbPow P₀.L (N * nn a))) →
  ∃ x : (E →+* ℂ) → L →+ (Fin P.g → ℂ), (∀ a, u.IsDiff (∑ τ, x τ a) (v₀ ≫ φ a)) ∧
    (∀ τ (s : 𝓞 E) a, x τ (s • a) = τ (s : E) • x τ a) ∧ (∀ τ, τ (H.rt : E) ≠ ρ → x τ = 0) ∧
    ∀ τ τ' a b, τ (H.rt : E) = ρ →
      hermForm Hm (x τ a) (x τ' b) = open Classical in if τ' = τ then hermForm H₀ w₀ w₀ * τ (h a b) else 0 := by
  intro E _ _ _ H P₀ P _ u₀ u H₀ χ₀ Hm χ hu₀ hu hT hT' act L _ _ h ρ φ v₀ w₀ m e nn hρ hadd hsmul hsymm hnn hφ hφa hφs
    hv₀ hw₀ hLie he hiso
  classical
  choose F hF _ hFd _ using fun a =>
    GlobalTheory.HomLinear.exists_linear_of_isMonHom P₀.A P.A P₀.isAb P.isAb P₀.L P.L P₀.g P.g u₀ u hT hT' (φ a) (hφ a)
  have hFa : ∀ a b, F (a + b) = F a + F b := fun a b => lift_unique u _ _ fun z => by
    rw [LinearMap.add_apply, u.ex_add, hF, hF, hF, hφa, MonObj.comp_mul]
  let X : L →+ (Fin P.g → ℂ) := AddMonoidHom.mk' (fun a => F a w₀) fun a b => by
    rw [hFa, LinearMap.add_apply]
  have hX : ∀ a, X a = F a w₀ := fun _ => rfl
  have hXd : ∀ a, u.IsDiff (X a) (v₀ ≫ φ a) := fun a => (hFd a w₀ v₀ hv₀ hw₀).2
  have hXrt : ∀ a, X (H.rt • a) = ρ • X a := fun a => by
    refine (hT _ (hFd (H.rt • a) w₀ v₀ hv₀ hw₀).1).unique (hXd _) ?_
    rw [hφs]
    exact isDiff_of_isLieComb u (hXd a) ρ (hLie a)
  obtain ⟨x, hx⟩ := exists_eigen_components (E := E) X
  have hsum : ∀ a, ∑ τ, x τ a = X a := fun a => by
    simpa using (hx 1 a).symm
  have hxs : ∀ τ (s : 𝓞 E) a, x τ (s • a) = τ (s : E) • x τ a := fun τ s a => by
    refine sub_eq_zero.1 (eq_zero_of_sum_embedding_smul (fun τ => x τ (s • a) - τ (s : E) • x τ a) (fun t => ?_) τ)
    have h1 := hx (t * s) a
    rw [mul_smul, hx] at h1
    simp only [smul_sub, Finset.sum_sub_distrib, h1, smul_smul]
    simp
  have hx0 : ∀ τ, τ (H.rt : E) ≠ ρ → x τ = 0 := fun τ hτ => by
    ext1 a
    have := eq_zero_of_sum_embedding_smul (fun τ => (τ (H.rt : E) - ρ) • x τ a) (fun t => by
      have h1 := hx (H.rt * t) a
      rw [mul_smul, hXrt, hx, Finset.smul_sum] at h1
      simp only [sub_smul, smul_sub, smul_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [smul_smul, mul_comm] using h1.symm) τ
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hτ)
  have hc : (((hermForm H₀ w₀ w₀).re : ℝ) : ℂ) = hermForm H₀ w₀ w₀ :=
    Complex.conj_eq_iff_re.1 (EigenNorm.hermForm_conj H₀ hu₀.1 w₀ w₀).symm
  refine ⟨x, fun a => hsum a ▸ hXd a, hxs, hx0, ?_⟩
  rw [← hc]
  refine EigenNorm.hermForm_eigen E H P.g Hm hu.1 L h ρ _ x hρ hadd hsmul hsymm hxs hx0 fun a => ?_
  rw [hc, hsum]
  have haddr : ∀ a b c, h a (b + c) = h a b + h a c := fun a b c => by
    rw [hsymm (b + c) a, hsymm b a, hsymm c a, hadd, map_add]
  have key : ∀ a, ((∃ i, a = e i) ∨ ∃ i j, a = e i + e j) → hermForm Hm (X a) (X a) - hermForm H₀ w₀ w₀ *
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a a) = 0 := fun a ha => by
    obtain ⟨N, hN, hiso⟩ := hiso a ha
    have h1 := hermForm_pull_eq_of_lbIso_pow P₀.A P.A P₀.L P.L P₀.isLB P.isLB P₀.g P.g u₀ u H₀ χ₀ Hm χ hu₀ hu
      (φ a) (F a) (hF a) N (N * nn a) hiso w₀ w₀
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [← hnn, hX]
    apply mul_left_cancel₀ hN'
    push_cast at h1
    linear_combination h1
  exact sub_eq_zero.1 (quadratic_eq_zero (fun a b => hermForm Hm (X a) (X b) - hermForm H₀ w₀ w₀ *
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a b))
    (fun a b c => by
      simp only [map_add, EigenNorm.hermForm_add_left, hadd, Finset.sum_add_distrib]; ring)
    (fun a b c => by
      simp only [map_add, EigenNorm.hermForm_add_right, haddr, Finset.sum_add_distrib]; ring)
    e he (fun i => key _ (Or.inl ⟨i, rfl⟩)) (fun i j => key _ (Or.inr ⟨i, j, rfl⟩)) a)
end GlobalTheory.CMNormIdentity
