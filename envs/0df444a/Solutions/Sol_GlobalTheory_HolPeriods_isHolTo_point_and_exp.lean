-- Prove2me | solution 1 for GlobalTheory.HolPeriods.isHolTo_point_and_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:54:06.117479+00:00
-- url     : https://prove2.me/submissions/24b1dde3-2e61-484b-ab9c-a533d2af4d5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsHolToPointAndExp
import Theorems.Thm_GlobalTheory_HolPeriods_Uniformises_comp_equiv
import Theorems.Thm_GlobalTheory_HolPeriods_exists_differentiableOn_transfer
import Theorems.Thm_GlobalTheory_HolPeriods_exists_local_section
import Theorems.Thm_GlobalTheory_HolPeriods_isHolTo_comp
import Theorems.Thm_GlobalTheory_HolPeriods_isHolTo_congr
import Theorems.Thm_GlobalTheory_HolPeriods_isHolTo_of_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolPeriods
namespace GlobalTheory.HolPeriods
theorem _root_.solution : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' D''
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t' : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ)) (P'
    : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (e'
    : (Fin g → ℂ) → (Over.mk y' ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧
    ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left)
    ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y' ≫ Xo.s = spMap σ ∧ IsPeriod
    D'' ty P' ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ
    (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y' ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e'
    z).left) w v.left) ∧ (∀ v : epsPt y' ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧
    (∀ z, e' z = 1 ↔ z ∈ (P').range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a
    : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D''.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D''.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P'
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P' (t' a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P' (t' a))) → (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞
    E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D''.EF (gam a) (gam
    b) = D'.EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧ (∀ a, ∃ x, gam (t
    a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a))) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P
    : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶
    Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧
    ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left)
    ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y ≫ Xo.s = spMap σ ∧ IsPeriod D'
    ty P ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ
    (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e'
    z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧
    (∀ z, e' z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a
    : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P a)) (e' ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P (t a))) → e = e') → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ
    : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀
    : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P₀ → ∃ (Z : (D.La →+ (Fin g →
    ℂ)) → (Fin D.dim → ℂ)) (s : Finset D.La) (ε : ℝ), 0 < ε ∧ (∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D.La →+ (Fin g →
    ℂ))), IsOpen B → IsHolPeriods D ty B P → (∀ b ∈ B, ∀ x ∈ s, ‖P b x - P₀ x‖ < ε) → DifferentiableOn ℂ (fun b => Z (P
    b)) B) ∧ ∀ P P' : D.La →+ (Fin g →
    ℂ), IsPeriod D ty P → IsPeriod D ty P' → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → (∀ x ∈ s, ‖P' x - P₀ x‖ < ε) → Z P = Z P' → ∃ h : (Fin
    g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, P' a = h (P a)) ∧ ∀ (a : 𝓞 E) z, h (fun k => ty k (a
    : E) * z k) = fun k => ty k (a : E) * h z k) → (∀ (n : ℕ) (U : Set (Fin n → ℂ)) (f : (Fin n →
    ℂ) → (Fin n →
    ℂ)), IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U → ∀ a ∈ U, Function.Bijective (fderiv ℂ f
    a)) → (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀
    : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y
    : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X,
    U)), IsOpen B ∧ (0
    : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r
    i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField
    E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D'
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+
    (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) /
    l.A) ∧ t = f l.M') → IsOpen B → IsHolPeriods D' ty B P → (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧
    IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧
    IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → IsHolTo B y ∧ IsHolTo (B
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  intro hUniq hExp hLift hCoord hOpen hChart E _ _ _ H D l Xo σ g ty hpq hσ hty D' t m B P y e hgen hB hP hU
  have hU' : ∀ b ∈ B, Uniformises Xo σ ty D' t (P b) (y b) (e b) := hU
  have uniq : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ Xo.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ Xo.univ.t.G)},
      Uniformises Xo σ ty D' t Q x u → Uniformises Xo σ ty D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) → x = x' := by
    intro Q Q' x x' u u' h h' k hk
    exact (hUniq E H D l Xo σ g ty hpq hσ hty D' D' t t Q Q' x x' u u' h h').2
      ⟨LinearEquiv.refl _ _, k, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hk⟩
  have expo : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ Xo.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ Xo.univ.t.G)},
      Uniformises Xo σ ty D' t Q x u → Uniformises Xo σ ty D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) →
      (∀ (a : 𝓞 E) z, k (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * k z i) →
      ∀ z, (show Sp ℂ ⟶ Xo.univ.t.G.left from (u z).left) = (u' (k z)).left := by
    intro Q Q' x x' u u' h h' k hk hlin z
    obtain rfl := uniq h h' k hk
    have := hExp E H D l Xo σ g ty hpq hσ hty D' t Q x u (fun z => u' (k z)) hgen h
      (h'.comp_equiv h.2.1 k hk hlin)
    rw [this]
  have hdim : D'.dim = D.dim := by simp only [Datum.dim, hgen.1, hgen.2.1]
  have hsm : SmoothOfRelativeDimension D'.dim Xo.s := hdim ▸ Xo.smooth
  have hty' : IsTypeFn H D'.p D'.q ty := by rw [hgen.1, hgen.2.1]; exact hty
  have near : ∀ {n : ℕ} {C : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → (D'.La →+ (Fin g → ℂ))}
      (P₀ : D'.La →+ (Fin g → ℂ)) (s : Finset D'.La) (ε : ℝ), IsOpen C → IsHolPeriods D' ty C R →
      IsOpen {c | c ∈ C ∧ ∀ x ∈ s, ‖R c x - P₀ x‖ < ε} := by
    intro n C R P₀ s ε hC hR
    refine isOpen_iff_mem_nhds.2 fun c hc => ?_
    refine Filter.Eventually.and (hC.mem_nhds hc.1) ((Filter.eventually_all_finset s).2 fun x hx => ?_)
    have : ContinuousAt (fun c => ‖R c x - P₀ x‖) c :=
      (((hR.2 x).continuousOn.continuousAt (hC.mem_nhds hc.1)).sub continuousAt_const).norm
    exact this.eventually_lt continuousAt_const (hc.2 x hx)
  have loc : ∀ b₀ ∈ B, ∃ B' : Set (Fin m → ℂ), b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y ∧
      IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
    intro b₀ hb₀
    obtain ⟨C₀, y₁, -, -, -, -, hC₀, h0, hy0, hover, hhol, hinj, -⟩ :=
      hChart (KA l) σ Xo.X Xo.s D'.dim (y b₀) hsm (hU' b₀ hb₀).1
    obtain ⟨e₀, he₀⟩ : ∃ e₀, Uniformises Xo σ ty D' t (P b₀) (y₁ 0) e₀ := by
      rw [hy0]; exact ⟨_, hU' b₀ hb₀⟩
    obtain ⟨C₁, P₁, e₁, hC₁, h01, hsub, hP0, hP₁, he₁, hU₁⟩ :=
      hLift E H D l Xo σ g ty hpq hσ hty D' t D'.dim C₀ y₁ 0 (P b₀) e₀ hC₀ h0 hover hhol he₀
    have hU₁' : ∀ c ∈ C₁, Uniformises Xo σ ty D' t (P₁ c) (y₁ c) (e₁ c) := hU₁
    obtain ⟨Z, s, ε, hε, hZ, hZinj⟩ := hCoord E H D' g ty (P b₀) hty' (hP.1 b₀ hb₀)
    set C₂ := {c | c ∈ C₁ ∧ ∀ x ∈ s, ‖P₁ c x - P b₀ x‖ < ε} with hC₂def
    have hC₂ : IsOpen C₂ := near (P b₀) s ε hC₁ hP₁
    have h02 : (0 : Fin D'.dim → ℂ) ∈ C₂ := ⟨h01, fun x _ => by simpa [hP0] using hε⟩
    have hF : DifferentiableOn ℂ (fun c => Z (P₁ c)) C₂ :=
      hZ _ C₂ P₁ hC₂ ⟨fun c hc => hP₁.1 c hc.1, fun x => (hP₁.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    have hFinj : Set.InjOn (fun c => Z (P₁ c)) C₂ := by
      intro c hc c' hc' hcc
      obtain ⟨k, hk, -⟩ := hZinj _ _ (hP₁.1 c hc.1) (hP₁.1 c' hc'.1) hc.2 hc'.2 hcc
      exact hinj (hsub hc.1) (hsub hc'.1) (uniq (hU₁' c hc.1) (hU₁' c' hc'.1) k hk)
    obtain ⟨W, G, hW, hW0, hG, hGW⟩ :=
      exists_local_section hC₂ hF h02 (hOpen _ C₂ _ hC₂ hF hFinj 0 h02)
    set B₁ := {b | b ∈ B ∧ ∀ x ∈ s, ‖P b x - P b₀ x‖ < ε} with hB₁def
    have hB₁ : IsOpen B₁ := near (P b₀) s ε hB hP
    have hZP : DifferentiableOn ℂ (fun b => Z (P b)) B₁ :=
      hZ _ B₁ P hB₁ ⟨fun c hc => hP.1 c hc.1, fun x => (hP.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    set B₂ := B₁ ∩ (fun b => Z (P b)) ⁻¹' W with hB₂def
    have hB₂ : IsOpen B₂ := hZP.continuousOn.isOpen_inter_preimage hB₁ hW
    have hb₂ : b₀ ∈ B₂ := ⟨⟨hb₀, fun x _ => by simpa using hε⟩, by simpa [hP0] using hW0⟩
    have hβ : DifferentiableOn ℂ (fun b => G (Z (P b))) B₂ :=
      hG.comp (hZP.mono Set.inter_subset_left) fun b hb => hb.2
    have hβC : ∀ b ∈ B₂, G (Z (P b)) ∈ C₂ := fun b hb => (hGW _ hb.2).1
    have hk : ∀ b, ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), b ∈ B₂ → (∀ a, P₁ (G (Z (P b))) a = k (P b a)) ∧
        ∀ (a : 𝓞 E) z, k (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * k z i := by
      intro b
      by_cases hb : b ∈ B₂
      · obtain ⟨k, hk⟩ := hZinj _ _ (hP.1 b hb.1.1) (hP₁.1 _ (hβC b hb).1) hb.1.2 (hβC b hb).2
          (hGW _ hb.2).2.symm
        exact ⟨k, fun _ => hk⟩
      · exact ⟨LinearEquiv.refl _ _, fun h => absurd h hb⟩
    choose k hk using hk
    obtain ⟨B₃, hB₃, hb₃, hsub₃, hkd⟩ := exists_differentiableOn_transfer (Q := P)
      (Q' := fun b => P₁ (G (Z (P b)))) hB₂ (fun x => (hP.2 x).mono fun b hb => hb.1.1)
      (fun x => (hP₁.2 x).comp hβ fun b hb => (hβC b hb).1) hb₂ (hP.1 b₀ hb₀).2.2.2.1
      (fun b => (k b).toLinearMap) fun b hb x => (hk b hb).1 x
    refine ⟨B₃, hb₃, fun b hb => (hsub₃ hb).1.1, ?_, ?_⟩
    · refine isHolTo_congr (isHolTo_comp hhol hB₃ (hβ.mono hsub₃)
        fun b hb => hsub (hβC b (hsub₃ hb)).1) fun b hb => ?_
      exact uniq (hU' b (hsub₃ hb).1.1) (hU₁' _ (hβC b (hsub₃ hb)).1) (k b) (hk b (hsub₃ hb)).1
    · have hφ : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (G (Z (P bz.1)), k bz.1 bz.2))
          (B₃ ×ˢ Set.univ) :=
        (hβ.comp differentiableOn_fst fun bz hbz => hsub₃ hbz.1).prodMk hkd
      refine isHolTo_congr (isHolTo_comp he₁ (hB₃.prod isOpen_univ) hφ
        fun bz hbz => ⟨(hβC _ (hsub₃ hbz.1)).1, trivial⟩) fun bz hbz => ?_
      exact expo (hU' _ (hsub₃ hbz.1).1.1) (hU₁' _ (hβC _ (hsub₃ hbz.1)).1) (k bz.1)
        (hk _ (hsub₃ hbz.1)).1 (hk _ (hsub₃ hbz.1)).2 bz.2
  refine ⟨isHolTo_of_local fun b hb => ?_, isHolTo_of_local fun bz hbz => ?_⟩
  · obtain ⟨B', h1, h2, h3, -⟩ := loc b hb
    exact ⟨B', h1, h2, h3⟩
  · obtain ⟨B', h1, h2, -, h4⟩ := loc bz.1 hbz.1
    exact ⟨B' ×ˢ Set.univ, ⟨h1, trivial⟩, Set.prod_mono h2 le_rfl, h4⟩
end GlobalTheory.HolPeriods
