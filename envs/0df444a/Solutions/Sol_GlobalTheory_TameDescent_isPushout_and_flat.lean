-- Prove2me | solution 1 for GlobalTheory.TameDescent.isPushout_and_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:53.503551+00:00
-- url     : https://prove2.me/submissions/6c1d6be8-8b46-436e-bc14-68bea2ec7acd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemMapKerOfOneTmulEqZeroOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPullbackFlatOfTame
import Theorems.Thm_GlobalTheory_TameDescent_specMap_fromSpec_comp_eq_iff
import Theorems.Thm_GlobalTheory_TameDescent_appLE_sub_mem_map
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_T_invariant_tower_isPushout
import Theorems.Thm_GlobalTheory_exists_finsum_smul_eq_one_of_tame
import Theorems.Thm_GlobalTheory_flat_of_tame_descent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameDescent
namespace GlobalTheory.TameDescent
theorem _root_.solution {Γ : Type} [Group Γ] [Finite Γ] {X X' Y Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsFinite π] [IsFinite φ] [Flat p]
    (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hπ' : ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
      (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (π.app V).hom)
    (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hφ' : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (w : φ ≫ p' = p ≫ π) (hp : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x →
      pullback.fst p x ≫ (τ g).hom = pullback.fst p x)
    (V : X'.Opens) (W : Y'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V) :
    IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e') ∧
      (p'.appLE V W e).hom.Flat := by
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hU' : IsAffineOpen (φ ⁻¹ᵁ W) := hW.preimage φ
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ W
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  let := (π.app V).hom.toAlgebra
  let := (φ.app W).hom.toAlgebra
  let := (p'.appLE V W e).hom.toAlgebra
  let := (p.appLE _ _ e').hom.toAlgebra
  let := (p'.appLE V W e ≫ φ.app W).hom.toAlgebra
  have sq : p'.appLE V W e ≫ φ.app W = π.app V ≫ p.appLE _ _ e' := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w]
  have : IsScalarTower Γ(X', V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) :=
    .of_algebraMap_eq' congr(($sq).hom)
  have : SMulCommClass Γ Γ(X', V) Γ(X, π ⁻¹ᵁ V) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(X', V) Γ(X, π ⁻¹ᵁ V) a = algebraMap _ _ a :=
      (isInvariantSection_app ρ π hπ V a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : SMulCommClass Γ Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) a = algebraMap _ _ a :=
      (isInvariantSection_app τ φ hφ W a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ := ⟨fun s hs ↦
    (hπ' V).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩
  have : Algebra.IsInvariant Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    (hφ' W).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (τ g⁻¹⁻¹).hom.appLE _ _ (hst' _) s = s from hs g⁻¹)⟩
  have heq : ∀ (g : Γ) (b : Γ(X, π ⁻¹ᵁ V)), g • algebraMap _ Γ(Y, φ ⁻¹ᵁ W) b =
      algebraMap _ Γ(Y, φ ⁻¹ᵁ W) (g • b) := fun g b => by
    change (τ g⁻¹).hom.appLE _ _ (hst' _) (p.appLE _ _ e' b) =
      p.appLE _ _ e' ((ρ g⁻¹).hom.appLE _ _ (hst _) b)
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hp]
  have hflat : Module.Flat Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) := p.flat_appLE hU hU' e'
  have key : ∀ q : Ideal Γ(X, π ⁻¹ᵁ V), q.IsPrime → ((Nat.card (q.inertia Γ) : Γ(X, π ⁻¹ᵁ V)) ∉ q) ∧
      ∀ g ∈ q.inertia Γ, ∀ c : Γ(Y, φ ⁻¹ᵁ W), g • c - c ∈ q.map (algebraMap _ Γ(Y, φ ⁻¹ᵁ W)) := by
    intro q hq
    let k := AlgebraicClosure q.ResidueField
    let a : Γ(X, π ⁻¹ᵁ V) →+* k := (algebraMap q.ResidueField k).comp (algebraMap _ _)
    have ha : ∀ b, a b = 0 ↔ b ∈ q := fun b => by
      simp [a]
    have hker : RingHom.ker a = q := Ideal.ext ha
    let x : Sp k ⟶ X := Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec
    have hx : ∀ g, x ≫ (ρ g⁻¹).hom = x ↔ g ∈ q.inertia Γ := fun g =>
      (specMap_fromSpec_comp_eq_iff _ hU (hst _) _).trans (forall_congr' fun b => ha _)
    refine ⟨fun h => htame k x ?_, fun g hg c => ?_⟩
    · rw [← Nat.card_congr ((Equiv.inv Γ).subtypeEquiv (p := fun g => g ∈ q.inertia Γ)
        (q := fun g => x ≫ (ρ g).hom = x) fun g => (hx g).symm), ← map_natCast a]
      exact (ha _).2 h
    · rw [← hker]
      exact appLE_sub_mem_map p _ hU hU' e' (hst' _) a (hfix k x _ ((hx g).2 hg)) c
  have hpo : Algebra.IsPushout Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) :=
    GlobalTheory.T.invariant_tower_isPushout Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq
      (IsLocallyNoetherian.component_noetherian ⟨W, hW⟩) (π.finite_app V hV) (φ.finite_app W hW)
      hflat (fun q hq => (key q hq).1) (fun q hq => (key q hq).2)
  refine ⟨CommRingCat.isPushout_iff_isPushout.2 hpo.symm, ?_⟩
  exact flat_of_tame_descent Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq hpo hflat
    (exists_finsum_smul_eq_one_of_tame Γ _ fun q hq => (key q hq).1)
end GlobalTheory.TameDescent
