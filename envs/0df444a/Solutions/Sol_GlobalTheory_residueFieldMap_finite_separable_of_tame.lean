-- Prove2me | solution 1 for GlobalTheory.residueFieldMap_finite_separable_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:12:58.26324+00:00
-- url     : https://prove2.me/submissions/4111d503-bf80-49d4-a608-5b64bea86a0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ResidueFieldMapFiniteSeparableOfTame
import Theorems.Thm_GlobalTheory_isFractionRing_residueField
import Theorems.Thm_GlobalTheory_TameResidue_residue_finite_separable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    (ht : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (x : X) :
    letI := (π.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (X'.residueField (π x)) (X.residueField x) ∧
      Algebra.IsSeparable (X'.residueField (π x)) (X.residueField x) := by
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨_, ⟨(W : X'.Opens), hW, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π x)) isOpen_univ
  have hx : π x ∈ W := hx
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have hst := preimage_le_of_invariant ρ π hπ W
  let := sectionsAction ρ _ hst
  let := (π.app W).hom.toAlgebra
  have hfix (g : Γ) (a : Γ(X', W)) : g • algebraMap Γ(X', W) Γ(X, π ⁻¹ᵁ W) a = algebraMap _ _ a :=
    (isInvariantSection_app ρ π hπ W a g⁻¹).2
  have : SMulCommClass Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', W) Γ(X, π ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    hinv W hW s fun g ↦ ⟨hst g, by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩⟩
  let ev := X.evaluation (π ⁻¹ᵁ W) x hx
  let q : Ideal Γ(X, π ⁻¹ᵁ W) := RingHom.ker ev.hom
  have : q.IsPrime := RingHom.ker_isPrime _
  have hq : ∀ a, a ∈ q ↔ ev a = 0 := fun a ↦ Iff.rfl
  have hnat (a : Γ(X', W)) : π.residueFieldMap x (X'.evaluation W (π x) hx a) = ev (π.app W a) :=
    Scheme.evaluation_naturality_apply π x hx a
  have hp : ∀ a, a ∈ q.under Γ(X', W) ↔ X'.evaluation W (π x) hx a = 0 := fun a ↦ by
    rw [← map_eq_zero_iff _ (π.residueFieldMap x).hom.injective, hnat]
    rfl
  let := (Ideal.Quotient.lift q ev.hom fun a ha ↦ (hq a).1 ha).toAlgebra
  let := (Ideal.Quotient.lift _ (X'.evaluation W (π x) hx).hom fun a ha ↦ (hp a).1 ha).toAlgebra
  have := isFractionRing_residueField hU x hx q hq
  have := isFractionRing_residueField hW (π x) hx _ hp
  refine TameResidue.residue_finite_separable Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) q _ _ hnat fun hc ↦ ?_
  let Ω := AlgebraicClosure (X.residueField x)
  let jΩ : X.residueField x ⟶ CommRingCat.of Ω := CommRingCat.ofHom (algebraMap (X.residueField x) Ω)
  let y : Sp Ω ⟶ X := Spec.map (ev ≫ jΩ) ≫ hU.fromSpec
  have key (g : Γ) : g⁻¹ ∈ q.inertia Γ ↔ y ≫ (ρ g).hom = y := by
    have e : y ≫ (ρ g).hom = Spec.map ((ρ g).hom.appLE _ _ (hst g) ≫ ev ≫ jΩ) ≫ hU.fromSpec := by
      rw [Spec.map_comp, Category.assoc, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hU]
    have : Mono jΩ := ConcreteCategory.mono_of_injective _ jΩ.hom.injective
    rw [e, cancel_mono, Spec.map_inj, ← Category.assoc, cancel_mono]
    have e₂ (s) : g⁻¹ • s = (ρ g).hom.appLE _ _ (hst g) s := by
      change (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = _
      simp only [inv_inv]
    refine Iff.trans AddSubgroup.mem_inertia ⟨fun h ↦ ?_, fun h s ↦ ?_⟩
    · ext s
      have := (hq _).1 (h s)
      rw [map_sub, sub_eq_zero, e₂] at this
      exact this
    · refine (hq _).2 ?_
      rw [map_sub, sub_eq_zero, e₂]
      exact congr($h s)
  have hcard : Nat.card {g // y ≫ (ρ g).hom = y} = Nat.card (q.inertia Γ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g ↦ (key g).symm.trans (inv_mem_iff (H := q.inertia Γ)))
  apply ht Ω y
  rw [hcard]
  have := congrArg jΩ.hom ((hq _).1 hc)
  simpa using this
end GlobalTheory
