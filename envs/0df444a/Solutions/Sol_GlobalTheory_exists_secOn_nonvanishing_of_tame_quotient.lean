-- Prove2me | solution 1 for GlobalTheory.exists_secOn_nonvanishing_of_tame_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:54:57.254616+00:00
-- url     : https://prove2.me/submissions/f5664f6d-6c4c-4bd2-a1d0-ddb5ecce9e5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_resG
import Theorems.Thm_GlobalTheory_DescTheta_nonvanishing_iso
import Theorems.Thm_GlobalTheory_DescTheta_exists_nhds_nonvanishing
import Theorems.Thm_GlobalTheory_DescTheta_exists_sec_nonvanishing
import Theorems.Thm_GlobalTheory_DescTheta_nonvanishing_pullSec
import Theorems.Thm_GlobalTheory_DescTheta_exists_descent_nonvanishing
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_quotient_flat_baseChange
import Theorems.Thm_GlobalTheory_quotient_isIntegral_surjective_orbits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open DescTheta GlobalTheory.LB
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (L : LB G.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ G.hom = G.hom ≫ (ρ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst G.hom x ≫ (τ g).hom = pullback.fst G.hom x) → L.IsLB → L'.IsLB → LBIso L (L'.pull φ) → PushInvertible G L → (∀ x : X', ∃ V : X'.Opens, x ∈ V ∧ ∃ θ ∈ secOn L' (G'.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G'.left) (i : L'.ι), G'.hom g = y ∧ g ∈ G'.left.basicOpen (θ i)) := by
  intro Γ _ _ X X' ρ π G G' φ τ L L' hQ H hflat hτ htame hfib hL hL' ⟨w, hw⟩ hP x'
  obtain ⟨-, hφ, hq⟩ := (quotient_flat_baseChange Γ X X' _ _ ρ π φ G.hom G'.hom hQ H hflat).2 τ hτ
  obtain ⟨-, hsurj, -, -, hopen⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨_, hπ, -⟩ := hQ
  have hM := Semi.LB.isLB_pull hL' φ
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := IsAffineOpen.preimage hV π
  obtain ⟨x, rfl⟩ := π.surjective x'
  have e : φ ⁻¹ᵁ G'.hom ⁻¹ᵁ V = G.hom ⁻¹ᵁ π ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  obtain ⟨s, u, rfl, i, hi⟩ := exists_sec_nonvanishing hP hW hx
  obtain ⟨t, ht⟩ := exists_descent_nonvanishing ρ π G.hom G'.hom φ τ hπ H.w hφ (fun g => (hτ g).2)
    hq htame hfib hW ((isoOfGen hL hM w hw).hom.app _ ((toMod L).presheaf.map (homOfLE e.le).op s))
    u ((nonvanishing_iso hL hM w hw _ u).2 ⟨i, by
      rw [coord_map, mem_basicOpen_resG]
      exact ⟨⟨e.ge hx, (G.left.basicOpen_le _ hi).2⟩, hi⟩⟩)
  obtain ⟨s', hs'⟩ := (ConcreteCategory.bijective_of_isIso
    ((isoOfGen hL hM w hw).hom.app (φ ⁻¹ᵁ G'.hom ⁻¹ᵁ V))).2 (pullSec L' φ _ t)
  have key (y : G.left) : (∃ i, y ∈ G.left.basicOpen (coord s' i)) ↔
      ∃ i, φ y ∈ G'.left.basicOpen (coord t i) := by
    rw [← nonvanishing_iso hL hM w hw, hs', nonvanishing_pullSec]
  obtain ⟨U, -, hxU, hU⟩ := exists_nhds_nonvanishing hP e.ge s' u hx ((key u).2 ht)
  obtain ⟨V', hV'⟩ := hopen (⨆ g, (ρ g).hom ⁻¹ᵁ U) fun g => by
    have (h : Γ) : (ρ g).hom ⁻¹ᵁ (ρ h).hom ⁻¹ᵁ U = (ρ (h * g)).hom ⁻¹ᵁ U := by
      rw [map_mul]; rfl
    simp only [Scheme.Hom.preimage_iSup, this]
    exact Equiv.iSup_comp (g := fun h => (ρ h).hom ⁻¹ᵁ U) (Equiv.mulRight g)
  have hle : G'.hom ⁻¹ᵁ (V ⊓ V') ≤ G'.hom ⁻¹ᵁ V := G'.hom.preimage_mono inf_le_left
  refine ⟨V ⊓ V', ⟨hx, hV'.ge (TopologicalSpace.Opens.mem_iSup.2 ⟨1, ?_⟩)⟩, _,
    coord_mem ((toMod L').presheaf.map (homOfLE hle).op t), fun y hy => ?_⟩
  · rw [map_one]; exact hxU
  obtain ⟨z, rfl⟩ := π.surjective y
  obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV'.le hy.2)
  obtain ⟨v, hv, hv'⟩ := hU _ hg
  obtain ⟨j, hj⟩ := (key v).1 hv'
  have e2 : G'.hom (φ v) = π z := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply, hπ]
  refine ⟨φ v, j, e2, ?_⟩
  rw [coord_map, mem_basicOpen_resG]
  exact ⟨⟨by rw [← e2] at hy; exact hy, (G'.left.basicOpen_le _ hj).2⟩, hj⟩
end GlobalTheory
