-- Prove2me | solution 1 for GlobalTheory.DescTheta.exists_descent_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:34:21.208415+00:00
-- url     : https://prove2.me/submissions/2a25bfb2-dc0d-4f46-9bc1-226cad278b29

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
import Theorems.Thm_GlobalTheory_DescTheta_exists_trace_ne_zero
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_resG
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_appLE
import Theorems.Thm_GlobalTheory_DescTheta_exists_descent
import Theorems.Thm_GlobalTheory_DescTheta_evalAt_ne_zero
import Theorems.Thm_GlobalTheory_DescTheta_evalAt_appLE
import Theorems.Thm_GlobalTheory_DescTheta_mem_inertia_iff
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.DescTheta
theorem _root_.solution {Γ : Type} [Group Γ] [Finite Γ] {X' G G' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') (p : G ⟶ X) (p' : G' ⟶ X') (φ : G ⟶ G') (τ : Γ →* Aut G)
    (hπ : ∀ g, (ρ g).hom ≫ π = π) (w : φ ≫ p' = p ≫ π) (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hp : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom)
    (hq : ∀ V : G'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(G, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x →
      pullback.fst p x ≫ (τ g).hom = pullback.fst p x)
    {L : LB G'} {V : X'.Opens} (hW : IsAffineOpen (π ⁻¹ᵁ V))
    (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ p' ⁻¹ᵁ V)) (u : G) (hs : ∃ j, u ∈ G.basicOpen (coord s j)) :
    ∃ (t : Γ(toMod L, p' ⁻¹ᵁ V)) (i : L.ι), φ u ∈ G'.basicOpen (coord t i) := by
  have := Fintype.ofFinite Γ
  obtain ⟨j, hj⟩ := hs
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j PUnit.unit, rfl⟩
  have hu : u ∈ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) := pull_inf_le φ _ _ (G.basicOpen_le _ hj)
  let k := AlgebraicClosure (G.residueField u)
  let ζ : Sp k ⟶ G := Spec.map (CommRingCat.ofHom (algebraMap (G.residueField u) k)) ≫
    G.fromSpecResidueField u
  have hζ (z : Sp k) : ζ z = u :=
    (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply _ _)
  have e : φ ⁻¹ᵁ p' ⁻¹ᵁ V = p ⁻¹ᵁ π ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, w, Scheme.Hom.comp_preimage]
  have hA : φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) ≤ p ⁻¹ᵁ π ⁻¹ᵁ V :=
    (φ.preimage_mono inf_le_left).trans e.le
  have h1 : ⊤ ≤ ζ ⁻¹ᵁ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) := fun z _ => by
    change ζ z ∈ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i)
    rwa [hζ]
  have h2 : ⊤ ≤ (ζ ≫ p) ⁻¹ᵁ π ⁻¹ᵁ V := h1.trans (ζ.preimage_mono hA)
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ (p' ⁻¹ᵁ V ⊓ L.U i)
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  have hev : (evalAt ζ _ h1).comp (p.appLE _ _ hA).hom = evalAt (ζ ≫ p) _ h2 :=
    RingHom.ext fun b => evalAt_appLE ζ p _ _ h1 hA b _ rfl h2
  have hI (g : Γ) := mem_inertia_iff ρ hW hst (ζ ≫ p) h2 g
  let z : Sp k := default
  obtain ⟨c, hc⟩ := exists_trace_ne_zero (Γ := Γ) (p.appLE _ _ hA).hom (fun g b => by
      change (p.appLE _ _ hA).hom (((ρ g⁻¹).hom.appLE _ _ (hst _)).hom b) =
        ((τ g⁻¹).hom.appLE _ _ (hst' _)).hom ((p.appLE _ _ hA).hom b)
      simp only [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE, hp])
    (evalAt ζ _ h1) (by
      rw [hev]
      convert htame k (ζ ≫ p) using 2
      exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [← hI, inv_mem_iff]))
    (resG G (le_pull_chart φ _ i) (coord s fun _ => i)) (fun g hg => by
      rw [hev, ← inv_inv g, hI] at hg
      have := pullback.lift ζ (𝟙 _) (Category.id_comp _).symm ≫= hfib k (ζ ≫ p) _ hg
      rw [pullback.lift_fst_assoc, pullback.lift_fst] at this
      exact evalAt_appLE ζ (τ g⁻¹).hom _ _ h1 (hst' _) _ ζ this h1)
    (by
      rw [evalAt_ne_zero _ _ _ _ z, hζ, mem_basicOpen_resG]
      exact ⟨hu, hj⟩)
  obtain ⟨t, ht⟩ := exists_descent τ φ hφ hq _ ((p.appLE _ _ e.le).hom c • s)
  refine ⟨t, i, ?_⟩
  rw [evalAt_ne_zero _ _ _ _ z, hζ] at hc
  have h3 := ht i
  rw [coord_smul (L := L.pull φ) _ s (fun _ => i), map_mul, resG_resG, resG_appLE, Scheme.Hom.app_eq_appLE] at h3
  refine ((mem_basicOpen_appLE φ le_rfl (coord t i) u).1 ?_).2
  rw [h3]
  exact hc
end GlobalTheory.DescTheta
