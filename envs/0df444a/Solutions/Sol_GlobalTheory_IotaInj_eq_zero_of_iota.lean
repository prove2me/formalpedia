-- Prove2me | solution 1 for GlobalTheory.IotaInj.eq_zero_of_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:00.048994+00:00
-- url     : https://prove2.me/submissions/a22fb4d6-0fed-41fa-a7c5-20c90efa865f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemOfNonempty
import Theorems.Thm_GlobalTheory_IotaInj_mem_of_nonempty
import Theorems.Thm_GlobalTheory_IotaInj_eq_zero_of_gs
import Theorems.Thm_GlobalTheory_IotaInj_not_isUnit_germ
import Theorems.Thm_GlobalTheory_IotaInj_exists_val_psi
import Theorems.Thm_GlobalTheory_IotaInj_val_tau
import Theorems.Thm_GlobalTheory_IotaInj_c_left_eq
import Theorems.Thm_GlobalTheory_TorusExt_iota_b
import Theorems.Thm_GlobalTheory_TorusExt_iota_val
import Theorems.Thm_GlobalTheory_TorusExt_zero_b
import Theorems.Thm_GlobalTheory_TorusExt_zero_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.IotaInj
open GlobalTheory.TorusExt
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
attribute [local instance] gtGroup
namespace GlobalTheory.IotaInj
theorem _root_.solution {I : Ideal R} (hI : I ≠ ⊤) (D : DegData R I) (z : D.toPre.X)
    (h : iota D.tau_bimult F z = 0) : z = 0 := by
  by_contra hz
  have hL := D.toPre.P.isLB
  have c₁ : (D.toPre.c z).left = eSec D.toPre.P.A := c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, h, zero_b])
  have c₂ : (D.toPre.c (-z)).left = eSec D.toPre.P.A :=
    c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, map_neg, h, neg_zero, zero_b])
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  let p : Spec (CommRingCat.of R) := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  obtain ⟨j, hj⟩ := exists_chart hL (eSec D.toPre.P.A p)
  obtain ⟨V, hV, hp, hle⟩ : ∃ V : (Spec (CommRingCat.of R)).Opens, IsAffineOpen V ∧ p ∈ V ∧
      V ≤ eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hp, hle⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ ((eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j : (Spec (CommRingCat.of R)).Opens) : Set _) from hj)
      (eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j).isOpen
    exact ⟨V, hV, hp, hle⟩
  let y : Spec (CommRingCat.of F) := (⊥ : PrimeSpectrum F)
  have hy := mem_of_nonempty (R := R) y hp
  obtain ⟨J, hJ, hJj⟩ := exists_good D.toPre.P.L hL y (K := PUnit)
    (fun _ => (jFK (R := R) F ≫ jK R) ≫ eSec D.toPre.P.A) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hle hy)
  obtain ⟨r, hr, e₁⟩ := exists_val_psi D.toPre (D.psi_pos z hz) c₁ j hV hle y hy J (hJj PUnit.unit)
  obtain ⟨r', -, e₂⟩ := exists_val_psi D.toPre (D.psi_pos (-z) (neg_ne_zero.2 hz)) c₂ j hV hle y hy J (hJj PUnit.unit)
  have τ : ∀ χ, val (D.toPre.tau z χ) (jFK (R := R) F) y J = 1 := fun χ => by
    have e := iota_val (F := F) D.tau_bimult z χ (y := y) hJ
    rw [h, zero_val χ hJ] at e
    exact e.symm
  have hle' : V ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => j) := fun x hx =>
    Set.mem_iInter.2 fun _ => hle hx
  obtain ⟨u, e₃⟩ : ∃ u : Γ(Spec (CommRingCat.of R), V),
      (val D.toPre.rigK (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V u := by
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.toPre.rig.s (fun _ => j)).val, ?_⟩
    have a₁ : val D.toPre.rigK (jFK (R := R) F) y J = val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A)
        (ε := fun _ => 1) D.toPre.rig (jFK (R := R) F ≫ jK R) y J := val_pull hJ _ _ _
    rw [a₁, val_of _ _ y J (fun _ => j) (fun _ => hJj PUnit.unit)]
    exact (gs_unit _ y _ (hle' hy) _).symm.trans (gs_res _ y hle' hy _).symm
  have t₀ := τ 0
  have t₁ := τ (-z)
  rw [val_tau _ _ _ hJ, add_zero] at t₀
  rw [val_tau _ _ _ hJ, add_neg_cancel] at t₁
  have t : val (D.toPre.psi z) (jFK (R := R) F) y J * (val (D.toPre.psi (-z)) (jFK (R := R) F) y J *
      (val D.toPre.rigK (jFK (R := R) F) y J * val D.toPre.rigK (jFK (R := R) F) y J)) = 1 := by
    have a₀ := congrArg Additive.ofMul t₀
    have a₁ := congrArg Additive.ofMul t₁
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₀ a₁ ⊢
    linear_combination (norm := abel) -a₀ - a₁
  have t' := congrArg Units.val t
  rw [Units.val_mul, Units.val_mul, Units.val_mul, e₁, e₂, e₃, ← gs_mul _ y V hy, ← gs_mul _ y V hy, ← gs_mul _ y V hy,
    Units.val_one] at t'
  have one : r * (r' * (u * u)) - 1 = 0 := eq_zero_of_gs y hp _ (by
    rw [gs_eq _ y V hy] at t' ⊢
    rw [map_sub, map_sub, map_one, map_one, t', sub_self])
  exact not_isUnit_germ hp hIm hr ((IsUnit.of_mul_eq_one _ (sub_eq_zero.1 one)).map _)
end GlobalTheory.IotaInj
