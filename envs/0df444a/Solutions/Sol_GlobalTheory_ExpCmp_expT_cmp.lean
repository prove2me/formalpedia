-- Prove2me | solution 1 for GlobalTheory.ExpCmp.expT_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:38.365109+00:00
-- url     : https://prove2.me/submissions/61aae3da-4c40-4e9c-926b-3e7336f8623a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitMapSnd
import Theorems.Thm_GlobalTheory_ExpCmp_unitMap_snd
import Theorems.Thm_GlobalTheory_ExpCmp_eq_unitMap
import Theorems.Thm_GlobalTheory_ExpCmp_fst_unit
import Theorems.Thm_P2M_GlobalTheory_ExpCmp_fam_B_comp_5fb0830a2fdc
import Theorems.Thm_GlobalTheory_ExpCmp_prod_fam
import Theorems.Thm_GlobalTheory_ExpCmp_exists_level
import Theorems.Thm_GlobalTheory_ExpTrans_prod_fam
import Theorems.Thm_GlobalTheory_ExpTrans_sec_val
import Theorems.Thm_GlobalTheory_SecPull_existsUnique_secPull
import Theorems.Thm_P2M_GlobalTheory_UnitSec_fam_T_eq_8be3ac41ab2a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
set_option maxHeartbeats 1600000
namespace GlobalTheory.ExpCmp
theorem _root_.solution : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → ∃ (σ' : U'.SecGT (𝟙_ _) k) (f' : ∀ α, SecBT D' (𝟙_ _) k α), U'.ExpT (𝟙_ _) k σ' f' ∧ (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') ∧ ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, gw C.v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ C.β)) (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
  intro R V _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F C k σ f hE
  classical
  have hcG : ∀ _ : Fin 1, (snd (𝟙_ _) G').left ≫ F = unitMap F ≫ (snd (𝟙_ _) G).left :=
    fun _ => (unitMap_snd F).symm
  have hcB : ∀ α i, famφT D' (𝟙_ _) α i ≫ C.β = unitMap C.β ≫ famφT D (𝟙_ _) (C.xe α) i := fun α i => by
    rw [famφT_eq, famφT_eq, ← Category.assoc (unitMap _), unitMap_snd, Category.assoc, Category.assoc,
      famφB_comp C.pbB (C.c_pr α)]
  obtain ⟨σ', hσ, -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.P.L.L U'.P.L.L F U.P.L.isLB U'.P.L.isLB C.wL
    C.wL_map.gen (Fin 1) (fun _ => (snd (𝟙_ _) G').left) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ))
    (unitMap F) hcG σ
  choose f' hf using fun α => (SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L C.β D.P.isLB D'.P.isLB C.v
    C.v_gen (Fin 4) (famφT D' (𝟙_ _) α) (famφT D (𝟙_ _) (C.xe α)) (DegPre.famε k)
    (unitMap C.β) (hcB α) (f (C.xe α))).exists
  have Hσ : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J' := by
    intro Z r' r hr z J J' hJ hJ'
    have := sec_val C.wL _ _ _ (unitMap F) hcG σ σ' r' z (hσ Z r' z) hJ hJ'
    rw [← eq_unitMap F hr, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, om, Category.assoc, ← hr] at this
    exact this
  have Hf : ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, om C.v z J J' (r' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
    intro α Z r' r hr z J J' hJ hJ'
    have := sec_val C.v _ _ _ (unitMap C.β) (hcB α) (f (C.xe α)) (f' α) r' z (hf α Z r' z) hJ hJ'
    rw [← eq_unitMap C.β hr] at this
    exact this
  refine ⟨σ', f', fun e => ?_, Hσ, fun α Z r' r hr z J J' hJ hJ' => ?_⟩
  swap
  · have := Hf α Z r' r hr z J J' hJ hJ'
    simp only [om, Category.assoc] at this
    exact this
  obtain ⟨S, hS⟩ := hE e
  obtain ⟨m, hm⟩ := exists_level hI C.pb.1.w e
  refine ⟨S.map C.xe.symm.toEquiv.toEmbedding, fun Z x' rG' rB' hG' hB' _ z JG' J' hJG' hJ' => ?_⟩
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose JG hJG using fun ψ : Z ⟶ G.left => exists_chart U.P.L.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  have hJG : Good U.P.L.L z JG := hJG
  obtain ⟨x, hx⟩ : ∃ x : Z ⟶ (thickObj R I e G).left, x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F :=
    ⟨x' ≫ m, by rw [Category.assoc, hm]⟩
  obtain ⟨hq, hlev⟩ := C.lev e Z x' x hx
  obtain ⟨hT, hW⟩ := hlev z J J' hJ hJ'
  have hW := hW (JG (x ≫ (fstG I e G).left)) (JG' (x' ≫ (fstG I' e G').left)) (hJG _) (hJG' _)
  have rG₁ : (rG' ≫ unitMap F) ≫ (snd _ G).left = rG' ≫ (snd _ G').left ≫ F := by
    rw [Category.assoc, unitMap_snd]
  have rB₁ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = rB' ≫ (snd _ D'.P.A).left ≫ C.β := by
    rw [Category.assoc, unitMap_snd]
  have rG₂ : (rG' ≫ unitMap F) ≫ (snd _ G).left = x ≫ (fstG I e G).left := by
    rw [rG₁, hx, ← Category.assoc, hG', Category.assoc]
  have rB₂ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left := by
    rw [rB₁, ← hq, ← Category.assoc, hB', Category.assoc]
  have rBG : (rB' ≫ unitMap C.β) ≫ (fst _ D.P.A).left = (rG' ≫ unitMap F) ≫ (fst _ G).left := by
    rw [fst_unit, fst_unit, ← Category.assoc, ← Category.assoc, rG₂, rB₂, Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) ((Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm)
  obtain ⟨h0, hsum⟩ := hS Z x _ _ rG₂ rB₂ rBG z JG J hJG hJ
  have hF := fun α => Hf α Z rB' _ rB₁ z J J' hJ hJ'
  have Sg := Hσ Z rG' _ rG₁ z JG JG' hJG hJG'
  rw [rG₂, hG'] at Sg
  have hω : ∀ α, (∏ i : Fin 4, om C.v z J J' (rB' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i) *
      ∏ i : Fin 4, gw C.v (x' ≫ D'.Oφ (U'.gt e).pG α i) z (J (x' ≫ D'.Oφ (U'.gt e).pG α i ≫ C.β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG α i)) ^ Oinvε i =
      gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k := by
    intro α
    have := prod_fam (U'.gt e).pG k (fun ψ => om C.v z J J' (x' ≫ ψ)) α
    have e₁ : ∀ i, rB' ≫ famφT D' (𝟙_ _) α i = x' ≫ (U'.gt e).pG.left ≫ D'.famφB α i := fun i => by
      rw [famφT_eq, ← Category.assoc, hB', Category.assoc]
    rw [← hq, ← Category.assoc x' _ C.β]
    refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_)
      (Finset.prod_congr rfl fun i _ => ?_)) this
    · rw [e₁]
    · rw [← Category.assoc x' _ C.β]; rfl
  refine ⟨fun α' hα => ?_, ?_⟩
  · have hi : C.xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨C.xe α', hc, C.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans (h0 _ hi))
  · refine (gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul,
      _root_.mul_assoc, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← Sg, hsum, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨α', rfl⟩ := C.xe.surjective y
    have e₀ : C.xe.symm.toEquiv.toEmbedding (C.xe α') = α' := C.xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul]
    ring
end GlobalTheory.ExpCmp
