-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_branchPlace_of_igusaEnd_of_node_crossingPresentation_igusaBranch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/8f9d22d7-0ba0-53e2-895e-da5eb7e8de02

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
import Theorems.Thm_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_V_notMem_span_U
import Theorems.Thm_ModularCurve_UVCrossingModel_U_notMem_span_V
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian
import Theorems.Thm_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral
import Theorems.Thm_ValuationSubring_eq_of_constantsTower_of_forall_mem_iff
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_branchPlace_of_igusaEnd_of_node_crossingPresentation_igusaBranch

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

namespace NodePtSol

section Generic

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  (W : ValuationSubring F) (hA : ∀ x : L, algebraMap L F x ∈ W ↔ x ∈ A)

def toW : A →+* W where
  toFun a := ⟨algebraMap L F a, (hA a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem toW_apply (a : A) : ((toW A W hA a : W) : F) = algebraMap L F a := rfl

include hA in
theorem isUnit_of_isUnit_toW (a : A) (h : IsUnit (toW A W hA a)) : IsUnit a := by
  have ha0 : (a : L) ≠ 0 := by
    rintro h0
    have : toW A W hA a = 0 := Subtype.ext (by simp [h0])
    rw [this] at h; exact not_isUnit_zero h
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp h
  have hinv : (algebraMap L F a)⁻¹ ∈ W := by
    have : ((u : W) : F) = (algebraMap L F a)⁻¹ := by
      have h1 : algebraMap L F a * (u : F) = 1 := by
        have := congrArg Subtype.val hu; simpa using this
      exact (eq_inv_of_mul_eq_one_right h1)
    rw [← this]; exact u.2
  rw [← map_inv₀, hA] at hinv
  exact isUnit_iff_exists_inv.mpr ⟨⟨(a : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

scoped instance isLocalHom_toW : IsLocalHom (toW A W hA) := ⟨fun a h => isUnit_of_isUnit_toW A W hA a h⟩

@[reducible] def resAlg : Algebra (ResidueField A) (ResidueField W) :=
  (IsLocalRing.ResidueField.map (toW A W hA)).toAlgebra

theorem resAlg_residue (a : A) :
    letI := resAlg A W hA
    algebraMap (ResidueField A) (ResidueField W) (IsLocalRing.residue A a) =
      IsLocalRing.residue W (toW A W hA a) := by
  letI := resAlg A W hA
  show IsLocalRing.ResidueField.map (toW A W hA) (IsLocalRing.residue A a) = _
  rfl

@[reducible] def regularProlongationOf
    (hsm : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ W, IsUnit (⟨c • f, h⟩ : W)) :
    letI := resAlg A W hA
    RegularProlongation A F (ResidueField W) := by
  letI := resAlg A W hA
  exact
  { integers := W
    residue := IsLocalRing.residue W
    algebraMap_mem_iff := hA
    residue_surjective := IsLocalRing.residue_surjective
    ker_residue := IsLocalRing.ker_residue
    residue_algebraMap := fun a => by
      rw [resAlg_residue]; rfl
    exists_smul_mem := fun f hf => by
      obtain ⟨c, h, hu⟩ := hsm f hf
      exact ⟨c, h, (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu⟩ }

theorem regularProlongationOf_integers
    (hsm : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ W, IsUnit (⟨c • f, h⟩ : W)) :
    letI := resAlg A W hA
    (regularProlongationOf A W hA hsm).integers = W := rfl

theorem regularProlongationOf_residue_apply
    (hsm : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ W, IsUnit (⟨c • f, h⟩ : W)) :
    letI := resAlg A W hA
    ∀ (f : F) (h : f ∈ (regularProlongationOf A W hA hsm).integers) (h' : f ∈ W),
      (regularProlongationOf A W hA hsm).residue ⟨f, h⟩ = IsLocalRing.residue W ⟨f, h'⟩ := fun _ _ _ => rfl

end Generic

section Transfer

variable {K₁ K₂ F₁ F₂ : Type*} [Field K₁] [Field K₂] [Field F₁] [Field F₂] [Algebra K₁ F₁] [Algebra K₂ F₂]

def valEquiv (e : F₁ ≃+* F₂) (V : ValuationSubring F₁) : ↥V ≃+* ↥(V.comap e.symm.toRingHom) where
  toFun x := ⟨e x, ValuationSubring.mem_comap.mpr (by
    change e.symm (e x) ∈ V
    rw [e.symm_apply_apply]; exact x.2)⟩
  invFun y := ⟨e.symm y, ValuationSubring.mem_comap.mp y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

@[scoped simp] theorem coe_valEquiv (e : F₁ ≃+* F₂) (V : ValuationSubring F₁) (x : ↥V) :
    ((valEquiv e V x : ↥(V.comap e.symm.toRingHom)) : F₂) = e x := rfl

theorem mem_comap_symm_iff (e : F₁ ≃+* F₂) (V : ValuationSubring F₁) (y : F₂) :
    y ∈ V.comap e.symm.toRingHom ↔ e.symm y ∈ V := ValuationSubring.mem_comap

def transfer (e : F₁ ≃+* F₂) (P : Place K₁ F₁)
    (hK : ∀ a : K₂, e.symm (algebraMap K₂ F₂ a) ∈ P.toValuationSubring) : Place K₂ F₂ where
  toValuationSubring := P.toValuationSubring.comap e.symm.toRingHom
  algebraMap_mem' a := ValuationSubring.mem_comap.mpr (hK a)
  ne_top' h := by
    apply P.ne_top'
    ext x
    refine ⟨fun _ => ValuationSubring.mem_top _, fun _ => ?_⟩
    have hx : e x ∈ P.toValuationSubring.comap e.symm.toRingHom := by rw [h]; exact ValuationSubring.mem_top _
    rw [mem_comap_symm_iff, e.symm_apply_apply] at hx
    exact hx
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (valEquiv e P.toValuationSubring).toRingHom (valEquiv e P.toValuationSubring).surjective

@[scoped simp] theorem transfer_toValuationSubring (e : F₁ ≃+* F₂) (P : Place K₁ F₁)
    (hK : ∀ a : K₂, e.symm (algebraMap K₂ F₂ a) ∈ P.toValuationSubring) :
    (transfer e P hK).toValuationSubring = P.toValuationSubring.comap e.symm.toRingHom := rfl

theorem mem_transfer_iff (e : F₁ ≃+* F₂) (P : Place K₁ F₁)
    (hK : ∀ a : K₂, e.symm (algebraMap K₂ F₂ a) ∈ P.toValuationSubring) (y : F₂) :
    y ∈ (transfer e P hK).toValuationSubring ↔ e.symm y ∈ P.toValuationSubring := ValuationSubring.mem_comap

theorem algebraMap_residueField_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F) (a : K) :
    algebraMap K P.ResidueField a = IsLocalRing.residue ↥P.toValuationSubring (algebraMap K ↥P.toValuationSubring a) := rfl

theorem transfer_isRational (e : F₁ ≃+* F₂) (P : Place K₁ F₁)
    (hK : ∀ a : K₂, e.symm (algebraMap K₂ F₂ a) ∈ P.toValuationSubring) (hP : P.IsRational)
    (hc : ∀ a₁ : K₁, ∃ a₂ : K₂, e (algebraMap K₁ F₁ a₁) = algebraMap K₂ F₂ a₂) :
    (transfer e P hK).IsRational := by
  intro z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  set x : ↥P.toValuationSubring := (valEquiv e P.toValuationSubring).symm y with hx
  obtain ⟨a₁, ha₁⟩ := hP (IsLocalRing.residue _ x)
  obtain ⟨a₂, ha₂⟩ := hc a₁
  refine ⟨a₂, ?_⟩
  rw [algebraMap_residueField_eq] at ha₁ ⊢
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at ha₁ ⊢

  have hy : y = valEquiv e P.toValuationSubring x := by rw [hx, RingEquiv.apply_symm_apply]
  have himg : valEquiv e P.toValuationSubring (algebraMap K₁ ↥P.toValuationSubring a₁) =
      algebraMap K₂ ↥(transfer e P hK).toValuationSubring a₂ := by
    apply Subtype.ext
    show e (algebraMap K₁ F₁ a₁) = algebraMap K₂ F₂ a₂
    exact ha₂
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha₁ ⊢
  intro hu
  apply ha₁
  rw [← isUnit_map_iff (valEquiv e P.toValuationSubring), map_sub, himg, ← hy]
  exact hu

theorem transfer_ord_eq_one (e : F₁ ≃+* F₂) (P : Place K₁ F₁)
    (hK : ∀ a : K₂, e.symm (algebraMap K₂ F₂ a) ∈ P.toValuationSubring) {f : F₁}
    (hf : f ∈ P.toValuationSubring) (h1 : P.ord f = 1) : (transfer e P hK).ord (e f) = 1 := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥P.toValuationSubring
  obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf0 hϖ
  rw [h1, zpow_one] at hu
  have hirr : Irreducible (⟨f, hf⟩ : ↥P.toValuationSubring) := by
    have hassoc : Associated ϖ (⟨f, hf⟩ : ↥P.toValuationSubring) :=
      ⟨u, Subtype.ext (by
        show ((ϖ : ↥P.toValuationSubring) : F₁) * (((u : ↥P.toValuationSubring)) : F₁) = f
        rw [hu]; ring)⟩
    exact hassoc.irreducible hϖ
  have hirr' : Irreducible (valEquiv e P.toValuationSubring ⟨f, hf⟩) :=
    (MulEquiv.irreducible_iff (valEquiv e P.toValuationSubring)).mpr hirr
  have := (transfer e P hK).ord_coe_irreducible hirr'
  first | exact this | simpa [valEquiv] using this

theorem transfer_eq_iff (e : F₁ ≃+* F₂) (P : Place K₁ F₁)
    (hK : ∀ a : K₂, e.symm (algebraMap K₂ F₂ a) ∈ P.toValuationSubring) (Q : Place K₂ F₂) :
    Q = transfer e P hK ↔ ∀ y : F₂, y ∈ Q.toValuationSubring ↔ e.symm y ∈ P.toValuationSubring := by
  constructor
  · rintro rfl y; exact mem_transfer_iff e P hK y
  · intro h; apply Place.ext; ext y; rw [h y, mem_transfer_iff]

end Transfer

abbrev A0 (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ValuationSubring ↥k₀ := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))

abbrev FB (q M' : ℕ) : Type := ↥(fieldBar q M')

section Lbar
variable (q M' : ℕ) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))

scoped instance algK : Algebra ↥k₀ (FB q M') :=
  ((algebraMap (AlgebraicClosure ℚ) (FB q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

def ιL : AlgebraicClosure ℚ →ₐ[↥k₀] FB q M' :=
  { algebraMap (AlgebraicClosure ℚ) (FB q M') with commutes' := fun _ => rfl }

@[scoped simp] theorem ιL_apply (x : AlgebraicClosure ℚ) : ιL q M' k₀ x = algebraMap (AlgebraicClosure ℚ) (FB q M') x := rfl

def Lbar : IntermediateField ↥k₀ (FB q M') := (ιL q M' k₀).fieldRange

def eL : AlgebraicClosure ℚ ≃ₐ[↥k₀] ↥(Lbar q M' k₀) := AlgEquiv.ofInjectiveField (ιL q M' k₀)

theorem eL_apply (x : AlgebraicClosure ℚ) :
    ((eL q M' k₀ x : ↥(Lbar q M' k₀)) : FB q M') = algebraMap (AlgebraicClosure ℚ) (FB q M') x := rfl

def AL (A : ValuationSubring (AlgebraicClosure ℚ)) : ValuationSubring ↥(Lbar q M' k₀) :=
  A.comap (eL q M' k₀).symm.toAlgHom.toRingHom

theorem mem_AL (A : ValuationSubring (AlgebraicClosure ℚ)) (x : ↥(Lbar q M' k₀)) :
    x ∈ AL q M' k₀ A ↔ (eL q M' k₀).symm x ∈ A := Iff.rfl

theorem eL_mem_AL (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) :
    eL q M' k₀ x ∈ AL q M' k₀ A ↔ x ∈ A := by
  rw [mem_AL, AlgEquiv.symm_apply_apply]

theorem Lbar_eq_adjoin :
    Lbar q M' k₀ = IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := (AlgHom.mem_fieldRange).mp hx
    exact IntermediateField.subset_adjoin ↥k₀ _ ⟨y, rfl⟩
  · exact IntermediateField.adjoin_le_iff.mpr fun x ⟨y, hy⟩ => (AlgHom.mem_fieldRange).mpr ⟨y, hy⟩

end Lbar

section Centre
variable {F : Type*} [Field F]

def toVal (O : Subring F) (V : ValuationSubring F) (h : ∀ f : F, f ∈ O → f ∈ V) : ↥O →+* ↥V where
  toFun b := ⟨(b : F), h _ b.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

def centre (O : Subring F) (V : ValuationSubring F) (h : ∀ f : F, f ∈ O → f ∈ V) : Ideal ↥O :=
  (maximalIdeal ↥V).comap (toVal O V h)

theorem mem_centre_iff (O : Subring F) (V : ValuationSubring F) (h : ∀ f : F, f ∈ O → f ∈ V) (b : ↥O) :
    b ∈ centre O V h ↔ (b : F) ∈ V.nonunits :=
  (Ideal.mem_comap).trans (ValuationSubring.coe_mem_nonunits_iff (a := ⟨(b : F), h _ b.2⟩)).symm

end Centre

theorem mem_span_of_not_isUnit_of_ringEquiv_uvCrossingModel
    {O : Type*} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ E))
    (p x y : O) (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hp : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) p) = const (π ^ E) π)
    (hx : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) x) = (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hy : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) y) = (γV : UVCrossingModel W (π ^ E)) * V (π ^ E)) :
    (∀ f : O, ¬ IsUnit f → ∃ a b c : O, f = a * x + b * y + c * p) ∧ ¬ IsUnit x := by
  classical
  have hE0 : E ≠ 0 := by omega
  have hπE : ¬ IsUnit (π ^ E) := fun h => hπ.not_isUnit ((isUnit_pow_iff hE0).mp h)
  haveI : Nontrivial (W ⧸ Ideal.span {π ^ E}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hVU : V (π ^ E) ∉ Ideal.span {U (π ^ E)} := V_notMem_span_U (π ^ E)
  have hUnu : ¬ IsUnit (U (π ^ E) : UVCrossingModel W (π ^ E)) := fun hu =>
    hVU (by rw [Ideal.span_singleton_eq_top.mpr hu]; exact Submodule.mem_top)
  haveI : Nontrivial (UVCrossingModel W (π ^ E)) := ⟨⟨U (π ^ E), 1, fun h => hUnu (h ▸ isUnit_one)⟩⟩
  haveI hMloc : IsLocalRing (UVCrossingModel W (π ^ E)) :=
    IsLocalRing.of_surjective' (UVCrossingModel.mk (π ^ E)) (UVCrossingModel.mk_surjective _)
  haveI : Module.FaithfullyFlat O (AdicCompletion (maximalIdeal O) O) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal O
  set φ : O →+* UVCrossingModel W (π ^ E) :=
    ι.toRingHom.comp (algebraMap O (AdicCompletion (maximalIdeal O) O)) with hφ
  have hφapp : ∀ z, φ z = ι (algebraMap O (AdicCompletion (maximalIdeal O) O) z) := fun z => rfl
  have hcm : ∀ I : Ideal O,
      (I.map (algebraMap O (AdicCompletion (maximalIdeal O) O))).comap
        (algebraMap O (AdicCompletion (maximalIdeal O) O)) = I :=
    fun I => Ideal.comap_map_eq_self_of_faithfullyFlat I
  have hunit : ∀ z : O, IsUnit (φ z) → IsUnit z := by
    intro z hz
    have hz' : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) z) := by
      have := hz.map ι.symm; rwa [hφapp, RingEquiv.symm_apply_apply] at this
    rw [← Ideal.span_singleton_eq_top] at hz' ⊢
    rw [← hcm (Ideal.span {z}), Ideal.map_span, Set.image_singleton, hz', Ideal.comap_top]
  have hxnu : ¬ IsUnit x := by
    intro hxu
    have h1 : IsUnit (φ x) := hxu.map φ
    rw [hφapp, hx] at h1
    exact hUnu ((Units.isUnit_units_mul γU _).mp h1)
  refine ⟨?_, hxnu⟩
  intro f hf
  have hmW : maximalIdeal W = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hmM : maximalIdeal (UVCrossingModel W (π ^ E)) ≤ Ideal.span {φ x, φ y, φ p} := by
    rw [maximalIdeal_eq_map_maximalIdeal_sup_span_pair (W := W) (π := π ^ E) hπE, hmW, Ideal.map_span,
      Set.image_singleton, constHom_apply, sup_le_iff]
    constructor
    · rw [Ideal.span_singleton_le_iff_mem, ← hp, ← hφapp]
      exact Ideal.subset_span (by simp)
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · have : U (π ^ E) = ((γU⁻¹ : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) * φ x := by
          rw [hφapp, hx, ← mul_assoc, Units.inv_mul, one_mul]
        rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · have : V (π ^ E) = ((γV⁻¹ : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) * φ y := by
          rw [hφapp, hy, ← mul_assoc, Units.inv_mul, one_mul]
        rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hfm : φ f ∈ Ideal.span {φ x, φ y, φ p} :=
    hmM ((IsLocalRing.mem_maximalIdeal _).mpr (fun h => hf (hunit f h)))
  have hspan : Ideal.span {φ x, φ y, φ p} =
      ((Ideal.span {x, y, p}).map (algebraMap O (AdicCompletion (maximalIdeal O) O))).map ι.toRingHom := by
    rw [Ideal.map_map, ← hφ, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  have : algebraMap O (AdicCompletion (maximalIdeal O) O) f ∈
      (((Ideal.span {x, y, p}).map (algebraMap O (AdicCompletion (maximalIdeal O) O))).map ι.toRingHom).comap
        ι.toRingHom := by
    rw [Ideal.mem_comap, ← hspan]; exact hfm
  rw [Ideal.comap_map_of_bijective ι.toRingHom (show Function.Bijective ι.toRingHom from ι.bijective)] at this
  have hmem : f ∈ Ideal.span {x, y, p} := by
    rw [← hcm (Ideal.span {x, y, p}), Ideal.mem_comap]
    exact this
  obtain ⟨a, b, c, habc⟩ := Submodule.mem_span_triple.mp hmem
  exact ⟨a, b, c, by simpa only [smul_eq_mul] using habc.symm⟩

theorem exists_smul_isUnit_of_uniformizer {L F : Type*} [Field L] [Field F] [Algebra L F]
    (W : ValuationSubring F) [IsDiscreteValuationRing ↥W] (π₀ : L) (hπW : algebraMap L F π₀ ∈ W)
    (hunif : maximalIdeal ↥W = Ideal.span {(⟨_, hπW⟩ : ↥W)}) (f : F) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ W, IsUnit (⟨c • f, h⟩ : ↥W) := by
  have hϖ : Irreducible (⟨_, hπW⟩ : ↥W) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif
  have hp0 : algebraMap L F π₀ ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have key : ∀ g : F, g ∈ W → g ≠ 0 → ∃ (n : ℕ) (v : (↥W)ˣ), g = ((v : ↥W) : F) * algebraMap L F π₀ ^ n := by
    intro g hg hg0
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (show (⟨g, hg⟩ : ↥W) ≠ 0 from fun h => hg0 (congrArg Subtype.val h)) hϖ
    exact ⟨n, v, by simpa using congrArg Subtype.val hv⟩
  rcases W.mem_or_inv_mem f with hfW | hfW
  · obtain ⟨n, v, hv⟩ := key f hfW hf
    have hcf : (π₀ ^ n)⁻¹ • f = ((v : ↥W) : F) := by
      rw [Algebra.smul_def, map_inv₀, map_pow, hv, ← mul_assoc, mul_comm ((algebraMap L F π₀ ^ n)⁻¹), mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero n hp0), mul_one]
    refine ⟨(π₀ ^ n)⁻¹, by rw [hcf]; exact (v : ↥W).2, ?_⟩
    convert v.isUnit using 1
    exact Subtype.ext hcf
  · obtain ⟨n, v, hv⟩ := key f⁻¹ hfW (inv_ne_zero hf)
    have hvinv : (((v⁻¹ : (↥W)ˣ) : ↥W) : F) = (((v : ↥W) : F))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      exact_mod_cast congrArg Subtype.val v.mul_inv
    have hf' : f = (((v : ↥W) : F))⁻¹ * (algebraMap L F π₀ ^ n)⁻¹ := by
      rw [← mul_inv, ← hv, inv_inv]
    have hcf : (π₀ ^ n) • f = (((v⁻¹ : (↥W)ˣ) : ↥W) : F) := by
      rw [Algebra.smul_def, map_pow, hf', mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hp0), mul_one, hvinv]
    refine ⟨π₀ ^ n, by rw [hcf]; exact ((v⁻¹ : (↥W)ˣ) : ↥W).2, ?_⟩
    convert (v⁻¹).isUnit using 1
    exact Subtype.ext hcf

theorem not_isUnit_of_apply_eq_mul_V
    {O : Type*} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ E))
    (y : O) (γV : (UVCrossingModel W (π ^ E))ˣ)
    (hy : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) y) = (γV : UVCrossingModel W (π ^ E)) * V (π ^ E)) :
    ¬ IsUnit y := by
  have hE0 : E ≠ 0 := by omega
  have hπE : ¬ IsUnit (π ^ E) := fun h => hπ.not_isUnit ((isUnit_pow_iff hE0).mp h)
  haveI : Nontrivial (W ⧸ Ideal.span {π ^ E}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hUV : U (π ^ E) ∉ Ideal.span {V (π ^ E)} := U_notMem_span_V (π ^ E)
  have hVnu : ¬ IsUnit (V (π ^ E) : UVCrossingModel W (π ^ E)) := fun hu =>
    hUV (by rw [Ideal.span_singleton_eq_top.mpr hu]; exact Submodule.mem_top)
  intro hyu
  have h1 : IsUnit (ι (algebraMap O (AdicCompletion (maximalIdeal O) O) y)) := (hyu.map _).map ι
  rw [hy] at h1
  exact hVnu ((Units.isUnit_units_mul γV _).mp h1)

end NodePtSol
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_branchPlace_of_igusaEnd_of_node_crossingPresentation_igusaBranch.NodePtSol"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_branchPlace_of_igusaEnd_of_node_crossingPresentation_igusaBranch.NodePtSol"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 64000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (hGU : ∀ V : ValuationSubring ↥(modularFunctionFieldBar M'),
        (∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a ∈ V ↔ a ∈ A) →
        ∀ hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ V,
          (∀ p : Polynomial (AlgebraicClosure ℚ), (∀ n, p.coeff n ∈ A) →
            (∃ hm : Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) p ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
              ∀ n, ∃ hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p.coeff n) ∈ V, (⟨_, hc⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ f : ↥(modularFunctionFieldBar M'), f ∈ V ↔ f ∈ R₀.integers)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
    ∀ (W₀ : ValuationSubring ↥F₀),

      ((∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})) →

    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) →
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →

      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
      (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
      (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) →
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ((cy : ↥F₀) ∈ W₀) → (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
      (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) →

    ∀ (Wx : ValuationSubring ↥F₀),
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) →
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx) →
                IsDiscreteValuationRing ↥Wx →
                (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) →
                (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                  (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
                (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                  (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                  (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                      ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                      ↥(modularFunctionFieldBar M'))) →
                  ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                    (⟨_, hF⟩ : ↥F₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥F₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                    ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                      (⟨_, hF⟩ : ↥F₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥F₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥F₀ c ∈ O),
                        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) →

    ∀ (FI : Type) [Field FI] [Algebra (ResidueField ↥A) FI] (Rx : RegularProlongation A ↥(fieldBar q M') FI),
      (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ Rx.integers ↔ f ∈ Wx)) →
      ∃ bx : Place (ResidueField ↥A) FI,
        bx.IsRational ∧

        (∀ (f : ↥F₀) (_ : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ bx.toValuationSubring) ∧
        (∀ (f : ↥F₀) (hf : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
          ∃ hm : Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ bx.toValuationSubring,
            (⟨_, hm⟩ : ↥bx.toValuationSubring) ∈ maximalIdeal ↥bx.toValuationSubring) ∧
        (∀ y : Place (ResidueField ↥A) FI,
          (∀ (f : ↥F₀) (_ : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ y.toValuationSubring) →
          (∀ (f : ↥F₀) (hf : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
            ∃ hm : Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ y.toValuationSubring,
              (⟨_, hm⟩ : ↥y.toValuationSubring) ∈ maximalIdeal ↥y.toValuationSubring) →
          y = bx) ∧

        (∀ h₁ : ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Rx.integers, Rx.residue ⟨((cx : ↥F₀) : ↥(fieldBar q M')), h₁⟩ = 0) ∧
        (∀ h₁ : ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Rx.integers, bx.ord (Rx.residue ⟨((cy : ↥F₀) : ↥(fieldBar q M')), h₁⟩) = 1) := by
  intro F₀ hK1 hLD W₀ hK2 O instL instN hOW₀ hOk hOres hOfrac E₀ hE₀ hπO cx cy u ι γU γV hxy hconst hιx hιy hcyW₀ hcyW₀m
    hcxW₀m Wx hOW hWxk₀ hWxdvr hWxunif hWxt hcxWxm hcyWxm hN3 FSS instF instA R hRW
  classical
  obtain ⟨hK2a₀, hK2b₀, hπW₀, hunifW₀⟩ := hK2
  obtain ⟨hπW, hunifW⟩ := hWxunif
  have hK2a : ∀ x : ↥k₀, (x : AlgebraicClosure ℚ) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx := hWxk₀
  have hK2b : IsDiscreteValuationRing ↥Wx := hWxdvr
  haveI := hK2b
  haveI := hdvr

  have hϖ : Irreducible (⟨π₀, hπ⟩ : ↥(NodePtSol.A0 k₀ A)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif
  obtain ⟨instDom, instDVR, instCpl, hirr, -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
      (↥(NodePtSol.A0 k₀ A)) ⟨π₀, hπ⟩ hϖ

  obtain ⟨hdesc, hcxnu⟩ :=
    NodePtSol.mem_span_of_not_isUnit_of_ringEquiv_uvCrossingModel _ hirr E₀ hE₀ ι ⟨_, hπO⟩ cx cy γU γV
      (hconst π₀ hπ hπO) hιx hιy
  have hcynu : ¬ IsUnit cy := NodePtSol.not_isUnit_of_apply_eq_mul_V _ hirr E₀ hE₀ ι cy γV hιy

  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI halg : Algebra.IsAlgebraic ↥k₀ ↥(NodePtSol.Lbar q M' k₀) := by
    haveI : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
    exact (NodePtSol.eL q M' k₀).isAlgebraic
  have hkL : ∀ c : ↥k₀, algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀) c = NodePtSol.eL q M' k₀ (c : AlgebraicClosure ℚ) :=
    fun c => ((NodePtSol.eL q M' k₀).commutes c).symm
  have hcomapEq : NodePtSol.A0 k₀ A =
      (NodePtSol.AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀)) := by
    ext x
    show (x : AlgebraicClosure ℚ) ∈ A ↔ algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀) x ∈ NodePtSol.AL q M' k₀ A
    rw [hkL, NodePtSol.eL_mem_AL]
  obtain ⟨hπ', hunif'⟩ : ∃ hπ' : π₀ ∈ (NodePtSol.AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀)),
      maximalIdeal ↥((NodePtSol.AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀))) =
        Ideal.span {⟨π₀, hπ'⟩} :=
    hcomapEq ▸ (⟨hπ, hunif⟩ : ∃ hπ' : π₀ ∈ NodePtSol.A0 k₀ A,
      maximalIdeal ↥(NodePtSol.A0 k₀ A) = Ideal.span {⟨π₀, hπ'⟩})
  have hdvr' : IsDiscreteValuationRing ↥((NodePtSol.AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀))) :=
    hcomapEq ▸ hdvr
  have hhens' : HenselianLocalRing ↥((NodePtSol.AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀))) :=
    hcomapEq ▸ hhens
  have hres' : IsAlgClosed (ResidueField ↥((NodePtSol.AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀)))) :=
    hcomapEq ▸ hres
  obtain ⟨hint, htower⟩ :=
    @ValuationSubring.isIntegral_and_exists_totallyRamified_layers_of_henselian ↥k₀ (NodePtSol.FB q M') _ _ _ _
      (NodePtSol.Lbar q M' k₀) halg (NodePtSol.AL q M' k₀ A) π₀ hπ' hdvr' hunif' hhens' hres'
  have hgen : NodePtSol.Lbar q M' k₀ ⊔ F₀ = ⊤ := by rw [NodePtSol.Lbar_eq_adjoin]; exact hK1
  have hagree : ∀ x : ↥k₀, algebraMap ↥k₀ ↥(NodePtSol.Lbar q M' k₀) x ∈ NodePtSol.AL q M' k₀ A ↔
      algebraMap ↥k₀ ↥F₀ x ∈ Wx := by
    intro x; rw [hkL, NodePtSol.eL_mem_AL]; exact hK2a x
  obtain ⟨Ot, hOA, hOF₀, hOtres, hOsm⟩ :=
    ValuationSubring.exists_constantsTower_of_totallyRamified_of_isIntegral ↥k₀ (NodePtSol.FB q M')
      (NodePtSol.Lbar q M' k₀) F₀ hgen (NodePtSol.AL q M' k₀ A) Wx hagree hK2b π₀ hπW hunifW hint htower
  have hReq : R.integers = Ot :=
    ValuationSubring.eq_of_constantsTower_of_forall_mem_iff ↥k₀ (NodePtSol.FB q M') (NodePtSol.Lbar q M' k₀) F₀ hgen
      (NodePtSol.AL q M' k₀ A) Wx hagree hK2b π₀ hπW hunifW hint htower R.integers Ot hRW hOF₀
  subst hReq

  have hRW' : ∀ x : ↥F₀, algebraMap ↥F₀ (NodePtSol.FB q M') x ∈ R.integers ↔ x ∈ Wx := fun x => hRW x
  obtain ⟨ψ₀, hψ₀val, hψ₀u⟩ : ∃ ψ₀ : ↥Wx →+* ↥R.integers,
      (∀ f : ↥Wx, ((ψ₀ f : ↥R.integers) : NodePtSol.FB q M') = ((f : ↥F₀) : NodePtSol.FB q M')) ∧
      (∀ f : ↥Wx, IsUnit (ψ₀ f) → IsUnit f) :=
    ⟨NodePtSol.toW Wx R.integers hRW', fun f => rfl, fun f h => NodePtSol.isUnit_of_isUnit_toW Wx R.integers hRW' f h⟩
  have hNNR : ∀ w : ↥R.integers, ∃ f : ↥Wx, R.residue w = R.residue (ψ₀ f) := by
    intro w
    obtain ⟨f, hf, hdiff⟩ := hOtres w
    refine ⟨f, ?_⟩
    rw [← sub_eq_zero, ← map_sub]
    have hker : w - ψ₀ f ∈ RingHom.ker R.residue := by
      rw [R.ker_residue]
      have hψf : ψ₀ f = ⟨_, hf⟩ := Subtype.ext (hψ₀val f)
      rw [hψf]; exact hdiff
    exact hker

  have hAW : ∀ x : ↥k₀, algebraMap ↥k₀ ↥F₀ x ∈ Wx ↔ x ∈ NodePtSol.A0 k₀ A := fun x => (hK2a x).symm
  have hsm : ∀ f : ↥F₀, f ≠ 0 → ∃ c : ↥k₀, ∃ h : c • f ∈ Wx, IsUnit (⟨c • f, h⟩ : ↥Wx) :=
    NodePtSol.exists_smul_isUnit_of_uniformizer Wx π₀ hπW hunifW
  letI instRA := NodePtSol.resAlg (NodePtSol.A0 k₀ A) Wx hAW
  obtain ⟨RW, hRWint, hRWres0⟩ : ∃ RW : RegularProlongation (NodePtSol.A0 k₀ A) ↥F₀ (ResidueField ↥Wx),
      RW.integers = Wx ∧ ∀ (f : ↥F₀) (h : f ∈ RW.integers) (h' : f ∈ Wx),
        RW.residue ⟨f, h⟩ = IsLocalRing.residue ↥Wx ⟨f, h'⟩ :=
    ⟨NodePtSol.regularProlongationOf (NodePtSol.A0 k₀ A) Wx hAW hsm,
      NodePtSol.regularProlongationOf_integers (NodePtSol.A0 k₀ A) Wx hAW hsm,
      NodePtSol.regularProlongationOf_residue_apply (NodePtSol.A0 k₀ A) Wx hAW hsm⟩
  have hmemRW : ∀ f : ↥F₀, f ∈ RW.integers ↔ f ∈ Wx := fun f => by rw [hRWint]
  have hOW' : ∀ f : ↥F₀, f ∈ O → f ∈ RW.integers := fun f hf => (hmemRW f).mpr (hOW f hf)
  have hA' : ∀ a : ↥(NodePtSol.A0 k₀ A), algebraMap ↥k₀ ↥F₀ (a : ↥k₀) ∈ O := fun a => (hOk a).mp a.2
  have hres'' : ∀ g : ↥O, ∃ a : ↥(NodePtSol.A0 k₀ A), ¬ IsUnit (g - ⟨algebraMap ↥k₀ ↥F₀ (a : ↥k₀), hA' a⟩) := by
    intro g
    obtain ⟨x, hxO, hxA, hnu⟩ := hOres g g.2
    exact ⟨⟨x, hxA⟩, hnu⟩
  have hRWres : ∀ (f : ↥F₀) (h : f ∈ RW.integers), RW.residue ⟨f, h⟩ = IsLocalRing.residue ↥Wx ⟨f, (hmemRW f).mp h⟩ :=
    fun f h => hRWres0 f h _
  have hy0 : RW.residue ⟨((cy : ↥O) : ↥F₀), hOW' _ cy.2⟩ ≠ 0 := by
    rw [hRWres, IsLocalRing.residue_ne_zero_iff_isUnit]
    have := hcyWxm (hOW _ cy.2)
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this
  have hmax : ∀ f : ↥O, ¬ IsUnit f → ∃ g h : ↥O, RW.residue ⟨(h : ↥F₀), hOW' h h.2⟩ = 0 ∧ f = cy * g + h := by
    intro f hf
    obtain ⟨a, b, c, habc⟩ := hdesc f hf
    refine ⟨b, a * cx + c * ⟨_, hπO⟩, ?_, by rw [habc]; ring⟩
    rw [hRWres]
    have hcxM : (⟨((cx : ↥O) : ↥F₀), hOW _ cx.2⟩ : ↥Wx) ∈ maximalIdeal ↥Wx := hcxWxm (hOW _ cx.2)
    have hπM : (⟨_, hπW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx := hunifW.ge (Ideal.mem_span_singleton_self _)
    have hcx0 : IsLocalRing.residue ↥Wx (NodePtSol.toVal O Wx hOW cx) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hcxM
    have hp0 : IsLocalRing.residue ↥Wx (NodePtSol.toVal O Wx hOW ⟨_, hπO⟩) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hπM
    have hsum : IsLocalRing.residue ↥Wx (NodePtSol.toVal O Wx hOW (a * cx + c * ⟨_, hπO⟩)) = 0 := by
      simp only [map_add, map_mul, hcx0, hp0, zero_mul, mul_zero, add_zero, zero_add]
    exact hsum
  have hnoeth : IsNoetherianRing
      ↥(RW.residue.comp (Subring.inclusion (show O ≤ RW.integers.toSubring from fun f hf => hOW' f hf))).range := by
    set ψ := RW.residue.comp (Subring.inclusion (show O ≤ RW.integers.toSubring from fun f hf => hOW' f hf))
    haveI : IsNoetherianRing (↥O ⧸ RingHom.ker ψ) := inferInstance
    exact isNoetherianRing_of_ringEquiv _ (RingHom.quotientKerEquivRange ψ)
  have hPm : NodePtSol.centre O Wx hOW ≠ maximalIdeal ↥O := by
    intro heq
    have hmem : cy ∈ NodePtSol.centre O Wx hOW := by rw [heq]; exact (IsLocalRing.mem_maximalIdeal _).mpr hcynu
    rw [NodePtSol.mem_centre_iff] at hmem
    exact hcyWxm (hOW _ cy.2) ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hOW _ cy.2⟩)).mp hmem)
  have hfrac : ∀ z : ResidueField ↥Wx, ∃ f g : ↥O, RW.residue ⟨(g : ↥F₀), hOW' g g.2⟩ ≠ 0 ∧
      z * RW.residue ⟨(g : ↥F₀), hOW' g g.2⟩ = RW.residue ⟨(f : ↥F₀), hOW' f f.2⟩ := by
    intro z
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨g, h, hgO, hhO, hh0, hwh⟩ := hOfrac (w : ↥F₀)
    obtain ⟨r, s, hsP, hrs⟩ :=
      IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
        _ hirr E₀ hE₀ ι O.subtype (fun a b hab => Subtype.ext hab) Wx (fun b => hOW _ b.2)
        (NodePtSol.centre O Wx hOW) (fun b => NodePtSol.mem_centre_iff O Wx hOW b) hPm
        (w : ↥F₀) w.2 ⟨⟨g, hgO⟩, ⟨h, hhO⟩, fun h0 => hh0 (congrArg Subtype.val h0), hwh⟩
    refine ⟨r, s, ?_, ?_⟩
    · rw [hRWres, IsLocalRing.residue_ne_zero_iff_isUnit]
      rw [NodePtSol.mem_centre_iff] at hsP
      by_contra hsu
      exact hsP ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hOW _ s.2⟩)).mpr
        ((IsLocalRing.mem_maximalIdeal _).mpr hsu))
    · rw [hRWres, hRWres, ← map_mul]
      congr 1
      exact Subtype.ext hrs
  obtain ⟨x₁, hx₁rat, hx₁val, hx₁nu, -, hx₁ord, -, hx₁uniq⟩ :=
    AlgebraicCurve.RegularProlongation.exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
      (NodePtSol.A0 k₀ A) RW O hOW' hA' hres'' cy hcynu hy0 hmax hnoeth hfrac

  haveI hψloc : IsLocalHom (R.residue.comp ψ₀) := ⟨fun f hu =>
    hψ₀u f (R.isUnit_of_residue_ne_zero hu.ne_zero)⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField ↥Wx →+* FSS, ∀ f : ↥Wx, φ (IsLocalRing.residue ↥Wx f) = R.residue (ψ₀ f) :=
    ⟨IsLocalRing.ResidueField.lift (R.residue.comp ψ₀), fun f => IsLocalRing.ResidueField.lift_residue_apply _ _⟩
  have hφbij : Function.Bijective φ := by
    refine ⟨φ.injective, fun z => ?_⟩
    obtain ⟨w, rfl⟩ := R.residue_surjective z
    obtain ⟨f, hf⟩ := hNNR w
    exact ⟨IsLocalRing.residue ↥Wx f, by rw [hφ, hf]⟩
  obtain ⟨e, he⟩ : ∃ e : ResidueField ↥Wx ≃+* FSS, ∀ f : ↥Wx, e (IsLocalRing.residue ↥Wx f) = R.residue (ψ₀ f) :=
    ⟨RingEquiv.ofBijective φ hφbij, fun f => hφ f⟩

  have hres_eq : ∀ (f : ↥F₀) (hW : f ∈ Wx) (hR : (f : NodePtSol.FB q M') ∈ R.integers),
      R.residue ⟨(f : NodePtSol.FB q M'), hR⟩ = e (IsLocalRing.residue ↥Wx ⟨f, hW⟩) := by
    intro f hW hR; rw [he]; congr 1; exact Subtype.ext (by rw [hψ₀val])

  have hconstC : ∀ c : ↥(NodePtSol.A0 k₀ A),
      R.residue (ψ₀ (NodePtSol.toW (NodePtSol.A0 k₀ A) Wx hAW c)) =
        algebraMap (ResidueField ↥A) FSS (IsLocalRing.residue ↥A ⟨((c : ↥k₀) : AlgebraicClosure ℚ), c.2⟩) := by
    intro c
    have h1 : ψ₀ (NodePtSol.toW (NodePtSol.A0 k₀ A) Wx hAW c) =
        ⟨algebraMap (AlgebraicClosure ℚ) (NodePtSol.FB q M') ((c : ↥k₀) : AlgebraicClosure ℚ),
          (R.algebraMap_mem_iff _).mpr c.2⟩ := Subtype.ext (by rw [hψ₀val]; rfl)
    rw [h1]
    exact R.residue_algebraMap ⟨((c : ↥k₀) : AlgebraicClosure ℚ), c.2⟩
  have hc : ∀ a₁ : ResidueField ↥(NodePtSol.A0 k₀ A), ∃ a₂ : ResidueField ↥A,
      e (algebraMap (ResidueField ↥(NodePtSol.A0 k₀ A)) (ResidueField ↥Wx) a₁) = algebraMap (ResidueField ↥A) FSS a₂ := by
    intro a₁
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective a₁
    refine ⟨IsLocalRing.residue ↥A ⟨((c : ↥k₀) : AlgebraicClosure ℚ), c.2⟩, ?_⟩
    rw [NodePtSol.resAlg_residue, he, hconstC]
  have hK : ∀ a : ResidueField ↥A, e.symm (algebraMap (ResidueField ↥A) FSS a) ∈ x₁.toValuationSubring := by
    intro a
    obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c, hcA, hm, hmx⟩ := hκ a' a'.2
    have hsplit : algebraMap (ResidueField ↥A) FSS (IsLocalRing.residue ↥A a') =
        R.residue (ψ₀ (NodePtSol.toW (NodePtSol.A0 k₀ A) Wx hAW ⟨c, hcA⟩)) := by
      have h1 : a' = ⟨(c : AlgebraicClosure ℚ), hcA⟩ + ⟨(a' : AlgebraicClosure ℚ) - c, hm⟩ := Subtype.ext (by simp)
      rw [hconstC, h1, map_add, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmx, map_zero, add_zero]
    rw [hsplit, ← he, RingEquiv.symm_apply_apply, ← NodePtSol.resAlg_residue]
    exact x₁.algebraMap_mem' _
  refine ⟨NodePtSol.transfer e x₁ hK, NodePtSol.transfer_isRational e x₁ hK hx₁rat hc, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro f hfO hR
    rw [NodePtSol.mem_transfer_iff, hres_eq f (hOW f hfO) hR, RingEquiv.symm_apply_apply]
    exact (hx₁val _).mpr ⟨⟨f, hfO⟩, hRWres _ _⟩
  ·
    intro f hfO hR hnu
    have hmem : e.symm (R.residue ⟨(f : NodePtSol.FB q M'), hR⟩) ∈ x₁.toValuationSubring := by
      rw [hres_eq f (hOW f hfO) hR, RingEquiv.symm_apply_apply]; exact (hx₁val _).mpr ⟨⟨f, hfO⟩, hRWres _ _⟩
    refine ⟨(NodePtSol.mem_transfer_iff e x₁ hK _).mpr hmem, ?_⟩
    have hnu' := hx₁nu ⟨f, hfO⟩ hnu
    have hxm : (⟨_, hmem⟩ : ↥x₁.toValuationSubring) ∈ maximalIdeal ↥x₁.toValuationSubring := by
      apply (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mp
      show e.symm (R.residue ⟨(f : NodePtSol.FB q M'), hR⟩) ∈ x₁.toValuationSubring.nonunits
      rw [hres_eq f (hOW f hfO) hR, RingEquiv.symm_apply_apply, ← hRWres]
      exact hnu'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm ⊢
    intro hu; apply hxm
    have : NodePtSol.valEquiv e x₁.toValuationSubring ⟨_, hmem⟩ =
        (⟨R.residue ⟨(f : NodePtSol.FB q M'), hR⟩, (NodePtSol.mem_transfer_iff e x₁ hK _).mpr hmem⟩ :
          ↥(NodePtSol.transfer e x₁ hK).toValuationSubring) :=
      Subtype.ext (show e (e.symm _) = _ from e.apply_symm_apply _)
    rw [← this] at hu
    exact (isUnit_map_iff (NodePtSol.valEquiv e x₁.toValuationSubring) _).mp hu
  ·
    intro y hy₁ hy₂
    have hK' : ∀ a₁ : ResidueField ↥(NodePtSol.A0 k₀ A),
        e.symm.symm (algebraMap (ResidueField ↥(NodePtSol.A0 k₀ A)) (ResidueField ↥Wx) a₁) ∈ y.toValuationSubring := by
      intro a₁
      obtain ⟨a₂, ha₂⟩ := hc a₁
      rw [RingEquiv.symm_symm, ha₂]
      exact y.algebraMap_mem' _
    have hyx : NodePtSol.transfer e.symm y hK' = x₁ := by
      apply hx₁uniq
      intro f
      rw [NodePtSol.mem_transfer_iff, RingEquiv.symm_symm, hRWres,
        ← hres_eq (f : ↥F₀) (hOW _ f.2) ((hRW _).mpr (hOW _ f.2))]
      exact hy₁ f f.2 _
    apply (NodePtSol.transfer_eq_iff e x₁ hK y).mpr
    intro z
    rw [← hyx, NodePtSol.mem_transfer_iff, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
  ·
    intro h₂
    rw [hres_eq _ (hOW _ cx.2) h₂, (IsLocalRing.residue_eq_zero_iff _).mpr (hcxWxm (hOW _ cx.2)), map_zero]
  ·
    intro h₂
    rw [hres_eq _ (hOW _ cy.2) h₂]
    have hx₁ord' : x₁.ord (IsLocalRing.residue ↥Wx ⟨((cy : ↥O) : ↥F₀), hOW _ cy.2⟩) = 1 := by
      rw [hRWres] at hx₁ord; exact hx₁ord
    exact NodePtSol.transfer_ord_eq_one e x₁ hK ((hx₁val _).mpr ⟨cy, hRWres _ _⟩) hx₁ord'

end S_ModularCurve_FullLevel_exists_branchPlace_of_igusaEnd_of_node_crossingPresentation_igusaBranch
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_branchPlace_of_igusaEnd_of_node_crossingPresentation_igusaBranch (solution)
