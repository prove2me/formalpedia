-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/95ab63f3-1e62-5868-9483-976612488792

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isProper_toCrossing
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_isInvertible_of_mul_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero.AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient"

noncomputable section

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.IdealSheafData.support_comap IsClosedImmersion.of_isPreimmersion Spec.map_apply Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Opens.range_ι Scheme.Hom Scheme.IdealSheafData.support_pow_succ Etale.of_comp IsOpenImmersion.of_flat_of_mono Scheme.IdealSheafData.top_mul UniversallyClosed Scheme.Hom.support_ker LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Scheme.Hom.comp_base Scheme.IdealSheafData.support_top Flat Scheme.IdealSheafData.ideal IsClosedImmersion IsSeparated HasRingHomProperty.appLE Scheme.IdealSheafData.support_sup Scheme.Cover.mkOfCovers Etale Scheme.Hom.preimage_image_eq Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.IdealSheafData.comap Scheme.Opens Scheme.Opens.mem_ι_image_iff Scheme.IdealSheafData.ofIdealTop Scheme.Pullback.exists_preimage_pullback Scheme.IdealSheafData.ext HasRingHomProperty Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Cover Scheme.ΓSpecIso Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.IdealSheafData.IsInvertible Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso isOpenImmersion_and_isClosedImmersion_of_comp_eq_id Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.comap_ofIdealTop Scheme.IdealSheafData.isInvertible_and_isInvertible_of_mul_of_sup_eq_top Scheme.IdealSheafData.IsInvertible.comap_of_isIntegral Scheme.IdealSheafData.ideal_comap_of_le Scheme.Modules.exists_hom_tensorUnit_app_eq_smul Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.IdealSheafData.nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen IdealSheafData.support_comap IdealSheafData.one_eq_top Modules.pullback Opens.range_ι Hom mk IdealSheafData.support_pow_succ Γ empty IdealSheafData.top_mul Hom.support_ker IdealSheafData.comap_top OpenCover IdealSheafData.ker_fst_of_isClosedImmersion Hom.comp_base IdealSheafData.support_top IdealSheafData.ideal affineBasicOpen affineOpens basicOpen IdealSheafData.support_sup Cover.mkOfCovers Hom.preimage_image_eq isBasis_affineOpens IdealSheafData.support_eq_bot_iff Modules IdealSheafData.comap Opens residue Opens.mem_ι_image_iff IdealSheafData.ofIdealTop Pullback.exists_preimage_pullback IdealSheafData.ext basicOpen_le Hom.comp_apply IdealSheafData Cover ΓSpecIso evaluation IdealSheafData.module IdealSheafData.invModule IdealSheafData.IsInvertible Modules.zeroSchemeIdeal Modules.IsInvertible Modules.pullbackUnitIso Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support IdealSheafData.comap_mul IdealSheafData.comap_ofIdealTop IdealSheafData.isInvertible_and_isInvertible_of_mul_of_sup_eq_top IdealSheafData.IsInvertible.comap_of_isIntegral IdealSheafData.ideal_comap_of_le Modules.exists_hom_tensorUnit_app_eq_smul Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul Modules.IsInvertible.isIso_ev_app_tensorUnit IdealSheafData.nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "support_comap one_eq_top support_pow_succ mk map top_mul vanishingIdeal comap_top ker_fst_of_isClosedImmersion support_top ideal support_sup support_eq_bot_iff comap ofIdealTop support module invModule IsInvertible isInvertible_top IsInvertible.mul IsInvertible.pow comap_mul comap_ofIdealTop isInvertible_and_isInvertible_of_mul_of_sup_eq_top IsInvertible.comap_of_isIntegral ideal_comap_of_le IsInvertible.nonempty_mul_module_iso_tensor IsInvertible.nonempty_mul_invModule_iso_tensor IsInvertible.isInvertible_module nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem mem_nonZeroDivisors_of_isSMulRegular {S : Type*} [CommRing S] {s : S} (h : IsSMulRegular S s) :
    s ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => h ?_, fun x hx => h ?_⟩
  · show s • x = s • 0
    rw [smul_eq_mul, smul_eq_mul, mul_zero]; exact hx
  · show s • x = s • 0
    rw [smul_eq_mul, smul_eq_mul, mul_zero, mul_comm]; exact hx

theorem map_mem_nonZeroDivisors_of_flat {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    {a : R} (ha : a ∈ nonZeroDivisors R) : φ a ∈ nonZeroDivisors S := by
  letI := φ.toAlgebra
  haveI : Module.Flat R S := hφ
  have reg : IsSMulRegular R a := (isRegular_iff_mem_nonZeroDivisors.mpr ha).left
  exact mem_nonZeroDivisors_of_isSMulRegular reg.of_flat

namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" "mul pow comap_of_isIntegral nonempty_mul_module_iso_tensor nonempty_mul_invModule_iso_tensor isInvertible_module" end IsInvertible
p2m_open_scoped "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" in

theorem IsInvertible.comap_of_flat {X Y : Scheme.{u}} {I : Y.IdealSheafData} (hI : I.IsInvertible)
    (g : X ⟶ Y) [Flat g] : (I.comap g).IsInvertible := by
  intro x
  obtain ⟨U, f, hxf, a, ha, hIa⟩ := hI (g.base x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (g ⁻¹ᵁ Y.basicOpen f : X.Opens) from hxf) (g ⁻¹ᵁ Y.basicOpen f).isOpen
  let V' : X.affineOpens := ⟨V, hV⟩
  refine ⟨V', 1, by simpa using hxV, ?_⟩
  have hVle' : (V' : X.Opens) ≤ g ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) := hVle
  have hle : (X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) ≤ g ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) :=
    (X.basicOpen_le (1 : Γ(X, V'))).trans hVle'
  have key := Scheme.IdealSheafData.ideal_comap_of_le I g (Y.affineBasicOpen f)
    (X.affineBasicOpen (1 : Γ(X, V'))) hle
  rw [hIa, Ideal.map_span, Set.image_singleton] at key
  refine ⟨(g.appLE _ _ hle).hom a, ?_, key⟩
  have hflat : RingHom.Flat (g.appLE (Y.affineBasicOpen f) (X.affineBasicOpen (1 : Γ(X, V'))) hle).hom :=
    HasRingHomProperty.appLE @Flat g inferInstance _ _ hle
  exact map_mem_nonZeroDivisors_of_flat _ hflat ha

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.IdealSheafData.support_comap IsClosedImmersion.of_isPreimmersion Spec.map_apply Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Opens.range_ι Scheme.Hom Scheme.IdealSheafData.support_pow_succ Etale.of_comp IsOpenImmersion.of_flat_of_mono Scheme.IdealSheafData.top_mul UniversallyClosed Scheme.Hom.support_ker LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Scheme.Hom.comp_base Scheme.IdealSheafData.support_top Flat Scheme.IdealSheafData.ideal IsClosedImmersion IsSeparated HasRingHomProperty.appLE Scheme.IdealSheafData.support_sup Scheme.Cover.mkOfCovers Etale Scheme.Hom.preimage_image_eq Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules FormallyUnramified Scheme.IdealSheafData.comap Scheme.Opens Scheme.Opens.mem_ι_image_iff Scheme.IdealSheafData.ofIdealTop Scheme.Pullback.exists_preimage_pullback Scheme.IdealSheafData.ext HasRingHomProperty Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Cover Scheme.ΓSpecIso Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.IdealSheafData.IsInvertible Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso isOpenImmersion_and_isClosedImmersion_of_comp_eq_id Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.comap_ofIdealTop Scheme.IdealSheafData.isInvertible_and_isInvertible_of_mul_of_sup_eq_top Scheme.IdealSheafData.IsInvertible.comap_of_isIntegral Scheme.IdealSheafData.ideal_comap_of_le Scheme.Modules.exists_hom_tensorUnit_app_eq_smul Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.IdealSheafData.nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg"
namespace Layer0
namespace DescLoc
p2m_open "AlgebraicGeometry"

def princ {B : Type u} [CommRing B] (b : B) : (Spec (CommRingCat.of B)).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b})))).ker

def twist {Z : Scheme.{u}} (I : Z.IdealSheafData) (pos neg : ℕ) : Z.Modules :=
  (I ^ pos).invModule ⊗ (I ^ neg).module

def vertTwist {Z : Scheme.{u}} {n : ℕ} (I : Fin n → Z.IdealSheafData) (pos neg : Fin n → ℕ) : Z.Modules :=
  (List.finRange n).foldr (fun k M => twist (I k) (pos k) (neg k) ⊗ M) (𝟙_ Z.Modules)

def Principal {Z : Scheme.{u}} (J : Z.IdealSheafData) : Prop :=
  ∃ t : 𝟙_ Z.Modules ⟶ 𝟙_ Z.Modules, J = Scheme.Modules.zeroSchemeIdeal t

theorem eq_add_mul_of_second_diff_eq_zero (e : ℕ) (a : ℕ → ℤ)
    (h : ∀ k, 0 < k → k < e → a (k - 1) - 2 * a k + a (k + 1) = 0) :
    ∀ k ≤ e, a k = a 0 + k * (a 1 - a 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k with
    | 0 => simp
    | 1 => simp
    | (n + 2) =>
      have h1 := ih (n + 1) (by omega) (by omega)
      have h0 := ih n (by omega) (by omega)
      have hh := h (n + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hh
      push_cast at h0 h1 ⊢
      linear_combination hh + 2 * h1 - h0

theorem isOpenImmersion_and_isClosedImmersion_of_comp_eq_id' {Z T : Scheme.{u}} (p : Z ⟶ T) [Etale p] [IsSeparated p]
    (s : T ⟶ Z) (hs : s ≫ p = 𝟙 T) : IsOpenImmersion s ∧ IsClosedImmersion s :=
  AlgebraicGeometry.isOpenImmersion_and_isClosedImmersion_of_comp_eq_id p s hs

theorem exists_comap_ker_eq_ker_mul {Y M T : Scheme.{u}} (πY : Y ⟶ T) (πM : M ⟶ T) (g : Y ⟶ M) (hg : g ≫ πM = πY)
    [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated πY] (t : T ⟶ M) (ht : t ≫ πM = 𝟙 T) [IsClosedImmersion t]
    (σ : T ⟶ Y) (hσ : σ ≫ g = t) :
    ∃ H : Y.IdealSheafData, t.ker.comap g = σ.ker * H ∧ σ.ker ⊔ H = ⊤ ∧
      (H.support : Set Y) = ((t.ker.comap g).support : Set Y) \ Set.range σ.base := by

  set i : pullback g t ⟶ Y := pullback.fst g t with hi
  set p₂ : pullback g t ⟶ T := pullback.snd g t with hp₂
  have hip : i ≫ πY = p₂ := by
    rw [hi, hp₂, ← hg, pullback.condition_assoc, ht, Category.comp_id]
  haveI : IsSeparated p₂ := by rw [← hip]; infer_instance
  haveI : FormallyUnramified p₂ := MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance

  set s : T ⟶ pullback g t := pullback.lift σ (𝟙 T) (by rw [hσ, Category.id_comp]) with hs
  have hs₂ : s ≫ p₂ = 𝟙 T := pullback.lift_snd _ _ _
  have hsi : s ≫ i = σ := pullback.lift_fst _ _ _
  obtain ⟨hso, hsc⟩ := AlgebraicGeometry.isOpenImmersion_and_isClosedImmersion_of_comp_eq_id p₂ s hs₂

  let W : (pullback g t).Opens := ⟨(Set.range s.base)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hWc : IsClosed (W : Set ↥(pullback g t)) := s.isOpenEmbedding.isOpen_range.isClosed_compl

  let 𝒰 : (pullback g t).OpenCover := Scheme.Cover.mkOfCovers Bool (fun b => bif b then T else (W : Scheme.{u}))
    (fun b => match b with
      | true => s
      | false => W.ι)
    (fun z => by
      by_cases hz : z ∈ Set.range s.base
      · obtain ⟨w, rfl⟩ := hz; exact ⟨true, w, rfl⟩
      · exact ⟨false, ⟨z, hz⟩, rfl⟩)
    (fun b => by cases b <;> dsimp <;> infer_instance)
  haveI : IsClosedImmersion σ := by rw [← hsi]; infer_instance

  have hA : ((σ.ker).support : Set Y) = Set.range σ.base := by
    rw [Scheme.Hom.support_ker, σ.isClosedEmbedding.isClosed_range.closure_eq]
  haveI : IsClosedImmersion W.ι := IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hWc)
  have hB : (((W.ι ≫ i).ker).support : Set Y) = i.base '' (W : Set ↥(pullback g t)) := by
    rw [Scheme.Hom.support_ker, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      (i.isClosedEmbedding.isClosedMap _ hWc).closure_eq]
  have hrs : Set.range σ.base = i.base '' Set.range s.base := by
    rw [← hsi, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hdisj : Set.range σ.base ∩ i.base '' (W : Set ↥(pullback g t)) = ∅ := by
    rw [hrs, ← Set.image_inter i.isClosedEmbedding.injective]
    show i.base '' (Set.range s.base ∩ (Set.range s.base)ᶜ) = ∅
    rw [Set.inter_compl_self, Set.image_empty]

  have hcop : σ.ker ⊔ (W.ι ≫ i).ker = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    apply SetLike.coe_injective
    show ((σ.ker ⊔ (W.ι ≫ i).ker).support : Set Y) = ((⊥ : TopologicalSpace.Closeds Y) : Set Y)
    rw [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf, hA, hB, hdisj, TopologicalSpace.Closeds.coe_bot]

  have hinf : i.ker = σ.ker ⊓ (W.ι ≫ i).ker := by
    rw [← i.iInf_ker_openCover_map_comp 𝒰]
    show (⨅ b : Bool, (𝒰.f b ≫ i).ker) = _
    rw [iInf_bool_eq]
    show (s ≫ i).ker ⊓ (W.ι ≫ i).ker = _
    rw [hsi]
  refine ⟨(W.ι ≫ i).ker, ?_, hcop, ?_⟩
  · rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion t g]
    show i.ker = _
    rw [hinf]
    refine Scheme.IdealSheafData.ext ?_
    funext V
    show σ.ker.ideal V ⊓ ((W.ι ≫ i).ker).ideal V = σ.ker.ideal V * ((W.ι ≫ i).ker).ideal V
    exact (Ideal.mul_eq_inf_of_coprime (congrFun (congrArg Scheme.IdealSheafData.ideal hcop) V)).symm
  · rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion t g, hB, Scheme.Hom.support_ker,
      i.isClosedEmbedding.isClosed_range.closure_eq, hrs]
    show i.base '' (Set.range s.base)ᶜ = _
    rw [Set.image_compl_eq_range_diff_image i.isClosedEmbedding.injective]

theorem support_inter_fibre_eq_empty {Y M T : Scheme.{u}} (πY : Y ⟶ T) (πM : M ⟶ T) (g : Y ⟶ M) (hg : g ≫ πM = πY)
    (t : T ⟶ M) (ht : t ≫ πM = 𝟙 T) [IsClosedImmersion t] (σ : T ⟶ Y)
    (H : Y.IdealSheafData) (hsupp : (H.support : Set Y) = ((t.ker.comap g).support : Set Y) \ Set.range σ.base)
    (s₀ : T) (hinj : ∀ y : Y, πY.base y = s₀ → g.base y = t.base s₀ → y = σ.base s₀) :
    (H.support : Set Y) ∩ πY.base ⁻¹' {s₀} = ∅ := by
  rw [hsupp, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, Scheme.Hom.support_ker,
    t.isClosedEmbedding.isClosed_range.closure_eq]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and, and_imp]
  rintro ⟨s', hs'⟩ hy2 hy3
  have hs0 : s' = s₀ := by
    have h1 : (t ≫ πM).base s' = s' := by rw [ht]; rfl
    rw [← h1, Scheme.Hom.comp_apply, hs', ← Scheme.Hom.comp_apply, hg, hy3]
  exact hy2 ⟨s₀, (hinj y hy3 (by rw [← hs', hs0])).symm⟩

section Bridges

variable {X Y : Scheme.{u}}

theorem principal_ofIdealTop_span (r : Γ(X, ⊤)) : Principal (Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})) := by
  obtain ⟨t, -, ht⟩ := AlgebraicGeometry.Scheme.Modules.exists_hom_tensorUnit_app_eq_smul r
  exact ⟨t, (AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul t r ht).symm⟩

theorem comap_ofIdealTop_span (r : Γ(Y, ⊤)) (f : X ⟶ Y) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})).comap f = Scheme.IdealSheafData.ofIdealTop (Ideal.span {f.appTop.hom r}) := by
  rw [Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]

theorem comap_pow (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.one_eq_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

theorem comap_prod {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData) (f : X ⟶ Y) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.one_eq_top]
  | cons i s hi ih => rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

end Bridges

section TwistCalcE23
variable {X : Scheme.{u}}

namespace TwistCalc

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable def moduleTensorInvModuleIso {I : X.IdealSheafData} (hI : I.IsInvertible) :
    I.module ⊗ I.invModule ≅ 𝟙_ X.Modules :=
  (@asIso _ _ _ _ ((ihom.ev I.module).app (𝟙_ X.Modules))
    (Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit (IsInvertible.isInvertible_module hI)) :
      I.module ⊗ I.invModule ≅ 𝟙_ X.Modules)

noncomputable def invModuleTensorModuleIso {I : X.IdealSheafData} (hI : I.IsInvertible) :
    I.invModule ⊗ I.module ≅ 𝟙_ X.Modules :=
  β_ _ _ ≪≫ moduleTensorInvModuleIso hI

noncomputable def mulModuleIso {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (I * J).module ≅ I.module ⊗ J.module :=
  (IsInvertible.nonempty_mul_module_iso_tensor hI hJ).some

noncomputable def mulInvModuleIso {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (I * J).invModule ≅ I.invModule ⊗ J.invModule :=
  (IsInvertible.nonempty_mul_invModule_iso_tensor hI hJ).some

noncomputable def shuffle (W X' Y Z : X.Modules) : (W ⊗ X') ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X' ⊗ Z) :=
  α_ W X' (Y ⊗ Z) ≪≫ whiskerLeftIso W ((α_ X' Y Z).symm ≪≫ whiskerRightIso (β_ X' Y) Z ≪≫ α_ Y X' Z) ≪≫
    (α_ W Y (X' ⊗ Z)).symm

noncomputable def moduleTopIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  let hT : (⊤ : X.IdealSheafData).IsInvertible := isInvertible_top
  let U : X.Modules := (⊤ : X.IdealSheafData).module
  let e : U ≅ U ⊗ U :=
    eqToIso (congrArg Scheme.IdealSheafData.module (Scheme.IdealSheafData.top_mul (I := ⊤)).symm) ≪≫
      mulModuleIso hT hT
  (ρ_ U).symm ≪≫ whiskerLeftIso U (moduleTensorInvModuleIso hT).symm ≪≫ (α_ U U _).symm ≪≫
    whiskerRightIso e.symm _ ≪≫ moduleTensorInvModuleIso hT

noncomputable def invModuleTopIso : (⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules :=
  (λ_ _).symm ≪≫ whiskerRightIso moduleTopIso.symm _ ≪≫ moduleTensorInvModuleIso isInvertible_top

theorem isInvertible_list_prod (l : List X.IdealSheafData) (hl : ∀ I ∈ l, I.IsInvertible) :
    l.prod.IsInvertible := by
  induction l with
  | nil => exact isInvertible_top
  | cons a l ih =>
    rw [List.prod_cons]
    exact IsInvertible.mul (hl a (by simp)) (ih fun I hI => hl I (by simp [hI]))

noncomputable def splitIso {A A' B B' : X.IdealSheafData}
    (hA : A.IsInvertible) (hA' : A'.IsInvertible) (hB : B.IsInvertible) (hB' : B'.IsInvertible) :
    (A * A').invModule ⊗ (B * B').module ≅ (A.invModule ⊗ B.module) ⊗ (A'.invModule ⊗ B'.module) :=
  (mulInvModuleIso hA hA' ⊗ᵢ mulModuleIso hB hB') ≪≫ shuffle _ _ _ _

theorem nonempty_foldr_list {m : ℕ} (A B : Fin m → X.IdealSheafData)
    (hA : ∀ j, (A j).IsInvertible) (hB : ∀ j, (B j).IsInvertible) (p n : Fin m → ℕ) (M : X.Modules)
    (l : List (Fin m)) :
    Nonempty (l.foldr (fun j N => ((A j ^ p j).invModule ⊗ (B j ^ n j).module) ⊗ N) M ≅
      (((l.map fun j => A j ^ p j).prod).invModule ⊗ ((l.map fun j => B j ^ n j).prod).module) ⊗ M) := by
  induction l with
  | nil =>
    refine ⟨(λ_ M).symm ≪≫ whiskerRightIso ((λ_ (𝟙_ X.Modules)).symm ≪≫
      (invModuleTopIso.symm ⊗ᵢ moduleTopIso.symm)) M⟩
  | cons j l ih =>
    obtain ⟨e⟩ := ih
    have hP : ((l.map fun j => A j ^ p j).prod).IsInvertible :=
      isInvertible_list_prod _ (by
        intro I hI; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hI; exact IsInvertible.pow (hA k) _)
    have hQ : ((l.map fun j => B j ^ n j).prod).IsInvertible :=
      isInvertible_list_prod _ (by
        intro I hI; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hI; exact IsInvertible.pow (hB k) _)
    refine ⟨whiskerLeftIso _ e ≪≫ (α_ _ _ M).symm ≪≫ whiskerRightIso
      (splitIso (IsInvertible.pow (hA j) (p j)) hP (IsInvertible.pow (hB j) (n j)) hQ).symm M ≪≫ ?_⟩
    simp only [List.map_cons, List.prod_cons]
    exact Iso.refl _

end TwistCalc

p2m_open "P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero.AlgebraicGeometry.Layer0.DescLoc.TwistCalc AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero.AlgebraicGeometry.Scheme.IdealSheafData"

theorem nonempty_invModule_mul_tensor_module_mul_iso (A B C : X.IdealSheafData)
    (hA : A.IsInvertible) (hB : B.IsInvertible) (hC : C.IsInvertible) :
    Nonempty ((A * C).invModule ⊗ (B * C).module ≅ A.invModule ⊗ B.module) := by
  refine ⟨(mulInvModuleIso hA hC ⊗ᵢ mulModuleIso hB hC) ≪≫ shuffle _ _ _ _ ≪≫
    whiskerLeftIso _ (invModuleTensorModuleIso hC) ≪≫ ρ_ _⟩

theorem nonempty_invModule_mul_tensor_module_mul_iso_tensor (A A' B B' : X.IdealSheafData)
    (hA : A.IsInvertible) (hA' : A'.IsInvertible) (hB : B.IsInvertible) (hB' : B'.IsInvertible) :
    Nonempty ((A * A').invModule ⊗ (B * B').module ≅ (A.invModule ⊗ B.module) ⊗ (A'.invModule ⊗ B'.module)) :=
  ⟨splitIso hA hA' hB hB'⟩

theorem nonempty_foldr_tensor_iso_prod {m : ℕ} (A B : Fin m → X.IdealSheafData)
    (hA : ∀ j, (A j).IsInvertible) (hB : ∀ j, (B j).IsInvertible) (p n : Fin m → ℕ) (M : X.Modules) :
    Nonempty ((List.finRange m).foldr (fun j N => ((A j ^ p j).invModule ⊗ (B j ^ n j).module) ⊗ N) M ≅
      ((∏ j, A j ^ p j).invModule ⊗ (∏ j, B j ^ n j).module) ⊗ M) := by
  rw [Fin.prod_univ_def, Fin.prod_univ_def]
  exact nonempty_foldr_list A B hA hB p n M (List.finRange m)

theorem nonempty_pow_invModule_iso_and_module_iso_of_eq_zeroSchemeIdeal (P : X.IdealSheafData) (hP : P.IsInvertible)
    (t : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (h : P = Scheme.Modules.zeroSchemeIdeal t) (n : ℕ) :
    Nonempty ((P ^ n).invModule ≅ 𝟙_ X.Modules) ∧ Nonempty ((P ^ n).module ≅ 𝟙_ X.Modules) := by

  have h1 : Nonempty (P.invModule ≅ 𝟙_ X.Modules) := by
    have := nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
      (ι := PUnit.{u + 1}) (fun _ => P) (fun _ => hP) (fun _ => 1) t
      (by rw [Fintype.prod_unique]; simpa only [pow_one] using h)
    rwa [Fintype.prod_unique, pow_one] at this
  obtain ⟨e₁⟩ := h1
  have e₂ : P.module ≅ 𝟙_ X.Modules :=
    (ρ_ _).symm ≪≫ whiskerLeftIso _ e₁.symm ≪≫ moduleTensorInvModuleIso hP
  constructor
  · induction n with
    | zero => exact ⟨(eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_zero P))) ≪≫ invModuleTopIso⟩
    | succ k ih =>
      obtain ⟨e⟩ := ih
      exact ⟨eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_succ P k)) ≪≫
        mulInvModuleIso (IsInvertible.pow hP k) hP ≪≫ (e ⊗ᵢ e₁) ≪≫ λ_ _⟩
  · induction n with
    | zero => exact ⟨(eqToIso (congrArg Scheme.IdealSheafData.module (pow_zero P))) ≪≫ moduleTopIso⟩
    | succ k ih =>
      obtain ⟨e⟩ := ih
      exact ⟨eqToIso (congrArg Scheme.IdealSheafData.module (pow_succ P k)) ≪≫
        mulModuleIso (IsInvertible.pow hP k) hP ≪≫ (e ⊗ᵢ e₂) ≪≫ λ_ _⟩

theorem TwistCalc.isInvertible_finset_prod {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact IsInvertible.mul (hI a (Finset.mem_insert_self a s))
      (ih fun i hi => hI i (Finset.mem_insert_of_mem hi))

theorem nonempty_prod_pow_invModule_iso_and_module_iso_of_eq_zeroSchemeIdeal {ι : Type*} [Fintype ι]
    (P : ι → X.IdealSheafData) (hP : ∀ i, (P i).IsInvertible) (t : ι → (𝟙_ X.Modules ⟶ 𝟙_ X.Modules))
    (h : ∀ i, P i = Scheme.Modules.zeroSchemeIdeal (t i)) (n : ι → ℕ) :
    Nonempty ((∏ i, P i ^ n i).invModule ≅ 𝟙_ X.Modules) ∧ Nonempty ((∏ i, P i ^ n i).module ≅ 𝟙_ X.Modules) := by
  classical
  suffices key : ∀ s : Finset ι, Nonempty ((∏ i ∈ s, P i ^ n i).invModule ≅ 𝟙_ X.Modules) ∧
      Nonempty ((∏ i ∈ s, P i ^ n i).module ≅ 𝟙_ X.Modules) from key Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact ⟨⟨invModuleTopIso⟩, ⟨moduleTopIso⟩⟩
  | insert a s ha ih =>
    obtain ⟨⟨e⟩, ⟨e'⟩⟩ := ih
    obtain ⟨⟨f⟩, ⟨f'⟩⟩ := nonempty_pow_invModule_iso_and_module_iso_of_eq_zeroSchemeIdeal (P a) (hP a) (t a) (h a) (n a)
    have ha' : (P a ^ n a).IsInvertible := IsInvertible.pow (hP a) (n a)
    have hs : (∏ i ∈ s, P i ^ n i).IsInvertible :=
      TwistCalc.isInvertible_finset_prod s _ fun i _ => IsInvertible.pow (hP i) (n i)
    rw [Finset.prod_insert ha]
    exact ⟨⟨mulInvModuleIso ha' hs ≪≫ (f ⊗ᵢ e) ≪≫ λ_ _⟩, ⟨mulModuleIso ha' hs ≪≫ (f' ⊗ᵢ e') ≪≫ λ_ _⟩⟩

end TwistCalcE23

theorem exists_open_preimage_subset_compl {X Y : Scheme.{u}} (U : X.Opens) (q : Y ⟶ (U : Scheme.{u})) [UniversallyClosed q]
    (Z : Set Y) (hZ : IsClosed Z) (x : X) (hxU : x ∈ U) (hx : ∀ z ∈ Z, (q.base z).1 ≠ x) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧ ((q ⁻¹ᵁ (U.ι ⁻¹ᵁ V) : Y.Opens) : Set Y) ⊆ Zᶜ := by
  have hC : IsClosed (q.base '' Z) := q.isClosedMap _ hZ
  let Vu : (U : Scheme.{u}).Opens := ⟨(q.base '' Z)ᶜ, hC.isOpen_compl⟩
  refine ⟨U.ι ''ᵁ Vu, ?_, U.ι_image_le Vu, ?_⟩
  · rw [show x = ((⟨x, hxU⟩ : U) : X) from rfl, Scheme.Opens.mem_ι_image_iff]
    rintro ⟨z, hz, hzx⟩
    exact hx z hz (congrArg Subtype.val hzx)
  · intro y hy hyZ
    have hy' : y ∈ q ⁻¹ᵁ Vu := by rwa [Scheme.Hom.preimage_image_eq] at hy
    exact hy' ⟨y, hyZ, rfl⟩

theorem support_pow_subset {Y : Scheme.{u}} (I : Y.IdealSheafData) (n : ℕ) :
    ((I ^ n).support : Set Y) ⊆ (I.support : Set Y) := by
  cases n with
  | zero =>
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot]
    exact Set.empty_subset _
  | succ n => rw [Scheme.IdealSheafData.support_pow_succ]

theorem nonempty_pullback_foldr_twist_iso {Y Y' : Scheme.{u}} (ι : Y' ⟶ Y)
    {r : ℕ} (J : Fin r → Y.IdealSheafData) (hJ : ∀ i, (J i).IsInvertible)
    (hJs : ∀ i (y : Y'), ι.base y ∉ ((J i).support : Set Y)) (jp jn : Fin r → ℕ) (M : Y.Modules)
    (hM : Nonempty ((Scheme.Modules.pullback ι).obj M ≅ (Scheme.Modules.pullback ι).obj (𝟙_ Y.Modules))) :
    Nonempty ((Scheme.Modules.pullback ι).obj ((List.finRange r).foldr (fun i N => twist (J i) (jp i) (jn i) ⊗ N) M) ≅
      (Scheme.Modules.pullback ι).obj (𝟙_ Y.Modules)) := by
  suffices h : ∀ l : List (Fin r), Nonempty ((Scheme.Modules.pullback ι).obj
      (l.foldr (fun i N => twist (J i) (jp i) (jn i) ⊗ N) M) ≅ (Scheme.Modules.pullback ι).obj (𝟙_ Y.Modules)) from h _
  intro l
  induction l with
  | nil => exact hM
  | cons i l ih =>
    rw [List.foldr_cons]
    have hsub : ∀ y : Y', ι.base y ∉ (((J i) ^ jn i).support : Set Y) := fun y h => hJs i y (support_pow_subset (J i) (jn i) h)
    obtain ⟨ε⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
      ι (J i) (hJ i) ((J i) ^ jn i) ((hJ i).pow (jn i)) (jp i) (hJs i) hsub _ ih
    exact ⟨(Scheme.Modules.pullback ι).mapIso (β_ _ _) ≪≫ ε⟩

theorem exists_arithProg_of_hdeg (e : ℕ) {m : ℕ} (pos neg d : Fin m → ℕ) (hd : ∀ j, 0 < d j ∧ d j < e)
    (vp vn : Fin (e + 1) → ℕ)
    (hdeg : ∀ k : ℕ, ∀ hk0 : 0 < k, ∀ hke : k < e,
      (∑ j, if d j = k then ((pos j : ℤ) - neg j) else 0) +
        (((vp ⟨k - 1, by omega⟩ : ℤ) - vn ⟨k - 1, by omega⟩) - 2 * ((vp ⟨k, by omega⟩ : ℤ) - vn ⟨k, by omega⟩) +
          ((vp ⟨k + 1, by omega⟩ : ℤ) - vn ⟨k + 1, by omega⟩)) = 0) :
    ∃ a₀ δ : ℤ, ∀ k : Fin (e + 1),
      ((vp k + ∑ j, neg j * min (k : ℕ) (d j) : ℕ) : ℤ) - ((vn k + ∑ j, pos j * min (k : ℕ) (d j) : ℕ) : ℤ) =
        a₀ + (k : ℕ) * δ := by

  let b : ℕ → ℤ := fun k => if h : k ≤ e then
    ((vp ⟨k, Nat.lt_succ_of_le h⟩ : ℤ) - vn ⟨k, Nat.lt_succ_of_le h⟩) - ∑ j, ((pos j : ℤ) - neg j) * min (k : ℤ) (d j : ℤ) else 0
  have hb : ∀ (k : ℕ) (h : k ≤ e), b k =
      ((vp ⟨k, Nat.lt_succ_of_le h⟩ : ℤ) - vn ⟨k, Nat.lt_succ_of_le h⟩) - ∑ j, ((pos j : ℤ) - neg j) * min (k : ℤ) (d j : ℤ) := by
    intro k h; simp only [b, dif_pos h]
  have h2 : ∀ k : ℕ, k + 1 < e → b k - 2 * b (k + 1) + b (k + 2) = 0 := by
    intro k hk
    rw [hb k (by omega), hb (k + 1) (by omega), hb (k + 2) (by omega)]
    have H := hdeg (k + 1) (by omega) hk
    simp only [Nat.add_sub_cancel] at H
    have hs : ∀ j, ((pos j : ℤ) - neg j) * min (k : ℤ) (d j) - 2 * (((pos j : ℤ) - neg j) * min ((k + 1 : ℕ) : ℤ) (d j)) +
        ((pos j : ℤ) - neg j) * min ((k + 2 : ℕ) : ℤ) (d j) = -(if d j = k + 1 then ((pos j : ℤ) - neg j) else 0) := by
      intro j
      have hm : min (k : ℤ) (d j) - 2 * min ((k + 1 : ℕ) : ℤ) (d j) + min ((k + 2 : ℕ) : ℤ) (d j) =
          if d j = k + 1 then -1 else 0 := by
        split_ifs <;> push_cast <;> omega
      split_ifs at hm ⊢ <;> linear_combination ((pos j : ℤ) - neg j) * hm
    have hs' := Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hs j)
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs'
    push_cast at H hs' ⊢
    linear_combination H - hs'
  refine ⟨b 0, b 1 - b 0, fun k => ?_⟩
  have hk : (k : ℕ) ≤ e := Nat.le_of_lt_succ k.2
  have := eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero e b h2 k hk
  rw [hb k hk] at this
  have hfin : (⟨(k : ℕ), Nat.lt_succ_of_le hk⟩ : Fin (e + 1)) = k := Fin.ext rfl
  rw [hfin] at this
  simp_rw [sub_mul, Finset.sum_sub_distrib] at this
  push_cast
  linear_combination this

theorem eq_of_U_mem_of_V_mem_of_algebraMap_mem {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ)
    (P P' : ↥(crossingScheme (ϖ ^ e)))
    (hU : CrossingQuotient.U (ϖ ^ e) ∈ P.asIdeal) (hV : CrossingQuotient.V (ϖ ^ e) ∈ P.asIdeal)
    (ht : algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ ∈ P.asIdeal)
    (hU' : CrossingQuotient.U (ϖ ^ e) ∈ P'.asIdeal) (hV' : CrossingQuotient.V (ϖ ^ e) ∈ P'.asIdeal)
    (ht' : algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ ∈ P'.asIdeal) : P = P' := by
  classical
  set B := CrossingQuotient O (ϖ ^ e) with hB
  let N : Ideal B := Ideal.span {CrossingQuotient.U (ϖ ^ e), CrossingQuotient.V (ϖ ^ e), algebraMap O B ϖ}
  have hNP : N ≤ P.asIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro b (rfl | rfl | rfl)
    exacts [hU, hV, ht]
  have hNP' : N ≤ P'.asIdeal := by
    refine Ideal.span_le.mpr ?_
    rintro b (rfl | rfl | rfl)
    exacts [hU', hV', ht']
  have hUN : CrossingQuotient.U (ϖ ^ e) ∈ N := Ideal.subset_span (by simp)
  have hVN : CrossingQuotient.V (ϖ ^ e) ∈ N := Ideal.subset_span (by simp)
  have htN : algebraMap O B ϖ ∈ N := Ideal.subset_span (by simp)

  let θ : O →+* B ⧸ N := (Ideal.Quotient.mk N).comp (algebraMap O B)
  have hsurj : Function.Surjective θ := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (ϖ ^ e)}) b
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
    | mul_X p i hp =>
      refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      fin_cases i
      · exact hUN
      · exact hVN

  have hNtop : N ≠ ⊤ := fun h => P.2.ne_top (top_le_iff.mp (h ▸ hNP))
  have hker : RingHom.ker θ = IsLocalRing.maximalIdeal O := by
    symm
    haveI : Nontrivial (B ⧸ N) := Ideal.Quotient.nontrivial_iff.mpr hNtop
    refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top θ) ?_
    rw [hϖ, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr htN
  have hmax : N.IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    have e₁ := RingHom.quotientKerEquivOfSurjective hsurj
    have hF : IsField (O ⧸ RingHom.ker θ) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (hker ▸ IsLocalRing.maximalIdeal.isMaximal O)
    exact MulEquiv.isField hF e₁.symm.toMulEquiv
  apply PrimeSpectrum.ext
  rw [← hmax.eq_of_le P.2.ne_top hNP, ← hmax.eq_of_le P'.2.ne_top hNP']

theorem apply_eq_closedPoint_of_U_mem_of_V_mem {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) (he : 1 ≤ e)
    {V : Scheme.{u}} (πV : V ⟶ Spec (CommRingCat.of O)) (f : V ⟶ crossingScheme (ϖ ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ e)))) = πV) (y : V)
    (hU : CrossingQuotient.U (ϖ ^ e) ∈ (f.base y).asIdeal) (hV : CrossingQuotient.V (ϖ ^ e) ∈ (f.base y).asIdeal) :
    πV.base y = IsLocalRing.closedPoint O := by
  rw [← hf, Scheme.Hom.comp_apply, Spec.map_apply]
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
  symm
  refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le Ideal.IsPrime.ne_top' ?_
  rw [hϖ, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  have hmem : (algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ) ^ e ∈ (f.base y).asIdeal := by
    rw [← map_pow, ← CrossingQuotient.U_mul_V]
    exact Ideal.mul_mem_left _ _ hV
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance e hmem

section Main

theorem exists_open_trivial
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) (he : 1 ≤ e)
    {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O)) [IsSeparated πX] (x : X) (U : X.Opens) (hxU : x ∈ U)
    (f : (U : Scheme.{u}) ⟶ crossingScheme (ϖ ^ e)) [LocallyOfFiniteType f] [FormallyUnramified f]
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ e)))) = U.ι ≫ πX)
    (f_mem_Vc_iff : ∀ y : U,
      f.base y ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens) ⊔
        (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens)) ↔ (y : X) ≠ x)

    (hinj : ∀ y y' : ↥(pullback f (Resolution.toCrossing ϖ e)),
      ((pullback.fst f (Resolution.toCrossing ϖ e)).base y).1 = x →
        ((pullback.fst f (Resolution.toCrossing ϖ e)).base y').1 = x →
          (pullback.snd f (Resolution.toCrossing ϖ e)).base y = (pullback.snd f (Resolution.toCrossing ϖ e)).base y' → y = y')

    [IsIntegral (pullback f (Resolution.toCrossing ϖ e))]
    (hgen : ∃ y : ↥(pullback f (Resolution.toCrossing ϖ e)),
      (pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX).base y ≠ IsLocalRing.closedPoint O)

    (Fc : Fin (e + 1) → (Resolution ϖ e).IdealSheafData) (hFc_inv : ∀ k, (Fc k).IsInvertible)
    (hFc_t : ∏ k, Fc k = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toSpec ϖ e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)}))
    (hFc_u : ∏ k, Fc k ^ (k : ℕ) = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toCrossing ϖ e).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom (CrossingQuotient.U (ϖ ^ e)))}))
    (hFc_supp : ∀ (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)), z ∈ (Fc k).support →
      (Resolution.toSpec ϖ e).base z = IsLocalRing.closedPoint O)
    (hFc_vertex : ∀ (k : ℕ) (hk0 : 0 < k) (hke : k < e) (z : ↥(Resolution ϖ e)), z ∈ (Fc ⟨k, by omega⟩).support →
      CrossingQuotient.U (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal ∧
        CrossingQuotient.V (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal)
    (hFc_node : ∀ (k : ℕ) (hke : k < e), ∃ z : ↥(Resolution ϖ e),
      z ∈ (Fc ⟨k, by omega⟩).support ∧ z ∈ (Fc ⟨k + 1, by omega⟩).support)
    (hFc_sect : ∀ (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e), t ≫ Resolution.toSpec ϖ e = 𝟙 _ →
      ∀ (dd : ℕ) (hd0 : 0 < dd) (hde : dd < e), t.base (IsLocalRing.closedPoint O) ∈ (Fc ⟨dd, by omega⟩).support →
      (∀ k : Fin (e + 1), (k : ℕ) ≠ dd → t.base (IsLocalRing.closedPoint O) ∉ (Fc k).support) →
      IsClosedImmersion t ∧ (t.ker).IsInvertible ∧
        ∃ rr : CrossingQuotient O (ϖ ^ e), t.ker * ∏ k, Fc k ^ (min (k : ℕ) dd) =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom rr)}))

    {m : ℕ} (σ : Fin m → (Spec (CommRingCat.of O) ⟶ pullback f (Resolution.toCrossing ϖ e)))
    (hσ : ∀ j, σ j ≫ pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX = 𝟙 _)
    (pos neg : Fin m → ℕ) (d : Fin m → ℕ) (hd : ∀ j, 0 < d j ∧ d j < e)
    (hσd : ∀ j, (σ j).base (IsLocalRing.closedPoint O) ∈
        ((Fc ⟨d j, (hd j).2.trans e.lt_succ_self⟩).comap (pullback.snd f (Resolution.toCrossing ϖ e))).support ∧
      ∀ k : Fin (e + 1), (k : ℕ) ≠ d j →
        (σ j).base (IsLocalRing.closedPoint O) ∉ ((Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e))).support)
    (vp vn : Fin (e + 1) → ℕ)
    {r : ℕ} (J : Fin r → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData) (hJ : ∀ i, (J i).IsInvertible)
    (hJs : ∀ i, ((J i).support : Set _) ∩
      (pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX).base ⁻¹' {IsLocalRing.closedPoint O} = ∅)
    (jp jn : Fin r → ℕ)
    (hdeg : ∀ k : ℕ, ∀ hk0 : 0 < k, ∀ hke : k < e,
      (∑ j, if d j = k then ((pos j : ℤ) - neg j) else 0) +
        (((vp ⟨k - 1, by omega⟩ : ℤ) - vn ⟨k - 1, by omega⟩) - 2 * ((vp ⟨k, by omega⟩ : ℤ) - vn ⟨k, by omega⟩) +
          ((vp ⟨k + 1, by omega⟩ : ℤ) - vn ⟨k + 1, by omega⟩)) = 0) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      Nonempty ((Scheme.Modules.pullback
          (pullback.fst f (Resolution.toCrossing ϖ e) ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).ι).obj
            ((List.finRange m).foldr (fun j M => ((((σ j).ker) ^ pos j).invModule ⊗ (((σ j).ker) ^ neg j).module) ⊗ M)
              ((List.finRange r).foldr (fun i M => (((J i) ^ jp i).invModule ⊗ ((J i) ^ jn i).module) ⊗ M)
                ((∏ k, (Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e)) ^ vp k).invModule ⊗
                  (∏ k, (Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e)) ^ vn k).module))) ≅
        𝟙_ _) := by
  classical

  haveI : IsProper (Resolution.toCrossing ϖ e) := Resolution.isProper_toCrossing ϖ e

  set q := pullback.fst f (Resolution.toCrossing ϖ e) with hq
  set g := pullback.snd f (Resolution.toCrossing ϖ e) with hg'
  set πY := q ≫ U.ι ≫ πX with hπY
  haveI : IsSeparated πY := by rw [hπY]; infer_instance
  haveI : LocallyOfFiniteType g := by rw [hg']; infer_instance
  haveI : FormallyUnramified g := by
    rw [hg']; exact MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance

  have hx' : ¬ (f.base ⟨x, hxU⟩ ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens) ⊔
      (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens))) := by
    rw [f_mem_Vc_iff]; exact fun h => h rfl
  have hUx : CrossingQuotient.U (ϖ ^ e) ∈ (f.base ⟨x, hxU⟩).asIdeal := by
    by_contra h
    exact hx' (TopologicalSpace.Opens.mem_sup.mpr (Or.inl ((PrimeSpectrum.mem_basicOpen _ _).mpr h)))
  have hVx : CrossingQuotient.V (ϖ ^ e) ∈ (f.base ⟨x, hxU⟩).asIdeal := by
    by_contra h
    exact hx' (TopologicalSpace.Opens.mem_sup.mpr (Or.inr ((PrimeSpectrum.mem_basicOpen _ _).mpr h)))
  have hxcl : (U.ι ≫ πX).base ⟨x, hxU⟩ = IsLocalRing.closedPoint O :=
    apply_eq_closedPoint_of_U_mem_of_V_mem ϖ hϖ e (by omega) (U.ι ≫ πX) f hf ⟨x, hxU⟩ hUx hVx

  have hover : ∀ P : ↥(crossingScheme (ϖ ^ e)),
      (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ e))))).base P = IsLocalRing.closedPoint O →
      algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ ∈ P.asIdeal := by
    intro P hP
    have h' := congrArg PrimeSpectrum.asIdeal hP
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom] at h'
    have : ϖ ∈ Ideal.comap (algebraMap O (CrossingQuotient O (ϖ ^ e))) P.asIdeal := by
      rw [h']
      show ϖ ∈ IsLocalRing.maximalIdeal O
      rw [hϖ]; exact Ideal.subset_span rfl
    exact Ideal.mem_comap.mp this
  have htx : algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ ∈ (f.base ⟨x, hxU⟩).asIdeal := by
    refine hover _ ?_
    rw [← Scheme.Hom.comp_apply, hf]; exact hxcl

  have hgS : g ≫ Resolution.toSpec ϖ e = πY := by
    rw [hπY, hg', hq, Resolution.toSpec, ← pullback.condition_assoc, hf]
  have hpt : ∀ y : ↥(pullback f (Resolution.toCrossing ϖ e)),
      f.base (q.base y) = (Resolution.toCrossing ϖ e).base (g.base y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hq, pullback.condition, Scheme.Hom.comp_apply]

  have key : ∀ (k : ℕ) (hk0 : 0 < k) (hke : k < e), ∀ y : ↥(pullback f (Resolution.toCrossing ϖ e)),
      g.base y ∈ (Fc ⟨k, by omega⟩).support → (q.base y).1 = x := by
    intro k hk0 hke y hy
    by_contra hne
    have hVc := (f_mem_Vc_iff (q.base y)).mpr hne
    rw [hpt y] at hVc
    obtain ⟨hU', hV'⟩ := hFc_vertex k hk0 hke _ hy
    rcases TopologicalSpace.Opens.mem_sup.mp hVc with h | h
    · exact (PrimeSpectrum.mem_basicOpen _ _).mp h hU'
    · exact (PrimeSpectrum.mem_basicOpen _ _).mp h hV'

  have ht : ∀ j, (σ j ≫ g) ≫ Resolution.toSpec ϖ e = 𝟙 _ := fun j => by rw [Category.assoc, hgS, hσ]
  have hmem : ∀ j, (σ j ≫ g).base (IsLocalRing.closedPoint O) ∈ (Fc ⟨d j, (hd j).2.trans e.lt_succ_self⟩).support := fun j => by
    have h := (hσd j).1
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h
  have hnot : ∀ j (k : Fin (e + 1)), (k : ℕ) ≠ d j → (σ j ≫ g).base (IsLocalRing.closedPoint O) ∉ (Fc k).support := by
    intro j k hne h
    have h' := (hσd j).2 k hne
    rw [Scheme.IdealSheafData.support_comap] at h'
    exact h' h
  have sect : ∀ j, ∃ rr : CrossingQuotient O (ϖ ^ e), IsClosedImmersion (σ j ≫ g) ∧ ((σ j ≫ g).ker).IsInvertible ∧
      (σ j ≫ g).ker * ∏ k, Fc k ^ (min (k : ℕ) (d j)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom rr)}) := fun j => by
    obtain ⟨h1, h2, rr, h3⟩ := hFc_sect (σ j ≫ g) (ht j) (d j) (hd j).1 (hd j).2 (hmem j) (hnot j)
    exact ⟨rr, h1, h2, h3⟩
  choose rr hci hkτ hrr using sect

  have step1 : ∀ j, ∃ (H : (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData),
      (σ j ≫ g).ker.comap g = (σ j).ker * H ∧ (σ j).ker ⊔ H = ⊤ ∧
      ((H.support : Set _) ∩ πY.base ⁻¹' {IsLocalRing.closedPoint O} = ∅) := by
    intro j
    haveI := hci j
    obtain ⟨H, hH1, hH2, hH3⟩ := exists_comap_ker_eq_ker_mul πY (Resolution.toSpec ϖ e) g hgS (σ j ≫ g) (ht j) (σ j) rfl
    refine ⟨H, hH1, hH2, ?_⟩
    refine support_inter_fibre_eq_empty πY (Resolution.toSpec ϖ e) g hgS (σ j ≫ g) (ht j) (σ j) H hH3
      (IsLocalRing.closedPoint O) fun y _ hy => ?_

    rw [Scheme.Hom.comp_apply] at hy
    have hm := hmem j
    rw [Scheme.Hom.comp_apply] at hm
    exact hinj y _ (key (d j) (hd j).1 (hd j).2 y (hy ▸ hm)) (key (d j) (hd j).1 (hd j).2 _ hm) hy
  choose H hHeq hHcop hHs using step1

  obtain ⟨y₀, hy₀⟩ := hgen
  have hFinv : ∀ k : Fin (e + 1), ((Fc k).comap g).IsInvertible := fun k => by
    refine (hFc_inv k).comap_of_isIntegral g fun huniv => hy₀ ?_
    have hy : y₀ ∈ (((Fc k).comap g).support : Set _) := huniv ▸ Set.mem_univ y₀
    rw [Scheme.IdealSheafData.support_comap] at hy
    rw [← hgS, Scheme.Hom.comp_apply]
    exact hFc_supp k _ hy
  have hKHinv : ∀ j, ((σ j).ker).IsInvertible ∧ (H j).IsInvertible := fun j => by
    refine Scheme.IdealSheafData.isInvertible_and_isInvertible_of_mul_of_sup_eq_top
      ((hHeq j) ▸ (hkτ j).comap_of_isIntegral g fun huniv => ?_) (hHcop j)

    obtain ⟨z, hz1, hz2⟩ := hFc_node (d j) (hd j).2
    obtain ⟨hUz, hVz⟩ := hFc_vertex (d j) (hd j).1 (hd j).2 z hz1
    have htz : algebraMap O (CrossingQuotient O (ϖ ^ e)) ϖ ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal := by
      refine hover _ ?_
      rw [← Scheme.Hom.comp_apply]
      exact hFc_supp _ z hz1
    have hfz : f.base ⟨x, hxU⟩ = (Resolution.toCrossing ϖ e).base z :=
      eq_of_U_mem_of_V_mem_of_algebraMap_mem ϖ hϖ e _ _ hUx hVx htx hUz hVz htz
    obtain ⟨y₁, -, hy1g⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := Resolution.toCrossing ϖ e) ⟨x, hxU⟩ z hfz
    have hy₁ : g.base y₁ ∉ Set.range (σ j ≫ g).base := by
      rintro ⟨s', hs'⟩
      have hs0 : s' = IsLocalRing.closedPoint O := by
        have h1 : ((σ j ≫ g) ≫ Resolution.toSpec ϖ e).base s' = s' := by rw [ht j]; rfl
        rw [← h1, Scheme.Hom.comp_apply, hs']
        show (Resolution.toSpec ϖ e).base (g.base y₁) = _
        rw [hg', hy1g]
        exact hFc_supp _ z hz1
      subst hs0
      have hmem' : (σ j ≫ g).base (IsLocalRing.closedPoint O) ∈ (Fc ⟨d j + 1, by have := (hd j).2; omega⟩).support := by
        rw [hs']
        show g.base y₁ ∈ _
        rw [hg', hy1g]; exact hz2
      exact hnot j ⟨d j + 1, by have := (hd j).2; omega⟩ (by simp) hmem'
    haveI := hci j
    have hy : y₁ ∈ ((((σ j ≫ g).ker).comap g).support : Set _) := huniv ▸ Set.mem_univ y₁
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, Scheme.Hom.support_ker,
      (σ j ≫ g).isClosedEmbedding.isClosed_range.closure_eq] at hy
    exact hy₁ hy
  have hKinv : ∀ j, ((σ j).ker).IsInvertible := fun j => (hKHinv j).1
  have hHinv : ∀ j, (H j).IsInvertible := fun j => (hKHinv j).2

  have step2a : Principal (∏ k, (Fc k).comap g) ∧ Principal (∏ k, (Fc k).comap g ^ (k : ℕ)) := by
    constructor
    · have h := congrArg (fun I => Scheme.IdealSheafData.comap I g) hFc_t
      simp only [comap_prod, comap_ofIdealTop_span] at h
      exact h ▸ principal_ofIdealTop_span _
    · have h := congrArg (fun I => Scheme.IdealSheafData.comap I g) hFc_u
      simp only [comap_prod, comap_pow, comap_ofIdealTop_span] at h
      exact h ▸ principal_ofIdealTop_span _
  have step2b : ∀ j, Principal ((σ j).ker * H j * ∏ k, (Fc k).comap g ^ (min (k : ℕ) (d j))) := by
    intro j
    have h := congrArg (fun I => Scheme.IdealSheafData.comap I g) (hrr j)
    simp only [Scheme.IdealSheafData.comap_mul, comap_prod, comap_pow, comap_ofIdealTop_span, hHeq j] at h
    exact h ▸ principal_ofIdealTop_span _

  obtain ⟨a₀, δ, hAP⟩ := exists_arithProg_of_hdeg e pos neg d hd vp vn hdeg
  choose tP htP using step2b
  obtain ⟨⟨tϖ, htϖ⟩, ⟨tu, htu⟩⟩ := step2a
  have step3 : Nonempty (
      (List.finRange m).foldr (fun j M => twist ((σ j).ker) (pos j) (neg j) ⊗ M)
        ((List.finRange r).foldr (fun i M => twist (J i) (jp i) (jn i) ⊗ M)
          ((∏ k, (Fc k).comap g ^ vp k).invModule ⊗ (∏ k, (Fc k).comap g ^ vn k).module)) ≅
      (List.finRange m).foldr (fun j M => twist (H j) (neg j) (pos j) ⊗ M)
        ((List.finRange r).foldr (fun i M => twist (J i) (jp i) (jn i) ⊗ M) (𝟙_ _))) := by

    let Fk : Fin (e + 1) → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData := fun k => (Fc k).comap g
    let K : Fin m → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData := fun j => (σ j).ker
    let Vj : Fin m → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData := fun j => ∏ k, Fk k ^ min (k : ℕ) (d j)
    let P : Fin m → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData := fun j => K j * H j * Vj j
    let KP := ∏ j, K j ^ pos j
    let KN := ∏ j, K j ^ neg j
    let HP := ∏ j, H j ^ pos j
    let HN := ∏ j, H j ^ neg j
    let JP := ∏ i, J i ^ jp i
    let JN := ∏ i, J i ^ jn i
    let Fvp := ∏ k, Fk k ^ vp k
    let Fvn := ∏ k, Fk k ^ vn k
    let C := ∏ j, (H j * Vj j) ^ (pos j + neg j)
    let W₁ := (∏ j, Vj j ^ neg j) * Fvp
    let W₂ := (∏ j, Vj j ^ pos j) * Fvn

    have hprod : ∀ {ι : Type} [Fintype ι] (I : ι → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData),
        (∀ i, (I i).IsInvertible) → (∏ i, I i).IsInvertible := fun I hI =>
      TwistCalc.isInvertible_finset_prod _ _ fun i _ => hI i
    have hVinv : ∀ j, (Vj j).IsInvertible := fun j => hprod _ fun k => (hFinv k).pow _
    have hPinv : ∀ j, (P j).IsInvertible := fun j => ((hKinv j).mul (hHinv j)).mul (hVinv j)
    have hKP : KP.IsInvertible := hprod _ fun j => (hKinv j).pow _
    have hKN : KN.IsInvertible := hprod _ fun j => (hKinv j).pow _
    have hHP : HP.IsInvertible := hprod _ fun j => (hHinv j).pow _
    have hHN : HN.IsInvertible := hprod _ fun j => (hHinv j).pow _
    have hFvp : Fvp.IsInvertible := hprod _ fun k => (hFinv k).pow _
    have hFvn : Fvn.IsInvertible := hprod _ fun k => (hFinv k).pow _
    have hC : C.IsInvertible := hprod _ fun j => ((hHinv j).mul (hVinv j)).pow _
    have hW₁ : W₁.IsInvertible := (hprod _ fun j => (hVinv j).pow _).mul hFvp
    have hW₂ : W₂.IsInvertible := (hprod _ fun j => (hVinv j).pow _).mul hFvn
    have hPi1 : (∏ j, P j ^ pos j).IsInvertible := hprod _ fun j => (hPinv j).pow _
    have hPi2 : (∏ j, P j ^ neg j).IsInvertible := hprod _ fun j => (hPinv j).pow _

    have I1 : KP * Fvp * C = (∏ j, P j ^ pos j) * (HN * W₁) := by
      simp only [KP, Fvp, C, P, HN, W₁, K, mul_pow, pow_add, Finset.prod_mul_distrib]; ring
    have I2 : KN * Fvn * C = (∏ j, P j ^ neg j) * (HP * W₂) := by
      simp only [KN, Fvn, C, P, HP, W₂, K, mul_pow, pow_add, Finset.prod_mul_distrib]; ring
    have I3 : ∀ (q : Fin m → ℕ) (w : Fin (e + 1) → ℕ),
        (∏ j, Vj j ^ q j) * ∏ k, Fk k ^ w k = ∏ k, Fk k ^ (w k + ∑ j, q j * min (k : ℕ) (d j)) := by
      intro q w
      show (∏ j, (∏ k, Fk k ^ min (k : ℕ) (d j)) ^ q j) * ∏ k, Fk k ^ w k = _
      simp_rw [← Finset.prod_pow, ← pow_mul]
      rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
      congr 1
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => Nat.mul_comm _ _

    have eW : W₁.invModule ⊗ W₂.module ≅ 𝟙_ _ := by
      have h := AlgebraicGeometry.Scheme.IdealSheafData.nonempty_invModule_prod_pow_tensor_module_prod_pow_iso_tensorUnit_of_arithProg
        Fk hFinv tϖ tu htϖ htu (fun k => vp k + ∑ j, neg j * min (k : ℕ) (d j)) (fun k => vn k + ∑ j, pos j * min (k : ℕ) (d j))
        a₀ δ hAP
      rw [← I3 neg vp, ← I3 pos vn] at h
      exact h.some

    have ePi := nonempty_prod_pow_invModule_iso_and_module_iso_of_eq_zeroSchemeIdeal P hPinv tP htP
    obtain ⟨ePi1⟩ := (ePi pos).1
    obtain ⟨ePi2⟩ := (ePi neg).2

    obtain ⟨eM2⟩ := nonempty_invModule_mul_tensor_module_mul_iso (KP * Fvp) (KN * Fvn) C (hKP.mul hFvp) (hKN.mul hFvn) hC
    have e32 : (KP.invModule ⊗ KN.module) ⊗ (Fvp.invModule ⊗ Fvn.module) ≅ HN.invModule ⊗ HP.module :=
      (TwistCalc.splitIso hKP hFvp hKN hFvn).symm ≪≫ eM2.symm ≪≫
        eqToIso (congrArg₂ (fun A B : (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData => A.invModule ⊗ B.module) I1 I2) ≪≫
        TwistCalc.splitIso hPi1 (hHN.mul hW₁) hPi2 (hHP.mul hW₂) ≪≫
        ((ePi1 ⊗ᵢ ePi2) ⊗ᵢ (TwistCalc.splitIso hHN hW₁ hHP hW₂ ≪≫ whiskerLeftIso _ eW ≪≫ ρ_ _)) ≪≫
        whiskerRightIso (λ_ _) _ ≪≫ λ_ _

    obtain ⟨m1⟩ := nonempty_foldr_tensor_iso_prod K K hKinv hKinv pos neg
      ((List.finRange r).foldr (fun i M => twist (J i) (jp i) (jn i) ⊗ M) (Fvp.invModule ⊗ Fvn.module))
    obtain ⟨m2⟩ := nonempty_foldr_tensor_iso_prod J J hJ hJ jp jn (Fvp.invModule ⊗ Fvn.module)
    obtain ⟨m3⟩ := nonempty_foldr_tensor_iso_prod H H hHinv hHinv neg pos
      ((List.finRange r).foldr (fun i M => twist (J i) (jp i) (jn i) ⊗ M) (𝟙_ _))
    obtain ⟨m4⟩ := nonempty_foldr_tensor_iso_prod J J hJ hJ jp jn (𝟙_ (pullback f (Resolution.toCrossing ϖ e)).Modules)
    refine ⟨m1 ≪≫ whiskerLeftIso _ (m2 ≪≫ β_ _ _) ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e32 _ ≪≫
      whiskerLeftIso _ ((ρ_ _).symm ≪≫ m4.symm) ≪≫ m3.symm⟩

  let Z : Set ↥(pullback f (Resolution.toCrossing ϖ e)) := (⋃ j, ((H j).support : Set _)) ∪ (⋃ i, ((J i).support : Set _))
  have hZ : IsClosed Z :=
    (isClosed_iUnion_of_finite fun j => (H j).support.isClosed).union (isClosed_iUnion_of_finite fun i => (J i).support.isClosed)
  have hxZ : ∀ z ∈ Z, (q.base z).1 ≠ x := by
    intro z hz hzx
    have hzcl : πY.base z = IsLocalRing.closedPoint O := by
      rw [hπY, Scheme.Hom.comp_apply, ← hxcl]
      congr 1
      exact Subtype.ext hzx
    rcases hz with hz | hz
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      have := hHs j
      exact (Set.eq_empty_iff_forall_notMem.mp this z) ⟨hj, hzcl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      have := hJs i
      exact (Set.eq_empty_iff_forall_notMem.mp this z) ⟨hi, hzcl⟩
  obtain ⟨V, hxV, hVU, hV⟩ := exists_open_preimage_subset_compl U q Z hZ x hxU hxZ
  refine ⟨V, hxV, hVU, ?_⟩
  obtain ⟨e3⟩ := step3
  set ι := (q ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).ι with hι
  have hιH : ∀ j (y : ↥(q ⁻¹ᵁ (U.ι ⁻¹ᵁ V))), ι.base y ∉ ((H j).support : Set _) := fun j y h =>
    hV y.2 (Or.inl (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hιJ : ∀ i (y : ↥(q ⁻¹ᵁ (U.ι ⁻¹ᵁ V))), ι.base y ∉ ((J i).support : Set _) := fun i y h =>
    hV y.2 (Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩))
  have e5 := nonempty_pullback_foldr_twist_iso ι J hJ hιJ jp jn (𝟙_ _) ⟨Iso.refl _⟩
  obtain ⟨e4⟩ := nonempty_pullback_foldr_twist_iso ι H hHinv hιH neg pos
    ((List.finRange r).foldr (fun i M => twist (J i) (jp i) (jn i) ⊗ M) (𝟙_ _)) e5
  exact ⟨(Scheme.Modules.pullback ι).mapIso e3 ≪≫ e4 ≪≫ Scheme.Modules.pullbackUnitIso ι⟩

end Main

end AlgebraicGeometry.Layer0.DescLoc

theorem solution
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ) (he : 1 ≤ e)
    {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O)) [IsSeparated πX] (x : X) (U : X.Opens) (hxU : x ∈ U)
    (f : (U : Scheme.{u}) ⟶ crossingScheme (ϖ ^ e)) [LocallyOfFiniteType f] [FormallyUnramified f]
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ e)))) = U.ι ≫ πX)
    (f_mem_Vc_iff : ∀ y : U,
      f.base y ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens) ⊔
        (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ e)) : (crossingScheme (ϖ ^ e)).Opens)) ↔ (y : X) ≠ x)
    (hinj : ∀ y y' : ↥(pullback f (Resolution.toCrossing ϖ e)),
      ((pullback.fst f (Resolution.toCrossing ϖ e)).base y).1 = x →
        ((pullback.fst f (Resolution.toCrossing ϖ e)).base y').1 = x →
          (pullback.snd f (Resolution.toCrossing ϖ e)).base y = (pullback.snd f (Resolution.toCrossing ϖ e)).base y' → y = y')
    [IsIntegral (pullback f (Resolution.toCrossing ϖ e))]
    (hgen : ∃ y : ↥(pullback f (Resolution.toCrossing ϖ e)),
      (pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX).base y ≠ IsLocalRing.closedPoint O)
    (Fc : Fin (e + 1) → (Resolution ϖ e).IdealSheafData) (hFc_inv : ∀ k, (Fc k).IsInvertible)
    (hFc_t : ∏ k, Fc k = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toSpec ϖ e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)}))
    (hFc_u : ∏ k, Fc k ^ (k : ℕ) = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toCrossing ϖ e).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom (CrossingQuotient.U (ϖ ^ e)))}))
    (hFc_supp : ∀ (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)), z ∈ (Fc k).support →
      (Resolution.toSpec ϖ e).base z = IsLocalRing.closedPoint O)
    (hFc_vertex : ∀ (k : ℕ) (hk0 : 0 < k) (hke : k < e) (z : ↥(Resolution ϖ e)), z ∈ (Fc ⟨k, by omega⟩).support →
      CrossingQuotient.U (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal ∧
        CrossingQuotient.V (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal)
    (hFc_node : ∀ (k : ℕ) (hke : k < e), ∃ z : ↥(Resolution ϖ e),
      z ∈ (Fc ⟨k, by omega⟩).support ∧ z ∈ (Fc ⟨k + 1, by omega⟩).support)
    (hFc_sect : ∀ (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e), t ≫ Resolution.toSpec ϖ e = 𝟙 _ →
      ∀ (dd : ℕ) (hd0 : 0 < dd) (hde : dd < e), t.base (IsLocalRing.closedPoint O) ∈ (Fc ⟨dd, by omega⟩).support →
      (∀ k : Fin (e + 1), (k : ℕ) ≠ dd → t.base (IsLocalRing.closedPoint O) ∉ (Fc k).support) →
      IsClosedImmersion t ∧ (t.ker).IsInvertible ∧
        ∃ rr : CrossingQuotient O (ϖ ^ e), t.ker * ∏ k, Fc k ^ (min (k : ℕ) dd) =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom rr)}))
    {m : ℕ} (σ : Fin m → (Spec (CommRingCat.of O) ⟶ pullback f (Resolution.toCrossing ϖ e)))
    (hσ : ∀ j, σ j ≫ pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX = 𝟙 _)
    (pos neg : Fin m → ℕ) (d : Fin m → ℕ) (hd : ∀ j, 0 < d j ∧ d j < e)
    (hσd : ∀ j, (σ j).base (IsLocalRing.closedPoint O) ∈
        ((Fc ⟨d j, (hd j).2.trans e.lt_succ_self⟩).comap (pullback.snd f (Resolution.toCrossing ϖ e))).support ∧
      ∀ k : Fin (e + 1), (k : ℕ) ≠ d j →
        (σ j).base (IsLocalRing.closedPoint O) ∉ ((Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e))).support)
    (vp vn : Fin (e + 1) → ℕ)
    {r : ℕ} (J : Fin r → (pullback f (Resolution.toCrossing ϖ e)).IdealSheafData) (hJ : ∀ i, (J i).IsInvertible)
    (hJs : ∀ i, ((J i).support : Set _) ∩
      (pullback.fst f (Resolution.toCrossing ϖ e) ≫ U.ι ≫ πX).base ⁻¹' {IsLocalRing.closedPoint O} = ∅)
    (jp jn : Fin r → ℕ)
    (hdeg : ∀ k : ℕ, ∀ hk0 : 0 < k, ∀ hke : k < e,
      (∑ j, if d j = k then ((pos j : ℤ) - neg j) else 0) +
        (((vp ⟨k - 1, by omega⟩ : ℤ) - vn ⟨k - 1, by omega⟩) - 2 * ((vp ⟨k, by omega⟩ : ℤ) - vn ⟨k, by omega⟩) +
          ((vp ⟨k + 1, by omega⟩ : ℤ) - vn ⟨k + 1, by omega⟩)) = 0) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      Nonempty ((Scheme.Modules.pullback
          (pullback.fst f (Resolution.toCrossing ϖ e) ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).ι).obj
            ((List.finRange m).foldr (fun j M => ((((σ j).ker) ^ pos j).invModule ⊗ (((σ j).ker) ^ neg j).module) ⊗ M)
              ((List.finRange r).foldr (fun i M => (((J i) ^ jp i).invModule ⊗ ((J i) ^ jn i).module) ⊗ M)
                ((∏ k, (Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e)) ^ vp k).invModule ⊗
                  (∏ k, (Fc k).comap (pullback.snd f (Resolution.toCrossing ϖ e)) ^ vn k).module))) ≅
        𝟙_ _) :=
  AlgebraicGeometry.Layer0.DescLoc.exists_open_trivial ϖ hϖ e he πX x U hxU f hf f_mem_Vc_iff hinj hgen Fc hFc_inv hFc_t hFc_u hFc_supp hFc_vertex hFc_node hFc_sect σ hσ pos neg d hd hσd vp vn J hJ hJs jp jn hdeg

end

end S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero (solution)
