-- Prove2me | solution 1 for ModularCurve.exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/85bcee5f-f683-5c1d-b7bc-8098b4088530

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top
import Theorems.Thm_ModularCurve_comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve

open scoped MatrixGroups

namespace SSTransferPen12

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ord_pos_of_mem_maximalIdeal {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) (hmem : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) : 0 < v.ord f := by
  have h0 : 0 ≤ v.ord f := ord_nonneg_of_mem v hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    rw [← h, zpow_zero, mul_one] at hu
    have : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this] at hmax
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax u.isUnit

theorem mem_maximalIdeal_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (h : 0 < v.ord f) (hmem : f ∈ v.toValuationSubring) :
    (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem hasValue_iff_mem_and {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (f : F) (a : K) :
    v.HasValue f a ↔ f ∈ v.toValuationSubring ∧ (f - algebraMap K F a = 0 ∨ 0 < v.ord (f - algebraMap K F a)) := by
  constructor
  · rintro ⟨hmem, hres⟩
    refine ⟨hmem, ?_⟩
    have hdiff : (⟨f, hmem⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring a ∈
        IsLocalRing.maximalIdeal v.toValuationSubring := by
      rw [← Ideal.Quotient.eq]
      exact hres.trans (Place.residue_algebraMap v a).symm
    by_cases h0 : f - algebraMap K F a = 0
    · exact Or.inl h0
    · right
      have hmem' : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hmem (v.algebraMap_mem' a)
      have : (⟨f - algebraMap K F a, hmem'⟩ : v.toValuationSubring) = ⟨f, hmem⟩ - algebraMap K v.toValuationSubring a :=
        Subtype.ext rfl
      exact ord_pos_of_mem_maximalIdeal v h0 hmem' (this ▸ hdiff)
  · rintro ⟨hmem, h⟩
    refine ⟨hmem, ?_⟩
    rw [← Place.residue_algebraMap v a]
    apply Ideal.Quotient.eq.mpr
    have hmem' : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hmem (v.algebraMap_mem' a)
    have heq : (⟨f, hmem⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring a = ⟨f - algebraMap K F a, hmem'⟩ :=
      Subtype.ext rfl
    rw [heq]
    rcases h with h0 | hpos
    · have : (⟨f - algebraMap K F a, hmem'⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
      rw [this]; exact Ideal.zero_mem _
    · exact mem_maximalIdeal_of_ord_pos v hpos hmem'

theorem qExpand_coeffMap (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {K' : Type*} [Field K'] (τ : K →+* K') (s : LaurentSeries K) :
    ModularCurve.qExpand K' p (ModularCurve.coeffMap τ s) = ModularCurve.coeffMap τ (ModularCurve.qExpand K p s) := by
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.coeffMap_coeff, ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_mul]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd p _ hk, ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd p _ hk, map_zero]

end SSTransferPen12

theorem solution
    (p : ℕ) [Fact p.Prime]
    (κ K : Type*) [Field κ] [Field K] [IsAlgClosed κ] [IsAlgClosed K] [CharP κ p] [CharP K p] [Algebra κ K]
    (Γ : Subgroup SL(2, ℤ))
    [AlgebraicCurve.IsCurveOver κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)]
    [AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hfgκ : ∃ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), Transcendental κ x ∧
      FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set ↥(ModularCurve.qExpFunctionFieldC κ Γ))) ↥(ModularCurve.qExpFunctionFieldC κ Γ))
    (hfgK : ∃ x : ↥(ModularCurve.qExpFunctionFieldC K Γ), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(ModularCurve.qExpFunctionFieldC K Γ))) ↥(ModularCurve.qExpFunctionFieldC K Γ))
    (ι : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), ((ι x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ)) :
    ∃ ext : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) → AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
      Function.Injective ext ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)),
        f ∈ v.toValuationSubring ↔ ι f ∈ (ext v).toValuationSubring) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
        (∀ f : ↥(ModularCurve.qExpFunctionFieldC κ Γ), f ∈ v.toValuationSubring ↔ ι f ∈ w.toValuationSubring) → ext v = w) ∧
      (∀ w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ), w.toValuationSubring.comap ι ≠ ⊤ →
        ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), ext v = w) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)), (ext v).ord (ι f) = v.ord f) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (a : κ),
        v.HasValue f a ↔ (ext v).HasValue (ι f) (algebraMap κ K a)) ∧
      (∀ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        v ∈ ModularCurve.ssPlacesQExp κ Γ p ↔ ext v ∈ ModularCurve.ssPlacesQExp K Γ p) ∧
      (∀ w ∈ ModularCurve.ssPlacesQExp K Γ p, ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), ext v = w) ∧
      (∀ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        ext (ModularCurve.qExpFrobeniusPlaceModL κ Γ p v) = ModularCurve.qExpFrobeniusPlaceModL K Γ p (ext v)) := by
  classical

  letI : Algebra ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := ι.toAlgebra
  letI : Algebra κ ↥(ModularCurve.qExpFunctionFieldC K Γ) := ((algebraMap K ↥(ModularCurve.qExpFunctionFieldC K Γ)).comp (algebraMap κ K)).toAlgebra
  haveI : IsScalarTower κ K ↥(ModularCurve.qExpFunctionFieldC K Γ) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hιalg : ∀ a : κ, ι (algebraMap κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) a) = algebraMap K ↥(ModularCurve.qExpFunctionFieldC K Γ) (algebraMap κ K a) := by
    intro a
    apply Subtype.ext
    rw [hι]
    show ModularCurve.coeffMap (algebraMap κ K) (algebraMap κ (LaurentSeries κ) a) = algebraMap K (LaurentSeries K) (algebraMap κ K a)
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single]
  haveI : IsScalarTower κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := IsScalarTower.of_algebraMap_eq (fun a => (hιalg a).symm)

  have himage : ⇑((ModularCurve.qExpFunctionFieldC K Γ)).val '' Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)) =
      ⇑(ModularCurve.coeffMap (algebraMap κ K)) '' ((ModularCurve.qExpFunctionFieldC κ Γ) : Set (LaurentSeries κ)) := by
    ext s
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨(x : LaurentSeries κ), x.2, (hι x).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ι ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, hι ⟨t, ht⟩⟩
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    set S : Set ↥(ModularCurve.qExpFunctionFieldC K Γ) := Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)) with hSdef
    have h1 : IntermediateField.adjoin K (⇑((ModularCurve.qExpFunctionFieldC K Γ)).val '' S) ≤ (IntermediateField.adjoin K S).map ((ModularCurve.qExpFunctionFieldC K Γ)).val := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      show _ ∈ ((IntermediateField.map ((ModularCurve.qExpFunctionFieldC K Γ)).val (IntermediateField.adjoin K S) : IntermediateField K (LaurentSeries K)) : Set (LaurentSeries K))
      rw [IntermediateField.coe_map]
      exact ⟨x, IntermediateField.subset_adjoin K S hx, rfl⟩
    have hy0 : (y : LaurentSeries K) ∈ IntermediateField.adjoin K (⇑((ModularCurve.qExpFunctionFieldC K Γ)).val '' S) := by
      rw [himage, ← ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC κ K Γ]
      exact y.2
    have hy : (y : LaurentSeries K) ∈ ((IntermediateField.map ((ModularCurve.qExpFunctionFieldC K Γ)).val (IntermediateField.adjoin K S) : IntermediateField K (LaurentSeries K)) : Set (LaurentSeries K)) :=
      h1 hy0
    rw [IntermediateField.coe_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    rw [← this]; exact hz

  have key := fun v => AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
    κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) K ↥(ModularCurve.qExpFunctionFieldC K Γ) hfgκ hfgK hgen v
  choose ext hpre hord huniq using key
  have hord' : ∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)), (ext v).ord (ι f) = v.ord f := fun v f => hord v f
  have hpre' : ∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)),
      f ∈ v.toValuationSubring ↔ ι f ∈ (ext v).toValuationSubring := by
    intro v f
    rw [← hpre v]
    rfl
  have huniq' : ∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
      (∀ f : ↥(ModularCurve.qExpFunctionFieldC κ Γ), f ∈ v.toValuationSubring ↔ ι f ∈ w.toValuationSubring) → ext v = w := by
    intro v w h
    refine (huniq v w ?_).symm
    ext f
    rw [ValuationSubring.mem_comap]
    exact (h f).symm
  have hss := ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed p κ K
  have hsseng := fun w => ModularCurve.comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq p κ K Γ ι hι hss w
  have himg : ∀ w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ), w.toValuationSubring.comap ι ≠ ⊤ →
      ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), ext v = w := by
    intro w hne
    obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top (K := κ) ι w
      (fun a => by rw [hιalg]; exact w.algebraMap_mem' _) hne
    exact ⟨v, huniq' v w (fun f => by rw [hv, ValuationSubring.mem_comap])⟩
  refine ⟨ext, ?_, hpre', huniq', himg, hord', ?_, ?_, ?_, ?_⟩
  ·
    intro v v' h
    apply AlgebraicCurve.Place.ext
    rw [← hpre v, ← hpre v', h]
  ·
    intro v f a
    rw [SSTransferPen12.hasValue_iff_mem_and, SSTransferPen12.hasValue_iff_mem_and, hpre' v f, ← hιalg, ← map_sub, hord']
    have hinj : ι (f - algebraMap κ _ a) = 0 ↔ f - algebraMap κ _ a = 0 := map_eq_zero_iff ι ι.injective
    rw [hinj]
  ·
    intro v
    constructor
    · intro hv
      exact (hsseng (ext v)).2 v hv (hpre v)
    · intro hw
      exact ((hsseng (ext v)).1 hw).2 v (hpre v)
  ·
    intro w hw
    exact himg w ((hsseng w).1 hw).1
  ·
    intro v
    apply huniq'
    intro f
    rw [ModularCurve.mem_qExpFrobeniusPlaceModL_iff, ModularCurve.mem_qExpFrobeniusPlaceModL_iff, hpre' v]
    have hcomm : ι (ModularCurve.qExpFrobeniusModL κ Γ p f) = ModularCurve.qExpFrobeniusModL K Γ p (ι f) := by
      apply Subtype.ext
      rw [hι, ModularCurve.coe_qExpFrobeniusModL, ModularCurve.coe_qExpFrobeniusModL, hι, SSTransferPen12.qExpand_coeffMap]
    rw [hcomm]

end S_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed (solution)
