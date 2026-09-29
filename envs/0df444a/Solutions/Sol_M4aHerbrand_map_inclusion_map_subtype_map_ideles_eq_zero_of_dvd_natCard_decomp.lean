-- Prove2me | solution 1 for M4aHerbrand.map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/53789e8c-b589-5d39-953a-d760a0d034a8

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq
import Theorems.Thm_M4aHerbrand_map_prG_eq_map_map_prG_of_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower
import Theorems.Thm_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_map_eq_natCard_smul_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_M4aHerbrand_map_inclusion_map_subtype_eq_map_inclusion_map_decomp
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp.M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant IdeleGaloisDescent GenuineDescent.genuineBaseChange exists_hom_res_decomp_ideles_adicCompletion_apply map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower map_prG_eq_map_map_prG_of_smul_eq map_inclusion_map_subtype_eq_map_inclusion_map_decomp"
namespace C3FProof
p2m_open "M4aHerbrand"

theorem natCard_nsmul_eq_zero {G : Type} [Group G] [Finite G] (A : Rep ℤ G) (n : ℕ) (x : groupCohomology A (n + 1)) :
    Nat.card G • x = 0 := by
  obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊥ : Subgroup G) A (n + 1)
  haveI := ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_succ_of_subsingleton (Rep.res (⊥ : Subgroup G).subtype A) n)
  have h0 : (groupCohomology.map (⊥ : Subgroup G).subtype (𝟙 (Rep.res (⊥ : Subgroup G).subtype A)) (n + 1)).hom x = 0 :=
    Subsingleton.elim _ _
  rw [← Subgroup.index_bot, ← hcor x, h0, map_zero]

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

end M4aHerbrand.C3FProof

theorem solution
    (E F L M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra E F] [Algebra E L] [Algebra E M] [Algebra F M] [Algebra L M]
    [IsScalarTower E F M] [IsScalarTower E L M] [IsGalois E F] [IsGalois E L] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] (hM : IsPGroup p (M ≃ₐ[E] M))

    (DF : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactIF : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = DF.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)

    (SF : Subgroup (M ≃ₐ[E] M)) [SF.Normal] (ιF : (M ≃ₐ[E] M) ⧸ SF ≃* (F ≃ₐ[E] F))
    (hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x))
    (SL : Subgroup (M ≃ₐ[E] M)) [SL.Normal] (ιL : (M ≃ₐ[E] M) ⧸ SL ≃* (L ≃ₐ[E] L))
    (hιL : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ιL (QuotientGroup.mk g) y) = g (algebraMap L M y))

    (JF : Rep.res (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJF : ∀ x : (AdeleRing (𝓞 F) F)ˣ, JF.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (prH : ∀ W : HeightOneSpectrum (𝓞 M),
      Rep.res (Subgroup.inclusion (inf_le_left : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ SL))
          (Rep.res SL.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))
    (hprH : ∀ (W : HeightOneSpectrum (𝓞 M)) (x : (AdeleRing (𝓞 M) M)ˣ), (prH W).hom (Additive.ofMul x) = Additive.ofMul (finPart W x))

    (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

    (hdiv : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
          (prG (NumberField.PlaceAbove.above E F v)) 2).hom y ≠ 0 →
      ∀ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 E) = v →
        Nat.card (F ≃ₐ[E] F) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E L w')) :
    ∀ W : HeightOneSpectrum (𝓞 M),
      (groupCohomology.map (Subgroup.inclusion (inf_le_left : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ SL)) (prH W) 2).hom
        ((groupCohomology.map SL.subtype (𝟙 (Rep.res SL.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) 2).hom
          ((groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom y)) = 0 := by
  open M4aHerbrand.C3FProof in
  classical
  intro W

  obtain ⟨prM, hprM⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E M DM hactIM
  set xM := (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom y with hxM

  have hfactor : (groupCohomology.map (Subgroup.inclusion (inf_le_left : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ SL)) (prH W) 2).hom
        ((groupCohomology.map SL.subtype (𝟙 (Rep.res SL.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) 2).hom xM)
      = (groupCohomology.map (Subgroup.inclusion (inf_le_right : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : SL ⊓ NumberField.PlaceDecomp.decomp E M W ≤ NumberField.PlaceDecomp.decomp E M W))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ))) 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype (prM W) 2).hom xM) :=
    M4aHerbrand.map_inclusion_map_subtype_eq_map_inclusion_map_decomp E M SL W (prH W) (hprH W) (prM W) (hprM W) 2 xM
  rw [hfactor]

  obtain ⟨r, hrsurj, hrres, hrker, hrlift, hrcompat⟩ :=
    NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F M W
  have hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : F),
      algebraMap F M (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : M ≃ₐ[E] M) (algebraMap F M x) :=
    fun σ x => by rw [hrres]; exact AlgEquiv.restrictNormal_commutes (σ : M ≃ₐ[E] M) F x
  let incl := HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M))
  let fD : ((W.under (𝓞 F)).adicCompletion F)ˣ →* (W.adicCompletion M)ˣ := Units.map incl.toRingHom.toMonoidHom
  have hfD : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ, ((fD x : (W.adicCompletion M)ˣ) : W.adicCompletion M) = incl (x : (W.under (𝓞 F)).adicCompletion F) :=
    fun _ => rfl
  let iD : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ :=
    Rep.ofHom ⟨(MonoidHom.toAdditive fD).toIntLinearMap, fun σ => LinearMap.ext fun a => by
      change Additive.ofMul (fD ((r σ) • (Additive.toMul : Additive ((W.under (𝓞 F)).adicCompletion F)ˣ ≃ ((W.under (𝓞 F)).adicCompletion F)ˣ) a))
        = Additive.ofMul (σ • fD ((Additive.toMul : Additive ((W.under (𝓞 F)).adicCompletion F)ˣ ≃ ((W.under (𝓞 F)).adicCompletion F)ˣ) a))
      congr 1
      apply Units.ext
      rw [hfD, NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.coe_smul_units, hfD]
      exact hrcompat σ _⟩
  have hiD : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iD.hom (Additive.ofMul x)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) = incl (x : (W.under (𝓞 F)).adicCompletion F) :=
    fun _ => rfl

  have hcoord := M4aHerbrand.map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower E F M SF ιF hιF JF hJF W
    (prG (W.under (𝓞 F))) (hprG (W.under (𝓞 F))) (prM W) (hprM W) r hr iD hiD 2 y
  rw [← hxM] at hcoord
  rw [hcoord]

  set v : HeightOneSpectrum (𝓞 E) := (W.under (𝓞 F)).under (𝓞 E) with hv
  have hunder₀ : (NumberField.PlaceAbove.above E F v).under (𝓞 E) = v :=
    HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E F v)
  have hmem : (W.under (𝓞 F)) ∈ MulAction.orbit (F ≃ₐ[E] F) (NumberField.PlaceAbove.above E F v) := by
    rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq]
    show (W.under (𝓞 F)).under (𝓞 E) = (NumberField.PlaceAbove.above E F v).under (𝓞 E)
    rw [hunder₀]
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 hmem

  obtain ⟨-, c, T, -, hc, hT⟩ := NumberField.PlaceDecomp.exists_conj_and_transport_repHom_of_smul_eq E F
    (NumberField.PlaceAbove.above E F v) (W.under (𝓞 F)) σ hσ
  have hconj := M4aHerbrand.map_prG_eq_map_map_prG_of_smul_eq E F DF hactIF prG hprG (NumberField.PlaceAbove.above E F v) (W.under (𝓞 F)) σ hσ c hc T hT 2 y

  by_cases h0 : (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
      (prG (NumberField.PlaceAbove.above E F v)) 2).hom y = 0
  · rw [hconj, h0, map_zero, map_zero, map_zero]

  have hunderL : (W.under (𝓞 L)).under (𝓞 E) = v := by
    apply HeightOneSpectrum.ext
    change (W.asIdeal.under (𝓞 L)).under (𝓞 E) = (W.asIdeal.under (𝓞 F)).under (𝓞 E)
    rw [Ideal.under_under, Ideal.under_under]
  have hG : Nat.card (F ≃ₐ[E] F) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E L (W.under (𝓞 L))) := hdiv v h0 _ hunderL
  have hdvd : Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E L (W.under (𝓞 L))) :=
    dvd_trans (Subgroup.card_subgroup_dvd_card _) hG
  obtain ⟨hprodF, -, hdd⟩ := NumberField.PlaceDecomp.natCard_decomp_eq_mul_and_natCard_inf_decomp_dvd_of_dvd E F L M SF ιF hιF SL ιL hιL W hdvd

  have hkercard : Nat.card ↥r.ker = Nat.card ↥(SF ⊓ NumberField.PlaceDecomp.decomp E M W) := by
    have h1 : Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) = Nat.card ↥r.ker * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hrsurj).toEquiv, mul_comm,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have hpos : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans hprodF)

  obtain ⟨q, hq, Lb, L2, hle, finLb, finL2, actLb, faithLb, actULb, actL2, faithL2, actUL2, Φ, Φ2, hΦ, hΦ2, hQ, hQ2, hU, hU2, htower, -⟩ :=
    NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower E F M W
  obtain ⟨K₀, finK₀, hK₀le, hK₀mem⟩ := ExtCitation.LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq q Lb
    ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) hQ
  have hB₁ : ExtCitation.LocalLevel.IsBase q Lb ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) K₀ := ⟨hK₀le, hK₀mem⟩
  have hGF : IsPGroup p (F ≃ₐ[E] F) :=
    hM.of_surjective (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) (ιF.surjective.comp (QuotientGroup.mk'_surjective SF))
  have hsolv₁ : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := by
    haveI := (hGF.to_subgroup (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))).isNilpotent
    infer_instance
  have hsolvD : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E M W) := by
    haveI := (hM.to_subgroup (NumberField.PlaceDecomp.decomp E M W)).isNilpotent
    infer_instance
  obtain ⟨u₁, hu₁, -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q Lb
    ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) hQ hU hsolv₁ K₀ hB₁

  let f₁ : (↥Lb)ˣ →* ((W.under (𝓞 F)).adicCompletion F)ˣ := (Units.mapEquiv Φ.symm.toMulEquiv).toMonoidHom
  have hf₁ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (y : (↥Lb)ˣ), f₁ (g • y) = g • f₁ y := fun g y => by
    apply Units.ext
    change Φ.symm ((g • y : (↥Lb)ˣ) : Lb) = ((g • f₁ y : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F)
    rw [hU, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ.injective
    rw [RingEquiv.apply_symm_apply, hΦ]
    exact congrArg _ (Φ.apply_symm_apply _).symm
  let θ₁ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥Lb)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ :=
    M4aHerbrand.repHomOfMulEquivariant f₁ hf₁
  have hθ₁ : ∀ y : (↥Lb)ˣ, ((Additive.toMul (θ₁.hom (Additive.ofMul y)) : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F)
      = Φ.symm (y : Lb) := fun _ => rfl

  obtain ⟨m, hm⟩ := NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass E F (W.under (𝓞 F)) hsolv₁ q Lb Φ hQ hU hΦ K₀ hB₁
    θ₁ hθ₁ u₁ hu₁ ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (prG (W.under (𝓞 F))) 2).hom y)
  rw [hm, map_zsmul, map_zsmul]

  have hΦtower : ∀ z : (W.under (𝓞 F)).adicCompletion F, IntermediateField.inclusion hle (Φ z) = Φ2 (incl z) := fun z =>
    Subtype.ext (htower z).symm
  have hEQV : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (yb : Lb),
      g • IntermediateField.inclusion hle yb = IntermediateField.inclusion hle (r g • yb) := fun g yb => by
    obtain ⟨z, rfl⟩ : ∃ z, Φ z = yb := ⟨Φ.symm yb, Φ.apply_symm_apply yb⟩
    rw [hΦtower, ← hΦ2, ← hrcompat, ← hΦtower, hΦ]
  have hsmul_eq : ∀ (τ : ↥(NumberField.PlaceDecomp.decomp F M W)) (σ' : ↥(NumberField.PlaceDecomp.decomp E M W)),
      (σ' : M ≃ₐ[E] M) = AlgEquiv.restrictScalars E (τ : M ≃ₐ[F] M) → ∀ z : W.adicCompletion M, τ • z = σ' • z := fun τ σ' h z => by
    rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
    rw [NumberField.PlaceDecomp.actRingEquiv_apply, NumberField.PlaceDecomp.actRingEquiv_apply, h]
    rfl
  haveI : IsGalois F M := IsGalois.tower_top_of_isGalois E F M
  have hL : ∀ x : L2, (x : PadicAlgCl q) ∈ Lb ↔ ∀ n ∈ r.ker, n • x = x := fun x => by
    constructor
    · intro hx n hn
      have hx' : x = IntermediateField.inclusion hle ⟨x, hx⟩ := Subtype.ext rfl
      rw [hx', hEQV, MonoidHom.mem_ker.1 hn, one_smul]
    · intro hfix
      have hz : ∀ τ : ↥(NumberField.PlaceDecomp.decomp F M W), τ • Φ2.symm x = Φ2.symm x := fun τ => by
        obtain ⟨σ', hσ', hrσ'⟩ := hrlift τ
        rw [hsmul_eq τ σ' hσ']
        apply Φ2.injective
        rw [hΦ2, RingEquiv.apply_symm_apply]
        exact hfix σ' (MonoidHom.mem_ker.2 hrσ')
      obtain ⟨z, hz'⟩ := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom F M W (Φ2.symm x)).1 hz
      have : x = Φ2 (incl z) := by rw [hz', RingEquiv.apply_symm_apply]
      rw [this, ← hΦtower]
      exact (Φ z).2

  let e : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) ≃* ↥(NumberField.PlaceDecomp.decomp E M W) ⧸ r.ker :=
    (QuotientGroup.quotientKerEquivOfSurjective r hrsurj).symm
  have he_mk : ∀ h : ↥(NumberField.PlaceDecomp.decomp E M W), e.symm (QuotientGroup.mk h) = r h := fun h =>
    QuotientGroup.kerLift_mk r h
  have he : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (h : ↥(NumberField.PlaceDecomp.decomp E M W)),
      (QuotientGroup.mk h : ↥(NumberField.PlaceDecomp.decomp E M W) ⧸ r.ker) = e g →
      ∀ x : Lb, ((g • x : Lb) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hle x.2⟩ : L2) : L2) : PadicAlgCl q) := by
    intro g h hgh x
    have hrg : r h = g := by rw [← he_mk, hgh, MulEquiv.symm_apply_apply]
    change _ = ((h • IntermediateField.inclusion hle x : L2) : PadicAlgCl q)
    rw [hEQV, hrg]
    rfl

  have hB2 : ExtCitation.LocalLevel.IsBase q L2 ↥(NumberField.PlaceDecomp.decomp E M W) K₀ := by
    refine ⟨hK₀le.trans hle, fun x => ⟨fun hx g => ?_, fun hfix => ?_⟩⟩
    · have hxb : (x : PadicAlgCl q) ∈ Lb := hK₀le hx
      have hx' : x = IntermediateField.inclusion hle ⟨x, hxb⟩ := Subtype.ext rfl
      have hfix₁ : ∀ g₁ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))), g₁ • (⟨x, hxb⟩ : Lb) = ⟨x, hxb⟩ := (hK₀mem _).1 hx
      rw [hx', hEQV, hfix₁]
    · have hxb : (x : PadicAlgCl q) ∈ Lb := (hL x).2 fun n _ => hfix n
      have hx' : x = IntermediateField.inclusion hle ⟨x, hxb⟩ := Subtype.ext rfl
      refine (hK₀mem ⟨x, hxb⟩).2 fun g₁ => ?_
      obtain ⟨g, rfl⟩ := hrsurj g₁
      apply IntermediateField.inclusion_injective hle
      rw [← hEQV, ← hx']
      exact hfix g
  obtain ⟨u2, hu2, -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L2
    ↥(NumberField.PlaceDecomp.decomp E M W) hQ2 hU2 hsolvD K₀ hB2

  let fι : (↥Lb)ˣ →* (↥L2)ˣ := Units.map (IntermediateField.inclusion hle).toRingHom.toMonoidHom
  have hfιval : ∀ u : (↥Lb)ˣ, ((fι u : (↥L2)ˣ) : L2) = IntermediateField.inclusion hle (u : Lb) := fun _ => rfl
  let ιu : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker))
      (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥Lb)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L2)ˣ :=
    Rep.ofHom ⟨(MonoidHom.toAdditive fι).toIntLinearMap, fun h => LinearMap.ext fun a => by
      change Additive.ofMul (fι ((e.symm (QuotientGroup.mk' r.ker h)) • (Additive.toMul : Additive (↥Lb)ˣ ≃ (↥Lb)ˣ) a))
        = Additive.ofMul (h • fι ((Additive.toMul : Additive (↥Lb)ˣ ≃ (↥Lb)ˣ) a))
      congr 1
      apply Units.ext
      rw [hfιval, hU, hU2, hfιval, QuotientGroup.mk'_apply, he_mk, hEQV]⟩
  have hιu : ∀ u : (↥Lb)ˣ, (((Additive.toMul (ιu.hom (Additive.ofMul u)) : (↥L2)ˣ) : L2) : PadicAlgCl q) = ((u : Lb) : PadicAlgCl q) :=
    fun _ => rfl
  have hinfl := ExtCitation.LocalLevel.map_eq_natCard_smul_of_isLocalFundamentalClass q L2 ↥(NumberField.PlaceDecomp.decomp E M W)
    hQ2 hU2 hsolvD K₀ hB2 Lb hle ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) hU r.ker e hL he u₁ hu₁ u2 hu2 ιu hιu

  let f2 : (↥L2)ˣ →* (W.adicCompletion M)ˣ := (Units.mapEquiv Φ2.symm.toMulEquiv).toMonoidHom
  have hf2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (y : (↥L2)ˣ), f2 (g • y) = g • f2 y := fun g y => by
    apply Units.ext
    change Φ2.symm ((g • y : (↥L2)ˣ) : L2) = ((g • f2 y : (W.adicCompletion M)ˣ) : W.adicCompletion M)
    rw [hU2, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ2.injective
    rw [RingEquiv.apply_symm_apply, hΦ2]
    exact congrArg _ (Φ2.apply_symm_apply _).symm
  let θ2 : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L2)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ :=
    M4aHerbrand.repHomOfMulEquivariant f2 hf2
  have key : (groupCohomology.map r iD 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ₁ 2).hom u₁)
      = (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) θ2 2).hom
        ((groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)) ιu 2).hom u₁) := by
    have h1 := congrArg (fun T => T.hom u₁)
      (groupCohomology.map_comp (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) r θ₁ iD 2)
    have h2 := congrArg (fun T => T.hom u₁)
      (groupCohomology.map_comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)) (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) ιu θ2 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
    rw [← h1, ← h2]
    have hgrp : (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))).comp r
        = (e.symm.toMonoidHom.comp (QuotientGroup.mk' r.ker)).comp (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) :=
      MonoidHom.ext fun h => by
        change r h = e.symm (QuotientGroup.mk' r.ker h)
        rw [QuotientGroup.mk'_apply, he_mk]
    refine congrArg
      (fun (T : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥Lb)ˣ) 2 ⟶
          groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ) 2) => T.hom u₁)
      (map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) 2)
    obtain ⟨u, rfl⟩ : ∃ u : (↥Lb)ˣ, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
    change Additive.ofMul (fD (f₁ u)) = Additive.ofMul (f2 (fι u))
    congr 1
    apply Units.ext
    change incl (Φ.symm (u : Lb)) = Φ2.symm (IntermediateField.inclusion hle (u : Lb))
    apply Φ2.injective
    rw [RingEquiv.apply_symm_apply, ← hΦtower, RingEquiv.apply_symm_apply]

  rw [key, hinfl, map_nsmul, map_nsmul, hkercard]
  obtain ⟨k, hk⟩ := hdd
  rw [hk, mul_nsmul, natCard_nsmul_eq_zero, smul_zero, zsmul_zero]

end S_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp
end P2MW
export P2MW.S_M4aHerbrand_map_inclusion_map_subtype_map_ideles_eq_zero_of_dvd_natCard_decomp (solution)
