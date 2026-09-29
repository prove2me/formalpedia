-- Prove2me | solution 1 for NumberField.IdeleLocalInv.hasLocalInv_map_genuineBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f1e600bd-69e9-5eba-bf2c-cbf43543add2

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceAbove
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange.NumberField IsDedekindDomain M4aHerbrand"
open M4aHerbrand.GenuineDescent
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceAbove.above PlaceAbove.comap_above IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp smul_def coe_smul_units exists_localLevel_ringEquiv_adicCompletion"
namespace FCFamily
p2m_open "NumberField.PlaceDecomp NumberField"

theorem exists_isBase (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), ExtCitation.LocalLevel.IsBase q L G K := by
  haveI : SMulCommClass G ℚ_[q] L := ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG]⟩
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toLinearMap
      (fun a b h => (IntermediateField.inclusion
        (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toRingHom.injective h)
  · refine ⟨IntermediateField.lift_le _, fun x => ?_⟩
    rw [IntermediateField.mem_lift]
    exact Iff.rfl

section Solvable
open ExtCitation.LocalLevel

theorem isSolvable_layer (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀] (hK : IsBase q L G K₀) : Group.IsSolvable G := by
  classical
  haveI := Fintype.ofFinite G
  let E' : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.extendScalars hK.le
  have memE : ∀ x : PadicAlgCl q, x ∈ E' ↔ x ∈ L := fun x => Iff.rfl
  let toL : E' → L := fun x => ⟨x.1, (memE x.1).1 x.2⟩
  let ofL : L → E' := fun y => ⟨y.1, (memE y.1).2 y.2⟩
  have hfix : ∀ (g : G) (r : K₀), g • toL (algebraMap K₀ E' r) = toL (algebraMap K₀ E' r) :=
    fun g r => (hK.mem_iff _).1 r.2 g

  let ψ₀ : G → (E' ≃ₐ[K₀] E') := fun g =>
    { toFun := fun x => ofL (g • toL x)
      invFun := fun x => ofL (g⁻¹ • toL x)
      left_inv := fun x => by
        change ofL (g⁻¹ • g • toL x) = x
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        change ofL (g • g⁻¹ • toL x) = x
        rw [← mul_smul, mul_inv_cancel, one_smul]
      map_mul' := fun x y => by
        change ofL (g • (toL x * toL y)) = ofL (g • toL x) * ofL (g • toL y)
        rw [smul_mul']
        rfl
      map_add' := fun x y => by
        change ofL (g • (toL x + toL y)) = ofL (g • toL x) + ofL (g • toL y)
        rw [smul_add]
        rfl
      commutes' := fun r => by
        change ofL (g • toL (algebraMap K₀ E' r)) = _
        rw [hfix] }
  have ψ₀_apply : ∀ (g : G) (x : E'), toL (ψ₀ g x) = g • toL x := fun g x => rfl
  let ψ : G →* (E' ≃ₐ[K₀] E') :=
    { toFun := ψ₀
      map_one' := by
        ext x
        change ((ofL ((1 : G) • toL x) : E') : PadicAlgCl q) = x
        rw [one_smul]
      map_mul' := fun g h => by
        ext x
        change ((ofL ((g * h) • toL x) : E') : PadicAlgCl q) = ((ofL (g • toL (ofL (h • toL x))) : E') : PadicAlgCl q)
        rw [mul_smul] }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro y
    have := congrArg (fun f : E' ≃ₐ[K₀] E' => toL (f (ofL y))) hgh
    exact this

  let eL : E' ≃ₗ[ℚ_[q]] L :=
    { toFun := toL, invFun := ofL, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℚ_[q] E' := Module.Finite.equiv eL.symm
  haveI : FiniteDimensional K₀ E' := Module.Finite.of_restrictScalars_finite ℚ_[q] K₀ E'
  have hdeg : Module.finrank K₀ E' = Fintype.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K₀ hK.le hK.mem_iff
    have h2 := Module.finrank_mul_finrank ℚ_[q] K₀ E'
    rw [LinearEquiv.finrank_eq eL, h1, Nat.card_eq_fintype_card, mul_comm] at h2
    have hpos : 0 < Module.finrank ℚ_[q] K₀ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hcard : Fintype.card (E' ≃ₐ[K₀] E') = Module.finrank K₀ E' := by
    apply le_antisymm AlgEquiv.card_le
    rw [hdeg]
    exact Fintype.card_le_of_injective ψ hψ
  haveI : IsGalois K₀ E' := IsGalois.of_card_aut_eq_finrank K₀ E' (by rw [Nat.card_eq_fintype_card]; exact hcard)
  haveI := IntermediateField.isSolvable_algEquiv_of_padic q K₀ E'
  exact solvable_of_solvable_injective hψ

end Solvable

structure BridgeFC (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) where
  q : ℕ
  [hq : Fact q.Prime]
  L : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd : FiniteDimensional ℚ_[q] L]
  [act : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [faith : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [actU : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ]
  Φ : w.adicCompletion F ≃+* L
  h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x
  h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)
  h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x
  hqw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal
  K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd₀ : FiniteDimensional ℚ_[q] K₀]
  base : ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀
  θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ
  hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L)
  u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ)
  hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u

theorem nonempty_bridgeFC (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) : Nonempty (BridgeFC E F w) := by
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  obtain ⟨q, hq, L, fd, act, faith, actU, Φ, h1, h2, h3, hqw⟩ := NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion E F w
  obtain ⟨K₀, fd₀, base⟩ := exists_isBase q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1
  let ΦM : (↥L)ˣ →* (w.adicCompletion F)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ΦM (g • y) = g • ΦM y := by
    intro g y
    apply Units.ext
    show Φ.symm ((g • y : (↥L)ˣ) : ↥L) = ((g • ΦM y : (w.adicCompletion F)ˣ) : w.adicCompletion F)
    rw [h2 g y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ.injective
    rw [h3 g, RingEquiv.apply_symm_apply]
    congr 1
    show (y : ↥L) = Φ (Φ.symm (y : ↥L))
    exact (Φ.apply_symm_apply _).symm
  let θ := M4aHerbrand.repHomOfMulEquivariant ΦM hΦM
  have hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : ↥L) :=
    fun y => rfl
  have hsolv : Group.IsSolvable (↥(NumberField.PlaceDecomp.decomp E F w)) := isSolvable_layer q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1 K₀ base
  obtain ⟨u, hu⟩ := (ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1 h2 hsolv K₀ base).exists
  exact ⟨{ q := q, L := L, Φ := Φ, h1 := h1, h2 := h2, h3 := h3, hqw := hqw, K₀ := K₀, base := base, θ := θ, hθ := hθ, u := u, hu := hu }⟩

noncomputable def chosen (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) : BridgeFC E F w :=
  Classical.choice (nonempty_bridgeFC E F w)

end NumberField.PlaceDecomp.FCFamily

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceAbove.above PlaceAbove.comap_above IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace IdeleLocalInv
p2m_export "NumberField.IdeleLocalInv" "HasLocalInv"
namespace ReadingExists
p2m_open "NumberField.IdeleLocalInv NumberField"
open NumberField.PlaceDecomp.FCFamily

set_option maxHeartbeats 6400000 in

theorem exists_eq_zsmul_map
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K w) L] [FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K w) L]
    [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L y = algebraMap ℚ_[q] L y)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (base : ExtCitation.LocalLevel.IsBase q L ↥(NumberField.PlaceDecomp.decomp E K w) K₀)
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ)
    (hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ))
    (hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E K w) K₀ u)
    (X : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ) 2) :
    ∃ n : ℤ, X = n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u := by
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w) := isSolvable_layer q L (↥(NumberField.PlaceDecomp.decomp E K w)) h1 K₀ base
  obtain ⟨-, -, hspan⟩ :=
    ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
      q L (↥(NumberField.PlaceDecomp.decomp E K w)) h1 h2 hsolv K₀ base u hu

  have hres_inj : Function.Injective
      (groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom := by
    let eT : ↥(NumberField.PlaceDecomp.decomp E K w) →* ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))) := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))) ≃* ↥(NumberField.PlaceDecomp.decomp E K w)).symm.toMonoidHom
    have key : groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2 ≫
        groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)))) 2 = 𝟙 _ := by
      rw [← groupCohomology.map_comp]
      exact groupCohomology.map_id (B := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)) (n := 2)
    have hleft : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ),
        (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)))) 2).hom
          ((groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom y) = y := by
      intro y
      have hy := congrArg (fun T => (ModuleCat.Hom.hom T) y) key
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
      exact hy
    exact Function.LeftInverse.injective hleft

  have hθiso : ∃ θ' : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ), θ' ≫ θ = 𝟙 _ := by
    let ΦM : (w.adicCompletion K)ˣ →* (↥L)ˣ := Units.map Φ.toRingHom.toMonoidHom
    have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (m : (w.adicCompletion K)ˣ), ΦM (g • m) = g • ΦM m := by
      intro g m
      apply Units.ext
      rw [h2 g (ΦM m)]
      show Φ ((g • m : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) = g • Φ (m : (w.adicCompletion K))
      rw [NumberField.PlaceDecomp.coe_smul_units, h3 g]
    refine ⟨M4aHerbrand.repHomOfMulEquivariant ΦM hΦM, ?_⟩
    refine Rep.hom_ext ?_
    ext z
    rw [Rep.hom_comp, Rep.hom_id]
    show θ.hom ((M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom z) = z
    rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    change Additive.ofMul (Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z))))) = Additive.ofMul (Additive.toMul z)
    congr 1
    apply Units.ext
    have h : ((Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z)))) : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) =
        Φ.symm ((ΦM (Additive.toMul z) : (↥L)ˣ) : ↥L) := hθ (ΦM (Additive.toMul z))
    refine h.trans ?_
    show Φ.symm (Φ ((Additive.toMul z : (w.adicCompletion K)ˣ) : (w.adicCompletion K))) = ((Additive.toMul z : (w.adicCompletion K)ˣ) : (w.adicCompletion K))
    exact Φ.symm_apply_apply _

  obtain ⟨θ', hθ'⟩ := hθiso
  have hback : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ),
      (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ' 2).hom y) = y := by
    intro y
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ' θ 2)
    simp only [hθ', groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  set X' := (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ' 2).hom X with hX'
  have hmem : (groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom X' ∈ Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom u} := by
    rw [hspan ⊤]; trivial
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨n, ?_⟩
  have hXu : X' = n • u := by
    apply hres_inj
    rw [map_zsmul, ← hn]
    exact int_smul_eq_zsmul _ n _
  calc X = (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ 2).hom X' := (hback _).symm
    _ = n • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ 2).hom u := by rw [hXu, map_zsmul]

end NumberField.IdeleLocalInv.ReadingExists

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceAbove.above PlaceAbove.comap_above IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace IdeleLocalInv
p2m_export "NumberField.IdeleLocalInv" "HasLocalInv"
namespace BCTransfer
p2m_open "NumberField.IdeleLocalInv NumberField"

theorem transport_res {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep.{0} k H} {B : Rep.{0} k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ : Rep.res f₁ A ⟶ B) :
    ∃ φ' : Rep.res f₂ A ⟶ B, (∀ z, φ'.hom z = φ.hom z) ∧ groupCohomology.map f₁ φ 2 = groupCohomology.map f₂ φ' 2 := by
  subst h
  exact ⟨φ, fun _ => rfl, rfl⟩

end NumberField.IdeleLocalInv.BCTransfer

set_option maxHeartbeats 6400000 in
open NumberField.PlaceDecomp.FCFamily NumberField.IdeleLocalInv.ReadingExists NumberField.IdeleLocalInv.BCTransfer in

theorem solution
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (D'' : IdeleGaloisDescent (𝓞 K'') E K'')
    [MulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ]
    (hactI'' : ∀ (g : K'' ≃ₐ[E] K'') (x : (AdeleRing (𝓞 K'') K'')ˣ), g • x = D''.unitsAct g x)

    (J : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ))
    (hJ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, Additive.toMul (J.hom (Additive.ofMul z)) =
      Units.map (genuineBaseChange K K'').β.toMonoidHom z)
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2) (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ))
    (h : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t) :
    NumberField.IdeleLocalInv.HasLocalInv E K'' D'' hactI''
      ((groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) J 2).hom x) v t := by

  let res : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K) := AlgEquiv.restrictNormalHom K
  have hsurj : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective K''
  let ιq : (K'' ≃ₐ[E] K'') ⧸ res.ker ≃* (K ≃ₐ[E] K) := QuotientGroup.quotientKerEquivOfSurjective res hsurj
  have hιq : ∀ (g : K'' ≃ₐ[E] K'') (y : K), algebraMap K K'' (ιq (QuotientGroup.mk g) y) = g (algebraMap K K'' y) :=
    fun g y => AlgEquiv.restrictNormal_commutes g K y
  have hr : (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) = ιq.toMonoidHom.comp (QuotientGroup.mk' res.ker) :=
    MonoidHom.ext fun _ => rfl
  obtain ⟨J', hJ'v, hmapJ⟩ := transport_res hr J
  have hJ' : ∀ z : (AdeleRing (𝓞 K) K)ˣ, J'.hom (Additive.ofMul z) = Additive.ofMul (Units.map (genuineBaseChange K K'').β.toMonoidHom z) := by
    intro z
    rw [hJ'v, ← hJ z]
    rfl

  obtain ⟨prG, hprG, w, hw, q, hq, hqw, L', fdL', actL', faithL', actUL', Φ, h1, h2, h3, K₀, fdK₀, hbase, θ, hθ, u, hu, n, hcoord, ht⟩ := h
  haveI := hq
  haveI := fdL'
  letI := actL'
  haveI := faithL'
  letI := actUL'
  haveI := fdK₀

  obtain ⟨W, hWw⟩ : ∃ W : HeightOneSpectrum (𝓞 K''), W.under (𝓞 K) = w :=
    ⟨NumberField.PlaceAbove.above K K'' w, HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above K K'' w)⟩
  subst hWw

  obtain ⟨prM, hprM⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E K'' D'' hactI''
  obtain ⟨B⟩ := nonempty_bridgeFC E K'' W
  letI := B.hq; letI := B.fd; letI := B.act; letI := B.faith; letI := B.actU; letI := B.fd₀
  obtain ⟨nM, hnM⟩ := exists_eq_zsmul_map E K'' W B.q B.L B.Φ B.h1 B.h2 B.h3 B.K₀ B.base B.θ B.hθ B.u B.hu
    ((groupCohomology.map (NumberField.PlaceDecomp.decomp E K'' W).subtype (prM W) 2).hom
      ((groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) J 2).hom x))

  have key := M4aHerbrand.div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
    E K K'' res.ker ιq hιq J' hJ' W (prG (W.under (𝓞 K))) (hprG _) (prM W) (hprM W)
    x q L' Φ h1 h2 h3 K₀ hbase θ hθ u hu n hcoord
    B.q B.L B.Φ B.h1 B.h2 B.h3 B.K₀ B.base B.θ B.hθ B.u B.hu nM (by rw [← hmapJ]; exact hnM)
  refine ⟨prM, hprM, W, ?_, B.q, B.hq, B.hqw, B.L, B.fd, B.act, B.faith, B.actU, B.Φ, B.h1, B.h2, B.h3, B.K₀, B.fd₀, B.base,
    B.θ, B.hθ, B.u, B.hu, nM, hnM, ?_⟩
  ·
    rw [← hw]
    change W.asIdeal.comap _ = (W.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K''))).comap _
    rw [Ideal.comap_comap]
    congr 1
    exact IsScalarTower.algebraMap_eq (𝓞 E) (𝓞 K) (𝓞 K'')
  · rw [ht]; exact key.symm

end S_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange (solution)
