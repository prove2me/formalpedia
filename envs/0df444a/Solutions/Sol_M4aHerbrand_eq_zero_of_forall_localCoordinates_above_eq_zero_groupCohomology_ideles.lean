-- Prove2me | solution 1 for M4aHerbrand.eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e52d3d94-8701-57ba-884c-718375800916

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
import Theorems.Thm_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq
import Theorems.Thm_M4aHerbrand_map_prG_eq_map_map_prG_of_smul_eq
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_trans_transport
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_groupCohomology_map_conj_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles.M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp
open scoped NumberField.PlaceTransport

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart IdeleGaloisDescent GenuineDescent.genuineDescentDatum injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles map_prG_eq_map_map_prG_of_smul_eq GenuineDescent.genuineDescentDatum_act_fst_apply subsingleton_ideleGaloisDescent"
namespace InjChosenProof
p2m_open "M4aHerbrand"

open NumberField.InfPlaceDecomp NumberField.InfinitePlaceTransport

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

noncomputable def resRepHom {G H : Type} [Group G] [Group H] (φ : H →* G) {M N : Type} [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N] (f : M →* N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    Rep.res φ (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction H N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun h => LinearMap.ext fun a => by
    change Additive.ofMul (f (φ h • (Additive.toMul : _ ≃ M) a)) = Additive.ofMul (h • f ((Additive.toMul : _ ≃ M) a))
    rw [hf]⟩

noncomputable def conjRepHom {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] (σ : G) :
    Rep.res (MulAut.conj σ⁻¹).toMonoidHom (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction G M :=
  resRepHom (MulAut.conj σ⁻¹).toMonoidHom (MulDistribMulAction.toMonoidHom M σ) fun h m => by
    change σ • ((MulAut.conj σ⁻¹) h • m) = h • σ • m
    rw [MulAut.conj_apply, inv_inv, ← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

theorem conjRepHom_spec {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] (σ : G)
    (m : Rep.res (MulAut.conj σ⁻¹).toMonoidHom (Rep.ofMulDistribMulAction G M)) :
    (conjRepHom (M := M) σ).hom m = (Rep.ofMulDistribMulAction G M).ρ (σ⁻¹)⁻¹ m := by
  rw [inv_inv]
  rfl

variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

theorem infTransport_congr {σ τ : F ≃ₐ[E] F} (hστ : σ = τ) {w w' : InfinitePlace F} (h : σ • w = w') (h' : τ • w = w') :
    transport σ h = transport τ h' := by
  subst hστ
  rfl

theorem mem_infDecomp_smul_iff (w : InfinitePlace F) (σ τ : F ≃ₐ[E] F) :
    τ ∈ decomp E F (σ • w) ↔ σ⁻¹ * τ * σ ∈ decomp E F w := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]

noncomputable def conjHomInf (w : InfinitePlace F) (σ : F ≃ₐ[E] F) : ↥(decomp E F (σ • w)) →* ↥(decomp E F w) where
  toFun τ := ⟨σ⁻¹ * (τ : F ≃ₐ[E] F) * σ, (mem_infDecomp_smul_iff w σ τ).1 τ.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change σ⁻¹ * ((a : F ≃ₐ[E] F) * b) * σ = σ⁻¹ * (a : F ≃ₐ[E] F) * σ * (σ⁻¹ * (b : F ≃ₐ[E] F) * σ)
    group)

theorem coe_conjHomInf (w : InfinitePlace F) (σ : F ≃ₐ[E] F) (τ : ↥(decomp E F (σ • w))) :
    ((conjHomInf w σ τ : ↥(decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ := rfl

theorem infTransport_smul (w : InfinitePlace F) (σ : F ≃ₐ[E] F) (τ : ↥(decomp E F (σ • w))) (y : w.Completion) :
    transport σ rfl ((conjHomInf w σ τ) • y) = τ • transport σ rfl y := by
  have hc : ((conjHomInf w σ τ : ↥(decomp E F w)) : F ≃ₐ[E] F) • w = w := MulAction.mem_stabilizer_iff.mp (conjHomInf w σ τ).2
  have hτ : ((τ : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) • (σ • w) = σ • w := MulAction.mem_stabilizer_iff.mp τ.2
  have h₃ : (σ * (σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)) • w = σ • w := by
    rw [show σ * (σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) = (τ : F ≃ₐ[E] F) * σ by group, mul_smul, hτ]
  have h₃' : ((τ : F ≃ₐ[E] F) * σ) • w = σ • w := by rw [mul_smul, hτ]
  rw [NumberField.InfPlaceDecomp.smul_def, NumberField.InfPlaceDecomp.smul_def,
    ← NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv E F w (conjHomInf w σ τ) hc,
    ← NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv E F (σ • w) τ hτ, ← RingEquiv.trans_apply, ← RingEquiv.trans_apply,
    NumberField.InfinitePlaceTransport.transport_trans_transport E F σ _ hc rfl h₃,
    NumberField.InfinitePlaceTransport.transport_trans_transport E F (τ : F ≃ₐ[E] F) σ rfl hτ h₃']
  exact congrFun (congrArg DFunLike.coe (infTransport_congr (by group) h₃ h₃')) y

noncomputable def TInf (w : InfinitePlace F) (σ : F ≃ₐ[E] F) :
    Rep.res (conjHomInf w σ) (localUnits E F w) ⟶ localUnits E F (σ • w) :=
  resRepHom (conjHomInf w σ) (Units.map (transport σ (rfl : σ • w = σ • w)).toRingHom.toMonoidHom) fun τ x => Units.ext (by
    rw [NumberField.InfPlaceDecomp.coe_smul_units, Units.coe_map, Units.coe_map, NumberField.InfPlaceDecomp.coe_smul_units]
    exact infTransport_smul w σ τ (x : w.Completion))

theorem TInf_apply (w : InfinitePlace F) (σ : F ≃ₐ[E] F) (x : (w.Completion)ˣ) :
    ((Additive.toMul ((TInf (E := E) w σ).hom (Additive.ofMul x)) : ((σ • w).Completion)ˣ) : (σ • w).Completion) = transport σ rfl (x : w.Completion) := rfl

theorem map_prInf_smul_eq [IsGalois E F] (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (hprInf : ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ), (prInf v).hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)))
    (w : InfinitePlace F) (σ : F ≃ₐ[E] F) (n : ℕ) (y : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) n) :
    (groupCohomology.map (decomp E F (σ • w)).subtype (prInf (σ • w)) n).hom y =
      (groupCohomology.map (conjHomInf w σ) (TInf w σ) n).hom ((groupCohomology.map (decomp E F w).subtype (prInf w) n).hom y) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _

  have hid := groupCohomology.map_conj_eq_id (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) σ⁻¹ n
    (conjRepHom (M := (AdeleRing (𝓞 F) F)ˣ) σ) (conjRepHom_spec σ)
  have hy : (groupCohomology.map (MulAut.conj σ⁻¹).toMonoidHom (conjRepHom (M := (AdeleRing (𝓞 F) F)ˣ) σ) n).hom y = y := by
    rw [hid]; rfl
  conv_lhs => rw [← hy]
  have h1 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
      (B := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (C := localUnits E F (σ • w))
      (MulAut.conj σ⁻¹).toMonoidHom (decomp E F (σ • w)).subtype (conjRepHom (M := (AdeleRing (𝓞 F) F)ˣ) σ) (prInf (σ • w)) n)
  have h2 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
      (B := localUnits E F w) (C := localUnits E F (σ • w))
      (decomp E F w).subtype (conjHomInf w σ) (prInf w) (TInf w σ) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2]
  have hgrp : (MulAut.conj σ⁻¹).toMonoidHom.comp (decomp E F (σ • w)).subtype = (decomp E F w).subtype.comp (conjHomInf w σ) := by
    ext τ : 1
    change (MulAut.conj σ⁻¹) (τ : F ≃ₐ[E] F) = ((conjHomInf w σ τ : ↥(decomp E F w)) : F ≃ₐ[E] F)
    rw [coe_conjHomInf, MulAut.conj_apply, inv_inv]
  refine congrArg
    (fun (S : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) n ⟶ groupCohomology (localUnits E F (σ • w)) n) => S.hom y)
    (map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) n)
  obtain ⟨x, rfl⟩ : ∃ x : (AdeleRing (𝓞 F) F)ˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
  change (prInf (σ • w)).hom (Additive.ofMul (σ • x)) = (TInf w σ).hom ((prInf w).hom (Additive.ofMul x))
  rw [hactI]
  erw [hprInf, hprInf]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_ofMul]
  erw [TInf_apply]
  rw [Units.coe_map, Units.coe_map]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply E F σ (x : AdeleRing (𝓞 F) F) rfl

theorem under_above (v : HeightOneSpectrum (𝓞 E)) : (NumberField.PlaceAbove.above E F v).under (𝓞 E) = v :=
  HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def]; exact NumberField.PlaceAbove.comap_above E F v)

end M4aHerbrand.InjChosenProof

open M4aHerbrand.InjChosenProof in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (pr : ∀ w : HeightOneSpectrum (𝓞 F), Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w).adicCompletion F)ˣ)
    (hpr : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (pr w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (hprInf : ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ), (prInf v).hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)))
    (n : ℕ) (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = 0)
    (hinf : ∀ v : InfinitePlace E,
      (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (prInf (NumberField.ArchIdele.above E F v)) (n + 1)).hom x = 0) :
    x = 0  := by
  obtain ⟨hINJ, -, -⟩ := M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles E F D hactI pr hpr prInf hprInf n
  refine hINJ x (fun w => ?_) (fun w => ?_)
  ·
    have hmem : w ∈ MulAction.orbit (F ≃ₐ[E] F) (NumberField.PlaceAbove.above E F (w.under (𝓞 E))) := by
      rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E F]
      exact (under_above (F := F) (w.under (𝓞 E))).symm ▸ rfl
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 hmem
    obtain ⟨-, c, T, -, hc, hT⟩ := NumberField.PlaceDecomp.exists_conj_and_transport_repHom_of_smul_eq E F
      (NumberField.PlaceAbove.above E F (w.under (𝓞 E))) w σ hσ
    rw [M4aHerbrand.map_prG_eq_map_map_prG_of_smul_eq E F D hactI pr hpr (NumberField.PlaceAbove.above E F (w.under (𝓞 E))) w σ hσ
      c hc T hT (n + 1) x, hfin, map_zero]
  ·
    obtain ⟨v, hv⟩ : ∃ v, w.comap (algebraMap E F) = v := ⟨_, rfl⟩
    obtain ⟨σ, hσ⟩ : ∃ σ : F ≃ₐ[E] F, σ • NumberField.ArchIdele.above E F v = w :=
      NumberField.InfinitePlace.exists_smul_eq_of_comap_eq ((NumberField.ArchIdele.comap_above E F v).trans hv.symm)
    subst hσ
    have key := map_prInf_smul_eq D hactI prInf hprInf (NumberField.ArchIdele.above E F v) σ (n + 1) x
    rw [hinf v, map_zero] at key
    exact key

end S_M4aHerbrand_eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles
end P2MW
export P2MW.S_M4aHerbrand_eq_zero_of_forall_localCoordinates_above_eq_zero_groupCohomology_ideles (solution)
