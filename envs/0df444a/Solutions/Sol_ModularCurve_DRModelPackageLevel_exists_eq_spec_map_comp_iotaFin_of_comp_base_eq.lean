-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7d10dc18-04ea-52b9-bee9-5b73c93802f2

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel ModularCurve.IgusaScheme ModularCurve.PlaceSpecialization Opposite TopologicalSpace

noncomputable section

namespace CoordSS

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}

namespace L1

theorem congr_hom {R S : CommRingCat.{0}} {f g : R ⟶ S} (h : f = g) (x : R) : f x = g x := by rw [h]

theorem pushout_inl_eq_inr_iff {U X Y : Scheme.{0}} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] (x : X) (y : Y) :
    (pushout.inl f g).base x = (pushout.inr f g).base y ↔
      ∃ w : U, f.base w = x ∧ g.base w = y := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span f g)
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x) (xj := y)).mp h
    rcases k with (_ | _ | _)
    · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      subst hfi hfj
      exact ⟨w, by simp at h₁; exact h₁, by simp at h₂; exact h₂⟩
    · change WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) at fj
      rcases fj with ⟨⟩
    · change WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) at fi
      rcases fi with ⟨⟩
  · rintro ⟨w, rfl, rfl⟩
    change (f ≫ pushout.inl f g).base w = (g ≫ pushout.inr f g).base w
    rw [pushout.condition]

theorem appLE_appIso_inv_eq {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g] (fg : X ⟶ Z)
    (H : fg = f ≫ g) (h : (⊤ : X.Opens) ≤ fg ⁻¹ᵁ (g ''ᵁ ⊤)) (s : Γ(Y, ⊤)) :
    fg.appLE (g ''ᵁ ⊤) ⊤ h ((g.appIso ⊤).inv s) = f.appTop s := by
  subst H
  have h₁ : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ ⊤) := (g.preimage_image_eq ⊤).ge
  have hc : (f ≫ g).appLE (g ''ᵁ ⊤) ⊤ h = g.appLE (g ''ᵁ ⊤) ⊤ h₁ ≫ f.appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have h2 : (g.appIso ⊤).inv ≫ g.appLE (g ''ᵁ ⊤) ⊤ h₁ = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    simp
  have h3 : f.appLE ⊤ ⊤ le_top = f.appTop := by
    rw [Scheme.Hom.appLE]
    simp
  rw [hc, ← h3, CommRingCat.comp_apply, ← CommRingCat.comp_apply (g.appIso ⊤).inv, h2, CommRingCat.id_apply]

end L1

namespace L1

section Igusa

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

abbrev VFin : (ModularCurve.IgusaScheme N ℓ).Opens := (ιFin N ℓ) ''ᵁ ⊤

abbrev VInf : (ModularCurve.IgusaScheme N ℓ).Opens := (ιInf N ℓ) ''ᵁ ⊤

abbrev ιMid : XMid N ℓ ⟶ ModularCurve.IgusaScheme N ℓ := fInf N ℓ ≫ ιInf N ℓ

abbrev VMid : (ModularCurve.IgusaScheme N ℓ).Opens := (ιMid N ℓ) ''ᵁ ⊤

theorem ιMid_eq : ιMid N ℓ = fFin N ℓ ≫ ιFin N ℓ := (glue_condition N ℓ).symm

theorem VMid_le_VFin : VMid N ℓ ≤ VFin N ℓ := by
  rintro z ⟨w, -, rfl⟩
  refine ⟨(fFin N ℓ).base w, trivial, ?_⟩
  change (fFin N ℓ ≫ ιFin N ℓ).base w = (fInf N ℓ ≫ ιInf N ℓ).base w
  rw [glue_condition]

theorem VMid_le_VInf : VMid N ℓ ≤ VInf N ℓ := by
  rintro z ⟨w, -, rfl⟩
  exact ⟨(fInf N ℓ).base w, trivial, rfl⟩

theorem inf_le_VMid : VFin N ℓ ⊓ VInf N ℓ ≤ VMid N ℓ := by
  rintro z ⟨⟨a, -, rfl⟩, ⟨b, -, hb⟩⟩
  obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (fFin N ℓ) (fInf N ℓ) a b).mp hb.symm
  exact ⟨w, trivial, by rw [← hb, ← hw]; rfl⟩

abbrev tFin : Γ(ModularCurve.IgusaScheme N ℓ, VFin N ℓ) :=
  ((ιFin N ℓ).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin N ℓ))).inv (jChartFin N ℓ))

abbrev tInf : Γ(ModularCurve.IgusaScheme N ℓ, VInf N ℓ) :=
  ((ιInf N ℓ).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf N ℓ))).inv (jInvChartInf N ℓ))

theorem top_le_preimage {U : (ModularCurve.IgusaScheme N ℓ).Opens} (hU : VMid N ℓ ≤ U) :
    (⊤ : (XMid N ℓ).Opens) ≤ ιMid N ℓ ⁻¹ᵁ U :=
  ((ιMid N ℓ).preimage_image_eq ⊤).ge.trans ((Opens.map (ιMid N ℓ).base).map (homOfLE hU)).le

def Φ (U : (ModularCurve.IgusaScheme N ℓ).Opens) (hU : VMid N ℓ ≤ U) :
    Γ(ModularCurve.IgusaScheme N ℓ, U) ⟶ Γ(XMid N ℓ, ⊤) :=
  (ιMid N ℓ).appLE U ⊤ (top_le_preimage N ℓ hU)

variable {N ℓ} in
theorem Φ_map {U U' : (ModularCurve.IgusaScheme N ℓ).Opens} (hU' : VMid N ℓ ≤ U') (i : U' ≤ U)
    (s : Γ(ModularCurve.IgusaScheme N ℓ, U)) :
    Φ N ℓ U' hU' ((ModularCurve.IgusaScheme N ℓ).presheaf.map (homOfLE i).op s) = Φ N ℓ U (hU'.trans i) s := by
  rw [Φ, Φ, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem Φ_tFin : Φ N ℓ (VFin N ℓ) (VMid_le_VFin N ℓ) (tFin N ℓ) =
    (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid N ℓ))).inv (inclFin N ℓ (jChartFin N ℓ)) := by
  rw [Φ, appLE_appIso_inv_eq (fFin N ℓ) (ιFin N ℓ) (ιMid N ℓ) (ιMid_eq N ℓ), ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem Φ_tInf : Φ N ℓ (VInf N ℓ) (VMid_le_VInf N ℓ) (tInf N ℓ) =
    (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid N ℓ))).inv (inclInf N ℓ (jInvChartInf N ℓ)) := by
  rw [Φ, appLE_appIso_inv_eq (fInf N ℓ) (ιInf N ℓ) (ιMid N ℓ) rfl, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem Φ_VMid_injective : Function.Injective (Φ N ℓ (VMid N ℓ) le_rfl) := by
  have h : ((ιMid N ℓ).appIso ⊤).inv ≫ Φ N ℓ (VMid N ℓ) le_rfl = 𝟙 _ := by
    rw [Φ, Scheme.Hom.appIso_inv_appLE]
    simp
  have h' : Φ N ℓ (VMid N ℓ) le_rfl = ((ιMid N ℓ).appIso ⊤).hom := by
    rw [← Category.comp_id ((ιMid N ℓ).appIso ⊤).hom, ← h, Iso.hom_inv_id_assoc]
  rw [h']
  exact ((ιMid N ℓ).appIso ⊤).commRingCatIsoToRingEquiv.injective

theorem inclFin_mul_inclInf : inclFin N ℓ (jChartFin N ℓ) * inclInf N ℓ (jInvChartInf N ℓ) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf]
    exact mul_inv_cancel₀ (jFull_ne_zero N))

theorem tFin_mul_tInf :
    (ModularCurve.IgusaScheme N ℓ).presheaf.map (homOfLE (VMid_le_VFin N ℓ)).op (tFin N ℓ) *
      (ModularCurve.IgusaScheme N ℓ).presheaf.map (homOfLE (VMid_le_VInf N ℓ)).op (tInf N ℓ) = 1 := by
  apply Φ_VMid_injective N ℓ
  rw [map_mul, map_one, Φ_map, Φ_map, Φ_tFin, Φ_tInf, ← map_mul, inclFin_mul_inclInf, map_one]

end Igusa

end L1

namespace L1

section Read

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} (𝔓 : DRModelPackageLevel N₀ p hpN₀)
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)

abbrev hh : (𝔓.Mfib κ toκ).C ⟶ X0 N₀ p :=
  𝔓.efib κ toκ ≫ pullback.fst (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))

def rd (U : (X0 N₀ p).Opens) [Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ U))] : Γ(X0 N₀ p, U) →+* ↥(modularFunctionFieldC κ N₀) :=
  (𝔓.Mfib κ toκ).ffEquiv.symm.toRingHom.comp
    ((((𝔓.Mfib κ toκ).C.germToFunctionField (hh 𝔓 κ toκ ⁻¹ᵁ U)).hom).comp ((hh 𝔓 κ toκ).app U).hom)

theorem rd_apply (U : (X0 N₀ p).Opens) [Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ U))] (s : Γ(X0 N₀ p, U)) :
    rd 𝔓 κ toκ U s = (𝔓.Mfib κ toκ).ffEquiv.symm
      ((𝔓.Mfib κ toκ).C.germToFunctionField (hh 𝔓 κ toκ ⁻¹ᵁ U) (((hh 𝔓 κ toκ).app U).hom s)) := rfl

theorem rd_map {U U' : (X0 N₀ p).Opens} (i : U' ≤ U) [Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ U))]
    [Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ U'))] (s : Γ(X0 N₀ p, U)) :
    rd 𝔓 κ toκ U' ((X0 N₀ p).presheaf.map (homOfLE i).op s) = rd 𝔓 κ toκ U s := by
  have key : (X0 N₀ p).presheaf.map (homOfLE i).op ≫ (hh 𝔓 κ toκ).app U' ≫
      (𝔓.Mfib κ toκ).C.germToFunctionField (hh 𝔓 κ toκ ⁻¹ᵁ U') =
      (hh 𝔓 κ toκ).app U ≫ (𝔓.Mfib κ toκ).C.germToFunctionField (hh 𝔓 κ toκ ⁻¹ᵁ U) := by
    rw [(hh 𝔓 κ toκ).naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  have h := congr_hom key s
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  rw [rd_apply, rd_apply]
  congr 1

theorem rd_eq_of_mem (U : (X0 N₀ p).Opens) [Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ U))] (s : Γ(X0 N₀ p, U))
    (z : ↥(𝔓.Mfib κ toκ).C) (hz : z ∈ hh 𝔓 κ toκ ⁻¹ᵁ U) :
    rd 𝔓 κ toκ U s = (𝔓.Mfib κ toκ).ffEquiv.symm
      (algebraMap ((𝔓.Mfib κ toκ).C.presheaf.stalk z) (𝔓.Mfib κ toκ).C.functionField
        ((𝔓.Mfib κ toκ).C.presheaf.germ (hh 𝔓 κ toκ ⁻¹ᵁ U) z hz (((hh 𝔓 κ toκ).app U).hom s))) := by
  have h := congr_hom (TopCat.Presheaf.germ_stalkSpecializes (𝔓.Mfib κ toκ).C.presheaf hz
    ((genericPoint_spec (𝔓.Mfib κ toκ).C).specializes trivial)) (((hh 𝔓 κ toκ).app U).hom s)
  rw [CommRingCat.comp_apply] at h
  rw [rd_apply]
  congr 1
  rw [RingHom.algebraMap_toAlgebra]
  exact h.symm

theorem rd_tFin : rd 𝔓 κ toκ (VFin N₀ p) (tFin N₀ p) = jGeomGen κ N₀ :=
  (DRModelPackageLevel.Mfib_pin 𝔓 κ toκ (jChartFin N₀ p)).1 rfl

theorem iotaInf_jInvChartInf : 𝔓.iotaInf (jInvChartInf N₀ p) = jInvChartInf (N₀ * p) p := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔓.iotaInf_spec]
  simp [coe_jInvChartInf, coe_jFull]

end Read

end L1

open L1 in

theorem exists_eq_spec_map_comp_ιFin_of_crossing (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    {A : Type} [CommRing A] [IsLocalRing A] (red : A →+* κ)
    (hker : ∀ c : A, c ∈ IsLocalRing.maximalIdeal A → red c = 0)
    (f : Spec (CommRingCat.of A) ⟶ X N₀ p)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ)
    (h₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ f)
    (n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)))
    (hn : (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n =
      uκ.base (IsLocalRing.closedPoint κ)) :
    ∃ φ : ↥(chartAlgFin (N₀ * p) p) →+* A, f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p := by
  rcases ModularCurve.IgusaScheme.exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal (N₀ * p) p f
    with hfin | ⟨ψ, hf, hψ⟩
  · exact hfin
  exfalso

  obtain ⟨⟨hxc, hplace⟩, -⟩ := 𝔓.node_pin κ toκ n
  set P := (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base n with hP
  set x := (inv (𝔓.efib κ toκ)).base P with hxdef

  set β : ↥(chartAlgInf N₀ p) →+* κ := (red.comp ψ).comp 𝔓.iotaInf.toRingHom with hβ
  set y : ↥(XInf N₀ p) := (Spec.map (CommRingCat.ofHom β)).base (closedPoint κ) with hy
  have hβj : β (jInvChartInf N₀ p) = 0 := by
    simp only [hβ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, iotaInf_jInvChartInf]
    exact hker _ hψ
  have hyj : jInvChartInf N₀ p ∈ y.asIdeal := by
    rw [hy, Spec.map_base]
    show β (jInvChartInf N₀ p) ∈ (closedPoint κ).asIdeal
    rw [hβj]; exact Ideal.zero_mem _

  have hhx : (hh 𝔓 κ toκ).base x = (ιInf N₀ p).base y := by
    have e1 : (hh 𝔓 κ toκ).base x = (pullback.fst (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))).base P := by
      show (inv (𝔓.efib κ toκ) ≫ 𝔓.efib κ toκ ≫ pullback.fst _ _).base P = _
      rw [IsIso.inv_hom_id_assoc]
    have e2 : (𝔓.comp κ toκ 0).base P = uκ.base (closedPoint κ) := by rw [← hn]; rfl
    have e3 : 𝔓.comp κ toκ 0 ≫ fibreMap0 𝔓.π toκ ≫ pullback.fst _ _ =
        pullback.fst (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ)) := by
      rw [← Category.assoc, 𝔓.comp_pi, Category.id_comp]
    have e4 : uκ ≫ fibreMap0 𝔓.π toκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ ιInf N₀ p := by
      rw [show fibreMap0 𝔓.π toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.π.1 from pullback.lift_fst _ _ _,
        reassoc_of% h₁, hf, Category.assoc, 𝔓.pi_chartInf]
      simp only [hβ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, AlgHom.toRingHom_eq_coe]
    rw [e1, ← e3]
    show (fibreMap0 𝔓.π toκ ≫ pullback.fst _ _).base ((𝔓.comp κ toκ 0).base P) = _
    rw [e2]
    show (uκ ≫ fibreMap0 𝔓.π toκ ≫ pullback.fst _ _).base (closedPoint κ) = _
    rw [e4]
    rfl

  have hxInf : x ∈ hh 𝔓 κ toκ ⁻¹ᵁ VInf N₀ p := by
    show (hh 𝔓 κ toκ).base x ∈ (VInf N₀ p : Set _)
    rw [hhx]; exact ⟨y, trivial, rfl⟩
  set g := (𝔓.Mfib κ toκ).C.presheaf.germ (hh 𝔓 κ toκ ⁻¹ᵁ VInf N₀ p) x hxInf
    (((hh 𝔓 κ toκ).app (VInf N₀ p)).hom (tInf N₀ p)) with hg
  have hgu : ¬ IsUnit g := by
    rw [hg, ← Scheme.mem_basicOpen]
    intro hmem
    have h' : x ∈ hh 𝔓 κ toκ ⁻¹ᵁ (X0 N₀ p).basicOpen (tInf N₀ p) := by rwa [Scheme.preimage_basicOpen]
    have h'' : (hh 𝔓 κ toκ).base x ∈ ((X0 N₀ p).basicOpen (tInf N₀ p) : Set _) := h'
    rw [hhx, ← Scheme.image_basicOpen, basicOpen_eq_of_affine] at h''
    obtain ⟨y', hy', hyy'⟩ := h''
    rw [(ιInf N₀ p).isOpenEmbedding.injective hyy'] at hy'
    exact hy' hyj

  haveI : Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ VInf N₀ p)) := ⟨⟨x, hxInf⟩⟩
  haveI : Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ VMid N₀ p)) := by
    obtain ⟨⟨z₀, hz₀⟩⟩ := (inferInstance : Nonempty (Scheme.Opens.toScheme (hh 𝔓 κ toκ ⁻¹ᵁ VFin N₀ p)))
    have hF : (SetLike.coe (hh 𝔓 κ toκ ⁻¹ᵁ VFin N₀ p)).Nonempty := ⟨z₀, hz₀⟩
    obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter (hh 𝔓 κ toκ ⁻¹ᵁ VFin N₀ p).isOpen
      (hh 𝔓 κ toκ ⁻¹ᵁ VInf N₀ p).isOpen hF ⟨x, hxInf⟩
    exact ⟨⟨z, inf_le_VMid N₀ p ⟨hz1, hz2⟩⟩⟩

  have hprod : jGeomGen κ N₀ * rd 𝔓 κ toκ (VInf N₀ p) (tInf N₀ p) = 1 := by
    rw [← rd_tFin 𝔓 κ toκ, ← rd_map 𝔓 κ toκ (VMid_le_VFin N₀ p), ← rd_map 𝔓 κ toκ (VMid_le_VInf N₀ p),
      ← map_mul, tFin_mul_tInf, map_one]

  set θ := ((𝔓.Mfib κ toκ).ffEquiv.symm : (𝔓.Mfib κ toκ).C.functionField ≃+* ↥(modularFunctionFieldC κ N₀)).toRingHom.comp
    (algebraMap ((𝔓.Mfib κ toκ).C.presheaf.stalk x) (𝔓.Mfib κ toκ).C.functionField) with hθ
  have hrd : rd 𝔓 κ toκ (VInf N₀ p) (tInf N₀ p) = θ g := rd_eq_of_mem 𝔓 κ toκ _ _ x hxInf

  have hw : IsAffineGeomPlace κ N₀ ((𝔓.Mfib κ toκ).placeOfPoint ⟨x, hxc⟩) := by
    rw [hplace]
    exact ((isSupersingularPlace_iff p N₀ κ _).mp ((mem_ssPlaces_iff p N₀ κ).mp (𝔓.nodeEquiv κ toκ n).2)).2.1
  have hmem : jGeomGen κ N₀ ∈ θ.range := by
    rw [hθ, (𝔓.Mfib κ toκ).range_stalk_eq ⟨x, hxc⟩]
    exact hw.1
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp hmem

  have hk : θ (r * g - 1) = 0 := by rw [map_sub, map_mul, hr, map_one, ← hrd, hprod, sub_self]
  have hk' : r * g - 1 ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map θ
    rw [hk] at hu'
    exact not_isUnit_zero hu'
  have hg' : r * g ∈ IsLocalRing.maximalIdeal _ :=
    Ideal.mul_mem_left _ r ((IsLocalRing.mem_maximalIdeal _).mpr hgu)
  have h1 : (1 : ↑((𝔓.Mfib κ toκ).C.presheaf.stalk x)) ∈ IsLocalRing.maximalIdeal _ := by
    simpa using Ideal.sub_mem _ hg' hk'
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end CoordSS

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    {A : Type} [CommRing A] [IsLocalRing A] (red : A →+* κ)
    (hker : ∀ c : A, c ∈ IsLocalRing.maximalIdeal A → red c = 0)
    (f : Spec (CommRingCat.of A) ⟶ X N₀ p)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ)
    (h₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ f)
    (n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)))
    (hn : (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n =
      uκ.base (IsLocalRing.closedPoint κ)) :
    ∃ φ : ↥(chartAlgFin (N₀ * p) p) →+* A, f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p :=
  CoordSS.exists_eq_spec_map_comp_ιFin_of_crossing 𝔓 κ toκ red hker f uκ h₁ n hn

#print axioms solution

end
end S_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq (solution)
