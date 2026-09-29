-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_partialAction_compatible_maximal_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/469fa830-338c-5224-817b-bf32d11b64c0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
import Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra (SchemeHomOver)

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
p2m_open "GoodReductionJacobian"

namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "pair Defined liftDom liftDom_ι act_coe modelPoint modelPoint_coe Compatible Maximal hom_comp mk dom dense_dom hom"
p2m_open "GoodReductionJacobian.PartialAction"

namespace InducedOperation

section Points

variable {B T'' T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {t'' : T'' ⟶ B} {g : A ⟶ B}

theorem comp_comp (ψ' : T'' ⟶ T') (hψ' : ψ' ≫ t' = t'') (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ' hψ' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp (ψ' ≫ ψ) (by rw [Category.assoc, hψ, hψ']) x :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem comp_congr {ψ₁ ψ₂ : T' ⟶ T} (e : ψ₁ = ψ₂) (h₁ : ψ₁ ≫ t = t') (h₂ : ψ₂ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ₁ h₁ x = schemeHomOverComp ψ₂ h₂ x := by
  subst e; rfl

end Points

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

theorem pair_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) :
    pair (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x) = ψ ≫ pair γ x := by
  apply pullback.hom_ext <;>
    simp only [pair, schemeHomOverComp_coe, pullback.lift_fst, pullback.lift_snd, Category.assoc]

theorem comp_mul (L : RelativeGroupLaw k f) {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.mul t x y) =
      L.mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y) :=
  L.mul_natural t t' ψ hψ x y

theorem liftDom_eq (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x)
    (φ : T ⟶ (a.dom : Scheme.{u})) (h : φ ≫ a.dom.ι = pair γ x) : a.liftDom γ x hd = φ := by
  rw [← cancel_mono a.dom.ι, liftDom_ι, h]

section Chart

variable (L : RelativeGroupLaw k f) {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
  (hι : ι ≫ p = V.ι ≫ f)

abbrev q (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    pullback f p ⟶ Spec (CommRingCat.of k) :=
  pullback.fst f p ≫ f

def U₁ (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] : (pullback f p).Opens :=
  pullback.snd f p ⁻¹ᵁ (Scheme.Hom.opensRange ι)

abbrev tU (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (U₁ f p ι).ι ≫ q f p

def γU (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] : SchemeHomOver (tU f p ι) f :=
  ⟨(U₁ f p ι).ι ≫ pullback.fst f p, rfl⟩

@[scoped simp] theorem γU_coe (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    (γU f p ι).1 = (U₁ f p ι).ι ≫ pullback.fst f p := rfl

def vLift (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}) ⟶ (V : Scheme.{u}) :=
  IsOpenImmersion.lift ι ((U₁ f p ι).ι ≫ pullback.snd f p) (by
    rintro _ ⟨z, rfl⟩
    exact z.2)

@[reassoc (attr := simp)]
theorem vLift_ι (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))
    (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] :
    vLift f p ι ≫ ι = (U₁ f p ι).ι ≫ pullback.snd f p :=
  IsOpenImmersion.lift_fac _ _ _

include hι in
theorem vLift_comp : (vLift f p ι ≫ V.ι) ≫ f = tU f p ι := by
  rw [Category.assoc, ← hι, vLift_ι_assoc, ← pullback.condition]

def vU : SchemeHomOver (tU f p ι) f := ⟨vLift f p ι ≫ V.ι, vLift_comp ι hι⟩

@[scoped simp] theorem vU_coe : (vU ι hι).1 = vLift f p ι ≫ V.ι := rfl

def mU : SchemeHomOver (tU f p ι) f := L.mul (tU f p ι) (γU f p ι) (vU ι hι)

def W : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens := (mU L ι hι).1 ⁻¹ᵁ V

def dom₀ : (pullback f p).Opens := (U₁ f p ι).ι ''ᵁ (W L ι hι)

def isoW : ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) : Scheme.{u}) ≅
    ((dom₀ L ι hι : (pullback f p).Opens) : Scheme.{u}) :=
  (U₁ f p ι).ι.isoImage (W L ι hι)

@[reassoc]
theorem isoW_hom_ι : (isoW L ι hι).hom ≫ (dom₀ L ι hι).ι = (W L ι hι).ι ≫ (U₁ f p ι).ι :=
  Scheme.Hom.isoImage_hom_ι _ _

@[reassoc]
theorem isoW_inv_ι : (isoW L ι hι).inv ≫ (W L ι hι).ι ≫ (U₁ f p ι).ι = (dom₀ L ι hι).ι :=
  Scheme.Hom.isoImage_inv_ι _ _

def mW : ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) : Scheme.{u}) ⟶
    (V : Scheme.{u}) :=
  (mU L ι hι).1 ∣_ V

@[reassoc]
theorem mW_ι : mW L ι hι ≫ V.ι = (W L ι hι).ι ≫ (mU L ι hι).1 := morphismRestrict_ι _ _

def hom₀ : ((dom₀ L ι hι : (pullback f p).Opens) : Scheme.{u}) ⟶ P :=
  (isoW L ι hι).inv ≫ mW L ι hι ≫ ι

include hι in

theorem hom₀_comp : hom₀ L ι hι ≫ p = (dom₀ L ι hι).ι ≫ pullback.snd f p ≫ p := by
  simp only [hom₀, Category.assoc]
  rw [hι, mW_ι_assoc, (mU L ι hι).2, isoW_inv_ι_assoc]
  dsimp only [q]
  rw [pullback.condition]

section TPoints

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
  (v w : SchemeHomOver t (V.ι ≫ f))

def liftU : T ⟶ ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (U₁ f p ι).ι (pair γ (modelPoint ι hι v)) (by
    rintro _ ⟨τ, rfl⟩
    rw [Scheme.Opens.range_ι]
    show pullback.snd f p (pair γ (modelPoint ι hι v) τ) ∈ Scheme.Hom.opensRange ι
    rw [← Scheme.Hom.comp_apply, pair, pullback.lift_snd, modelPoint_coe, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩)

@[reassoc (attr := simp)]
theorem liftU_ι : liftU ι hι γ v ≫ (U₁ f p ι).ι = pair γ (modelPoint ι hι v) :=
  IsOpenImmersion.lift_fac _ _ _

theorem liftU_tU : liftU ι hι γ v ≫ tU f p ι = t := by
  rw [tU, q, liftU_ι_assoc, pair, pullback.lift_fst_assoc]
  exact γ.2

theorem comp_liftU_γU : schemeHomOverComp (liftU ι hι γ v) (liftU_tU ι hι γ v) (γU f p ι) = γ :=
  Subtype.ext (by
    simp only [schemeHomOverComp_coe, γU_coe, liftU_ι_assoc, pair, pullback.lift_fst])

theorem liftU_vLift : liftU ι hι γ v ≫ vLift f p ι = v.1 := by
  rw [← cancel_mono ι, Category.assoc, vLift_ι, liftU_ι_assoc, pair, pullback.lift_snd,
    modelPoint_coe]

theorem comp_liftU_vU : schemeHomOverComp (liftU ι hι γ v) (liftU_tU ι hι γ v) (vU ι hι) =
    NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) :=
  Subtype.ext (by
    simp only [schemeHomOverComp_coe, vU_coe, NeronModelInfra.schemeHomOverComp_coe,
      ← Category.assoc, liftU_vLift])

theorem comp_liftU_mU : schemeHomOverComp (liftU ι hι γ v) (liftU_tU ι hι γ v) (mU L ι hι) =
    L.mul t γ (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
  rw [mU, comp_mul, comp_liftU_γU, comp_liftU_vU]

variable (hvw : NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
  L.mul t γ (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)))

include hvw in
theorem liftU_mU : liftU ι hι γ v ≫ (mU L ι hι).1 = w.1 ≫ V.ι := by
  have h := congrArg Subtype.val ((comp_liftU_mU L ι hι γ v).trans hvw.symm)
  simpa only [schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe] using h

include hvw in
theorem range_liftU_subset :
    Set.range (liftU ι hι γ v) ⊆ ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) :
      Scheme.{u}).Opens) : Set _) := by
  rintro _ ⟨τ, rfl⟩
  show (mU L ι hι).1 (liftU ι hι γ v τ) ∈ V
  rw [← Scheme.Hom.comp_apply, liftU_mU L ι hι γ v w hvw, Scheme.Hom.comp_apply]
  exact (w.1 τ).2

def liftW : T ⟶ ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) :
    Scheme.{u}) :=
  IsOpenImmersion.lift (W L ι hι).ι (liftU ι hι γ v) (by
    rw [Scheme.Opens.range_ι]; exact range_liftU_subset L ι hι γ v w hvw)

@[reassoc (attr := simp)]
theorem liftW_ι : liftW L ι hι γ v w hvw ≫ (W L ι hι).ι = liftU ι hι γ v :=
  IsOpenImmersion.lift_fac _ _ _

theorem pair_eq_liftW :
    pair γ (modelPoint ι hι v) = (liftW L ι hι γ v w hvw ≫ (isoW L ι hι).hom) ≫ (dom₀ L ι hι).ι := by
  rw [Category.assoc, isoW_hom_ι, liftW_ι_assoc, liftU_ι]

include hvw in
theorem range_pair_subset_dom₀ :
    Set.range (pair γ (modelPoint ι hι v)) ⊆ ((dom₀ L ι hι : (pullback f p).Opens) : Set _) := by
  rw [pair_eq_liftW L ι hι γ v w hvw]
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact (_ : ↥(dom₀ L ι hι)).2

theorem liftW_mW : liftW L ι hι γ v w hvw ≫ mW L ι hι = w.1 := by
  rw [← cancel_mono V.ι, Category.assoc, mW_ι, liftW_ι_assoc, liftU_mU L ι hι γ v w hvw]

theorem liftW_hom₀ : (liftW L ι hι γ v w hvw ≫ (isoW L ι hι).hom) ≫ hom₀ L ι hι = w.1 ≫ ι := by
  rw [hom₀, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, liftW_mW]

end TPoints

def idV (V : G.Opens) : SchemeHomOver (V.ι ≫ f) (V.ι ≫ f) := ⟨𝟙 _, Category.id_comp _⟩

theorem idV_eq : NeronModelInfra.schemeHomOverComp (idV V) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
    L.mul (V.ι ≫ f) (L.one _)
      (NeronModelInfra.schemeHomOverComp (idV V) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
  rw [L.one_mul]

theorem nonempty_W [Nonempty (V : Scheme.{u})] :
    Nonempty ((W L ι hι : ((U₁ f p ι : (pullback f p).Opens) : Scheme.{u}).Opens) :
      Scheme.{u}) :=
  Nonempty.map (liftW L ι hι (L.one _) (idV V) (idV V) (idV_eq L)) inferInstance

theorem dense_dom₀ [Nonempty (V : Scheme.{u})] [IrreducibleSpace ↥(pullback f p)] :
    Dense ((dom₀ L ι hι : (pullback f p).Opens) : Set ↥(pullback f p)) := by
  refine (dom₀ L ι hι).2.dense ?_
  obtain ⟨x⟩ := nonempty_W L ι hι
  exact ⟨_, ((isoW L ι hι).hom x).2⟩

end Chart

section Extension

variable (L : RelativeGroupLaw k f) {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
  (hι : ι ≫ p = V.ι ≫ f) [Nonempty (V : Scheme.{u})] [IrreducibleSpace ↥(pullback f p)]

def chart : (pullback f p).PartialMap P := ⟨dom₀ L ι hι, dense_dom₀ L ι hι, hom₀ L ι hι⟩

@[scoped simp] theorem chart_domain : (chart L ι hι).domain = dom₀ L ι hι := rfl
@[scoped simp] theorem chart_hom : (chart L ι hι).hom = hom₀ L ι hι := rfl

def ρ : (pullback f p) ⤏ P := (chart L ι hι).toRationalMap

variable [IsReduced (pullback f p)] [P.IsSeparated]

theorem toPartialMap_domain : (ρ L ι hι).toPartialMap.domain = (ρ L ι hι).domain := rfl

include hι in

theorem toPartialMap_hom_comp :
    (ρ L ι hι).toPartialMap.hom ≫ p =
      (ρ L ι hι).toPartialMap.domain.ι ≫ pullback.snd f p ≫ p := by
  letI : (pullback f p).Over (Spec (CommRingCat.of k)) := ⟨q f p⟩
  letI : P.Over (Spec (CommRingCat.of k)) := ⟨p⟩
  haveI : (chart L ι hι).IsOver (Spec (CommRingCat.of k)) := by
    rw [Scheme.PartialMap.isOver_iff]
    show hom₀ L ι hι ≫ p = (dom₀ L ι hι).ι ≫ pullback.fst f p ≫ f
    rw [hom₀_comp, pullback.condition]
  haveI : (ρ L ι hι).IsOver (Spec (CommRingCat.of k)) := by
    unfold ρ; infer_instance
  have h : (ρ L ι hι).toPartialMap.IsOver (Spec (CommRingCat.of k)) := inferInstance
  rw [Scheme.PartialMap.isOver_iff] at h
  have h' : (ρ L ι hι).toPartialMap.hom ≫ p =
      (ρ L ι hι).toPartialMap.domain.ι ≫ pullback.fst f p ≫ f := h
  rw [h', pullback.condition]

def action : PartialAction k f p where
  dom := (ρ L ι hι).toPartialMap.domain
  dense_dom := (ρ L ι hι).toPartialMap.dense_domain
  hom := (ρ L ι hι).toPartialMap.hom
  hom_comp := toPartialMap_hom_comp L ι hι

theorem action_dom : (action L ι hι).dom = (ρ L ι hι).domain := rfl

theorem dom₀_le : dom₀ L ι hι ≤ (action L ι hι).dom :=
  (chart L ι hι).le_domain_toRationalMap

theorem homOfLE_hom :
    (pullback f p).homOfLE (dom₀_le L ι hι) ≫ (action L ι hι).hom = hom₀ L ι hι := by
  have := (chart L ι hι).toPartialMap_toRationalMap_restrict
  rwa [Scheme.PartialMap.restrict_hom] at this

include hι in

theorem compatible : (action L ι hι).Compatible L V ι hι := by
  intro T t γ v w hvw
  have hd : (action L ι hι).Defined γ (modelPoint ι hι v) :=
    (range_pair_subset_dom₀ L ι hι γ v w hvw).trans (dom₀_le L ι hι)
  refine ⟨hd, Subtype.ext ?_⟩
  have hlift : (action L ι hι).liftDom γ (modelPoint ι hι v) hd =
      (liftW L ι hι γ v w hvw ≫ (isoW L ι hι).hom) ≫
        (pullback f p).homOfLE (dom₀_le L ι hι) :=
    liftDom_eq _ _ _ hd _ (by
      rw [Category.assoc, Scheme.homOfLE_ι, ← pair_eq_liftW])
  rw [act_coe, hlift, Category.assoc, homOfLE_hom, liftW_hom₀, modelPoint_coe]

theorem maximal : (action L ι hι).Maximal := by
  intro U' h' hle heq
  refine le_antisymm ?_ hle
  let π' : (pullback f p).PartialMap P :=
    ⟨U', (action L ι hι).dense_dom.mono (by exact_mod_cast hle), h'⟩
  have hres : π'.restrict (action L ι hι).dom (action L ι hι).dense_dom hle =
      (ρ L ι hι).toPartialMap := by
    have hh : (pullback f p).homOfLE hle ≫ π'.hom = (ρ L ι hι).toPartialMap.hom := heq
    unfold Scheme.PartialMap.restrict
    rw [hh]
    rfl
  have hρ : π'.toRationalMap = ρ L ι hι := by
    rw [← Scheme.PartialMap.restrict_toRationalMap π' (action L ι hι).dom (action L ι hι).dense_dom
      hle, hres, Scheme.RationalMap.toRationalMap_toPartialMap]
  calc U' = π'.domain := rfl
    _ ≤ π'.toRationalMap.domain := π'.le_domain_toRationalMap
    _ = (action L ι hι).dom := by rw [hρ]; rfl

end Extension

section Structure

variable (L : RelativeGroupLaw k f)

include L in
theorem geometricallyIrreducible [LocallyOfFiniteType f] [QuasiCompact f] [ConnectedSpace G] :
    GeometricallyIrreducible f := by
  obtain ⟨G₀, i, L₀, hoi, -, -, hgi, -, hrange, -⟩ :=
    RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent k L
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  haveI : IsIso i :=
    (isIso_iff_isOpenImmersion_and_epi_base i).mpr ⟨hoi, (TopCat.epi_iff_surjective _).mpr hsurj⟩
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible i f).mp hgi

theorem isReduced_pullback [Smooth f] [IsReduced P] [IsLocallyNoetherian P] :
    IsReduced (pullback f p) :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f p)

theorem valuativeCriterion_existence [IsProper p] : ValuativeCriterion.Existence p := by
  have h : UniversallyClosed p := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

theorem valuationRing_of_ringKrullDim_le_one (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R] (h : ringKrullDim R ≤ 1) :
    ValuationRing R := by
  haveI : Ring.KrullDimLE 1 R := Order.KrullDimLE.mk (by rw [Nat.cast_one]; exact h)
  have key : IsIntegrallyClosed R ∧
      ∀ Q : Ideal R, Q ≠ ⊥ → Q.IsPrime → Q = IsLocalRing.maximalIdeal R :=
    ⟨inferInstance, fun Q hQ hQ' => IsLocalRing.eq_maximalIdeal (hQ'.isMaximal_of_ne_bot hQ)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 1 3).mpr key

theorem isIntegrallyClosed_stalk [Smooth f] [IsIntegral P] [IsIntegral (pullback f p)]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) (z : ↥(pullback f p)) :
    IsIntegrallyClosed ((pullback f p).presheaf.stalk z) := by
  have hP : ∀ U : P.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(P, U) := fun U hU =>
    AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk hn U hU
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
  haveI : Nonempty U := ⟨⟨z, hzU⟩⟩
  haveI : IsDomain Γ(pullback f p, U) := IsIntegral.component_integral U
  haveI : IsIntegrallyClosed Γ(pullback f p, U) :=
    AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
      (pullback.snd f p) hP U hU
  let _ := (pullback f p).presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  have := hU.isLocalization_stalk ⟨z, hzU⟩
  exact isIntegrallyClosed_of_isLocalization ((pullback f p).presheaf.stalk z)
    (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

theorem valuationRing_stalk [Smooth f] [IsIntegral P] [LocallyOfFiniteType p]
    [IsIntegral (pullback f p)]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) (z : ↥(pullback f p))
    (hz : ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1) :
    ValuationRing ((pullback f p).presheaf.stalk z) := by
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian (pullback f p) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f p)
  haveI := isIntegrallyClosed_stalk hn z
  exact valuationRing_of_ringKrullDim_le_one _ hz

end Structure

section Assembly

theorem exists_partialAction (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f) :
    ∃ a : PartialAction k f p, a.Compatible L V ι hι ∧ a.Maximal ∧
      ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom := by
  haveI : GeometricallyIrreducible f := geometricallyIrreducible L
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsReduced (pullback f p) := isReduced_pullback
  haveI : IrreducibleSpace ↥(pullback f p) := inferInstance
  haveI : IsIntegral (pullback f p) := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : P.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  refine ⟨action L ι hι, compatible L ι hι, maximal L ι hι, fun z hz => ?_⟩
  rw [action_dom]
  exact Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
    (pullback.snd f p ≫ p) p (valuativeCriterion_existence (p := p)) (chart L ι hι)
    (hom₀_comp L ι hι) z (valuationRing_stalk hn z hz)

end Assembly

end InducedOperation
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian.PartialAction.InducedOperation"

end PartialAction
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian.PartialAction.InducedOperation P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian.PartialAction"

end GoodReductionJacobian
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian.PartialAction.InducedOperation P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian.PartialAction.InducedOperation P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.GoodReductionJacobian in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f) :
    ∃ a : PartialAction k f p, a.Compatible L V ι hι ∧ a.Maximal ∧
      ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom :=
  GoodReductionJacobian.PartialAction.InducedOperation.exists_partialAction k f L p hn V ι hι

end S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper (solution)
