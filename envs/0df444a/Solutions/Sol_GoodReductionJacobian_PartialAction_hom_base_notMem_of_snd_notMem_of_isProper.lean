-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.hom_base_notMem_of_snd_notMem_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e1300547-4320-59d9-9438-2e57d95b1103

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
p2m_open "GoodReductionJacobian"
namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "Defined liftDom liftDom_ι act act_coe modelPoint modelPoint_coe Compatible hom_comp dom hom"
p2m_open "GoodReductionJacobian.PartialAction"
namespace BdryStable

section GroupLawAux

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (e : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst e
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

theorem inv_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (e : t = t')
    (x : SchemeHomOver t f) (x' : SchemeHomOver t' f) (hx : x.1 = x'.1) :
    (L.inv t x).1 = (L.inv t' x').1 := by
  subst e
  obtain rfl : x = x' := Subtype.ext hx
  rfl

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  exact (inv_eq_of_mul_eq_one_left h).symm

theorem inv_mul_cancel_left {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    L.mul t (L.inv t x) (L.mul t x y) = y := by
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul]

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

end GroupLawAux

section Main

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)
  {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) (hτ : τ ≫ f = D.ι ≫ p)
  {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
  [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
  (a : PartialAction k f p)

include hτ hτι in
theorem j_comp : (ι ≫ D.ι) ≫ p = V.ι ≫ f := by
  rw [Category.assoc, ← hτ, ← Category.assoc, hτι]

abbrev GV : Scheme.{u} := pullback (pullback.snd f p) (ι ≫ D.ι)

abbrev tGV : GV f p D ι ⟶ Spec (CommRingCat.of k) :=
  (pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.fst f p) ≫ f

def γ₀ : SchemeHomOver (tGV f p D ι) f :=
  ⟨pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.fst f p, rfl⟩

include hτ hτι in
theorem vG₀_over : (pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ V.ι) ≫ f = tGV f p D ι := by
  have h1 : pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ (ι ≫ D.ι) =
      pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.snd f p := pullback.condition.symm
  calc (pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ V.ι) ≫ f
      = pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ (V.ι ≫ f) := Category.assoc _ _ _
    _ = pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ ((ι ≫ D.ι) ≫ p) := by rw [j_comp f p D τ hτ ι hτι]
    _ = (pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ (ι ≫ D.ι)) ≫ p := (Category.assoc _ _ _).symm
    _ = (pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ pullback.snd f p) ≫ p := by rw [h1]
    _ = pullback.fst (pullback.snd f p) (ι ≫ D.ι) ≫ (pullback.fst f p ≫ f) := by
        rw [Category.assoc, ← pullback.condition]
    _ = tGV f p D ι := (Category.assoc _ _ _).symm

def vG₀ : SchemeHomOver (tGV f p D ι) f :=
  ⟨pullback.snd (pullback.snd f p) (ι ≫ D.ι) ≫ V.ι, vG₀_over f p D τ hτ ι hτι⟩

def v₀ : SchemeHomOver (tGV f p D ι) (V.ι ≫ f) :=
  ⟨pullback.snd (pullback.snd f p) (ι ≫ D.ι), by rw [← Category.assoc]; exact vG₀_over f p D τ hτ ι hτι⟩

def m₀ : SchemeHomOver (tGV f p D ι) f := L.mul _ (γ₀ f p D ι) (vG₀ f p D τ hτ ι hτι)

abbrev W : (GV f p D ι).Opens := (m₀ f L p D τ hτ ι hτι).1 ⁻¹ᵁ V

abbrev tW : ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (W f L p D τ hτ ι hτι).ι ≫ tGV f p D ι

def γW : SchemeHomOver (tW f L p D τ hτ ι hτι) f := schemeHomOverComp (W f L p D τ hτ ι hτι).ι rfl (γ₀ f p D ι)
def vW : SchemeHomOver (tW f L p D τ hτ ι hτι) (V.ι ≫ f) := schemeHomOverComp (W f L p D τ hτ ι hτι).ι rfl (v₀ f p D τ hτ ι hτι)
def vGW : SchemeHomOver (tW f L p D τ hτ ι hτι) f := schemeHomOverComp (W f L p D τ hτ ι hτι).ι rfl (vG₀ f p D τ hτ ι hτι)

theorem range_Wι_m₀ : Set.range ((W f L p D τ hτ ι hτι).ι ≫ (m₀ f L p D τ hτ ι hτι).1) ⊆ Set.range V.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact w.2

def wW : SchemeHomOver (tW f L p D τ hτ ι hτι) (V.ι ≫ f) :=
  ⟨IsOpenImmersion.lift V.ι _ (range_Wι_m₀ f L p D τ hτ ι hτι), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, (m₀ f L p D τ hτ ι hτι).2]⟩

theorem wW_ι : (wW f L p D τ hτ ι hτι).1 ≫ V.ι = (W f L p D τ hτ ι hτι).ι ≫ (m₀ f L p D τ hτ ι hτι).1 :=
  IsOpenImmersion.lift_fac _ _ _

theorem compat_hyp :
    NeronModelInfra.schemeHomOverComp (wW f L p D τ hτ ι hτι) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul _ (γW f L p D τ hτ ι hτι)
        (NeronModelInfra.schemeHomOverComp (vW f L p D τ hτ ι hτι) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
  have e : NeronModelInfra.schemeHomOverComp (vW f L p D τ hτ ι hτι) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      vGW f L p D τ hτ ι hτι :=
    Subtype.ext (by simp [vW, vGW, v₀, vG₀])
  rw [e]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, wW_ι]
  change _ = (L.mul _ (schemeHomOverComp _ rfl (γ₀ f p D ι)) (schemeHomOverComp _ rfl (vG₀ f p D τ hτ ι hτι))).1
  rw [← L.mul_natural]
  rfl

variable (hc : a.Compatible L V (ι ≫ D.ι) (by rw [Category.assoc, ← hτ, ← Category.assoc, hτι]))

include hc in
theorem definedW : a.Defined (γW f L p D τ hτ ι hτι) (modelPoint (ι ≫ D.ι) (j_comp f p D τ hτ ι hτι) (vW f L p D τ hτ ι hτι)) :=
  (hc _ _ _ _ (compat_hyp f L p D τ hτ ι hτι)).choose

include hc in
theorem actW : a.act _ _ (definedW f L p D τ hτ ι hτι a hc) =
    modelPoint (ι ≫ D.ι) (j_comp f p D τ hτ ι hτι) (wW f L p D τ hτ ι hτι) :=
  (hc _ _ _ _ (compat_hyp f L p D τ hτ ι hτι)).choose_spec

def θd : ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens) : Scheme.{u}) ⟶ (a.dom : Scheme.{u}) :=
  a.liftDom _ _ (definedW f L p D τ hτ ι hτι a hc)

theorem θd_ι : θd f L p D τ hτ ι hτι a hc ≫ a.dom.ι = (W f L p D τ hτ ι hτι).ι ≫ pullback.fst _ _ := by
  rw [θd, liftDom_ι]
  apply pullback.hom_ext
  · erw [pullback.lift_fst]
    simp only [γW, γ₀, schemeHomOverComp_coe, Category.assoc]
  · erw [pullback.lift_snd]
    simp only [modelPoint_coe, vW, v₀, schemeHomOverComp_coe, Category.assoc]
    rw [pullback.condition]

theorem θd_hom : θd f L p D τ hτ ι hτι a hc ≫ a.hom = (wW f L p D τ hτ ι hτι).1 ≫ ι ≫ D.ι := by
  have := congrArg Subtype.val (actW f L p D τ hτ ι hτι a hc)
  simp [act_coe, modelPoint] at this
  exact this

scoped instance : IsOpenImmersion (θd f L p D τ hτ ι hτι a hc) := by
  have : IsOpenImmersion (θd f L p D τ hτ ι hτι a hc ≫ a.dom.ι) := by
    rw [θd_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ a.dom.ι

abbrev U : (a.dom : Scheme.{u}).Opens := a.hom ⁻¹ᵁ D

theorem range_θd : Set.range (θd f L p D τ hτ ι hτι a hc) ⊆ Set.range (U f p D a).ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  show a.hom (θd f L p D τ hτ ι hτι a hc w) ∈ (D : Set P)
  rw [← Scheme.Hom.comp_apply, θd_hom, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (ι _).2

def θU : ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens) : Scheme.{u}) ⟶ ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (U f p D a).ι _ (range_θd f L p D τ hτ ι hτι a hc)

theorem θU_ι : θU f L p D τ hτ ι hτι a hc ≫ (U f p D a).ι = θd f L p D τ hτ ι hτι a hc :=
  IsOpenImmersion.lift_fac _ _ _

scoped instance : IsOpenImmersion (θU f L p D τ hτ ι hτι a hc) := by
  have : IsOpenImmersion (θU f L p D τ hτ ι hτι a hc ≫ (U f p D a).ι) := by
    rw [θU_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (U f p D a).ι

abbrev tU : ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  ((U f p D a).ι ≫ a.dom.ι ≫ pullback.fst f p) ≫ f

def γU : SchemeHomOver (tU f p D a) f := ⟨(U f p D a).ι ≫ a.dom.ι ≫ pullback.fst f p, rfl⟩

theorem range_Uι_hom : Set.range ((U f p D a).ι ≫ a.hom) ⊆ Set.range D.ι := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact u.2

def hU : ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ (D : Scheme.{u}) :=
  IsOpenImmersion.lift D.ι _ (range_Uι_hom f p D a)

theorem hU_ι : hU f p D a ≫ D.ι = (U f p D a).ι ≫ a.hom := IsOpenImmersion.lift_fac _ _ _

include hτ in
theorem gU_over : (hU f p D a ≫ τ) ≫ f = tU f p D a := by
  calc (hU f p D a ≫ τ) ≫ f = hU f p D a ≫ (τ ≫ f) := Category.assoc _ _ _
    _ = hU f p D a ≫ (D.ι ≫ p) := by rw [hτ]
    _ = (hU f p D a ≫ D.ι) ≫ p := (Category.assoc _ _ _).symm
    _ = ((U f p D a).ι ≫ a.hom) ≫ p := by rw [hU_ι]
    _ = (U f p D a).ι ≫ (a.hom ≫ p) := Category.assoc _ _ _
    _ = (U f p D a).ι ≫ (a.dom.ι ≫ pullback.snd f p ≫ p) := by rw [a.hom_comp]
    _ = (U f p D a).ι ≫ (a.dom.ι ≫ (pullback.fst f p ≫ f)) := by rw [← pullback.condition]
    _ = tU f p D a := by simp only [tU, Category.assoc]

def gU : SchemeHomOver (tU f p D a) f := ⟨hU f p D a ≫ τ, gU_over f p D τ hτ a⟩

def βU : SchemeHomOver (tU f p D a) f := L.mul _ (L.inv _ (γU f p D a)) (gU f p D τ hτ a)

def ψ : ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ pullback p f :=
  pullback.lift ((U f p D a).ι ≫ a.dom.ι ≫ pullback.snd f p) (βU f L p D τ hτ a).1 (by
    rw [(βU f L p D τ hτ a).2, Category.assoc, Category.assoc, ← pullback.condition]
    simp only [tU, Category.assoc])

def Γ : (D : Scheme.{u}) ⟶ pullback p f := pullback.lift D.ι τ hτ.symm

theorem isClosed_range_Γ [IsSeparated p] [IsProper τ] : IsClosed (Set.range (Γ f p D τ hτ)) := by
  haveI : IsProper (Γ f p D τ hτ ≫ pullback.snd p f) := by
    rw [Γ]; erw [pullback.lift_snd]; infer_instance
  haveI : IsProper (Γ f p D τ hτ) := IsProper.of_comp (Γ f p D τ hτ) (pullback.snd p f)
  exact (Γ f p D τ hτ).isClosedMap.isClosed_range

include hτι in
theorem θU_hU : θU f L p D τ hτ ι hτι a hc ≫ hU f p D a = (wW f L p D τ hτ ι hτι).1 ≫ ι := by
  rw [← cancel_mono D.ι, Category.assoc, hU_ι, ← Category.assoc, θU_ι, θd_hom, Category.assoc]

include hτι in
theorem θU_βU : θU f L p D τ hτ ι hτι a hc ≫ (βU f L p D τ hτ a).1 =
    (vW f L p D τ hτ ι hτι).1 ≫ V.ι := by

  have et : θU f L p D τ hτ ι hτι a hc ≫ tU f p D a = tW f L p D τ hτ ι hτι := by
    simp only [tU, tW, tGV, ← Category.assoc]
    rw [θU_ι, θd_ι]
  let X' : SchemeHomOver (θU f L p D τ hτ ι hτι a hc ≫ tU f p D a) f :=
    schemeHomOverComp _ rfl (γU f p D a)
  let Y' : SchemeHomOver (θU f L p D τ hτ ι hτι a hc ≫ tU f p D a) f :=
    schemeHomOverComp _ rfl (gU f p D τ hτ a)
  let Z' : SchemeHomOver (θU f L p D τ hτ ι hτι a hc ≫ tU f p D a) f :=
    ⟨(vW f L p D τ hτ ι hτι).1 ≫ V.ι, by rw [et]; exact (vGW f L p D τ hτ ι hτι).2⟩
  have hX : X'.1 = (γW f L p D τ hτ ι hτι).1 := by
    simp only [X', schemeHomOverComp_coe, γU, γW, γ₀, ← Category.assoc, θU_ι, θd_ι]
  have hY : Y'.1 = (L.mul _ X' Z').1 := by
    have h1 : Y'.1 = (L.mul _ (γW f L p D τ hτ ι hτι) (vGW f L p D τ hτ ι hτι)).1 := by
      simp only [Y', schemeHomOverComp_coe, gU]
      rw [← Category.assoc, θU_hU, Category.assoc, hτι, wW_ι]
      change _ = (L.mul _ (schemeHomOverComp _ rfl (γ₀ f p D ι)) (schemeHomOverComp _ rfl (vG₀ f p D τ hτ ι hτι))).1
      rw [← L.mul_natural]; rfl
    rw [h1]
    exact mul_val_congr L et.symm _ _ _ _ hX.symm rfl
  have key : schemeHomOverComp _ rfl (βU f L p D τ hτ a) = Z' := by
    rw [βU, L.mul_natural, inv_natural]
    change L.mul _ (L.inv _ X') Y' = Z'
    rw [Subtype.ext hY, inv_mul_cancel_left]
  exact congrArg Subtype.val key

include hτι in
theorem θU_ψ : θU f L p D τ hτ ι hτι a hc ≫ ψ f L p D τ hτ a =
    ((vW f L p D τ hτ ι hτι).1 ≫ ι) ≫ Γ f p D τ hτ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ψ, Category.assoc, Γ]
    erw [pullback.lift_fst, pullback.lift_fst]
    rw [← Category.assoc, θU_ι, ← Category.assoc, θd_ι, Category.assoc, pullback.condition]
    simp only [vW, v₀, schemeHomOverComp_coe, Category.assoc]
  · rw [Category.assoc, ψ, Category.assoc, Γ]
    erw [pullback.lift_snd, pullback.lift_snd]
    rw [θU_βU, Category.assoc, hτι]

include hτ hτι in

def σX : (V : Scheme.{u}) ⟶ pullback f p :=
  pullback.lift (L.one (V.ι ≫ f)).1 (ι ≫ D.ι) (by rw [(L.one (V.ι ≫ f)).2, j_comp f p D τ hτ ι hτι])

def σ : (V : Scheme.{u}) ⟶ GV f p D ι :=
  pullback.lift (σX f L p D τ hτ ι hτι) (𝟙 _) (by
    rw [Category.id_comp]; exact pullback.lift_snd _ _ _)

theorem σ_m₀ : σ f L p D τ hτ ι hτι ≫ (m₀ f L p D τ hτ ι hτι).1 = V.ι := by
  have et : σ f L p D τ hτ ι hτι ≫ tGV f p D ι = V.ι ≫ f := by
    simp only [tGV, σ, σX, ← Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst]
    exact (L.one (V.ι ≫ f)).2
  have h1 : (schemeHomOverComp (σ f L p D τ hτ ι hτι) rfl (m₀ f L p D τ hτ ι hτι)).1 =
      (L.mul _ (L.one (V.ι ≫ f)) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)).1 := by
    rw [m₀, L.mul_natural]
    apply mul_val_congr L et
    · simp only [schemeHomOverComp_coe, γ₀, σ, σX]
      erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · simp only [schemeHomOverComp_coe, vG₀, σ]
      erw [pullback.lift_snd_assoc, Category.id_comp]
  rw [L.one_mul] at h1
  exact h1

scoped instance [Nonempty (V : Scheme.{u})] : Nonempty ((W f L p D τ hτ ι hτι : (GV f p D ι).Opens) : Scheme.{u}) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
  refine ⟨⟨σ f L p D τ hτ ι hτι v, ?_⟩⟩
  show (m₀ f L p D τ hτ ι hτι).1 (σ f L p D τ hτ ι hτι v) ∈ (V : Set G)
  rw [← Scheme.Hom.comp_apply, σ_m₀]
  exact v.2

include L hτ hτι hc in
theorem snd_mem [IsAlgClosed k] [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P] [IsProper τ] [Nonempty (V : Scheme.{u})]
    (z : ↥(a.dom : Scheme.{u})) (hz : a.hom.base z ∈ (D : Set P)) :
    (pullback.snd f p).base (a.dom.ι.base z) ∈ (D : Set P) := by

  haveI : GeometricallyIrreducible f := geometricallyIrreducible L
  haveI : IrreducibleSpace ↥(pullback f p) := inferInstance
  haveI : Nonempty ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) := ⟨⟨z, hz⟩⟩
  haveI : Nonempty (a.dom : Scheme.{u}) := ⟨z⟩
  haveI : IrreducibleSpace (a.dom : Scheme.{u}) := a.dom.ι.isOpenEmbedding.irreducibleSpace
  haveI : IrreducibleSpace ((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) :=
    (U f p D a).ι.isOpenEmbedding.irreducibleSpace

  let S : Set ↥((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) :=
    (ψ f L p D τ hτ a).base ⁻¹' Set.range (Γ f p D τ hτ)
  have hS : IsClosed S := (isClosed_range_Γ f p D τ hτ).preimage (ψ f L p D τ hτ a).continuous
  have hsub : Set.range (θU f L p D τ hτ ι hτι a hc) ⊆ S := by
    rintro _ ⟨w, rfl⟩
    show (ψ f L p D τ hτ a) (θU f L p D τ hτ ι hτι a hc w) ∈ Set.range (Γ f p D τ hτ)
    rw [← Scheme.Hom.comp_apply, θU_ψ, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hopen : IsOpen (Set.range (θU f L p D τ hτ ι hτι a hc)) :=
    (θU f L p D τ hτ ι hτι a hc).isOpenEmbedding.isOpen_range
  have hne : (Set.range (θU f L p D τ hτ ι hτι a hc)).Nonempty := Set.range_nonempty _
  have hdense : Dense (Set.range (θU f L p D τ hτ ι hτι a hc)) := hopen.dense hne
  have hSuniv : S = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_eq]
    exact hS.closure_subset_iff.mpr hsub
  have hzS : (⟨z, hz⟩ : ↥((U f p D a : (a.dom : Scheme.{u}).Opens) : Scheme.{u})) ∈ S := by
    rw [hSuniv]; trivial
  obtain ⟨d, hd⟩ := hzS
  have h1 := congrArg (pullback.fst p f).base hd
  change ((Γ f p D τ hτ) ≫ pullback.fst p f) d = ((ψ f L p D τ hτ a) ≫ pullback.fst p f) ⟨z, hz⟩ at h1
  rw [Γ, ψ] at h1
  erw [pullback.lift_fst, pullback.lift_fst] at h1
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  have hz' : (U f p D a).ι ⟨z, hz⟩ = z := rfl
  rw [hz'] at h1
  rw [← h1, Scheme.Opens.ι_apply]
  exact d.2

end Main

end BdryStable
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian.PartialAction.BdryStable"
end PartialAction
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian.PartialAction.BdryStable P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian.PartialAction"
end GoodReductionJacobian
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian.PartialAction.BdryStable P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian.PartialAction.BdryStable P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.GoodReductionJacobian"

open GoodReductionJacobian.PartialAction.BdryStable in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
    (a : PartialAction k f p)
    (hc : a.Compatible L V (ι ≫ D.ι) (by rw [Category.assoc, ← hτ, ← Category.assoc, hτι]))
    (z : ↥(a.dom : Scheme.{u})) (hz : (pullback.snd f p).base (a.dom.ι.base z) ∉ (D : Set P)) :
    a.hom.base z ∉ (D : Set P) :=
  fun hmem => hz (snd_mem f L p D τ hτ ι hτι a hc z hmem)

end S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper (solution)
