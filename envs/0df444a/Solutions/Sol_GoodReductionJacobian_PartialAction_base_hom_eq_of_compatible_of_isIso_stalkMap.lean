-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.base_hom_eq_of_compatible_of_isIso_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/64d7431d-97d8-5ce5-9e82-53c01cb2a22b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
p2m_open "GoodReductionJacobian"
namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "Defined liftDom liftDom_ι act act_coe modelPoint modelPoint_coe Compatible hom_comp dom hom"
p2m_open "GoodReductionJacobian.PartialAction"
namespace OpTransport

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

section Chart

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)
  {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  {V : G.Opens} (j : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion j] (hj : j ≫ p = V.ι ≫ f)
  (a : PartialAction k f p)

abbrev GV : Scheme.{u} := pullback (pullback.snd f p) j

abbrev tGV : GV f p j ⟶ Spec (CommRingCat.of k) :=
  (pullback.fst (pullback.snd f p) j ≫ pullback.fst f p) ≫ f

def γ₀ : SchemeHomOver (tGV f p j) f :=
  ⟨pullback.fst (pullback.snd f p) j ≫ pullback.fst f p, rfl⟩

include hj in
theorem vG₀_over : (pullback.snd (pullback.snd f p) j ≫ V.ι) ≫ f = tGV f p j := by
  have h1 : pullback.snd (pullback.snd f p) j ≫ j =
      pullback.fst (pullback.snd f p) j ≫ pullback.snd f p := pullback.condition.symm
  calc (pullback.snd (pullback.snd f p) j ≫ V.ι) ≫ f
      = pullback.snd (pullback.snd f p) j ≫ (V.ι ≫ f) := Category.assoc _ _ _
    _ = pullback.snd (pullback.snd f p) j ≫ (j ≫ p) := by rw [hj]
    _ = (pullback.snd (pullback.snd f p) j ≫ j) ≫ p := (Category.assoc _ _ _).symm
    _ = (pullback.fst (pullback.snd f p) j ≫ pullback.snd f p) ≫ p := by rw [h1]
    _ = pullback.fst (pullback.snd f p) j ≫ (pullback.fst f p ≫ f) := by
        rw [Category.assoc, ← pullback.condition]
    _ = tGV f p j := (Category.assoc _ _ _).symm

def vG₀ : SchemeHomOver (tGV f p j) f :=
  ⟨pullback.snd (pullback.snd f p) j ≫ V.ι, vG₀_over f p j hj⟩

def v₀ : SchemeHomOver (tGV f p j) (V.ι ≫ f) :=
  ⟨pullback.snd (pullback.snd f p) j, by rw [← Category.assoc]; exact vG₀_over f p j hj⟩

def m₀ : SchemeHomOver (tGV f p j) f := L.mul _ (γ₀ f p j) (vG₀ f p j hj)

abbrev Wch : (GV f p j).Opens := (m₀ f L p j hj).1 ⁻¹ᵁ V

abbrev tWch : ((Wch f L p j hj : (GV f p j).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (Wch f L p j hj).ι ≫ tGV f p j

def γW : SchemeHomOver (tWch f L p j hj) f := schemeHomOverComp (Wch f L p j hj).ι rfl (γ₀ f p j)
def vW : SchemeHomOver (tWch f L p j hj) (V.ι ≫ f) := schemeHomOverComp (Wch f L p j hj).ι rfl (v₀ f p j hj)
def vGW : SchemeHomOver (tWch f L p j hj) f := schemeHomOverComp (Wch f L p j hj).ι rfl (vG₀ f p j hj)

theorem range_Wι_m₀ : Set.range ((Wch f L p j hj).ι ≫ (m₀ f L p j hj).1) ⊆ Set.range V.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact w.2

def wW : SchemeHomOver (tWch f L p j hj) (V.ι ≫ f) :=
  ⟨IsOpenImmersion.lift V.ι _ (range_Wι_m₀ f L p j hj), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, (m₀ f L p j hj).2]⟩

theorem wW_ι : (wW f L p j hj).1 ≫ V.ι = (Wch f L p j hj).ι ≫ (m₀ f L p j hj).1 :=
  IsOpenImmersion.lift_fac _ _ _

theorem compat_hyp :
    NeronModelInfra.schemeHomOverComp (wW f L p j hj) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul _ (γW f L p j hj)
        (NeronModelInfra.schemeHomOverComp (vW f L p j hj) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
  have e : NeronModelInfra.schemeHomOverComp (vW f L p j hj) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      vGW f L p j hj :=
    Subtype.ext (by simp [vW, vGW, v₀, vG₀])
  rw [e]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, wW_ι]
  change _ = (L.mul _ (schemeHomOverComp _ rfl (γ₀ f p j)) (schemeHomOverComp _ rfl (vG₀ f p j hj))).1
  rw [← L.mul_natural]
  rfl

variable (hc : a.Compatible L V j hj)

include hc in
theorem definedW : a.Defined (γW f L p j hj) (modelPoint j hj (vW f L p j hj)) :=
  (hc _ _ _ _ (compat_hyp f L p j hj)).choose

include hc in
theorem actW : a.act _ _ (definedW f L p j hj a hc) = modelPoint j hj (wW f L p j hj) :=
  (hc _ _ _ _ (compat_hyp f L p j hj)).choose_spec

def θd : ((Wch f L p j hj : (GV f p j).Opens) : Scheme.{u}) ⟶ (a.dom : Scheme.{u}) :=
  a.liftDom _ _ (definedW f L p j hj a hc)

theorem θd_ι : θd f L p j hj a hc ≫ a.dom.ι = (Wch f L p j hj).ι ≫ pullback.fst _ _ := by
  rw [θd, liftDom_ι]
  apply pullback.hom_ext
  · erw [pullback.lift_fst]
    simp only [γW, γ₀, schemeHomOverComp_coe, Category.assoc]
  · erw [pullback.lift_snd]
    simp only [modelPoint_coe, vW, v₀, schemeHomOverComp_coe, Category.assoc]
    rw [pullback.condition]

theorem θd_hom : θd f L p j hj a hc ≫ a.hom = (wW f L p j hj).1 ≫ j := by
  have := congrArg Subtype.val (actW f L p j hj a hc)
  simp [act_coe, modelPoint] at this
  exact this

scoped instance : IsOpenImmersion (θd f L p j hj a hc) := by
  have : IsOpenImmersion (θd f L p j hj a hc ≫ a.dom.ι) := by
    rw [θd_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ a.dom.ι

def σX : (V : Scheme.{u}) ⟶ pullback f p :=
  pullback.lift (L.one (V.ι ≫ f)).1 j (by rw [(L.one (V.ι ≫ f)).2, hj])

def σ : (V : Scheme.{u}) ⟶ GV f p j :=
  pullback.lift (σX f L p j hj) (𝟙 _) (by
    rw [Category.id_comp]; exact pullback.lift_snd _ _ _)

theorem σ_m₀ : σ f L p j hj ≫ (m₀ f L p j hj).1 = V.ι := by
  have et : σ f L p j hj ≫ tGV f p j = V.ι ≫ f := by
    simp only [tGV, σ, σX, ← Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst]
    exact (L.one (V.ι ≫ f)).2
  have h1 : (schemeHomOverComp (σ f L p j hj) rfl (m₀ f L p j hj)).1 =
      (L.mul _ (L.one (V.ι ≫ f)) (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)).1 := by
    rw [m₀, L.mul_natural]
    apply mul_val_congr L et
    · simp only [schemeHomOverComp_coe, γ₀, σ, σX]
      erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · simp only [schemeHomOverComp_coe, vG₀, σ]
      erw [pullback.lift_snd_assoc, Category.id_comp]
  rw [L.one_mul] at h1
  exact h1

scoped instance [Nonempty (V : Scheme.{u})] : Nonempty ((Wch f L p j hj : (GV f p j).Opens) : Scheme.{u}) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
  refine ⟨⟨σ f L p j hj v, ?_⟩⟩
  show (m₀ f L p j hj).1 (σ f L p j hj v) ∈ (V : Set G)
  rw [← Scheme.Hom.comp_apply, σ_m₀]
  exact v.2

end Chart

section Generic

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

theorem act_congr (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {γ γ' : SchemeHomOver t f} {x x' : SchemeHomOver t p} (eγ : γ = γ') (ex : x = x')
    (hd : a.Defined γ x) (hd' : a.Defined γ' x') : a.act γ x hd = a.act γ' x' hd' := by
  subst eγ ex; rfl

theorem compatible_restrict (L : RelativeGroupLaw k f) (a : PartialAction k f p)
    {V V' : G.Opens} (hV' : V' ≤ V) (ι₀ : (V : Scheme.{u}) ⟶ P) (hι₀ : ι₀ ≫ p = V.ι ≫ f)
    (hc : a.Compatible L V ι₀ hι₀)
    (hj : (G.homOfLE hV' ≫ ι₀) ≫ p = V'.ι ≫ f) :
    a.Compatible L V' (G.homOfLE hV' ≫ ι₀) hj := by
  intro T t γ v w hvw
  let vV : SchemeHomOver t (V.ι ≫ f) := ⟨v.1 ≫ G.homOfLE hV', by
    rw [Category.assoc, ← Category.assoc (G.homOfLE hV'), Scheme.homOfLE_ι]; exact v.2⟩
  let wV : SchemeHomOver t (V.ι ≫ f) := ⟨w.1 ≫ G.homOfLE hV', by
    rw [Category.assoc, ← Category.assoc (G.homOfLE hV'), Scheme.homOfLE_ι]; exact w.2⟩
  have hvw' : NeronModelInfra.schemeHomOverComp wV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul t γ (NeronModelInfra.schemeHomOverComp vV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
    have e1 : NeronModelInfra.schemeHomOverComp wV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
        NeronModelInfra.schemeHomOverComp w (⟨V'.ι, rfl⟩ : SchemeHomOver (V'.ι ≫ f) f) :=
      Subtype.ext (by simp [vV, wV])
    have e2 : NeronModelInfra.schemeHomOverComp vV (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
        NeronModelInfra.schemeHomOverComp v (⟨V'.ι, rfl⟩ : SchemeHomOver (V'.ι ≫ f) f) :=
      Subtype.ext (by simp [vV, wV])
    rw [e1, e2]; exact hvw
  obtain ⟨hd, hact⟩ := hc t γ vV wV hvw'
  have ev : modelPoint ι₀ hι₀ vV = modelPoint (G.homOfLE hV' ≫ ι₀) hj v := Subtype.ext (by simp [vV])
  have ew : modelPoint ι₀ hι₀ wV = modelPoint (G.homOfLE hV' ≫ ι₀) hj w := Subtype.ext (by simp [wV])
  rw [ev] at hd
  refine ⟨hd, ?_⟩
  rw [← ew, ← hact]
  exact act_congr a rfl ev.symm _ _

theorem eq_of_comp_eq_of_isIso_restrict {T P'' : Scheme.{u}} (β : P'' ⟶ P) (W : P.Opens) [IsIso (β ∣_ W)]
    (m₁ m₂ : T ⟶ P'') (h : m₁ ≫ β = m₂ ≫ β) (hW : Set.range (m₁ ≫ β) ⊆ (W : Set P)) : m₁ = m₂ := by
  have h₁ : Set.range m₁ ⊆ Set.range (β ⁻¹ᵁ W).ι := by
    rintro _ ⟨t, rfl⟩; rw [Scheme.Opens.range_ι]
    show β (m₁ t) ∈ (W : Set P)
    rw [← Scheme.Hom.comp_apply]; exact hW ⟨t, rfl⟩
  have h₂ : Set.range m₂ ⊆ Set.range (β ⁻¹ᵁ W).ι := by
    rintro _ ⟨t, rfl⟩; rw [Scheme.Opens.range_ι]
    show β (m₂ t) ∈ (W : Set P)
    rw [← Scheme.Hom.comp_apply, ← h]; exact hW ⟨t, rfl⟩
  let n₁ := IsOpenImmersion.lift (β ⁻¹ᵁ W).ι m₁ h₁
  let n₂ := IsOpenImmersion.lift (β ⁻¹ᵁ W).ι m₂ h₂
  have hn₁ : n₁ ≫ (β ⁻¹ᵁ W).ι = m₁ := IsOpenImmersion.lift_fac _ _ _
  have hn₂ : n₂ ≫ (β ⁻¹ᵁ W).ι = m₂ := IsOpenImmersion.lift_fac _ _ _
  have : n₁ ≫ (β ∣_ W) = n₂ ≫ (β ∣_ W) := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, hn₁,
      ← Category.assoc, hn₂, h]
  rw [cancel_mono] at this
  rw [← hn₁, ← hn₂, this]

end Generic

end OpTransport
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction.OpTransport"
end PartialAction
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction.OpTransport P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction"
end GoodReductionJacobian
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction.OpTransport P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction.OpTransport P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian"

open _root_.GoodReductionJacobian.PartialAction _root_.P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap.GoodReductionJacobian.PartialAction GoodReductionJacobian.PartialAction.OpTransport in
set_option maxHeartbeats 1600000 in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι₀ : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι₀]
    (hι₀ : ι₀ ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι₀ hι₀)
    (w : P) (ζ : ↥(pullback f p)) (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w})
    {P'' : Scheme.{u}} (p'' : P'' ⟶ Spec (CommRingCat.of k)) [IsIntegral P''] [IsSeparated p'']
    [LocallyOfFiniteType p'']
    (β : P'' ⟶ P) (hβ : β ≫ p = p'') (W : P.Opens) [IsIso (β ∣_ W)]
    (U' : (pullback f p).Opens) (hU' : U' ≤ a.dom) (hζU' : ζ ∈ U')
    (α' : (U' : Scheme.{u}) ⟶ P'') (hα' : α' ≫ β = (pullback f p).homOfLE hU' ≫ a.hom)
    {P' : Scheme.{u}} [IsIntegral P'] (ν : P' ⟶ P'') [IsIso ((ν ≫ β) ∣_ W)]
    (V' : G.Opens) [Nonempty (V' : Scheme.{u})] (hV' : V' ≤ V)
    (hV'W : Set.range (G.homOfLE hV' ≫ ι₀).base ⊆ (W : Set P))
    (ι' : (V' : Scheme.{u}) ⟶ P') [IsOpenImmersion ι'] (hι'ι₀ : ι' ≫ ν ≫ β = G.homOfLE hV' ≫ ι₀)
    (hι' : ι' ≫ (ν ≫ β) ≫ p = V'.ι ≫ f)
    (a' : PartialAction k f ((ν ≫ β) ≫ p)) (hc' : a'.Compatible L V' ι' hι')
    (w' : P') (hπw' : (ν ≫ β).base w' = w) (hiso : IsIso ((ν ≫ β).stalkMap w'))
    (ζ' : ↥(pullback f ((ν ≫ β) ≫ p))) (hζ' : ζ' ∈ a'.dom)
    (hζ'cl : closure ({ζ'} : Set ↥(pullback f ((ν ≫ β) ≫ p))) =
      (pullback.snd f ((ν ≫ β) ≫ p)).base ⁻¹' closure {w'}) :
    ν.base (a'.hom.base ⟨ζ', hζ'⟩) = α'.base ⟨ζ, hζU'⟩ := by

  obtain ⟨PiM, hPi₁, hPi₂⟩ : ∃ PiM : pullback f ((ν ≫ β) ≫ p) ⟶ pullback f p,
      PiM ≫ pullback.fst f p = pullback.fst _ _ ∧ PiM ≫ pullback.snd f p = pullback.snd _ _ ≫ (ν ≫ β) :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ (ν ≫ β)) (by rw [pullback.condition]; simp only [Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  haveI : GeometricallyIrreducible f := geometricallyIrreducible L
  haveI : IrreducibleSpace ↥(pullback f p) := inferInstance
  haveI : IrreducibleSpace ↥(pullback f ((ν ≫ β) ≫ p)) := inferInstance

  have hPiζ : PiM ζ' = ζ := by
    have hcl : closure ({PiM ζ'} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w} := by
      apply subset_antisymm
      · apply closure_minimal _ ((isClosed_closure).preimage (pullback.snd f p).continuous)
        rintro _ rfl
        show (pullback.snd f p) (PiM ζ') ∈ closure {w}
        rw [← Scheme.Hom.comp_apply, hPi₂, Scheme.Hom.comp_apply, ← hπw']
        have h1 : (pullback.snd f ((ν ≫ β) ≫ p)) ζ' ∈ closure {w'} := by
          rw [← Set.mem_preimage, ← hζ'cl]; exact subset_closure rfl
        have h2 := image_closure_subset_closure_image (ν ≫ β).continuous ⟨_, h1, rfl⟩
        rwa [Set.image_singleton] at h2
      · intro x hx
        rw [mem_closure_iff]
        intro O hO hxO
        have hsO : IsOpen ((pullback.snd f p).base '' O) := (pullback.snd f p).isOpenMap O hO
        have hw : w ∈ (pullback.snd f p).base '' O := by
          have hx' : (pullback.snd f p) x ∈ closure {w} := hx
          rw [mem_closure_iff] at hx'
          obtain ⟨y, hy, hy'⟩ := hx' _ hsO ⟨x, hxO, rfl⟩
          rw [Set.mem_singleton_iff] at hy'
          rw [← hy']; exact hy
        obtain ⟨x₀, hx₀O, hx₀⟩ := hw
        obtain ⟨z₀, hz₀₁, hz₀₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f p) (g := ν ≫ β) x₀ w'
          (by rw [hx₀]; exact hπw'.symm)
        have he : (pullbackLeftPullbackSndIso f p (ν ≫ β)).hom ≫ PiM = pullback.fst _ _ := by
          apply pullback.hom_ext
          · rw [Category.assoc, hPi₁, pullbackLeftPullbackSndIso_hom_fst]
          · rw [Category.assoc, hPi₂, ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.condition]
        have hz' : (pullbackLeftPullbackSndIso f p (ν ≫ β)).hom z₀ ∈ closure ({ζ'} : Set _) := by
          rw [hζ'cl, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullbackLeftPullbackSndIso_hom_snd, hz₀₂]
          exact subset_closure rfl
        rw [mem_closure_iff] at hz'
        obtain ⟨y, hy, hy'⟩ := hz' (PiM.base ⁻¹' O) (hO.preimage PiM.continuous) (by
          show PiM ((pullbackLeftPullbackSndIso f p (ν ≫ β)).hom z₀) ∈ O
          rw [← Scheme.Hom.comp_apply, he, hz₀₁]; exact hx₀O)
        rw [Set.mem_singleton_iff] at hy'
        rw [hy'] at hy
        exact ⟨_, hy, rfl⟩
    exact (inseparable_iff_closure_eq.mpr (hcl.trans hζcl.symm)).eq

  let D' : (pullback f ((ν ≫ β) ≫ p)).Opens := a'.dom ⊓ PiM ⁻¹ᵁ U'
  have hζ'D : ζ' ∈ D' := ⟨hζ', by show PiM ζ' ∈ (U' : Set _); rw [hPiζ]; exact hζU'⟩
  haveI : Nonempty (D' : Scheme.{u}) := ⟨⟨ζ', hζ'D⟩⟩
  haveI : IrreducibleSpace (D' : Scheme.{u}) := D'.ι.isOpenEmbedding.irreducibleSpace
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : (D' : Scheme.{u}) ⟶ (a'.dom : Scheme.{u}), e₁ ≫ a'.dom.ι = D'.ι :=
    ⟨(pullback f ((ν ≫ β) ≫ p)).homOfLE inf_le_left, Scheme.homOfLE_ι _ _⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : (D' : Scheme.{u}) ⟶ (U' : Scheme.{u}), lam ≫ U'.ι = D'.ι ≫ PiM :=
    ⟨IsOpenImmersion.lift U'.ι (D'.ι ≫ PiM) (by
      rintro _ ⟨d, rfl⟩; rw [Scheme.Opens.range_ι]; exact d.2.2), IsOpenImmersion.lift_fac _ _ _⟩
  let φ₁ : (D' : Scheme.{u}) ⟶ P'' := e₁ ≫ a'.hom ≫ ν
  let φ₂ : (D' : Scheme.{u}) ⟶ P'' := lam ≫ α'
  have hc1 : pullback.snd f ((ν ≫ β) ≫ p) ≫ (ν ≫ β) ≫ p = pullback.fst f ((ν ≫ β) ≫ p) ≫ f :=
    pullback.condition.symm
  have hc2 : pullback.snd f p ≫ p = pullback.fst f p ≫ f := pullback.condition.symm
  have hφ₁ : φ₁ ≫ p'' = D'.ι ≫ pullback.fst _ _ ≫ f := by
    have h3 : a'.hom ≫ ν ≫ β ≫ p = a'.dom.ι ≫ pullback.fst _ _ ≫ f := by
      rw [show ν ≫ β ≫ p = (ν ≫ β) ≫ p by simp only [Category.assoc], a'.hom_comp, hc1]
    simp only [φ₁, Category.assoc]
    rw [← hβ, h3, ← Category.assoc e₁, he₁]
  have hφ₂ : φ₂ ≫ p'' = D'.ι ≫ pullback.fst _ _ ≫ f := by
    simp only [φ₂, Category.assoc]
    calc lam ≫ α' ≫ p'' = lam ≫ α' ≫ β ≫ p := by rw [← hβ]
      _ = lam ≫ ((pullback f p).homOfLE hU' ≫ a.hom) ≫ p := by rw [← Category.assoc α', hα']
      _ = lam ≫ (pullback f p).homOfLE hU' ≫ a.dom.ι ≫ pullback.snd f p ≫ p := by
          rw [Category.assoc ((pullback f p).homOfLE hU') a.hom p, a.hom_comp]
      _ = lam ≫ U'.ι ≫ pullback.snd f p ≫ p := by
          rw [← Category.assoc ((pullback f p).homOfLE hU'), Scheme.homOfLE_ι]
      _ = (lam ≫ U'.ι) ≫ pullback.fst f p ≫ f := by rw [hc2]; exact (Category.assoc lam U'.ι _).symm
      _ = (D'.ι ≫ PiM) ≫ pullback.fst f p ≫ f := by rw [hlam]
      _ = D'.ι ≫ pullback.fst _ _ ≫ f := by
          rw [Category.assoc D'.ι PiM, ← Category.assoc PiM (pullback.fst f p) f, hPi₁]
  let ψ : (D' : Scheme.{u}) ⟶ pullback p'' p'' := pullback.lift φ₁ φ₂ (hφ₁.trans hφ₂.symm)
  have hS : IsClosed (ψ.base ⁻¹' Set.range (pullback.diagonal p'')) :=
    (pullback.diagonal p'').isClosedEmbedding.isClosed_range.preimage ψ.continuous

  let Wc := Wch f L ((ν ≫ β) ≫ p) ι' hι'
  let θ' := θd f L ((ν ≫ β) ≫ p) ι' hι' a' hc'
  have hθ'ι := θd_ι f L ((ν ≫ β) ≫ p) ι' hι' a' hc'
  have hθ'hom := θd_hom f L ((ν ≫ β) ≫ p) ι' hι' a' hc'

  have hjV : (G.homOfLE hV' ≫ ι₀) ≫ p = V'.ι ≫ f := by
    rw [Category.assoc, hι₀, ← Category.assoc, Scheme.homOfLE_ι]
  have hcV : a.Compatible L V' (G.homOfLE hV' ≫ ι₀) hjV := compatible_restrict L a hV' ι₀ hι₀ hc hjV
  obtain ⟨hd₂, hact₂⟩ := hcV (tWch f L ((ν ≫ β) ≫ p) ι' hι') (γW f L ((ν ≫ β) ≫ p) ι' hι') (vW f L ((ν ≫ β) ≫ p) ι' hι')
    (wW f L ((ν ≫ β) ≫ p) ι' hι') (compat_hyp f L ((ν ≫ β) ≫ p) ι' hι')
  let θ₂ := a.liftDom _ _ hd₂
  have hθ₂ι : θ₂ ≫ a.dom.ι = (Wc.ι ≫ pullback.fst _ _) ≫ PiM := by
    rw [liftDom_ι]
    apply pullback.hom_ext
    · erw [pullback.lift_fst]
      rw [Category.assoc _ PiM (pullback.fst f p), hPi₁]
      simp only [GoodReductionJacobian.PartialAction.OpTransport.γW, GoodReductionJacobian.PartialAction.OpTransport.γ₀, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
      rfl
    · erw [pullback.lift_snd]
      rw [Category.assoc _ PiM (pullback.snd f p), hPi₂, modelPoint_coe]
      simp only [GoodReductionJacobian.PartialAction.OpTransport.vW, GoodReductionJacobian.PartialAction.OpTransport.v₀, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
      rw [← hι'ι₀, pullback.condition_assoc]
  have hθ₂hom : θ₂ ≫ a.hom = (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ≫ G.homOfLE hV' ≫ ι₀ := by
    have := congrArg Subtype.val hact₂
    simp [act_coe, modelPoint] at this
    exact this

  let W₀ : Wc.toScheme.Opens := ((Wc.ι ≫ pullback.fst _ _) ≫ PiM) ⁻¹ᵁ U'

  have hW₀ne : Nonempty (W₀ : Scheme.{u}) := by
    have h1 : IsOpen (Set.range (Wc.ι ≫ pullback.fst (pullback.snd f ((ν ≫ β) ≫ p)) ι').base) :=
      (Wc.ι ≫ pullback.fst _ _).isOpenEmbedding.isOpen_range
    have h2 : (Set.range (Wc.ι ≫ pullback.fst (pullback.snd f ((ν ≫ β) ≫ p)) ι').base).Nonempty :=
      Set.range_nonempty _
    have h3 : IsOpen (PiM.base ⁻¹' (U' : Set _)) := U'.2.preimage PiM.continuous
    have h4 : (PiM.base ⁻¹' (U' : Set _)).Nonempty := ⟨ζ', by show PiM ζ' ∈ (U' : Set _); rw [hPiζ]; exact hζU'⟩
    obtain ⟨x, ⟨y, rfl⟩, hx2⟩ := nonempty_preirreducible_inter h1 h3 h2 h4
    exact ⟨⟨y, hx2⟩⟩
  haveI := hW₀ne

  obtain ⟨θD, hθD⟩ : ∃ θD : (W₀ : Scheme.{u}) ⟶ (D' : Scheme.{u}), θD ≫ D'.ι = W₀.ι ≫ Wc.ι ≫ pullback.fst _ _ :=
    ⟨IsOpenImmersion.lift D'.ι (W₀.ι ≫ Wc.ι ≫ pullback.fst _ _) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, ?_⟩
      · show (Wc.ι ≫ pullback.fst _ _) (W₀.ι x) ∈ (a'.dom : Set _)
        rw [← hθ'ι, Scheme.Hom.comp_apply]
        exact (θ' _).2
      · show PiM ((Wc.ι ≫ pullback.fst _ _) (W₀.ι x)) ∈ (U' : Set _)
        rw [← Scheme.Hom.comp_apply]
        exact x.2), IsOpenImmersion.lift_fac _ _ _⟩
  haveI : IsOpenImmersion θD := by
    have : IsOpenImmersion (θD ≫ D'.ι) := by rw [hθD]; infer_instance
    exact IsOpenImmersion.of_comp _ D'.ι

  have hE₁ : θD ≫ e₁ = W₀.ι ≫ θ' := by
    rw [← cancel_mono a'.dom.ι]
    simp only [Category.assoc]
    rw [he₁, hθD, hθ'ι]
  have hE₂ : θD ≫ lam ≫ (pullback f p).homOfLE hU' = W₀.ι ≫ θ₂ := by
    rw [← cancel_mono a.dom.ι]
    simp only [Category.assoc]
    rw [Scheme.homOfLE_ι, hlam, ← Category.assoc θD D'.ι PiM, hθD, hθ₂ι]
    simp only [Category.assoc]
  have l1 : (θD ≫ φ₁) ≫ β = W₀.ι ≫ (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ≫ G.homOfLE hV' ≫ ι₀ := by
    simp only [φ₁, Category.assoc]
    rw [← Category.assoc θD e₁, hE₁, Category.assoc W₀.ι θ', ← Category.assoc θ' a'.hom, hθ'hom,
      Category.assoc (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ι', hι'ι₀]
  have l2 : (θD ≫ φ₂) ≫ β = W₀.ι ≫ (wW f L ((ν ≫ β) ≫ p) ι' hι').1 ≫ G.homOfLE hV' ≫ ι₀ := by
    simp only [φ₂, Category.assoc]
    rw [hα', ← Category.assoc lam ((pullback f p).homOfLE hU') a.hom, ← Category.assoc θD (lam ≫ _) a.hom, hE₂,
      Category.assoc W₀.ι θ₂ a.hom, hθ₂hom]
  have hkey : θD ≫ φ₁ = θD ≫ φ₂ := by
    apply eq_of_comp_eq_of_isIso_restrict β W
    ·
      rw [l1, l2]
    · rintro _ ⟨x, rfl⟩
      rw [l1, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hV'W ⟨_, rfl⟩

  have hmor : (θD ≫ φ₁) ≫ pullback.diagonal p'' = θD ≫ ψ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      erw [pullback.lift_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      erw [pullback.lift_snd]
      exact hkey
  have hsub : Set.range θD.base ⊆ ψ.base ⁻¹' Set.range (pullback.diagonal p'') := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(θD ≫ φ₁) x, ?_⟩
    show (pullback.diagonal p'') ((θD ≫ φ₁) x) = ψ (θD x)
    rw [← Scheme.Hom.comp_apply, hmor, Scheme.Hom.comp_apply]
  have huniv : ψ.base ⁻¹' Set.range (pullback.diagonal p'') = Set.univ := by
    have hopen : IsOpen (Set.range θD.base) := θD.isOpenEmbedding.isOpen_range
    have hdense : Dense (Set.range θD.base) := hopen.dense (Set.range_nonempty _)
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_eq]
    exact hS.closure_subset_iff.mpr hsub

  have hz : (⟨ζ', hζ'D⟩ : ↥(D' : Scheme.{u})) ∈ ψ.base ⁻¹' Set.range (pullback.diagonal p'') := by
    rw [huniv]; trivial
  obtain ⟨d, hd⟩ := hz
  have h1 := congrArg (pullback.fst p'' p'').base hd
  have h2 := congrArg (pullback.snd p'' p'').base hd
  change (pullback.diagonal p'' ≫ pullback.fst p'' p'') d = (ψ ≫ pullback.fst p'' p'') ⟨ζ', hζ'D⟩ at h1
  change (pullback.diagonal p'' ≫ pullback.snd p'' p'') d = (ψ ≫ pullback.snd p'' p'') ⟨ζ', hζ'D⟩ at h2
  rw [pullback.diagonal_fst] at h1
  rw [pullback.diagonal_snd] at h2
  erw [pullback.lift_fst] at h1
  erw [pullback.lift_snd] at h2
  have hid : ∀ y : ↥P'', (𝟙 P'' : P'' ⟶ P'') y = y := fun y => by
    show (𝟙 P'' : P'' ⟶ P'').base y = y; rw [Scheme.Hom.id_base]; rfl
  rw [hid] at h1 h2

  have hζ₁ : e₁ ⟨ζ', hζ'D⟩ = ⟨ζ', hζ'⟩ := by
    apply Subtype.ext
    show (e₁ ≫ a'.dom.ι) ⟨ζ', hζ'D⟩ = ζ'
    rw [he₁]; rfl
  have hζ₂ : lam ⟨ζ', hζ'D⟩ = ⟨ζ, hζU'⟩ := by
    apply Subtype.ext
    show (lam ≫ U'.ι) ⟨ζ', hζ'D⟩ = ζ
    rw [hlam, Scheme.Hom.comp_apply]
    exact hPiζ
  have e₁' : φ₁ ⟨ζ', hζ'D⟩ = ν (a'.hom ⟨ζ', hζ'⟩) := by
    show ((e₁ ≫ a'.hom) ≫ ν) _ = _
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hζ₁]
  have e₂' : φ₂ ⟨ζ', hζ'D⟩ = α' ⟨ζ, hζU'⟩ := by
    show (lam ≫ α') _ = _
    rw [Scheme.Hom.comp_apply, hζ₂]
  change ν (a'.hom ⟨ζ', hζ'⟩) = α' ⟨ζ, hζU'⟩
  rw [← e₁', ← e₂', ← h1, ← h2]

end S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap (solution)
