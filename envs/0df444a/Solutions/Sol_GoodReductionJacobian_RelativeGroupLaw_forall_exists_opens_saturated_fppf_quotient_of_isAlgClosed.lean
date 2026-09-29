-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/79312515-ffdb-5547-8224-e7bcfa34ce8b

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace TranslateCoverGC3

variable {k : Type u} [CommRing k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

def const (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    SchemeHomOver t f :=
  schemeHomOverComp t (Category.comp_id t) a

@[scoped simp] theorem const_coe (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) : (const a t).1 = t ≫ a.1 := rfl

theorem comp_const (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (const a t) = const a t' := by
  apply Subtype.ext
  show ψ ≫ (t ≫ a.1) = t' ≫ a.1
  rw [← Category.assoc, hψ]

def rt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f RelativeGroupLaw.idPoint (const a f)).1

theorem rt_over (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : rt L a ≫ f = f :=
  (L.mul f RelativeGroupLaw.idPoint (const a f)).2

theorem comp_rt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f) :
    P.1 ≫ rt L a = (L.mul t P (const a t)).1 := by
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (Category.comp_id _)
  have := L.mul_natural f t P.1 P.2 RelativeGroupLaw.idPoint (const a f)
  rw [hP, comp_const] at this
  rw [← this]
  rfl

theorem rt_mul (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    rt L a ≫ rt L b = rt L (L.mul (𝟙 _) a b) := by
  have h1 : rt L a ≫ rt L b = (L.mul f (L.mul f RelativeGroupLaw.idPoint (const a f)) (const b f)).1 := by
    rw [← comp_rt L b f]; rfl
  rw [h1, L.mul_assoc]
  have h2 : L.mul f (const a f) (const b f) = const (L.mul (𝟙 _) a b) f := by
    simp only [const]
    rw [← L.mul_natural (𝟙 _) f f (Category.comp_id f)]
  rw [h2]; rfl

theorem rt_one : rt L (L.one (𝟙 _)) = 𝟙 G := by
  have : const (L.one (𝟙 (Spec (CommRingCat.of k)))) f = L.one f := L.one_natural (𝟙 _) f f (Category.comp_id f)
  show (L.mul f RelativeGroupLaw.idPoint (const (L.one (𝟙 _)) f)).1 = 𝟙 G
  rw [this, L.mul_one]

def rtIso (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ≅ G where
  hom := rt L a
  inv := rt L (L.inv (𝟙 _) a)
  hom_inv_id := by rw [rt_mul, L.mul_inv_cancel, rt_one]
  inv_hom_id := by rw [rt_mul, L.inv_mul_cancel, rt_one]

scoped instance (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : IsIso (rt L a) := (rtIso L a).isIso_hom

def Rt {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback (i ≫ f) f ⟶ pullback (i ≫ f) f :=
  pullback.lift (pullback.fst (i ≫ f) f) (pullback.snd (i ≫ f) f ≫ rt L a)
    (by rw [Category.assoc, rt_over, pullback.condition])

@[scoped simp] theorem Rt_fst {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Rt L i a ≫ pullback.fst (i ≫ f) f = pullback.fst (i ≫ f) f := pullback.lift_fst _ _ _

@[scoped simp] theorem Rt_snd {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Rt L i a ≫ pullback.snd (i ≫ f) f = pullback.snd (i ≫ f) f ≫ rt L a := pullback.lift_snd _ _ _

theorem Rt_action {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Rt L i a ≫ L.action i = L.action i ≫ rt L a := by
  have hsrc : Rt L i a ≫ RelativeGroupLaw.actionSource f i = RelativeGroupLaw.actionSource f i := by
    rw [RelativeGroupLaw.actionSource, ← Category.assoc, Rt_snd, Category.assoc, rt_over]

  have hR : L.action i ≫ rt L a =
      (L.mul (RelativeGroupLaw.actionSource f i) (L.actionFstPoint i)
        (L.mul _ (L.actionSndPoint i) (const a _))).1 := by
    rw [RelativeGroupLaw.action_def, comp_rt, L.mul_assoc]

  have h1 : schemeHomOverComp (Rt L i a) hsrc (L.actionFstPoint i) = L.actionFstPoint i := by
    apply Subtype.ext
    show Rt L i a ≫ (pullback.fst (i ≫ f) f ≫ i) = pullback.fst (i ≫ f) f ≫ i
    rw [← Category.assoc, Rt_fst]
  have h2 : schemeHomOverComp (Rt L i a) hsrc (L.actionSndPoint i) =
      L.mul _ (L.actionSndPoint i) (const a _) := by
    apply Subtype.ext
    show Rt L i a ≫ pullback.snd (i ≫ f) f = (L.mul _ (L.actionSndPoint i) (const a _)).1
    rw [Rt_snd, ← comp_rt]; rfl
  have hL : Rt L i a ≫ L.action i =
      (schemeHomOverComp (Rt L i a) hsrc (L.mul _ (L.actionFstPoint i) (L.actionSndPoint i))).1 := rfl
  rw [hL, L.mul_natural _ _ (Rt L i a) hsrc, h1, h2, hR]

theorem Rt_mul {N : Scheme.{u}} (i : N ⟶ G) (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Rt L i a ≫ Rt L i b = Rt L i (L.mul (𝟙 _) a b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Rt_fst, Rt_fst, Rt_fst]
  · rw [Category.assoc, Rt_snd, ← Category.assoc, Rt_snd, Category.assoc, rt_mul, Rt_snd]

theorem Rt_one {N : Scheme.{u}} (i : N ⟶ G) : Rt L i (L.one (𝟙 _)) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Rt_fst, Category.id_comp]
  · rw [Rt_snd, rt_one, Category.id_comp, Category.comp_id]

def RtIso {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback (i ≫ f) f ≅ pullback (i ≫ f) f where
  hom := Rt L i a
  inv := Rt L i (L.inv (𝟙 _) a)
  hom_inv_id := by rw [Rt_mul, L.mul_inv_cancel, Rt_one]
  inv_hom_id := by rw [Rt_mul, L.inv_mul_cancel, Rt_one]

scoped instance {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    IsIso (Rt L i a) := (RtIso L i a).isIso_hom

section transport

variable {N : Scheme.{u}} (i : N ⟶ G) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
  (U : G.Opens) (hU : pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U)

include hU in

theorem sat_preimage : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = L.action i ⁻¹ᵁ (rt L a ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← Rt_snd, ← Rt_action,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hU]

theorem preimage_Rt : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = Rt L i a ⁻¹ᵁ (pullback.snd (i ≫ f) f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Rt_snd]

def E : ((pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U)) : Scheme.{u}) ⟶ ((pullback.snd (i ≫ f) f ⁻¹ᵁ U) : Scheme.{u}) :=
  ((pullback (i ≫ f) f).isoOfEq (preimage_Rt L i a U)).hom ≫ (Rt L i a ∣_ (pullback.snd (i ≫ f) f ⁻¹ᵁ U))

scoped instance : IsIso (E L i a U) := by unfold E; infer_instance

@[reassoc]
theorem E_ι : E L i a U ≫ (pullback.snd (i ≫ f) f ⁻¹ᵁ U).ι = (pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U)).ι ≫ Rt L i a := by
  rw [E, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

theorem sq1 : E L i a U ≫ (pullback.snd (i ≫ f) f ∣_ U) = (pullback.snd (i ≫ f) f ∣_ (rt L a ⁻¹ᵁ U)) ≫ (rt L a ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, E_ι_assoc, Rt_snd, morphismRestrict_ι,
    morphismRestrict_ι_assoc]

theorem sq2 (hW : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = L.action i ⁻¹ᵁ (rt L a ⁻¹ᵁ U)) :
    E L i a U ≫ (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) =
      (((pullback (i ≫ f) f).isoOfEq hW).hom ≫ (L.action i ∣_ (rt L a ⁻¹ᵁ U))) ≫ (rt L a ∣_ U) := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [Scheme.isoOfEq_hom_ι_assoc, E_ι_assoc, Rt_action, morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]

theorem transport (hW : pullback.snd (i ≫ f) f ⁻¹ᵁ (rt L a ⁻¹ᵁ U) = L.action i ⁻¹ᵁ (rt L a ⁻¹ᵁ U))
    {Y : Scheme.{u}} (p : (U : Scheme.{u}) ⟶ Y)
    (hco : (pullback.snd (i ≫ f) f ∣_ U) ≫ p = (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p)
    [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p] [Surjective p]
    (hpb : IsPullback (pullback.snd (i ≫ f) f ∣_ U) (((pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p) :
    ((pullback.snd (i ≫ f) f ∣_ (rt L a ⁻¹ᵁ U)) ≫ ((rt L a ∣_ U) ≫ p) =
        (((pullback (i ≫ f) f).isoOfEq hW).hom ≫ (L.action i ∣_ (rt L a ⁻¹ᵁ U))) ≫ ((rt L a ∣_ U) ≫ p)) ∧
      Flat ((rt L a ∣_ U) ≫ p) ∧ LocallyOfFinitePresentation ((rt L a ∣_ U) ≫ p) ∧ QuasiCompact ((rt L a ∣_ U) ≫ p) ∧
      Surjective ((rt L a ∣_ U) ≫ p) ∧
      IsPullback (pullback.snd (i ≫ f) f ∣_ (rt L a ⁻¹ᵁ U)) (((pullback (i ≫ f) f).isoOfEq hW).hom ≫ (L.action i ∣_ (rt L a ⁻¹ᵁ U)))
        ((rt L a ∣_ U) ≫ p) ((rt L a ∣_ U) ≫ p) := by
  have s1 := sq1 L i a U
  have s2 := sq2 L i a U hU hW
  refine ⟨?_, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [← Category.assoc, ← s1, Category.assoc, hco, ← Category.assoc, s2, Category.assoc]
  · refine IsPullback.of_iso hpb (asIso (E L i a U)).symm (asIso (rt L a ∣_ U)).symm (asIso (rt L a ∣_ U)).symm (Iso.refl Y)
      ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, s1]
    · rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, s2]
    · rw [Iso.refl_hom, Iso.symm_hom, asIso_inv, Category.comp_id, IsIso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Iso.symm_hom, asIso_inv, Category.comp_id, IsIso.inv_hom_id_assoc]

end transport

end TranslateCoverGC3
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed.TranslateCoverGC3"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed.TranslateCoverGC3"

open TranslateCoverGC3 in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U) [Nonempty (U.toScheme)]
    (hloc : ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p) :
    ∀ x : G, ∃ (W : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ W = L.action i ⁻¹ᵁ W), x ∈ W ∧
      ∃ (Y : Scheme.{u}) (p : (W).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ W) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ W)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ W)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ W)) p p := by
  classical
  intro x
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f

  obtain ⟨z, hzcl, hzc⟩ := nonempty_inter_closedPoints (Z := closure {x}) ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hzc
  obtain ⟨u₀⟩ := (inferInstance : Nonempty (U.toScheme))
  obtain ⟨u, huU, huc⟩ := nonempty_inter_closedPoints (Z := (U : Set G)) ⟨u₀.1, u₀.2⟩ U.isOpen.isLocallyClosed
  rw [mem_closedPoints_iff] at huc
  let pz : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := ⟨pointOfClosedPoint f z hzc, pointOfClosedPoint_comp f z hzc⟩
  let pu : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := ⟨pointOfClosedPoint f u huc, pointOfClosedPoint_comp f u huc⟩
  let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := L.mul (𝟙 _) (L.inv (𝟙 _) pz) pu

  have hW := sat_preimage L i a U hU
  have hzW : z ∈ rt L a ⁻¹ᵁ U := by
    show (rt L a).base z ∈ U
    have h1 : (pz.1 ≫ rt L a) = (L.mul (𝟙 _) pz (const a (𝟙 _))).1 := comp_rt L a (𝟙 _) pz
    have h2 : const a (𝟙 (Spec (CommRingCat.of k))) = a := Subtype.ext (Category.id_comp _)
    rw [h2, show L.mul (𝟙 _) pz a = pu by rw [← L.mul_assoc, L.mul_inv_cancel, L.one_mul]] at h1
    have : (rt L a).base z = (pz.1 ≫ rt L a).base (IsLocalRing.closedPoint k) := by
      rw [Scheme.Hom.comp_apply]; exact congrArg _ (pointOfClosedPoint_apply f z hzc _).symm
    rw [this, h1]
    show (pointOfClosedPoint f u huc).base _ ∈ U
    rw [pointOfClosedPoint_apply]; exact huU
  have hxW : x ∈ rt L a ⁻¹ᵁ U := (specializes_iff_mem_closure.mpr hzcl).mem_open (rt L a ⁻¹ᵁ U).isOpen hzW
  obtain ⟨Y, p, hco, hfl, hlfp, hqc, hsj, hpb⟩ := hloc
  haveI := hfl; haveI := hlfp; haveI := hqc; haveI := hsj
  exact ⟨rt L a ⁻¹ᵁ U, hW, hxW, Y, (rt L a ∣_ U) ≫ p, transport L i a U hU hW p hco hpb⟩

end S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed (solution)
