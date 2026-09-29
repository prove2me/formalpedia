-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.eq_one_of_isTorsionPoint_of_comp_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/59325b76-7028-5300-a4fb-e5e5a4d4f55b

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

namespace REDINJ
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have hx : x.1 ≫ f = t := x.2
  have h := L.nsmul_natural f t x.1 hx n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp x.1 hx (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hid] at h
  have := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

theorem baseChangePointToBase_nsmul {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).nsmul t' n x) =
      L.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
      RelativeGroupLaw.baseChangePointToBase_mul, ih]

end REDINJ

open REDINJ in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) [LocallyOfFiniteType f]
    {B : Type u} [CommRing B] [IsLocalRing B]
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (m : ℕ) (hm : IsUnit (m : B))
    (s : SchemeHomOver t f)
    (hs : L.IsTorsionPoint t m s)
    (hred : schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl s =
        schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl (L.one t)) :
    s = L.one t := by

  let fB := RelativeGroupLaw.baseChangeStr t f
  let LB := L.baseChange t
  have hcB : LB.IsCommutative := hc.baseChange t
  let g : pullback f t ⟶ pullback f t := LB.schemeNsmul m
  have hg_over : g ≫ fB = fB := LB.schemeNsmul_over m

  haveI : FormallyUnramified g :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing LB
      (fun t x y => hcB t x y) m hm
  haveI : LocallyOfFiniteType fB := inferInstance
  haveI : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType (g ≫ fB) := by rw [hg_over]; infer_instance
    exact locallyOfFiniteType_of_comp g fB

  have h1t : 𝟙 (Spec (CommRingCat.of B)) ≫ t = t := Category.id_comp t
  let sB : SchemeHomOver (𝟙 (Spec (CommRingCat.of B))) fB :=
    RelativeGroupLaw.baseChangePointOfBase t ⟨s.1, by rw [h1t]; exact s.2⟩
  let eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of B))) fB := LB.one _
  have hsB_to : RelativeGroupLaw.baseChangePointToBase t sB = ⟨s.1, by rw [h1t]; exact s.2⟩ :=
    RelativeGroupLaw.baseChangePointToBase_ofBase t _

  have htor : LB.nsmul _ m sB = eB := by
    apply (RelativeGroupLaw.baseChangePointEquiv t (𝟙 _)).injective
    show RelativeGroupLaw.baseChangePointToBase t (LB.nsmul _ m sB) =
      RelativeGroupLaw.baseChangePointToBase t eB
    rw [baseChangePointToBase_nsmul, RelativeGroupLaw.baseChangePointToBase_one, hsB_to]

    have hcast : ∀ (t₁ t₂ : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (h : t₁ = t₂)
        (x : SchemeHomOver t₂ f), L.IsTorsionPoint t₂ m x →
        L.nsmul t₁ m ⟨x.1, by rw [h]; exact x.2⟩ = L.one t₁ := by
      intro t₁ t₂ h x hx; subst h; exact hx
    exact hcast _ _ h1t s hs

  have hu : sB.1 ≫ g = eB.1 ≫ g := by
    rw [comp_schemeNsmul, comp_schemeNsmul, htor, RelativeGroupLaw.nsmul_unit]

  let p : Spec (CommRingCat.of (IsLocalRing.ResidueField B)) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
  have hred1 : p ≫ s.1 = p ≫ (L.one t).1 := by
    have := congrArg Subtype.val hred
    simpa [GoodReductionJacobian.schemeHomOverComp_coe] using this
  have hp : p ≫ sB.1 = p ≫ eB.1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      show p ≫ (RelativeGroupLaw.baseChangePointToBase t sB).1 =
        p ≫ (RelativeGroupLaw.baseChangePointToBase t eB).1
      rw [hsB_to, RelativeGroupLaw.baseChangePointToBase_one]

      have : (L.one (𝟙 (Spec (CommRingCat.of B)) ≫ t)).1 = (L.one t).1 := by
        rw [h1t]
      rw [this]
      exact hred1
    · rw [Category.assoc, Category.assoc, sB.2, eB.2]

  have hEq : sB.1 = eB.1 :=
    AlgebraicGeometry.eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified g B sB.1 eB.1 hu hp

  apply Subtype.ext
  have := congrArg (fun q => q ≫ pullback.fst f t) hEq
  have e1 : sB.1 ≫ pullback.fst f t = s.1 := by
    show (RelativeGroupLaw.baseChangePointToBase t sB).1 = s.1
    rw [hsB_to]
  have e2 : eB.1 ≫ pullback.fst f t = (L.one t).1 := by
    show (RelativeGroupLaw.baseChangePointToBase t eB).1 = (L.one t).1
    rw [RelativeGroupLaw.baseChangePointToBase_one, h1t]
  rw [e1, e2] at this
  exact this

end S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq (solution)
