-- Prove2me | solution 1 for N25.ordinaryKummerFiniteFlat
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:10.87339+00:00
-- url     : https://prove2.me/submissions/22afc832-dcdc-446d-b79e-44be92c1355d

import Mathlib
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Theorems.Thm_AlgebraicGeometry_exists_integral_section_of_fixed_geometric_point
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finite_flat_division_fibre
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_finite_flat_sigma_desc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Limits
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_carry_coordinates
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AddCommGroup_exists_divisionFibreEquiv
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibreProjection
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_division_fibre_points
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFiniteFlatRepresentation
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_flat_of_grpObj_over_spec
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

open GoodReductionJacobian

namespace N25

local instance instL_N25_ordinaryKummerFiniteFlat_23397f_sd40306 : Fact (Nat.Prime 71) := ⟨by decide⟩

private theorem division_coordinate_add
    {G : Type} [AddCommGroup G] (Q v w : G) (a b : ZMod 71) :
    (v + w) + (a + b).val • Q =
      (v + a.val • Q) + (w + b.val • Q) -
        ((a.val + b.val) / 71) • ((71 : ℕ) • Q) := by
  have hnat : a.val + b.val = (a + b).val + ((a.val + b.val) / 71) * 71 := by
    rw [ZMod.val_add]
    simpa only [Nat.mul_comm] using (Nat.mod_add_div (a.val + b.val) 71).symm
  have hs := congrArg (fun n : ℕ => n • Q) hnat
  simp only [add_nsmul, mul_smul] at hs
  have hs' : (a + b).val • Q = a.val • Q + b.val • Q -
      ((a.val + b.val) / 71) • ((71 : ℕ) • Q) :=
    eq_sub_iff_add_eq.mpr hs.symm
  rw [hs']
  abel

private theorem division_point_coordinate
    {R G : Type} [CommRing R] [AddCommGroup G] {B U : Scheme.{0}}
    {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (t : U ⟶ Spec (CommRingCat.of R))
    (Q : G) (pts : G ≃ SchemeHomOver t f)
    (hadd : ∀ x y, pts (x + y) = L.mul t (pts x) (pts y))
    (hP : pts ((71 : ℕ) • Q) =
      GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S)
    (v w : G) (a b : ZMod 71) :
    (L.mul t (L.mul t (pts (v + a.val • Q)) (pts (w + b.val • Q)))
      (L.inv t (L.nsmul t ((a.val + b.val) / 71)
        (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S)))).1 =
      (pts ((v + w) + (a + b).val • Q)).1 := by
  letI := L.pointCommGroup hc t
  have hn (n : ℕ) (x : SchemeHomOver t f) : L.nsmul t n x = x ^ n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change L.nsmul t n x * x = x ^ (n + 1)
        rw [ih, pow_succ]
  change (pts (v + a.val • Q) * pts (w + b.val • Q) /
    L.nsmul t ((a.val + b.val) / 71)
      (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S)).1 = _
  rw [hn]
  let ep : G ≃+ Additive (SchemeHomOver t f) :=
    { toEquiv := pts
      map_add' := hadd }
  have hpts_add (x y : G) : pts (x + y) = pts x * pts y := hadd x y
  have hpts_sub (x y : G) : pts (x - y) = pts x / pts y := by
    change (ep (x - y)).toMul = _
    rw [map_sub]
    rfl
  have hpts_nsmul (n : ℕ) (x : G) : pts (n • x) = pts x ^ n := by
    change (ep (n • x)).toMul = _
    rw [map_nsmul]
    rfl
  rw [← hP, ← hpts_nsmul ((a.val + b.val) / 71) ((71 : ℕ) • Q)]
  rw [← hpts_add (v + a.val • Q) (w + b.val • Q)]
  rw [← hpts_sub ((v + a.val • Q) + (w + b.val • Q))
    (((a.val + b.val) / 71) • ((71 : ℕ) • Q))]
  exact congrArg (fun u : G => (pts u).1) (division_coordinate_add Q v w a b).symm

/-- Faithful component coordinates determine a binary operation on coproduct
points. No group law is assumed by this comparison. -/
private theorem coproduct_point_map_add
    {C B U : Scheme.{0}} {ι W : Type} [AddCommGroup W]
    (t : U ⟶ C) (X : ι → Scheme.{0}) (g : ∀ a, X a ⟶ C)
    (pr : ∀ a, X a ⟶ B)
    (hinj : ∀ a (x y : SchemeHomOver t (g a)),
      x.1 ≫ pr a = y.1 ≫ pr a → x = y)
    (index : W → ι) (u : W → (U ⟶ B))
    (E : W ≃ SchemeHomOver t (Sigma.desc g))
    (z : ∀ x, SchemeHomOver t (g (index x)))
    (hz : ∀ x, (z x).1 ≫ Sigma.ι X (index x) = (E x).1)
    (hp : ∀ x, (z x).1 ≫ pr (index x) = u x)
    (m : W → W → SchemeHomOver t (Sigma.desc g))
    (hm : ∀ x y, ∃ w : SchemeHomOver t (g (index (x + y))),
      (m x y).1 = w.1 ≫ Sigma.ι X (index (x + y)) ∧
      w.1 ≫ pr (index (x + y)) = u (x + y)) :
    ∀ x y, E (x + y) = m x y := by
  intro x y
  obtain ⟨w, hw, hwpr⟩ := hm x y
  have hww : w = z (x + y) := hinj _ _ _ (hwpr.trans (hp (x + y)).symm)
  apply Subtype.ext
  calc
    (E (x + y)).1 = (z (x + y)).1 ≫ Sigma.ι X (index (x + y)) := (hz _).symm
    _ = w.1 ≫ Sigma.ι X (index (x + y)) := by rw [hww]
    _ = (m x y).1 := hw.symm

/-- The actual point equivalence and its component lifts can be chosen
with their original ambient coordinates. -/
private theorem exists_division_point_coordinates
    {R G : Type} [CommRing R] [AddCommGroup G]
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {K : Type} [CommRing K] [IsLocalRing K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (Q : G) (T : AddSubgroup G)
    (hT : ∀ x : G, x ∈ T ↔ (71 : ℕ) • x = 0)
    (pts : G ≃ SchemeHomOver t f)
    (hadd : ∀ x y, pts (x + y) = L.mul t (pts x) (pts y))
    (hP : pts ((71 : ℕ) • Q) =
      GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ E : T × ZMod 71 ≃ SchemeHomOver t (Sigma.desc g),
      ∃ z : ∀ x : T × ZMod 71, SchemeHomOver t (g x.2),
        (∀ x, (z x).1 ≫ Sigma.ι X x.2 = (E x).1) ∧
        (∀ x, (z x).1 ≫ pullback.fst (L.schemeNsmul 71)
          (L.nsmul (𝟙 _) x.2.val S).1 = (pts ((x.1 : G) + x.2.val • Q)).1) := by
  classical
  dsimp only
  let X : ZMod 71 → Scheme.{0} := fun a =>
    pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
    pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  obtain ⟨EF, hEF⟩ := L.division_fibre_points S t pts hadd ((71 : ℕ) • Q) hP
  let K0 := (nsmulAddMonoidHom (α := G) 71).ker
  have hkill (v : T) : (71 : ℕ) • (v : G) = 0 := (hT v).mp v.2
  let eT : T ≃ K0 :=
    { toFun := fun v => ⟨v.1, hkill v⟩
      invFun := fun v => ⟨v.1, (hT v.1).mpr v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨eD, hDcoord, _, _⟩ := AddCommGroup.exists_divisionFibreEquiv G Q
  let F : T × ZMod 71 → Σ a : ZMod 71,
      {x : G // (71 : ℕ) • x = a.val • ((71 : ℕ) • Q)} := fun x =>
    ⟨x.2, ⟨(x.1 : G) + x.2.val • Q, by
      rw [nsmul_add, hkill, zero_add]
      exact smul_comm (71 : ℕ) x.2.val Q⟩⟩
  let C := (eT.prodCongr (Equiv.refl (ZMod 71))).trans eD
  have hCF (x : T × ZMod 71) : C x = F x := by
    rcases x with ⟨v, a⟩
    change eD (eT v, a) = F (v, a)
    rcases h : eD (eT v, a) with ⟨b, y⟩
    have ha : b = a := by simpa only [h] using (hDcoord (eT v) a).1
    have hval : ((eD (eT v, a)).2 : G) = (y : G) :=
      congrArg (fun d : Σ b : ZMod 71,
        {x : G // (71 : ℕ) • x = b.val • ((71 : ℕ) • Q)} => (d.2 : G)) h
    have hx : (y : G) = (v : G) + a.val • Q :=
      hval.symm.trans (hDcoord (eT v) a).2
    subst b
    apply congrArg (Sigma.mk a)
    exact Subtype.ext hx
  have hFbij : Function.Bijective F := by
    have hFC : F = C := funext fun x => (hCF x).symm
    rw [hFC]
    exact C.bijective
  let D := Equiv.ofBijective F hFbij
  let E := D.trans EF
  have hlift (x : T × ZMod 71) :
      ∃ z : SchemeHomOver t (g x.2),
        z.1 ≫ Sigma.ι X x.2 = (E x).1 ∧
        z.1 ≫ pullback.fst (L.schemeNsmul 71)
          (L.nsmul (𝟙 _) x.2.val S).1 = (pts ((x.1 : G) + x.2.val • Q)).1 := by
    obtain ⟨_, _, z, hz, hp⟩ := hEF (D x)
    exact ⟨z, hz, hp⟩
  choose z hz hp using hlift
  exact ⟨E, z, hz, hp⟩

/-- The division-carry group preserves the additive coordinates of a supplied
point equivalence. The coefficient group remains abstract throughout. -/
private theorem exists_division_group_additive_coordinates
    {R G : Type} [CommRing R] [AddCommGroup G]
    {B U : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (t : U ⟶ Spec (CommRingCat.of R))
    (Q : G) (T : AddSubgroup G) (pts : G ≃ SchemeHomOver t f)
    (hadd : ∀ x y, pts (x + y) = L.mul t (pts x) (pts y))
    (hP : pts ((71 : ℕ) • Q) =
      GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∀ (E : T × ZMod 71 ≃ SchemeHomOver t (Sigma.desc g))
      (z : ∀ x : T × ZMod 71, SchemeHomOver t (g x.2))
      (hz : ∀ x, (z x).1 ≫ Sigma.ι X x.2 = (E x).1)
      (hp : ∀ x, (z x).1 ≫ pullback.fst (L.schemeNsmul 71)
        (L.nsmul (𝟙 _) x.2.val S).1 = (pts ((x.1 : G) + x.2.val • Q)).1),
      ∃ H : RelativeGroupLaw R (Sigma.desc g), H.IsCommutative ∧
        ∀ x y, E (x + y) = H.mul t (E x) (E y) := by
  dsimp only
  intro E z hz hp
  let X : ZMod 71 → Scheme.{0} := fun a =>
    pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
    pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  obtain ⟨H, hcomm, hmul⟩ := L.exists_division_carry_coordinates hc S
  refine ⟨H, hcomm, ?_⟩
  let pr (a : ZMod 71) : X a ⟶ B :=
    pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  have hinj (a : ZMod 71) (u v : SchemeHomOver t (g a))
      (h : u.1 ≫ pr a = v.1 ≫ pr a) : u = v := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact h
    · exact u.2.trans v.2.symm
  apply coproduct_point_map_add t X g pr hinj
    (fun x : T × ZMod 71 => x.2)
    (fun x : T × ZMod 71 => (pts ((x.1 : G) + x.2.val • Q)).1)
    E z hz hp (fun x y => H.mul t (E x) (E y))
  intro x y
  obtain ⟨w, hw, hwpr⟩ := hmul t x.2 y.2 (z x) (z y)
    (pts ((x.1 : G) + x.2.val • Q)) (pts ((y.1 : G) + y.2.val • Q))
    (hp x) (hp y)
  refine ⟨w, ?_, ?_⟩
  · calc
      (H.mul t (E x) (E y)).1 =
          (H.mul t ⟨(z x).1 ≫ Sigma.ι X x.2, by
              rw [Category.assoc, Sigma.ι_desc]; exact (z x).2⟩
            ⟨(z y).1 ≫ Sigma.ι X y.2, by
              rw [Category.assoc, Sigma.ι_desc]; exact (z y).2⟩).1 := by
        exact congrArg (fun u : SchemeHomOver t (Sigma.desc g) => u.1)
          (congrArg₂ (H.mul t) (Subtype.ext (hz x).symm) (Subtype.ext (hz y).symm))
      _ = w.1 ≫ Sigma.ι X (x.2 + y.2) := hw
  · exact hwpr.trans (division_point_coordinate L hc S t Q pts hadd hP
      (x.1 : G) (y.1 : G) x.2 y.2)

/-- The actual division-fibre coproduct models the ordinary Kummer extension
at 71, with its prescribed additive and local Galois actions. -/
theorem _root_.solution : OrdinaryKummerFiniteFlat := by
  intro Q hQ
  let T := AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
    (ModularCurve.xHFunctionFieldBar 25 H25) 71
  let c : Gal → T := fun σ => ⟨σ • Q - Q, by
    apply AlgebraicCurve.Pic0.mem_torsion.mpr
    have hs : σ • ((71 : ℕ) • Q) = (71 : ℕ) • (σ • Q) :=
      (DistribSMul.toAddMonoidHom J σ).map_nsmul 71 Q
    have hNat : (71 : ℕ) • (σ • Q - Q) = 0 := by
      rw [nsmul_sub, ← hs, hQ σ, sub_self]
    exact (Nat.cast_smul_eq_nsmul ℤ 71 (σ • Q - Q)).trans hNat⟩
  let act : Gal → T × ZMod 71 → T × ZMod 71 := fun σ x =>
    (ModularCurve.JH.torsionGaloisRep 25 H25 71 σ x.1 + x.2.val • c σ, x.2)
  change groupCohomology.IsFiniteFlatRepresentation 71
    (fun σ => act (localGaloisToGlobal 71 σ))
  obtain ⟨B, f, L, pts, hB, hc, hadd, hgal, _⟩ :=
    ModularCurve.exists_abelianSchemePropertyBundle_model_jH 25 H25 71 (by decide)
  let R := GaloisRep.ratLocalizedAt 71
  let t := Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))
  have hfixed (σ : Gal) :
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pts ((71 : ℕ) • Q)).1 =
        (pts ((71 : ℕ) • Q)).1 := by
    have hh := hgal σ ((71 : ℕ) • Q)
    change (pts (σ • ((71 : ℕ) • Q))).1 =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pts ((71 : ℕ) • Q)).1 at hh
    rw [hQ σ] at hh
    exact hh.symm
  letI : IsProper f := hB.proper
  obtain ⟨S, hS⟩ := AlgebraicGeometry.exists_integral_section_of_fixed_geometric_point
    71 f (pts ((71 : ℕ) • Q)) hfixed
  have hP : pts ((71 : ℕ) • Q) =
      GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S :=
    Subtype.ext hS.symm
  let X : ZMod 71 → Scheme.{0} := fun a =>
    pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
    pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  letI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt 71 (Fact.out : Nat.Prime 71)
  have hfg (a : ZMod 71) := L.finite_flat_division_fibre hB hc 71 (by decide)
    (L.nsmul (𝟙 _) a.val S)
  letI : ∀ a, IsFinite (g a) := fun a => (hfg a).1
  letI : ∀ a, Flat (g a) := fun a => (hfg a).2
  obtain ⟨hfin, hflat⟩ := AlgebraicGeometry.finite_flat_sigma_desc R X g
  letI := hfin
  letI := hflat
  have hT (x : J) : x ∈ T ↔ (71 : ℕ) • x = 0 := by
    rw [AlgebraicCurve.Pic0.mem_torsion]
    constructor
    · intro h
      exact (Nat.cast_smul_eq_nsmul ℤ 71 x).symm.trans h
    · intro h
      exact (Nat.cast_smul_eq_nsmul ℤ 71 x).trans h
  obtain ⟨E, z, hz, hp⟩ := exists_division_point_coordinates L S t Q T hT pts hadd hP
  obtain ⟨H, hcomm, hEadd⟩ :=
    exists_division_group_additive_coordinates L hc S t Q T pts hadd hP E z hz hp
  apply GoodReductionJacobian.RelativeGroupLaw.isFiniteFlatRepresentation
    71 act (Sigma.desc g) H hcomm E
  · exact hEadd
  · intro σ x
    let sσ := Spec.map (CommRingCat.ofHom σ.toRingHom)
    have hσt : sσ ≫ t = t := by
      dsimp [sσ, t]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext r
      exact σ.commutes (r : ℚ)
    have hac : ((act σ x).1 : J) + (act σ x).2.val • Q =
        σ • ((x.1 : J) + x.2.val • Q) := by
      change (σ • (x.1 : J) + x.2.val • (σ • Q - Q)) + x.2.val • Q = _
      have hs : σ • (x.2.val • Q) = x.2.val • (σ • Q) :=
        (DistribSMul.toAddMonoidHom J σ).map_nsmul x.2.val Q
      rw [smul_add, hs, nsmul_sub]
      abel
    have hzz : GoodReductionJacobian.schemeHomOverComp sσ hσt (z x) = z (act σ x) := by
      apply Subtype.ext
      apply pullback.hom_ext
      · change (sσ ≫ (z x).1) ≫ _ = _
        rw [Category.assoc, hp x, hp (act σ x), hac]
        exact (hgal σ _).symm
      · exact (GoodReductionJacobian.schemeHomOverComp sσ hσt (z x)).2.trans
          (z (act σ x)).2.symm
    calc
      (E (act σ x)).1 = (z (act σ x)).1 ≫ Sigma.ι X x.2 := (hz _).symm
      _ = (sσ ≫ (z x).1) ≫ Sigma.ι X x.2 := by
        rw [← hzz]
        rfl
      _ = sσ ≫ (E x).1 := by rw [Category.assoc, hz x]

end N25
