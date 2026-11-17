-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_group
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:09.100407+00:00
-- url     : https://prove2.me/submissions/9d2837c8-3a93-424e-9510-3c846e915c91

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_carry_multiplication
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_carry_unit
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_sigma_point_equiv_of_localRing
import Theorems.Thm_AlgebraicGeometry_Scheme_hom_ext_of_localRing_points
import Theorems.Thm_ZMod_division_carry_assoc
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibreProjection
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem point_pow_eq_nsmul
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointCommGroup hc t
    x ^ n = L.nsmul t n x := by
  letI := L.pointCommGroup hc t
  induction n with
  | zero => rfl
  | succ n ih =>
      change x ^ (n + 1) = L.nsmul t n x * x
      rw [pow_succ, ih]

private theorem fibre_projection_pow
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n a : ℕ)
    (x : SchemeHomOver t
      (pullback.snd (L.schemeNsmul n) (L.nsmul (𝟙 _) a S).1)) :
    letI := L.pointCommGroup hc t
    (⟨x.1 ≫ pullback.fst (L.schemeNsmul n) (L.nsmul (𝟙 _) a S).1,
      by rw [Category.assoc, fibre_projection_over]; exact x.2⟩ : SchemeHomOver t f) ^ n =
      (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) ^ a := by
  letI := L.pointCommGroup hc t
  apply Subtype.ext
  rw [point_pow_eq_nsmul, L.coe_nsmul_eq_comp_schemeNsmul]
  change (x.1 ≫ pullback.fst _ _) ≫ L.schemeNsmul n = _
  rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]
  have h := congrArg Subtype.val (L.nsmul_natural (𝟙 _) t t (by simp) a S)
  rw [← point_pow_eq_nsmul L hc t a] at h
  exact h

private theorem inverse_carry_sum (a : ZMod 71) :
    a.val + (-a).val = ((a.val + (-a).val) / 71) * 71 := by
  have h := Nat.mod_add_div (a.val + (-a).val) 71
  have hz : (a.val + (-a).val) % 71 = 0 := by
    rw [← ZMod.val_add]
    simp
  rw [hz, zero_add] at h
  simpa [Nat.mul_comm] using h.symm

private theorem carry_associative
    {G : Type*} [CommGroup G] (s x y z : G) (a b c : ZMod 71) :
    (x * y / s ^ ((a.val + b.val) / 71)) * z /
        s ^ (((a + b).val + c.val) / 71) =
      x * (y * z / s ^ ((b.val + c.val) / 71)) /
        s ^ ((a.val + (b + c).val) / 71) := by
  have hl (m n : ℕ) : (x * y / s ^ m) * z / s ^ n =
      x * y * z / s ^ (m + n) := by
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have hr (m n : ℕ) : x * (y * z / s ^ m) / s ^ n =
      x * y * z / s ^ (m + n) := by
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  rw [hl, hr, ZMod.division_carry_assoc]

private theorem group_laws_of_division_carry_coordinates
    {P G : Type*} [CommGroup G] (s : G)
    (m : P → P → P) (one : P) (inverse : P → P)
    (c : P → ZMod 71 × G) (hcinj : Function.Injective c)
    (hcm : ∀ x y, c (m x y) =
      ((c x).1 + (c y).1,
        (c x).2 * (c y).2 / s ^ (((c x).1.val + (c y).1.val) / 71)))
    (hco : c one = (0, 1))
    (hci : ∀ x, c (inverse x) =
      (-(c x).1, (c x).2⁻¹ * s ^ (((c x).1.val + (-(c x).1).val) / 71))) :
    (∀ x y z, m (m x y) z = m x (m y z)) ∧
    (∀ x, m one x = x) ∧ (∀ x, m x one = x) ∧
    (∀ x, m (inverse x) x = one) ∧ (∀ x y, m x y = m y x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply hcinj
    rw [hcm, hcm, hcm, hcm]
    apply Prod.ext
    · exact add_assoc _ _ _
    · exact carry_associative (s) _ _ _ _ _ _
  · intro x
    apply hcinj
    rw [hcm, hco]
    apply Prod.ext
    · simp
    · simp only [Prod.fst, Prod.snd, ZMod.val_zero, zero_add, add_zero,
        Nat.div_eq_of_lt (c x).1.val_lt, pow_zero, div_one,
        _root_.one_mul, _root_.mul_one]
  · intro x
    apply hcinj
    rw [hcm, hco]
    apply Prod.ext
    · simp
    · simp only [Prod.fst, Prod.snd, ZMod.val_zero, zero_add, add_zero,
        Nat.div_eq_of_lt (c x).1.val_lt, pow_zero, div_one,
        _root_.one_mul, _root_.mul_one]
  · intro x
    apply hcinj
    rw [hcm, hci, hco]
    apply Prod.ext
    · simp
    · change ((c x).2⁻¹ * s ^ (((c x).1.val + (-(c x).1).val) / 71)) * (c x).2 /
        s ^ (((-(c x).1).val + (c x).1.val) / 71) = 1
      rw [show (((-(c x).1).val + (c x).1.val) / 71) = (((c x).1.val + (-(c x).1).val) / 71) by
        exact congrArg (fun n : ℕ => n / 71) (Nat.add_comm _ _)]
      have hx : ((c x).2⁻¹ * s ^ (((c x).1.val + (-(c x).1).val) / 71)) * (c x).2 =
          s ^ (((c x).1.val + (-(c x).1).val) / 71) := by
        calc
          _ = ((c x).2⁻¹ * (c x).2) * s ^ (((c x).1.val + (-(c x).1).val) / 71) := by ac_rfl
          _ = _ := by rw [_root_.inv_mul_cancel, _root_.one_mul]
      rw [hx]
      rw [div_eq_mul_inv]
      exact _root_.mul_inv_cancel _
  · intro x y
    apply hcinj
    rw [hcm, hcm]
    apply Prod.ext
    · exact add_comm _ _
    · change (c x).2 * (c y).2 / s ^ (((c x).1.val + (c y).1.val) / 71) =
        (c y).2 * (c x).2 / s ^ (((c y).1.val + (c x).1.val) / 71)
      rw [Nat.add_comm (c x).1.val (c y).1.val,
        _root_.mul_comm (c x).2 (c y).2]

/-- The actual coproduct of the division fibres has the commutative group law
with the integral carry. The component equations preserve the supplied law
on the ambient scheme. -/
theorem _root_.solution
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ H : RelativeGroupLaw R (Sigma.desc g), H.IsCommutative ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : ZMod 71)
        (x : SchemeHomOver t (g a)) (y : SchemeHomOver t (g b)),
        letI := L.pointCommGroup hc t
        let px : SchemeHomOver t f :=
          ⟨x.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1,
            by rw [Category.assoc, fibre_projection_over]; exact x.2⟩
        let py : SchemeHomOver t f :=
          ⟨y.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) b.val S).1,
            by rw [Category.assoc, fibre_projection_over]; exact y.2⟩
        ∃ z : SchemeHomOver t (g (a + b)),
          (H.mul t ⟨x.1 ≫ Sigma.ι X a, by rw [Category.assoc, Sigma.ι_desc]; exact x.2⟩
            ⟨y.1 ≫ Sigma.ι X b, by rw [Category.assoc, Sigma.ι_desc]; exact y.2⟩).1 = z.1 ≫ Sigma.ι X (a + b) ∧
          z.1 ≫ pullback.fst (L.schemeNsmul 71)
              (L.nsmul (𝟙 _) (a + b).val S).1 =
            (px * py /
              (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) ^
                ((a.val + b.val) / 71)).1 := by
  classical
  let X : ZMod 71 → Scheme.{0} := fun a =>
    pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
    pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let q := Sigma.desc g
  let pr {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a : ZMod 71)
      (x : SchemeHomOver t (g a)) : SchemeHomOver t f :=
    ⟨x.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1,
      by rw [Category.assoc, fibre_projection_over]; exact x.2⟩
  let j {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a : ZMod 71)
      (x : SchemeHomOver t (g a)) : SchemeHomOver t q :=
    ⟨x.1 ≫ Sigma.ι X a, by rw [Category.assoc, Sigma.ι_desc]; exact x.2⟩
  let s {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :=
    GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S
  let comp {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (t' : T' ⟶ Spec (CommRingCat.of R)) (p : T' ⟶ T) (hp : p ≫ t = t') :
      letI := L.pointCommGroup hc t
      letI := L.pointCommGroup hc t'
      SchemeHomOver t f →* SchemeHomOver t' f := by
    letI := L.pointCommGroup hc t
    letI := L.pointCommGroup hc t'
    exact
      { toFun := GoodReductionJacobian.schemeHomOverComp p hp
        map_one' := L.one_natural t t' p hp
        map_mul' := L.mul_natural t t' p hp }
  have hprNat {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (t' : T' ⟶ Spec (CommRingCat.of R)) (p : T' ⟶ T) (hp : p ≫ t = t')
      (a : ZMod 71) (x : SchemeHomOver t (g a)) :
      GoodReductionJacobian.schemeHomOverComp p hp (pr t a x) =
        pr t' a (GoodReductionJacobian.schemeHomOverComp p hp x) := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm
  obtain ⟨μ, hμ⟩ := L.exists_division_carry_multiplication hc S
  obtain ⟨η, z₀, hη, hz₀⟩ := L.exists_division_carry_unit S
  let d (a : ZMod 71) := (a.val + (-a).val) / 71
  have hv (a : ZMod 71) :
      ∃ z : SchemeHomOver (g a) (g (-a)),
        letI := L.pointCommGroup hc (g a)
        pr (g a) (-a) z =
          (pr (g a) a ⟨𝟙 _, by simp⟩)⁻¹ * s (g a) ^ d a := by
    letI := L.pointCommGroup hc (g a)
    let x : SchemeHomOver (g a) (g a) := ⟨𝟙 _, by simp⟩
    let v := (pr (g a) a x)⁻¹ * s (g a) ^ d a
    have hx : (pr (g a) a x) ^ 71 = s (g a) ^ a.val :=
      fibre_projection_pow L hc S (g a) 71 a.val x
    have hp : v ^ 71 = s (g a) ^ (-a).val := by
      dsimp [v]
      rw [mul_pow, inv_pow, hx, ← pow_mul]
      have hsum := inverse_carry_sum a
      change a.val + (-a).val = d a * 71 at hsum
      rw [← hsum, pow_add]
      simp
    have heq : v.1 ≫ L.schemeNsmul 71 =
        g a ≫ (L.nsmul (𝟙 _) (-a).val S).1 := by
      rw [← L.coe_nsmul_eq_comp_schemeNsmul,
        ← point_pow_eq_nsmul L hc (g a) 71 v, hp]
      have h := congrArg Subtype.val (L.nsmul_natural (𝟙 _) (g a) (g a)
        (by simp) (-a).val S)
      rw [← point_pow_eq_nsmul L hc (g a) (-a).val] at h
      exact h.symm
    refine ⟨⟨pullback.lift v.1 (g a) heq, pullback.lift_snd _ _ _⟩, ?_⟩
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  choose v hv using hv
  let ν : SchemeHomOver q q :=
    ⟨Sigma.desc (fun a => (v a).1 ≫ Sigma.ι X (-a)), by
      apply Sigma.hom_ext
      intro a
      rw [Sigma.ι_desc_assoc]
      change (v a).1 ≫ Sigma.ι X (-a) ≫ Sigma.desc g = Sigma.ι X a ≫ Sigma.desc g
      rw [Sigma.ι_desc, Sigma.ι_desc]
      exact (v a).2⟩
  let m {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t q) : SchemeHomOver t q :=
    ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ μ.1, by
      rw [Category.assoc, μ.2, pullback.lift_fst_assoc]
      exact x.2⟩
  let one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t q :=
    ⟨t ≫ η.1, by rw [Category.assoc, η.2, Category.comp_id]⟩
  let inverse {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver t q) : SchemeHomOver t q :=
    ⟨x.1 ≫ ν.1, by rw [Category.assoc, ν.2]; exact x.2⟩
  have hmNat {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (t' : T' ⟶ Spec (CommRingCat.of R)) (p : T' ⟶ T) (hp : p ≫ t = t')
      (x y : SchemeHomOver t q) :
      GoodReductionJacobian.schemeHomOverComp p hp (m t x y) =
        m t' (GoodReductionJacobian.schemeHomOverComp p hp x)
          (GoodReductionJacobian.schemeHomOverComp p hp y) := by
    apply Subtype.ext
    change p ≫ pullback.lift x.1 y.1 _ ≫ μ.1 =
      pullback.lift (p ≫ x.1) (p ≫ y.1) _ ≫ μ.1
    have hLift : p ≫ pullback.lift x.1 y.1 (x.2.trans y.2.symm) =
        pullback.lift (p ≫ x.1) (p ≫ y.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun r => p ≫ r) (x.2.trans y.2.symm)).trans
              (Category.assoc _ _ _).symm)) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        exact (pullback.lift_fst (p ≫ x.1) (p ≫ y.1) _).symm
      · rw [Category.assoc, pullback.lift_snd]
        exact (pullback.lift_snd (p ≫ x.1) (p ≫ y.1) _).symm
    simpa only [Category.assoc] using congrArg (fun r => r ≫ μ.1) hLift
  have hoNat {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (t' : T' ⟶ Spec (CommRingCat.of R)) (p : T' ⟶ T) (hp : p ≫ t = t') :
      GoodReductionJacobian.schemeHomOverComp p hp (one t) = one t' := by
    apply Subtype.ext
    change p ≫ t ≫ η.1 = t' ≫ η.1
    rw [← Category.assoc, hp]
  have hiNat {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (t' : T' ⟶ Spec (CommRingCat.of R)) (p : T' ⟶ T) (hp : p ≫ t = t')
      (x : SchemeHomOver t q) :
      GoodReductionJacobian.schemeHomOverComp p hp (inverse t x) =
        inverse t' (GoodReductionJacobian.schemeHomOverComp p hp x) := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm
  have hmComponent {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (a b : ZMod 71) (x : SchemeHomOver t (g a)) (y : SchemeHomOver t (g b)) :
      letI := L.pointCommGroup hc t
      ∃ z : SchemeHomOver t (g (a + b)),
        m t (j t a x) (j t b y) = j t (a + b) z ∧
        pr t (a + b) z = pr t a x * pr t b y / s t ^ ((a.val + b.val) / 71) := by
    letI := L.pointCommGroup hc t
    obtain ⟨xa, yb, za, hxa, hyb, hmap, hza⟩ := hμ a b
    let t₂ := pullback.fst (g a) (g b) ≫ g a
    letI := L.pointCommGroup hc t₂
    let k := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
    have hk : k ≫ t₂ = t := by
      change k ≫ pullback.fst (g a) (g b) ≫ g a = t
      rw [← Category.assoc, pullback.lift_fst]
      exact x.2
    let z := GoodReductionJacobian.schemeHomOverComp k hk za
    have hkmap :
        k ≫ pullback.map (g a) (g b) q q
          (Sigma.ι X a) (Sigma.ι X b) (𝟙 _)
          (by simp only [q, Category.comp_id, Sigma.ι_desc])
          (by simp only [q, Category.comp_id, Sigma.ι_desc]) =
        pullback.lift (j t a x).1 (j t b y).1
          ((j t a x).2.trans (j t b y).2.symm) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc]
        rw [show k ≫ pullback.fst (g a) (g b) = x.1 from
          pullback.lift_fst x.1 y.1 _]
        exact (pullback.lift_fst (j t a x).1 (j t b y).1 _).symm
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc]
        rw [show k ≫ pullback.snd (g a) (g b) = y.1 from
          pullback.lift_snd x.1 y.1 _]
        exact (pullback.lift_snd (j t a x).1 (j t b y).1 _).symm
    refine ⟨z, ?_, ?_⟩
    · apply Subtype.ext
      change pullback.lift (j t a x).1 (j t b y).1 _ ≫ μ.1 = _
      rw [← hkmap, Category.assoc, hmap]
      exact (Category.assoc _ _ _).symm
    · have hpz : pr t₂ (a + b) za =
          xa * yb / s t₂ ^ ((a.val + b.val) / 71) := Subtype.ext hza
      have hpx : (comp t₂ t k hk) xa = pr t a x := by
        apply Subtype.ext
        change k ≫ xa.1 = _
        rw [hxa, ← Category.assoc]
        exact congrArg (fun r => r ≫
          pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1)
          (pullback.lift_fst x.1 y.1 _)
      have hpy : (comp t₂ t k hk) yb = pr t b y := by
        apply Subtype.ext
        change k ≫ yb.1 = _
        rw [hyb, ← Category.assoc]
        exact congrArg (fun r => r ≫
          pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) b.val S).1)
          (pullback.lift_snd x.1 y.1 _)
      have hps : (comp t₂ t k hk) (s t₂) = s t := by
        apply Subtype.ext
        change k ≫ t₂ ≫ S.1 = t ≫ S.1
        rw [← Category.assoc, hk]
      have hh := congrArg (comp t₂ t k hk) hpz
      rw [map_div, map_mul, map_pow, hpx, hpy, hps] at hh
      exact (hprNat t₂ t k hk (a + b) za).symm.trans hh
  have hoComponent {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
      ∃ z : SchemeHomOver t (g 0), one t = j t 0 z ∧ pr t 0 z = L.one t := by
    let z := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) z₀
    refine ⟨z, ?_, ?_⟩
    · apply Subtype.ext
      change t ≫ η.1 = (t ≫ z₀.1) ≫ Sigma.ι X 0
      rw [hη, Category.assoc]
    · apply Subtype.ext
      change (t ≫ z₀.1) ≫ pullback.fst _ _ = (L.one t).1
      rw [Category.assoc, hz₀]
      exact congrArg Subtype.val (L.one_natural (𝟙 _) t t (by simp))
  have hiComponent {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (a : ZMod 71) (x : SchemeHomOver t (g a)) :
      letI := L.pointCommGroup hc t
      ∃ z : SchemeHomOver t (g (-a)), inverse t (j t a x) = j t (-a) z ∧
        pr t (-a) z = (pr t a x)⁻¹ * s t ^ d a := by
    letI := L.pointCommGroup hc t
    letI := L.pointCommGroup hc (g a)
    let z := GoodReductionJacobian.schemeHomOverComp x.1 x.2 (v a)
    refine ⟨z, ?_, ?_⟩
    · apply Subtype.ext
      change (x.1 ≫ Sigma.ι X a) ≫ ν.1 = _
      simp [ν, z, j, Category.assoc]
    · have hh := congrArg (comp (g a) t x.1 x.2) (hv a)
      rw [map_mul, map_inv, map_pow] at hh
      have hpx : (comp (g a) t x.1 x.2) (pr (g a) a ⟨𝟙 _, by simp⟩) =
          pr t a x := by apply Subtype.ext; simp [comp, pr]
      have hps : (comp (g a) t x.1 x.2) (s (g a)) = s t := by
        apply Subtype.ext
        change x.1 ≫ g a ≫ S.1 = t ≫ S.1
        rw [← Category.assoc, x.2]
      rw [hpx, hps] at hh
      exact (hprNat (g a) t x.1 x.2 (-a) (v a)).symm.trans hh
  have localLaws (K : Type) [CommRing K] [IsLocalRing K]
      (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
      (∀ x y z, m t (m t x y) z = m t x (m t y z)) ∧
      (∀ x, m t (one t) x = x) ∧
      (∀ x, m t x (one t) = x) ∧
      (∀ x, m t (inverse t x) x = one t) ∧
      (∀ x y, m t x y = m t y x) := by
    letI := L.pointCommGroup hc t
    obtain ⟨e, he⟩ := Scheme.exists_sigma_point_equiv_of_localRing X g t
    let c (x : SchemeHomOver t q) : ZMod 71 × SchemeHomOver t f :=
      ((e.symm x).1, pr t (e.symm x).1 (e.symm x).2)
    have hj (a : ZMod 71) (x : SchemeHomOver t (g a)) : e ⟨a, x⟩ = j t a x :=
      Subtype.ext (he ⟨a, x⟩)
    have hcj (a : ZMod 71) (x : SchemeHomOver t (g a)) :
        c (j t a x) = (a, pr t a x) := by
      rw [← hj]
      exact congrArg (fun u : Σ a, SchemeHomOver t (g a) =>
        (u.1, pr t u.1 u.2)) (e.symm_apply_apply ⟨a, x⟩)
    have hcinj : Function.Injective c := by
      intro x y h
      obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective x
      obtain ⟨⟨b, w⟩, rfl⟩ := e.surjective y
      rw [hj, hj, hcj, hcj] at h
      have hab : a = b := congrArg Prod.fst h
      subst b
      have hu : u = w := by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact congrArg Subtype.val (congrArg Prod.snd h)
        · exact u.2.trans w.2.symm
      subst w
      rfl
    have hcm (x y : SchemeHomOver t q) :
        c (m t x y) =
          ((c x).1 + (c y).1,
            (c x).2 * (c y).2 / s t ^ (((c x).1.val + (c y).1.val) / 71)) := by
      obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective x
      obtain ⟨⟨b, w⟩, rfl⟩ := e.surjective y
      rw [hj, hj]
      obtain ⟨z, hz, hpz⟩ := hmComponent t a b u w
      rw [hz, hcj, hcj, hcj, hpz]
    have hco : c (one t) = (0, 1) := by
      obtain ⟨z, hz, hpz⟩ := hoComponent t
      rw [hz, hcj, hpz]
      rfl
    have hci (x : SchemeHomOver t q) :
        c (inverse t x) = (-(c x).1, (c x).2⁻¹ * s t ^ d (c x).1) := by
      obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective x
      rw [hj]
      obtain ⟨z, hz, hpz⟩ := hiComponent t a u
      rw [hz, hcj, hcj, hpz]
    exact group_laws_of_division_carry_coordinates (s t) (m t) (one t) (inverse t)
      c hcinj hcm hco hci
  have pointExt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t q)
      (h : ∀ (K : Type) [CommRing K] [IsLocalRing K]
        (p : Spec (CommRingCat.of K) ⟶ T),
        GoodReductionJacobian.schemeHomOverComp p rfl x =
          GoodReductionJacobian.schemeHomOverComp p rfl y) : x = y := by
    apply Subtype.ext
    apply Scheme.hom_ext_of_localRing_points
    intro K _ _ p
    exact congrArg Subtype.val (h K p)
  have hAssoc {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y z : SchemeHomOver t q) : m t (m t x y) z = m t x (m t y z) := by
    apply pointExt t
    intro K _ _ p
    simp only [hmNat]
    exact (localLaws K (p ≫ t)).1 _ _ _
  have hOne {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver t q) : m t (one t) x = x := by
    apply pointExt t
    intro K _ _ p
    simp only [hmNat, hoNat]
    exact (localLaws K (p ≫ t)).2.1 _
  have hMulOne {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver t q) : m t x (one t) = x := by
    apply pointExt t
    intro K _ _ p
    simp only [hmNat, hoNat]
    exact (localLaws K (p ≫ t)).2.2.1 _
  have hInv {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver t q) : m t (inverse t x) x = one t := by
    apply pointExt t
    intro K _ _ p
    simp only [hmNat, hoNat, hiNat]
    exact (localLaws K (p ≫ t)).2.2.2.1 _
  have hComm {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t q) : m t x y = m t y x := by
    apply pointExt t
    intro K _ _ p
    simp only [hmNat]
    exact (localLaws K (p ≫ t)).2.2.2.2 _ _
  let H : RelativeGroupLaw R q :=
    { mul := m
      one := one
      inv := inverse
      mul_assoc := hAssoc
      one_mul := hOne
      mul_one := hMulOne
      inv_mul_cancel := hInv
      mul_natural := hmNat }
  refine ⟨H, hComm, ?_⟩
  intro T t a b x y
  obtain ⟨z, hz, hpz⟩ := hmComponent t a b x y
  exact ⟨z, congrArg Subtype.val hz, congrArg Subtype.val hpz⟩

end GoodReductionJacobian.RelativeGroupLaw
