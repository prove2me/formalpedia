-- Prove2me | solution 1 for ModularCurve.algebraicIndependent_variableChange_tateLaurent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0ed9e2a1-3759-5a7a-ac9b-b3b2d3a10ca2

import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_WeierstrassCurve_Generic
import Theorems.Thm_ModularCurve_j_tateLaurent
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_algebraicIndependent_variableChange_tateLaurent

set_option autoImplicit false

universe u

noncomputable section

open MvPolynomial WeierstrassCurve

namespace ModularCurve
p2m_export "ModularCurve" "tateLaurent jqModC j_tateLaurent transcendental_jqModC"
namespace TateDominance
p2m_open "ModularCurve"

section Coeff

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]

def cf (W : WeierstrassCurve A) : Fin 5 → A := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem cf_map (W : WeierstrassCurve A) (f : A →+* B) : cf (W.map f) = f ∘ cf W := by
  funext i
  fin_cases i <;> rfl

variable {κ : Type*} [CommRing κ]

def evP (i : κ →+* A) (W : WeierstrassCurve A) (P : MvPolynomial (Fin 5) κ) : A :=
  eval₂ i (cf W) P

theorem evP_map (i : κ →+* A) (W : WeierstrassCurve A) (f : A →+* B) (P : MvPolynomial (Fin 5) κ) :
    evP (f.comp i) (W.map f) P = f (evP i W P) := by
  rw [evP, evP, cf_map, eval₂_comp_left]

end Coeff

section Spec

variable {R₀ : Type*} [CommRing R₀] {σ : Type*} (d : MvPolynomial σ R₀)
  {B : Type*} [CommRing B] (i : R₀ →+* B) (v : σ → B)

def specAway (h : IsUnit (eval₂ i v d)) : Localization.Away d →+* B :=
  IsLocalization.Away.lift d (g := eval₂Hom i v) h

theorem specAway_algebraMap (h : IsUnit (eval₂ i v d)) (p : MvPolynomial σ R₀) :
    specAway d i v h (algebraMap (MvPolynomial σ R₀) (Localization.Away d) p) = eval₂ i v p :=
  IsLocalization.Away.lift_eq d h p

theorem specAway_X (h : IsUnit (eval₂ i v d)) (n : σ) :
    specAway d i v h (algebraMap (MvPolynomial σ R₀) (Localization.Away d) (X n)) = v n := by
  rw [specAway_algebraMap, eval₂_X]

theorem specAway_C (h : IsUnit (eval₂ i v d)) (r : R₀) :
    specAway d i v h (algebraMap (MvPolynomial σ R₀) (Localization.Away d) (C r)) = i r := by
  rw [specAway_algebraMap, eval₂_C]

theorem specAway_comp_C (h : IsUnit (eval₂ i v d)) :
    (specAway d i v h).comp ((algebraMap (MvPolynomial σ R₀) (Localization.Away d)).comp C) = i :=
  RingHom.ext fun r => specAway_C d i v h r

end Spec

section AwayLemmas

variable {R₀ : Type*} [CommRing R₀] {σ : Type*} (d : MvPolynomial σ R₀) {B : Type*} [CommRing B]

theorem injective_of_comp_algebraMap [IsDomain R₀] (hd : d ≠ 0) (φ : Localization.Away d →+* B)
    (h : Function.Injective (φ.comp (algebraMap (MvPolynomial σ R₀) (Localization.Away d)))) :
    Function.Injective φ := by
  haveI : IsDomain (Localization.Away d) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  refine (injective_iff_map_eq_zero φ).mpr fun w hw => ?_
  obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers d) w
  simp only at hz
  have h1 : φ (algebraMap _ (Localization.Away d) z) = 0 := by
    rw [← hz, map_mul, hw, zero_mul]
  have h2 : z = 0 := (injective_iff_map_eq_zero _).mp h z h1
  rw [h2, map_zero, mul_eq_zero] at hz
  rcases hz with hz | hz
  · exact hz
  · rw [map_pow] at hz
    exact absurd hz ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d).pow n).ne_zero

theorem eq_zero_of_forall_spec_eq_zero {L : Type*} [Field L] [Infinite L]
    (w : Localization.Away (X 0 : MvPolynomial (Fin 4) L))
    (h : ∀ (v : Fin 4 → L) (hv : IsUnit (eval₂ (RingHom.id L) v (X 0 : MvPolynomial (Fin 4) L))),
      specAway (X 0) (RingHom.id L) v hv w = 0) : w = 0 := by
  haveI : IsDomain (Localization.Away (X 0 : MvPolynomial (Fin 4) L)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (X 0 : MvPolynomial (Fin 4) L)) w
  simp only at hz

  have hz0 : (X 0 : MvPolynomial (Fin 4) L) * z = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_zero, map_mul, eval_X]
    by_cases hv : v 0 = 0
    · rw [hv, zero_mul]
    · have hu : IsUnit (eval₂ (RingHom.id L) v (X 0 : MvPolynomial (Fin 4) L)) := by
        rw [eval₂_X]; exact isUnit_iff_ne_zero.mpr hv
      have e := congrArg (specAway (X 0) (RingHom.id L) v hu) hz
      rw [map_mul, h v hu, zero_mul, specAway_algebraMap] at e
      rw [show MvPolynomial.eval v z = eval₂ (RingHom.id L) v z from rfl, ← e, mul_zero]
  rcases mul_eq_zero.mp hz0 with h0 | h0
  · exact absurd h0 (X_ne_zero 0)
  · rw [h0, map_zero, mul_eq_zero] at hz
    rcases hz with hz | hz
    · exact hz
    · rw [map_pow] at hz
      exact absurd hz ((IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (X 0 : MvPolynomial (Fin 4) L)) (X 0 : MvPolynomial (Fin 4) L)).pow n).ne_zero

end AwayLemmas

section Family

variable (κ : Type*) [CommRing κ]

abbrev P5 : Type _ := MvPolynomial (Fin 5) κ

def D5 : P5 κ := X 0 * (X 0 - 1728) * X 1

abbrev Λ₅ : Type _ := Localization.Away (D5 κ)

def iΛ₅ : κ →+* Λ₅ κ := (algebraMap (P5 κ) (Λ₅ κ)).comp C

def xv (n : Fin 5) : Λ₅ κ := algebraMap (P5 κ) (Λ₅ κ) (X n)

theorem isUnit_D5 : IsUnit (algebraMap (P5 κ) (Λ₅ κ) (D5 κ)) :=
  IsLocalization.Away.algebraMap_isUnit _

theorem isUnit_JJV : IsUnit (xv κ 0) ∧ IsUnit (xv κ 0 - 1728) ∧ IsUnit (xv κ 1) := by
  have h : IsUnit (algebraMap (P5 κ) (Λ₅ κ) (X 0 * (X 0 - 1728) * X 1)) := isUnit_D5 κ
  rw [map_mul, map_mul, map_sub, map_ofNat, IsUnit.mul_iff, IsUnit.mul_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem isUnit_J : IsUnit (xv κ 0) := (isUnit_JJV κ).1

theorem isUnit_J_sub : IsUnit (xv κ 0 - 1728) := (isUnit_JJV κ).2.1

theorem isUnit_V : IsUnit (xv κ 1) := (isUnit_JJV κ).2.2

def Cfam : VariableChange (Λ₅ κ) := ⟨(isUnit_V κ).unit, xv κ 2, xv κ 3, xv κ 4⟩

def Efam : WeierstrassCurve (Λ₅ κ) := Cfam κ • ofJNe0Or1728 (xv κ 0)

variable {κ}
variable {B : Type*} [CommRing B] (i : κ →+* B) (j v r s t : B) (hj : IsUnit j) (hj' : IsUnit (j - 1728))
  (hv : IsUnit v)

include hj hj' hv in
theorem isUnit_eval_D5 : IsUnit (eval₂ i ![j, v, r, s, t] (D5 κ)) := by
  change IsUnit (eval₂Hom i ![j, v, r, s, t] (D5 κ))
  simp only [D5, map_mul, map_sub, map_ofNat, coe_eval₂Hom, eval₂_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact (hj.mul hj').mul hv

def spec5 : Λ₅ κ →+* B := specAway (D5 κ) i ![j, v, r, s, t] (isUnit_eval_D5 i j v r s t hj hj' hv)

theorem spec5_xv (n : Fin 5) : spec5 i j v r s t hj hj' hv (xv κ n) = ![j, v, r, s, t] n :=
  specAway_X _ _ _ _ n

theorem spec5_comp_iΛ₅ : (spec5 i j v r s t hj hj' hv).comp (iΛ₅ κ) = i :=
  specAway_comp_C _ _ _ _

theorem ofJNe0Or1728_map {A : Type*} [CommRing A] (x : A) (f : A →+* B) :
    (ofJNe0Or1728 x).map f = ofJNe0Or1728 (f x) := by
  simp [ofJNe0Or1728, WeierstrassCurve.map, map_ofNat]

theorem Efam_map_spec5 :
    (Efam κ).map (spec5 i j v r s t hj hj' hv) = (⟨hv.unit, r, s, t⟩ : VariableChange B) • ofJNe0Or1728 j := by
  have h0 : spec5 i j v r s t hj hj' hv (xv κ 0) = j := spec5_xv i j v r s t hj hj' hv 0
  rw [Efam, ← map_variableChange, ofJNe0Or1728_map, h0]
  congr 1
  refine VariableChange.ext ?_ ?_ ?_ ?_
  · ext
    rw [VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe]
    exact spec5_xv i j v r s t hj hj' hv 1
  · exact spec5_xv i j v r s t hj hj' hv 2
  · exact spec5_xv i j v r s t hj hj' hv 3
  · exact spec5_xv i j v r s t hj hj' hv 4

theorem evP_spec5 (P : P5 κ) :
    evP i ((⟨hv.unit, r, s, t⟩ : VariableChange B) • ofJNe0Or1728 j) P =
      spec5 i j v r s t hj hj' hv (evP (iΛ₅ κ) (Efam κ) P) := by
  rw [← evP_map, spec5_comp_iΛ₅, Efam_map_spec5]

end Family

section LemmaA

variable {κ : Type*} [Field κ]

theorem D5_ne_zero : D5 κ ≠ 0 := by
  have h2 : (X 0 : P5 κ) - 1728 ≠ 0 := by
    intro h
    have e := congrArg (MvPolynomial.eval (fun _ => (1729 : κ))) h
    simp only [map_sub, map_ofNat, eval_X, map_zero] at e
    norm_num at e
  exact mul_ne_zero (mul_ne_zero (X_ne_zero 0) h2) (X_ne_zero 1)

variable {L : Type*} [Field L] (i : κ →+* L) (jL : L)
  (hjt : ∀ q : Polynomial κ, q.eval₂ i jL = 0 → q = 0)

include hjt in
theorem jL_ne_zero : jL ≠ 0 := fun h =>
  Polynomial.X_ne_zero (hjt Polynomial.X (by rw [Polynomial.eval₂_X, h]))

include hjt in
theorem jL_sub_ne_zero : jL - 1728 ≠ 0 := fun h =>
  Polynomial.X_sub_C_ne_zero (1728 : κ) (hjt _ (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_ofNat, h]))

abbrev ΛL (L : Type*) [Field L] : Type _ := Localization.Away (X 0 : MvPolynomial (Fin 4) L)

def iΛL (L : Type*) [Field L] : L →+* ΛL L := (algebraMap (MvPolynomial (Fin 4) L) (ΛL L)).comp C

def yv (L : Type*) [Field L] (n : Fin 4) : ΛL L := algebraMap (MvPolynomial (Fin 4) L) (ΛL L) (X n)

theorem isUnit_yv0 : IsUnit (yv L 0) := IsLocalization.Away.algebraMap_isUnit _

include hjt in
theorem isUnit_jΛL : IsUnit (iΛL L jL) := (isUnit_iff_ne_zero.mpr (jL_ne_zero i jL hjt)).map _

include hjt in
theorem isUnit_jΛL_sub : IsUnit (iΛL L jL - 1728) := by
  have h := (isUnit_iff_ne_zero.mpr (jL_sub_ne_zero i jL hjt)).map (iΛL L)
  rwa [map_sub, map_ofNat] at h

def σ₁ : Λ₅ κ →+* ΛL L :=
  spec5 ((iΛL L).comp i) (iΛL L jL) (yv L 0) (yv L 1) (yv L 2) (yv L 3)
    (isUnit_jΛL i jL hjt) (isUnit_jΛL_sub i jL hjt) (isUnit_yv0 (L := L))

theorem σ₁_evP_eq_zero [Infinite L] (P : P5 κ)
    (hP : ∀ C₀ : VariableChange L, evP i (C₀ • ofJNe0Or1728 jL) P = 0) :
    σ₁ i jL hjt (evP (iΛ₅ κ) (Efam κ) P) = 0 := by
  rw [σ₁, ← evP_spec5]
  refine eq_zero_of_forall_spec_eq_zero _ fun v hv => ?_
  set φ := specAway (X 0 : MvPolynomial (Fin 4) L) (RingHom.id L) v hv with hφ
  have hφi : φ.comp ((iΛL L).comp i) = i := by
    rw [← RingHom.comp_assoc, iΛL, specAway_comp_C, RingHom.id_comp]
  have hφj : φ (iΛL L jL) = jL := specAway_C _ _ _ hv jL
  have hv0 : IsUnit (v 0) := by rwa [eval₂_X] at hv
  have key : ((⟨(isUnit_yv0 (L := L)).unit, yv L 1, yv L 2, yv L 3⟩ : VariableChange (ΛL L)) •
      ofJNe0Or1728 (iΛL L jL)).map φ = (⟨hv0.unit, v 1, v 2, v 3⟩ : VariableChange L) • ofJNe0Or1728 jL := by
    rw [← map_variableChange, ofJNe0Or1728_map, hφj]
    congr 1
    refine VariableChange.ext ?_ ?_ ?_ ?_
    · ext
      rw [VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe]
      exact specAway_X _ _ _ hv 0
    · exact specAway_X _ _ _ hv 1
    · exact specAway_X _ _ _ hv 2
    · exact specAway_X _ _ _ hv 3
  have hmap := evP_map ((iΛL L).comp i)
    ((⟨(isUnit_yv0 (L := L)).unit, yv L 1, yv L 2, yv L 3⟩ : VariableChange (ΛL L)) •
      ofJNe0Or1728 (iΛL L jL)) φ P
  rw [← hmap, hφi, key]
  exact hP _

def g₀ : P5 κ →+* MvPolynomial (Fin 4) L :=
  eval₂Hom (C.comp i) ![C jL, X 0, X 1, X 2, X 3]

include hjt in

theorem g₀_injective : Function.Injective (g₀ i jL) := by
  let θ : Polynomial κ →+* L := Polynomial.eval₂RingHom i jL
  have hθ : Function.Injective θ := (injective_iff_map_eq_zero θ).mpr fun q hq => hjt q hq
  let e : P5 κ ≃ₐ[κ] MvPolynomial (Fin 4) (Polynomial κ) :=
    (MvPolynomial.renameEquiv κ (finSuccEquiv 4)).trans (MvPolynomial.optionEquivRight κ (Fin 4))
  have hfac : g₀ i jL = (MvPolynomial.map θ).comp (e : P5 κ →+* MvPolynomial (Fin 4) (Polynomial κ)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun n => ?_)
    · rw [g₀, eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply]
      show C (i c) = MvPolynomial.map θ (e (C c))
      simp only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, rename_C,
        MvPolynomial.optionEquivRight_C, map_C]
      simp [θ]
    · rw [g₀, eval₂Hom_X', RingHom.comp_apply]
      show _ = MvPolynomial.map θ (e (X n))
      simp only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, rename_X]
      refine Fin.cases ?_ (fun k => ?_) n
      · rw [finSuccEquiv_zero, MvPolynomial.optionEquivRight_X_none, map_C]
        simp [θ]
      · rw [finSuccEquiv_succ, MvPolynomial.optionEquivRight_X_some, map_X]
        fin_cases k <;> rfl
  rw [hfac, RingHom.coe_comp]
  exact (MvPolynomial.map_injective θ hθ).comp e.injective

include hjt in

theorem σ₁_injective : Function.Injective (σ₁ i jL hjt) := by
  refine injective_of_comp_algebraMap (D5 κ) D5_ne_zero _ ?_
  have hcomp : (σ₁ i jL hjt).comp (algebraMap (P5 κ) (Λ₅ κ)) =
      (algebraMap (MvPolynomial (Fin 4) L) (ΛL L)).comp (g₀ i jL) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun n => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, σ₁, spec5, specAway_C, g₀, eval₂Hom_C]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, σ₁, spec5, specAway_X, g₀, eval₂Hom_X']
      fin_cases n <;> rfl
  rw [hcomp, RingHom.coe_comp]
  exact (IsLocalization.injective (ΛL L)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))).comp (g₀_injective i jL hjt)

include hjt in

theorem evP_Efam_eq_zero [Infinite L] (P : P5 κ)
    (hP : ∀ C₀ : VariableChange L, evP i (C₀ • ofJNe0Or1728 jL) P = 0) :
    evP (iΛ₅ κ) (Efam κ) P = 0 :=
  (injective_iff_map_eq_zero _).mp (σ₁_injective i jL hjt) _ (σ₁_evP_eq_zero i jL hjt P hP)

end LemmaA

section LemmaB

variable (κ : Type u) [Field κ]

theorem c₄_poly_ne_zero : (Generic.poly κ).c₄ ≠ 0 := by
  intro h
  have e : ((Generic.poly κ).map (Generic.classify κ (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve κ) :
      MvPolynomial (Fin 5) κ →+* κ)).c₄ = 0 := by rw [map_c₄, h, map_zero]
  rw [Generic.poly_map_classify] at e
  norm_num [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄] at e

theorem c₆_poly_ne_zero : (Generic.poly κ).c₆ ≠ 0 := by
  intro h
  have e : ((Generic.poly κ).map (Generic.classify κ (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve κ) :
      MvPolynomial (Fin 5) κ →+* κ)).c₆ = 0 := by rw [map_c₆, h, map_zero]
  rw [Generic.poly_map_classify] at e
  norm_num [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at e

theorem c₄_curve_ne_zero : (Generic.curve κ).c₄ ≠ 0 := by
  rw [Generic.curve_def, map_c₄]
  exact (map_ne_zero_iff _ (Generic.algebraMap_closure_injective κ)).mpr (c₄_poly_ne_zero κ)

theorem c₆_curve_ne_zero : (Generic.curve κ).c₆ ≠ 0 := by
  rw [Generic.curve_def, map_c₆]
  exact (map_ne_zero_iff _ (Generic.algebraMap_closure_injective κ)).mpr (c₆_poly_ne_zero κ)

theorem j_curve_ne_zero : (Generic.curve κ).j ≠ 0 := by
  rw [WeierstrassCurve.j]
  exact mul_ne_zero (Units.ne_zero _) (pow_ne_zero 3 (c₄_curve_ne_zero κ))

theorem j_curve_sub_ne_zero : (Generic.curve κ).j - 1728 ≠ 0 := by
  set W := Generic.curve κ
  have hΔ : W.Δ ≠ 0 := Generic.Δ_curve_ne_zero κ
  have hrel := W.c_relation
  have hj : W.j * W.Δ = W.c₄ ^ 3 := by
    rw [WeierstrassCurve.j, mul_comm, ← mul_assoc, ← W.coe_Δ', Units.mul_inv, one_mul]
  intro h0
  have : W.c₆ ^ 2 = 0 := by
    have e : (W.j - 1728) * W.Δ = W.c₆ ^ 2 := by rw [sub_mul, hj]; linear_combination -hrel
    rw [h0, zero_mul] at e
    exact e.symm
  exact pow_ne_zero 2 (c₆_curve_ne_zero κ) this

theorem eq_zero_of_evP_Efam_eq_zero (P : P5 κ) (h : evP (iΛ₅ κ) (Efam κ) P = 0) : P = 0 := by
  set Ω' := Generic.Closure κ
  set W := Generic.curve κ
  set jg := W.j with hjg
  haveI h1 : Fact (IsUnit jg) := ⟨isUnit_iff_ne_zero.mpr (j_curve_ne_zero κ)⟩
  haveI h2 : Fact (IsUnit (jg - 1728)) := ⟨isUnit_iff_ne_zero.mpr (j_curve_sub_ne_zero κ)⟩

  have hjeq : (ofJNe0Or1728 jg).j = W.j := ofJNe0Or1728_j jg
  obtain ⟨C₂, hC₂⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hjeq

  have hu : IsUnit (C₂.u : Ω') := Units.isUnit _
  have hspec := evP_spec5 (algebraMap κ Ω') jg (C₂.u : Ω') C₂.r C₂.s C₂.t h1.out h2.out hu P
  rw [h, map_zero] at hspec
  have hC₂' : (⟨hu.unit, C₂.r, C₂.s, C₂.t⟩ : VariableChange Ω') = C₂ :=
    VariableChange.ext (Units.ext rfl) rfl rfl rfl
  rw [hC₂', hC₂] at hspec

  have hev : evP (algebraMap κ Ω') W P = algebraMap (MvPolynomial (Fin 5) κ) Ω' P := by
    have hcf : cf W = fun n => algebraMap (MvPolynomial (Fin 5) κ) Ω' (X n) := by
      funext n; fin_cases n <;> rfl
    rw [evP, hcf, IsScalarTower.algebraMap_eq κ (MvPolynomial (Fin 5) κ) Ω']
    show eval₂Hom _ _ P = _
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun n => ?_)
    · rw [eval₂Hom_C, RingHom.comp_apply, MvPolynomial.algebraMap_eq]
    · rw [eval₂Hom_X']
  rw [hev] at hspec
  exact (injective_iff_map_eq_zero _).mp (Generic.algebraMap_closure_injective κ) P hspec

end LemmaB

section Tate

variable (κ : Type u) [Field κ]

abbrev Cκ : κ →+* LaurentSeries κ := HahnSeries.C

theorem algebraMap_laurent_eq_C (c : κ) : algebraMap κ (LaurentSeries κ) c = Cκ κ c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C]

def CΛ : VariableChange (ΛL (LaurentSeries κ)) :=
  ⟨(isUnit_yv0 (L := LaurentSeries κ)).unit, yv (LaurentSeries κ) 1, yv (LaurentSeries κ) 2,
    yv (LaurentSeries κ) 3⟩

def EΛ : WeierstrassCurve (ΛL (LaurentSeries κ)) := CΛ κ • (tateLaurent κ).map (iΛL (LaurentSeries κ))

def iΛκ : κ →+* ΛL (LaurentSeries κ) := (iΛL (LaurentSeries κ)).comp (Cκ κ)

variable {κ}
variable {Y : Type*} [CommRing Y] (f : LaurentSeries κ →+* Y) (C₁ : VariableChange Y)

theorem isUnit_evalT :
    IsUnit (eval₂ f ![(C₁.u : Y), C₁.r, C₁.s, C₁.t] (X 0 : MvPolynomial (Fin 4) (LaurentSeries κ))) := by
  rw [eval₂_X]; exact Units.isUnit _

def specT : ΛL (LaurentSeries κ) →+* Y :=
  specAway (X 0) f ![(C₁.u : Y), C₁.r, C₁.s, C₁.t] (isUnit_evalT f C₁)

theorem EΛ_map_specT : (EΛ κ).map (specT f C₁) = C₁ • (tateLaurent κ).map f := by
  rw [EΛ, ← map_variableChange, WeierstrassCurve.map_map]
  have hf : (specT f C₁).comp (iΛL (LaurentSeries κ)) = f := specAway_comp_C _ _ _ _
  rw [hf]
  congr 1
  refine VariableChange.ext ?_ ?_ ?_ ?_
  · ext
    rw [VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe]
    exact specAway_X _ _ _ (isUnit_evalT f C₁) 0
  · exact specAway_X _ _ _ (isUnit_evalT f C₁) 1
  · exact specAway_X _ _ _ (isUnit_evalT f C₁) 2
  · exact specAway_X _ _ _ (isUnit_evalT f C₁) 3

theorem evP_specT (P : P5 κ) :
    evP (f.comp (Cκ κ)) (C₁ • (tateLaurent κ).map f) P = specT f C₁ (evP (iΛκ κ) (EΛ κ) P) := by
  rw [← EΛ_map_specT, ← evP_map, iΛκ, ← RingHom.comp_assoc]
  congr 2
  exact (specAway_comp_C _ _ _ (isUnit_evalT f C₁)).symm

end Tate

end ModularCurve.TateDominance

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_algebraicIndependent_variableChange_tateLaurent.ModularCurve ModularCurve.TateDominance MvPolynomial WeierstrassCurve in
theorem solution (κ : Type u) [Field κ]
    (Ω : Type u) [Field Ω] [Algebra κ Ω] [Algebra (LaurentSeries κ) Ω]
    [IsScalarTower κ (LaurentSeries κ) Ω] (C : WeierstrassCurve.VariableChange Ω)
    (hC : AlgebraicIndependent (LaurentSeries κ) ![(C.u : Ω), C.r, C.s, C.t]) :
    AlgebraicIndependent κ
      ![(C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₁,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₂,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₃,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₄,
        (C • (ModularCurve.tateLaurent κ).map (algebraMap (LaurentSeries κ) Ω)).a₆] := by
  set K₀ := LaurentSeries κ
  set fΩ : K₀ →+* Ω := algebraMap K₀ Ω

  have hR1 : fΩ.comp (Cκ κ) = algebraMap κ Ω := by
    ext c
    have h := smul_assoc c (1 : K₀) (1 : Ω)
    rw [one_smul, Algebra.smul_def c (1 : Ω), mul_one, ← HahnSeries.C_mul_eq_smul, mul_one,
      Algebra.smul_def, mul_one] at h
    exact h
  rw [algebraicIndependent_iff]
  intro P hP

  have h0 : evP (fΩ.comp (Cκ κ)) (C • (tateLaurent κ).map fΩ) P = 0 := by
    rw [hR1]; rw [MvPolynomial.aeval_def] at hP; exact hP
  have hΛ : evP (iΛκ κ) (EΛ κ) P = 0 := by
    rw [evP_specT fΩ C P] at h0
    refine (injective_iff_map_eq_zero _).mp ?_ _ h0
    refine injective_of_comp_algebraMap _ (X_ne_zero 0) _ ?_
    have hcomp : ((specT fΩ C).comp (algebraMap (MvPolynomial (Fin 4) K₀) (ΛL K₀)) :
        MvPolynomial (Fin 4) K₀ → Ω) = MvPolynomial.aeval ![(C.u : Ω), C.r, C.s, C.t] := by
      funext p
      rw [RingHom.comp_apply, specT, specAway_algebraMap, MvPolynomial.aeval_def]
    rw [hcomp]
    exact hC

  let L := AlgebraicClosure K₀
  let fL : K₀ →+* L := algebraMap K₀ L
  have hL : ∀ C₁ : VariableChange L, evP (fL.comp (Cκ κ)) (C₁ • (tateLaurent κ).map fL) P = 0 := by
    intro C₁
    rw [evP_specT fL C₁ P, hΛ, map_zero]

  set jL : L := fL (jqModC κ) with hjL
  have hjt : ∀ q : Polynomial κ, q.eval₂ (fL.comp (Cκ κ)) jL = 0 → q = 0 := by
    intro q hq
    rw [hjL, ← Polynomial.hom_eval₂, map_eq_zero_iff _ fL.injective] at hq
    have hinj := transcendental_iff_injective.mp (transcendental_jqModC κ)
    refine (injective_iff_map_eq_zero _).mp hinj q ?_
    rw [Polynomial.aeval_def, show algebraMap κ (LaurentSeries κ) = Cκ κ from RingHom.ext (algebraMap_laurent_eq_C κ)]
    exact hq

  haveI : ((tateLaurent κ).map fL).IsElliptic := inferInstance
  have hjT : ((tateLaurent κ).map fL).j = jL := by rw [map_j, j_tateLaurent]
  haveI hf1 : Fact (IsUnit jL) := ⟨isUnit_iff_ne_zero.mpr (jL_ne_zero _ jL hjt)⟩
  haveI hf2 : Fact (IsUnit (jL - 1728)) := ⟨isUnit_iff_ne_zero.mpr (jL_sub_ne_zero _ jL hjt)⟩
  have hP' : ∀ C₀ : VariableChange L, evP (fL.comp (Cκ κ)) (C₀ • ofJNe0Or1728 jL) P = 0 := by
    intro C₀
    have hj' : ((tateLaurent κ).map fL).j = (C₀ • ofJNe0Or1728 jL).j := by
      rw [hjT, variableChange_j, ofJNe0Or1728_j]
    obtain ⟨C₁, hC₁⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj'
    rw [← hC₁]
    exact hL C₁

  exact eq_zero_of_evP_Efam_eq_zero κ P (evP_Efam_eq_zero (fL.comp (Cκ κ)) jL hjt P hP')

end S_ModularCurve_algebraicIndependent_variableChange_tateLaurent
end P2MW
export P2MW.S_ModularCurve_algebraicIndependent_variableChange_tateLaurent (solution)
