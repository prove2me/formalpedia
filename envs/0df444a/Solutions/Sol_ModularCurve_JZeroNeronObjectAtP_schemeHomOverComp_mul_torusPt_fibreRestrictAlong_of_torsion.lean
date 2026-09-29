-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1444f79a-3cae-5a46-9541-a3ba6f4f4ce2

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.ModularCurve ModularCurve.JZeroNeronObjectAtP"

namespace ToricHeckeAlg

open AddMonoidAlgebra

def IsTorsChar (κ : Type*) [Field κ] {G : Type*} [AddCommGroup G] (F : Multiplicative G →* κ) : Prop :=
  ∃ m : ℕ, (m : κ) ≠ 0 ∧ ∀ v : Multiplicative G, F v ^ m = 1

theorem lift_single_one {κ : Type*} [Field κ] {H : Type*} [AddCommGroup H] (F : Multiplicative H →* κ) (g : H) :
    AddMonoidAlgebra.lift κ κ H F (single g 1) = F (Multiplicative.ofAdd g) := by
  rw [AddMonoidAlgebra.lift_single, one_smul]

end ToricHeckeAlg

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP"
namespace NeronCompare
namespace Tor
p2m_open "ModularCurve"

section plumbing

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t f) (h : L.mul t z z = z) : z = L.one t := by
  letI := L.pointGroup t
  have h' : z * z = z * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel h'

theorem comp_one_eq_one {Y : Scheme.{0}} {g : Y ⟶ Spec (CommRingCat.of R)}
    (LY : RelativeGroupLaw R g) (LX : RelativeGroupLaw R f) (φ : SchemeHomOver g f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (hφ : ∀ x y : SchemeHomOver t g, NeronModelInfra.schemeHomOverComp (LY.mul t x y) φ =
      LX.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    NeronModelInfra.schemeHomOverComp (LY.one t) φ = LX.one t := by
  apply eq_one_of_mul_self
  rw [← hφ, LY.one_mul]

variable {R' : Type} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem fibreRestrictAlong_mul {Y : Scheme.{0}} {g : Y ⟶ Spec (CommRingCat.of R)}
    (LY : RelativeGroupLaw R g) (LX : RelativeGroupLaw R f) (φ : SchemeHomOver g f)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (LY.mul s x y) φ =
        LX.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    NeronModelInfra.schemeHomOverComp ((LY.baseChange ι).mul s x y) (fibreRestrictAlong ι f g φ) =
      (LX.baseChange ι).mul s (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι f g φ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrictAlong ι f g φ)) := by
  apply (RelativeGroupLaw.baseChangePointEquiv ι s).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_mul,
    hφ, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

end plumbing

section torus

variable (S : Type) [Field S] (t : ℕ)

theorem exists_torusPt_eq (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) (torusStr S t)) :
    ∃ χ : torusCoord S t →ₐ[S] S, torusPt S t χ = u := by
  let r : CommRingCat.of (torusCoord S t) ⟶ CommRingCat.of S := Spec.preimage u.1
  have hr : Spec.map r = u.1 := Spec.map_preimage _
  have hcomp : r.hom.comp (algebraMap S (torusCoord S t)) = RingHom.id S := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t)) ≫ r) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, hr, Spec.map_id]; exact u.2
    have := Spec.map_injective h2
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨{ r.hom with commutes' := fun c ↦ ?_ }, ?_⟩
  · exact congrFun (congrArg DFunLike.coe hcomp) c
  · apply Subtype.ext
    change Spec.map _ = u.1
    rw [← hr]
    rfl

theorem torusPt_injective : Function.Injective (torusPt S t) := by
  intro χ χ' h
  have h1 := congrArg Subtype.val h
  change Spec.map (CommRingCat.ofHom χ.toRingHom) = Spec.map (CommRingCat.ofHom χ'.toRingHom) at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  simp only [CommRingCat.hom_ofHom] at h2
  exact AlgHom.ext fun x ↦ congrFun (congrArg DFunLike.coe h2) x

theorem torusPt_comp_specMap (t₀ : ℕ) (χ : torusCoord S t →ₐ[S] S) (E : torusCoord S t₀ →ₐ[S] torusCoord S t)
    (hE : Spec.map (CommRingCat.ofHom E.toRingHom) ≫ torusStr S t₀ = torusStr S t) :
    NeronModelInfra.schemeHomOverComp (torusPt S t χ) (⟨Spec.map (CommRingCat.ofHom E.toRingHom), hE⟩ :
      SchemeHomOver (torusStr S t) (torusStr S t₀)) = torusPt S t₀ (χ.comp E) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom E.toRingHom) =
    Spec.map (CommRingCat.ofHom (χ.comp E).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_algHom_specMap_eq (t₀ : ℕ) (y : SchemeHomOver (torusStr S t) (torusStr S t₀)) :
    ∃ E : torusCoord S t₀ →ₐ[S] torusCoord S t, Spec.map (CommRingCat.ofHom E.toRingHom) = y.1 := by
  let r : CommRingCat.of (torusCoord S t₀) ⟶ CommRingCat.of (torusCoord S t) := Spec.preimage y.1
  have hr : Spec.map r = y.1 := Spec.map_preimage _
  have hcomp : r.hom.comp (algebraMap S (torusCoord S t₀)) = algebraMap S (torusCoord S t) := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t₀)) ≫ r) =
        Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t))) := by
      rw [Spec.map_comp, hr]; exact y.2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ r.hom with commutes' := fun c ↦ ?_ }, ?_⟩
  · exact congrFun (congrArg DFunLike.coe hcomp) c
  · rw [← hr]; rfl

end torus

section conv

variable {S : Type} [Field S] {G : Type} [AddCommGroup G]

theorem convMul_ofConv_single (χ χ' : WithConv (AddMonoidAlgebra S G →ₐ[S] S)) (v : G) :
    (χ * χ').ofConv (AddMonoidAlgebra.single v 1) =
      χ.ofConv (AddMonoidAlgebra.single v 1) * χ'.ofConv (AddMonoidAlgebra.single v 1) := by
  change (χ * χ') (AddMonoidAlgebra.single v 1) = _
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem convMul_lift (F F' : Multiplicative G →* S) :
    (WithConv.toConv (AddMonoidAlgebra.lift S S G F) * WithConv.toConv (AddMonoidAlgebra.lift S S G F')).ofConv =
      AddMonoidAlgebra.lift S S G (F * F') := by
  refine AddMonoidAlgebra.algHom_ext (fun v ↦ ?_) (Subsingleton.elim _ _)
  rw [convMul_ofConv_single]
  change AddMonoidAlgebra.lift S S G F _ * AddMonoidAlgebra.lift S S G F' _ = _
  rw [ToricHeckeAlg.lift_single_one, ToricHeckeAlg.lift_single_one, ToricHeckeAlg.lift_single_one,
    MonoidHom.mul_apply]

def IsTorsPt (χ : AddMonoidAlgebra S G →ₐ[S] S) : Prop :=
  ∃ m : ℕ, (m : S) ≠ 0 ∧ ∀ v : G, χ (AddMonoidAlgebra.single v 1) ^ m = 1

theorem isTorsPt_lift_iff (F : Multiplicative G →* S) :
    IsTorsPt (AddMonoidAlgebra.lift S S G F) ↔ ToricHeckeAlg.IsTorsChar S F := by
  simp only [IsTorsPt, ToricHeckeAlg.IsTorsChar, ToricHeckeAlg.lift_single_one]
  constructor
  · rintro ⟨m, hm, h⟩; exact ⟨m, hm, fun v ↦ by simpa using h (Multiplicative.toAdd v)⟩
  · rintro ⟨m, hm, h⟩; exact ⟨m, hm, fun v ↦ h _⟩

end conv

section fibre2

variable {R : Type} [CommRing R] {C : Scheme.{0}}
  {G G₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}

noncomputable def fibreRestrict₂ {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    SchemeHomOver (pullback.snd g ι) (pullback.snd g₀ ι₀) :=
  ⟨pullback.lift (pullback.fst g ι ≫ Ψ.1) (pullback.snd g ι) (by rw [Category.assoc, Ψ.2, pullback.condition, hι]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem fibreRestrict₂_fst {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    (fibreRestrict₂ hι Ψ).1 ≫ pullback.fst g₀ ι₀ = pullback.fst g ι ≫ Ψ.1 := by
  simp only [fibreRestrict₂, pullback.lift_fst]

@[scoped simp] theorem fibreRestrict₂_snd {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    (fibreRestrict₂ hι Ψ).1 ≫ pullback.snd g₀ ι₀ = pullback.snd g ι := by
  simp only [fibreRestrict₂, pullback.lift_snd]

theorem fibreRestrict₂_rfl (ι : C ⟶ Spec (CommRingCat.of R)) (Ψ : SchemeHomOver g g₀) :
    fibreRestrict₂ (rfl : ι = ι) Ψ = fibreRestrictAlong ι g₀ g Ψ := rfl

end fibre2

section fibre2pts

variable {R R' : Type} [CommRing R] [CommRing R']
  {G G₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}

theorem toBase_comp_fibreRestrict₂ {ι ι₀ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀)
    (Ψ : SchemeHomOver g g₀) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    RelativeGroupLaw.baseChangePointToBase ι₀ (NeronModelInfra.schemeHomOverComp x (fibreRestrict₂ hι Ψ)) =
      castOver (by rw [hι]) (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase ι x) Ψ) := by
  subst hι
  rw [fibreRestrict₂_rfl, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]
  rfl

theorem fibreRestrict₂_mul {ι ι₀ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀)
    (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀) (Ψ : SchemeHomOver g g₀)
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (hΨ : ∀ x y : SchemeHomOver (s ≫ ι) g, NeronModelInfra.schemeHomOverComp (L.mul _ x y) Ψ =
      L₀.mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul s x y) (fibreRestrict₂ hι Ψ) =
      (L₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (fibreRestrict₂ hι Ψ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrict₂ hι Ψ)) := by
  subst hι
  rw [fibreRestrict₂_rfl]
  apply (RelativeGroupLaw.baseChangePointEquiv ι s).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_mul,
    hΨ, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

end fibre2pts

section laws

variable {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}

theorem castOver_mul' (L : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    (a b : SchemeHomOver s g) : castOver h (L.mul s a b) = L.mul s' (castOver h a) (castOver h b) := by
  subst h; rfl

theorem mul_eq_mul_of_eq (L Lc : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)}
    (h : s' = s) (hs : ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b) :
    ∀ a b : SchemeHomOver s' g, L.mul s' a b = Lc.mul s' a b := by
  subst h; exact hs

theorem eq_of_comp_eq {T T' : Scheme.{0}} [IsReduced T] [IsSeparated g] (s : T ⟶ Spec (CommRingCat.of R)) (j : T' ⟶ T) [IsDominant j]
    (a b : SchemeHomOver s g) (h : j ≫ a.1 = j ≫ b.1) : a = b := by
  apply Subtype.ext
  exact ext_of_isDominant_of_isSeparated g (by rw [a.2, b.2]) j h

theorem mul_eq_mul_of_dominant (L Lc : RelativeGroupLaw R g) {T T' : Scheme.{0}} [IsReduced T] [IsSeparated g]
    (s : T ⟶ Spec (CommRingCat.of R)) (j : T' ⟶ T) [IsDominant j]
    (hs : ∀ a b : SchemeHomOver (j ≫ s) g, L.mul _ a b = Lc.mul _ a b) :
    ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b := by
  intro a b
  apply eq_of_comp_eq s j
  have h := congrArg Subtype.val (hs (GoodReductionJacobian.schemeHomOverComp j rfl a) (GoodReductionJacobian.schemeHomOverComp j rfl b))
  rw [← L.mul_natural s (j ≫ s) j rfl, ← Lc.mul_natural s (j ≫ s) j rfl, GoodReductionJacobian.schemeHomOverComp_coe,
    GoodReductionJacobian.schemeHomOverComp_coe] at h
  exact h

theorem isDominant_barPt (A : ValuationSubring (AlgebraicClosure ℚ)) : IsDominant (barPt A) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap A.subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
  exact bot_le

theorem mul_eq_mul_of_pts (L Lc : RelativeGroupLaw R g) {V : Type} [Add V] {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ _}
    (pts : V ≃ SchemeHomOver s g)
    (hL : ∀ v w : V, pts (v + w) = L.mul _ (pts v) (pts w)) (hLc : ∀ v w : V, pts (v + w) = Lc.mul _ (pts v) (pts w)) :
    ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b := by
  intro a b
  obtain ⟨v, rfl⟩ := pts.surjective a
  obtain ⟨w, rfl⟩ := pts.surjective b
  rw [← hL, hLc]

end laws

namespace KRect

abbrev red (t m : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem red_apply (t m : ℕ) (z : Fin t → ℤ) (i : Fin t) : red t m z i = (z i : ZMod m) := rfl

private def _root_.ModularCurve.NeronCompare.Tor.KRect.lift (t m : ℕ) (g : Fin t → ZMod m) : Fin t → ℤ := fun i => ((g i).cast : ℤ)

p2m_export "ModularCurve.NeronCompare.Tor.KRect" "lift"
theorem red_lift (t m : ℕ) [NeZero m] (g : Fin t → ZMod m) : red t m (lift t m g) = g := by
  funext i
  simp [red_apply, lift, ZMod.intCast_zmod_cast]

theorem red_map_eq_of_red_eq (t t' m : ℕ) (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) (z z' : Fin t' → ℤ)
    (h : red t' m z = red t' m z') : red t m (M₀ z) = red t m (M₀ z') := by
  have hd : ∀ i, (m : ℤ) ∣ z i - z' i := by
    intro i
    have hi := congrFun h i
    rw [red_apply, red_apply] at hi
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (z' i) (z i) m).mp hi.symm
  choose w hw using hd
  have hz : z = z' + (m : ℤ) • (fun i => w i) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; have := hw i; omega
  funext i
  rw [red_apply, red_apply, hz, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]

def redHom (t t' m : ℕ) [NeZero m] (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) : (Fin t' → ZMod m) →+ (Fin t → ZMod m) where
  toFun g := red t m (M₀ (lift t' m g))
  map_zero' := by
    have h : red t' m (lift t' m 0) = red t' m 0 := by rw [red_lift, map_zero]
    rw [red_map_eq_of_red_eq t t' m M₀ _ _ h, map_zero, map_zero]
  map_add' g g' := by
    have h : red t' m (lift t' m (g + g')) = red t' m (lift t' m g + lift t' m g') := by
      rw [red_lift, map_add, red_lift, red_lift]
    rw [red_map_eq_of_red_eq t t' m M₀ _ _ h, map_add, map_add]

theorem redHom_red (t t' m : ℕ) [NeZero m] (M₀ : (Fin t' → ℤ) →+ (Fin t → ℤ)) (z : Fin t' → ℤ) :
    redHom t t' m M₀ (red t' m z) = red t m (M₀ z) := by
  show red t m (M₀ (lift t' m (red t' m z))) = red t m (M₀ z)
  apply red_map_eq_of_red_eq
  rw [red_lift]

theorem conv_single {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M : Type} [AddCommMonoid M]
    (χ ψ : WithConv (AddMonoidAlgebra S M →ₐ[S] T)) (g : M) :
    (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) = χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
  rw [AlgHom.convMul_def]
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]

theorem conv_comp_mapDomain {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M N : Type} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) (χ ψ : WithConv (AddMonoidAlgebra S N →ₐ[S] T)) :
    (χ * ψ).ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f) =
      (WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f)) *
        WithConv.toConv (ψ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f))).ofConv := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro g
  rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single, conv_single, conv_single]
  simp only [WithConv.ofConv_toConv, AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]

end KRect

section torsLift

open KRect

noncomputable def charOf {κ : Type} [Field κ] {G : Type} [AddCommGroup G] (χ : AddMonoidAlgebra κ G →ₐ[κ] κ) :
    Multiplicative G →* κ where
  toFun v := χ (AddMonoidAlgebra.single (Multiplicative.toAdd v) 1)
  map_one' := by
    rw [toAdd_one]
    exact map_one χ
  map_mul' a b := by
    rw [toAdd_mul, ← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]

theorem charOf_apply {κ : Type} [Field κ] {G : Type} [AddCommGroup G] (χ : AddMonoidAlgebra κ G →ₐ[κ] κ) (v : Multiplicative G) :
    charOf χ v = χ (AddMonoidAlgebra.single (Multiplicative.toAdd v) 1) := rfl

theorem lift_charOf {κ : Type} [Field κ] {G : Type} [AddCommGroup G] (χ : AddMonoidAlgebra κ G →ₐ[κ] κ) :
    AddMonoidAlgebra.lift κ κ G (charOf χ) = χ :=
  AddMonoidAlgebra.algHom_ext (fun v ↦ by rw [ToricHeckeAlg.lift_single_one, charOf_apply, toAdd_ofAdd])
    (Subsingleton.elim _ _)

theorem exists_monoidHom_comp_red_eq {κ : Type} [Field κ] {t : ℕ} (m : ℕ) [NeZero m]
    (F : Multiplicative (Fin t → ℤ) →* κ) (hF : ∀ w : Fin t → ℤ, F (Multiplicative.ofAdd w) ^ m = 1) :
    ∃ Fb : Multiplicative (Fin t → ZMod m) →* κ, ∀ v, Fb (Multiplicative.ofAdd (red t m v)) = F (Multiplicative.ofAdd v) := by
  classical
  let redM : Multiplicative (Fin t → ℤ) →* Multiplicative (Fin t → ZMod m) := AddMonoidHom.toMultiplicative (red t m)
  let liftM : Multiplicative (Fin t → ZMod m) → Multiplicative (Fin t → ℤ) :=
    fun g ↦ Multiplicative.ofAdd (KRect.lift t m (Multiplicative.toAdd g))
  have hredM : ∀ v : Fin t → ℤ, redM (Multiplicative.ofAdd v) = Multiplicative.ofAdd (red t m v) := fun v ↦ rfl
  have hright : Function.RightInverse liftM redM := by
    intro g
    show redM (Multiplicative.ofAdd (KRect.lift t m (Multiplicative.toAdd g))) = g
    rw [hredM, KRect.red_lift, ofAdd_toAdd]
  have hker : redM.ker ≤ F.toHomUnits.ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, Units.val_one]
    have hv' : red t m (Multiplicative.toAdd v) = 0 := by
      have := congrArg Multiplicative.toAdd hv
      rwa [toAdd_one] at this
    have hdvd : ∀ i, (m : ℤ) ∣ Multiplicative.toAdd v i := by
      intro i
      have := congrFun hv' i
      rw [Pi.zero_apply] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    choose w hw using hdvd
    have hvw : Multiplicative.toAdd v = m • (fun i ↦ w i) := by
      funext i; simp only [Pi.smul_apply, nsmul_eq_mul]; exact hw i
    have : v = Multiplicative.ofAdd (fun i ↦ w i) ^ m := by
      rw [← ofAdd_nsmul, ← hvw, ofAdd_toAdd]
    rw [this, map_pow, hF]
  let Fb' : Multiplicative (Fin t → ZMod m) →* κˣ := MonoidHom.liftOfRightInverse redM liftM hright ⟨F.toHomUnits, hker⟩
  refine ⟨(Units.coeHom κ).comp Fb', fun v ↦ ?_⟩
  rw [← hredM, MonoidHom.comp_apply]
  rw [show Fb' (redM (Multiplicative.ofAdd v)) = F.toHomUnits (Multiplicative.ofAdd v) from
    MonoidHom.liftOfRightInverse_comp_apply redM liftM hright ⟨F.toHomUnits, hker⟩ _]
  rfl

theorem exists_comp_mapDomainAlgHom_red_eq {κ : Type} [Field κ] {t : ℕ} (m : ℕ) [NeZero m]
    (χ : torusCoord κ t →ₐ[κ] κ) (hχ : ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ m = 1) :
    ∃ χb : muCoord κ t m →ₐ[κ] κ, χ = χb.comp (AddMonoidAlgebra.mapDomainAlgHom κ κ (red t m)) := by
  obtain ⟨Fb, hFb⟩ := exists_monoidHom_comp_red_eq m (charOf χ) (fun w ↦ by rw [charOf_apply, toAdd_ofAdd]; exact hχ w)
  refine ⟨AddMonoidAlgebra.lift κ κ _ Fb, AddMonoidAlgebra.algHom_ext (fun v ↦ ?_) (Subsingleton.elim _ _)⟩
  rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
    ToricHeckeAlg.lift_single_one, hFb, charOf_apply, toAdd_ofAdd]

theorem exists_residue_comp_eq_comp_mapRingHom (A : ValuationSubring (AlgebraicClosure ℚ)) {t : ℕ} (m : ℕ) [NeZero m]
    (hm : (m : ResidueField ↥A) ≠ 0) (χb : muCoord (ResidueField ↥A) t m →ₐ[ResidueField ↥A] ResidueField ↥A) :
    ∃ χA : muCoord ↥A t m →ₐ[↥A] ↥A,
      χb.toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue ↥A)) = (residue ↥A).comp χA.toRingHom := by
  classical
  obtain ⟨hinj, hsurj⟩ :=
    ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed (AlgebraicClosure ℚ) A m hm
  let Fb : Multiplicative (Fin t → ZMod m) →* ResidueField ↥A := charOf χb
  have hFbm : ∀ g, Fb g ^ m = 1 := by
    intro g
    have h0 : m • Multiplicative.toAdd g = 0 := funext fun i ↦ by simp [nsmul_eq_mul, ZMod.natCast_self]
    have hg : g ^ m = 1 := by rw [← ofAdd_toAdd g, ← ofAdd_nsmul, h0, ofAdd_zero]
    rw [← map_pow, hg, map_one]
  choose ζ hζm hζ using fun g ↦ hsurj (Fb g) (hFbm g)
  let FA : Multiplicative (Fin t → ZMod m) →* ↥A :=
    { toFun := ζ
      map_one' := hinj _ _ (hζm 1) (one_pow m) (by rw [hζ, map_one, map_one])
      map_mul' := fun g h ↦ hinj _ _ (hζm _) (by rw [mul_pow, hζm, hζm, one_mul])
        (by rw [hζ, map_mul, map_mul, hζ, hζ]) }
  have hFA : ∀ g, residue ↥A (FA g) = Fb g := fun g ↦ hζ g
  refine ⟨AddMonoidAlgebra.lift ↥A ↥A _ FA, ?_⟩
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single]
    change χb (AddMonoidAlgebra.single 0 (residue ↥A b)) = residue ↥A (AddMonoidAlgebra.lift ↥A ↥A _ FA (AddMonoidAlgebra.single 0 b))
    rw [AddMonoidAlgebra.lift_single, ← lift_charOf χb, AddMonoidAlgebra.lift_single, ofAdd_zero, map_one, map_one,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  · intro g
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, map_one]
    change χb (AddMonoidAlgebra.single g 1) = residue ↥A (AddMonoidAlgebra.lift ↥A ↥A _ FA (AddMonoidAlgebra.single g 1))
    rw [AddMonoidAlgebra.lift_single, one_smul, hFA, charOf_apply, toAdd_ofAdd]

end torsLift

section torsPoints

open KRect

theorem ofBase_mul {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) {T : Scheme.{0}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (a b : SchemeHomOver (t' ≫ ι) f) :
    RelativeGroupLaw.baseChangePointOfBase ι (L.mul _ a b) =
      (L.baseChange ι).mul t' (RelativeGroupLaw.baseChangePointOfBase ι a) (RelativeGroupLaw.baseChangePointOfBase ι b) := by
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase]

variable {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}

noncomputable def algCharPt (S B : Type) [CommRing S] [CommRing B] [Algebra S B] (χ : B →ₐ[S] S) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) (Spec.map (CommRingCat.ofHom (algebraMap S B))) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S B) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

@[scoped simp] theorem algCharPt_coe (S B : Type) [CommRing S] [CommRing B] [Algebra S B] (χ : B →ₐ[S] S) :
    (algCharPt S B χ).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) := rfl

theorem torusPt_eq_algCharPt (S : Type) [Field S] (t : ℕ) (χ : torusCoord S t →ₐ[S] S) : torusPt S t χ = algCharPt S _ χ :=
  Subtype.ext rfl

noncomputable def redPt (σ : Spec (CommRingCat.of ↥A) ⟶ base p) (P : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr σ g)) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g) :=
  RelativeGroupLaw.baseChangePointOfBase (resPt A ≫ σ)
    (GoodReductionJacobian.schemeHomOverComp (resPt A) (by rw [Category.id_comp, Category.id_comp])
      (RelativeGroupLaw.baseChangePointToBase σ P))

theorem toBase_redPt (σ : Spec (CommRingCat.of ↥A) ⟶ base p) (P : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr σ g)) :
    (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ σ) (redPt σ P)).1 = resPt A ≫ P.1 ≫ pullback.fst g σ := by
  rw [redPt, RelativeGroupLaw.baseChangePointToBase_ofBase, GoodReductionJacobian.schemeHomOverComp_coe,
    RelativeGroupLaw.baseChangePointToBase_coe]

theorem redPt_mul (σ : Spec (CommRingCat.of ↥A) ⟶ base p) (L : RelativeGroupLaw (baseRing p) g)
    (P Q : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr σ g)) :
    (L.baseChange (resPt A ≫ σ)).mul (𝟙 _) (redPt σ P) (redPt σ Q) = redPt σ ((L.baseChange σ).mul (𝟙 _) P Q) := by
  rw [redPt, redPt, redPt, ← ofBase_mul, RelativeGroupLaw.baseChangePointToBase_mul, L.mul_natural]

theorem redPt_comp (σ : Spec (CommRingCat.of ↥A) ⟶ base p) (Ψ : SchemeHomOver g g₀)
    (P : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr σ g)) :
    NeronModelInfra.schemeHomOverComp (redPt σ P) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ) =
      redPt σ (NeronModelInfra.schemeHomOverComp P (fibreRestrictAlong σ g₀ g Ψ)) := by
  apply (RelativeGroupLaw.baseChangePointEquiv (resPt A ≫ σ) (𝟙 _)).injective
  change RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
  apply Subtype.ext
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, NeronModelInfra.schemeHomOverComp_coe, toBase_redPt,
    toBase_redPt, NeronModelInfra.schemeHomOverComp_coe]
  simp only [Category.assoc, fibreRestrictAlong_coe_comp_fst]

theorem baseChange_mul_of_generic (σ : Spec (CommRingCat.of ↥A) ⟶ base p) [IsSeparated g] [IsSeparated g₀]
    (L Lc : RelativeGroupLaw (baseRing p) g) (L₀ Lc₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    (hΨc : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (Lc.mul s x y) Ψ =
        Lc₀.mul s (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (hL : ∀ a b : SchemeHomOver (barPt A ≫ σ) g, L.mul _ a b = Lc.mul _ a b)
    (hL₀ : ∀ a b : SchemeHomOver (barPt A ≫ σ) g₀, L₀.mul _ a b = Lc₀.mul _ a b)
    (P Q : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr σ g)) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange σ).mul (𝟙 _) P Q) (fibreRestrictAlong σ g₀ g Ψ) =
      (L₀.baseChange σ).mul (𝟙 _) (NeronModelInfra.schemeHomOverComp P (fibreRestrictAlong σ g₀ g Ψ))
        (NeronModelInfra.schemeHomOverComp Q (fibreRestrictAlong σ g₀ g Ψ)) := by
  haveI := isDominant_barPt A
  have h1 : barPt A ≫ 𝟙 _ ≫ σ = barPt A ≫ σ := by rw [Category.id_comp]
  have hLA : ∀ a b : SchemeHomOver (𝟙 _ ≫ σ) g, L.mul _ a b = Lc.mul _ a b :=
    mul_eq_mul_of_dominant L Lc (𝟙 _ ≫ σ) (barPt A) (mul_eq_mul_of_eq L Lc h1 hL)
  have hL₀A : ∀ a b : SchemeHomOver (𝟙 _ ≫ σ) g₀, L₀.mul _ a b = Lc₀.mul _ a b :=
    mul_eq_mul_of_dominant L₀ Lc₀ (𝟙 _ ≫ σ) (barPt A) (mul_eq_mul_of_eq L₀ Lc₀ h1 hL₀)
  have hΨ : ∀ x y : SchemeHomOver (𝟙 _ ≫ σ) g, NeronModelInfra.schemeHomOverComp (L.mul _ x y) Ψ =
      L₀.mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ) := by
    intro x y; rw [hLA, hΨc, hL₀A]
  simpa only [fibreRestrict₂_rfl] using fibreRestrict₂_mul rfl L L₀ Ψ (𝟙 _) hΨ P Q

theorem redPt_muPtA_toricLift (σ : Spec (CommRingCat.of ↥A) ⟶ base p) {t : ℕ} (m : ℕ) [NeZero m]
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (ιm : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (hιm_sp : muBaseChange (residue ↥A) t m ≫ ιm.1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (χ : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A)
    (χb : muCoord (ResidueField ↥A) t m →ₐ[ResidueField ↥A] ResidueField ↥A)
    (hχb : χ = χb.comp (AddMonoidAlgebra.mapDomainAlgHom _ _ (red t m)))
    (χA : muCoord ↥A t m →ₐ[↥A] ↥A)
    (hχA : χb.toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue ↥A)) = (residue ↥A).comp χA.toRingHom) :
    redPt σ (NeronModelInfra.schemeHomOverComp (algCharPt ↥A (muCoord ↥A t m) χA) ιm) =
      NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) t χ) τ := by
  apply (RelativeGroupLaw.baseChangePointEquiv (resPt A ≫ σ) (𝟙 _)).injective
  change RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
  apply Subtype.ext
  rw [toBase_redPt, RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
    NeronModelInfra.schemeHomOverComp_coe, algCharPt_coe]

  have h1 : resPt A ≫ Spec.map (CommRingCat.ofHom χA.toRingHom) =
      Spec.map (CommRingCat.ofHom χb.toRingHom) ≫ muBaseChange (residue ↥A) t m := by
    rw [resPt, muBaseChange, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hχA]

  have h2 : Spec.map (CommRingCat.ofHom χb.toRingHom) ≫ muToTorus (ResidueField ↥A) t m = (torusPt (ResidueField ↥A) t χ).1 := by
    change _ = Spec.map (CommRingCat.ofHom χ.toRingHom)
    rw [muToTorus, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχb]
    rfl
  simp only [Category.assoc]
  rw [← Category.assoc (resPt A), h1, Category.assoc, hιm_sp, ← Category.assoc, h2]

theorem comp_mul_torusPt_of_isTorsPt (σ : Spec (CommRingCat.of ↥A) ⟶ base p) [IsSeparated g] [IsSeparated g₀]
    (L Lc : RelativeGroupLaw (baseRing p) g) (L₀ Lc₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    (hΨc : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (Lc.mul s x y) Ψ =
        Lc₀.mul s (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (hL : ∀ a b : SchemeHomOver (barPt A ≫ σ) g, L.mul _ a b = Lc.mul _ a b)
    (hL₀ : ∀ a b : SchemeHomOver (barPt A ≫ σ) g₀, L₀.mul _ a b = Lc₀.mul _ a b)
    {t : ℕ} (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (ιm : ∀ m : ℕ, 0 < m → SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (hιm_sp : ∀ (m : ℕ) (hm : 0 < m), muBaseChange (residue ↥A) t m ≫ (ιm m hm).1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (χ χ' : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A) (hχ : IsTorsPt χ) (hχ' : IsTorsPt χ') :
    NeronModelInfra.schemeHomOverComp ((L.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ))
        (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ) =
      (L₀.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ))
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ)) := by
  classical
  set κ := ResidueField ↥A with hκ
  obtain ⟨m, hm, hχm⟩ := hχ
  obtain ⟨m', hm', hχm'⟩ := hχ'

  have hM : ((m * m' : ℕ) : κ) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hm hm'
  haveI : NeZero (m * m') := ⟨fun h ↦ hM (by rw [h, Nat.cast_zero])⟩
  have hMpos : 0 < m * m' := Nat.pos_of_ne_zero (NeZero.ne _)
  have hχM : ∀ v, χ (AddMonoidAlgebra.single v 1) ^ (m * m') = 1 := fun v ↦ by rw [pow_mul, hχm, one_pow]
  have hχM' : ∀ v, χ' (AddMonoidAlgebra.single v 1) ^ (m * m') = 1 := fun v ↦ by
    rw [mul_comm, pow_mul, hχm', one_pow]

  obtain ⟨χb, hχb⟩ := exists_comp_mapDomainAlgHom_red_eq (m * m') χ hχM
  obtain ⟨χb', hχb'⟩ := exists_comp_mapDomainAlgHom_red_eq (m * m') χ' hχM'
  obtain ⟨χA, hχA⟩ := exists_residue_comp_eq_comp_mapRingHom A (m * m') hM χb
  obtain ⟨χA', hχA'⟩ := exists_residue_comp_eq_comp_mapRingHom A (m * m') hM χb'

  have hP := redPt_muPtA_toricLift σ (m * m') τ (ιm _ hMpos) (hιm_sp _ hMpos) χ χb hχb χA hχA
  have hQ := redPt_muPtA_toricLift σ (m * m') τ (ιm _ hMpos) (hιm_sp _ hMpos) χ' χb' hχb' χA' hχA'
  rw [← hP, ← hQ, redPt_mul, redPt_comp, baseChange_mul_of_generic σ L Lc L₀ Lc₀ Ψ hΨc hL hL₀, ← redPt_mul,
    ← redPt_comp, ← redPt_comp]

end torsPoints

end ModularCurve.NeronCompare.Tor
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.ModularCurve.NeronCompare P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.ModularCurve.NeronCompare.Tor"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.ModularCurve.NeronCompare"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.ModularCurve"

open ModularCurve.NeronCompare.Tor in
theorem solution
    {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}
    (σ : Spec (CommRingCat.of ↥A) ⟶ base p) [IsSeparated g] [IsSeparated g₀]
    (L Lc : RelativeGroupLaw (baseRing p) g) (L₀ Lc₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    (hΨc : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (Lc.mul s x y) Ψ =
        Lc₀.mul s (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (hL : ∀ a b : SchemeHomOver (barPt A ≫ σ) g, L.mul _ a b = Lc.mul _ a b)
    (hL₀ : ∀ a b : SchemeHomOver (barPt A ≫ σ) g₀, L₀.mul _ a b = Lc₀.mul _ a b)
    {t : ℕ} (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (ιm : ∀ m : ℕ, 0 < m → SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (hιm_sp : ∀ (m : ℕ) (hm : 0 < m), muBaseChange (residue ↥A) t m ≫ (ιm m hm).1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (χ χ' : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A)
    (hχ : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1)
    (hχ' : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ))
        (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ) =
      (L₀.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ))
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ)) := by
  exact comp_mul_torusPt_of_isTorsPt σ L Lc L₀ Lc₀ Ψ hΨc hL hL₀ τ ιm hιm_sp χ χ' hχ hχ'

end S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion (solution)
