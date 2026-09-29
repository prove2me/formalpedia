-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_flat_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bf02e3c6-a99e-56ad-97c7-3f521b7fe5d2

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_unit nsmul_natural idPoint schemeNsmul schemeNsmul_over IsCommutative pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

theorem schemeHomOverComp_mk {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ rfl x).1 = ψ ≫ x.1 := rfl

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h1 : schemeHomOverComp ψ hψ (G.inv t x) * schemeHomOverComp ψ hψ x = 1 := by
    show G.mul t' _ _ = G.one t'
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  have h2 : G.inv t' (schemeHomOverComp ψ hψ x) * schemeHomOverComp ψ hψ x = 1 :=
    G.inv_mul_cancel t' _
  exact mul_right_cancel (h1.trans h2.symm)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "inv_natural"

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := by
    apply Subtype.ext
    simp [schemeHomOverComp]
  have := G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hx] at this
  rw [← this]
  rfl

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul_coe"

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_mul (hc : G.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x y : SchemeHomOver t f) : G.nsmul t n (G.mul t x y) = G.mul t (G.nsmul t n x) (G.nsmul t n y) := by
  induction n with
  | zero => simp only [nsmul_zero]; exact (G.one_mul t _).symm
  | succ n ih =>
      simp only [nsmul_succ, ih]

      letI := G.pointGroup t
      show (G.nsmul t n x * G.nsmul t n y) * (x * y) = (G.nsmul t n x * x) * (G.nsmul t n y * y)
      have hcomm : ∀ a b : SchemeHomOver t f, a * b = b * a := fun a b => hc t a b
      rw [_root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (G.nsmul t n y), hcomm (G.nsmul t n y) x, _root_.mul_assoc]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul_mul"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_inv (hc : G.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : G.nsmul t n (G.inv t x) = G.inv t (G.nsmul t n x) := by
  letI := G.pointGroup t
  have h : G.mul t (G.nsmul t n (G.inv t x)) (G.nsmul t n x) = G.one t := by
    rw [← G.nsmul_mul hc, G.inv_mul_cancel, G.nsmul_unit]
  have h2 : G.mul t (G.inv t (G.nsmul t n x)) (G.nsmul t n x) = G.one t := G.inv_mul_cancel t _
  exact mul_right_cancel (h.trans h2.symm : (_ : SchemeHomOver t f) * _ = _ * _)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul_inv"

section Shear

noncomputable abbrev prBase : pullback f f ⟶ Spec (CommRingCat.of R) := pullback.fst f f ≫ f

noncomputable abbrev ptFst : SchemeHomOver (prBase (f := f)) f := ⟨pullback.fst f f, rfl⟩

noncomputable abbrev ptSnd : SchemeHomOver (prBase (f := f)) f := ⟨pullback.snd f f, pullback.condition.symm⟩

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.mulHom : pullback f f ⟶ A := (G.mul prBase ptFst ptSnd).1

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mulHom"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.mulHom_comp : G.mulHom ≫ f = prBase := (G.mul prBase ptFst ptSnd).2

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mulHom_comp"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.shear : pullback f f ⟶ pullback f f :=
  pullback.lift G.mulHom (pullback.snd f f) (by rw [G.mulHom_comp]; exact pullback.condition)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "shear"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.shearInv : pullback f f ⟶ pullback f f :=
  pullback.lift (G.mul prBase ptFst (G.inv prBase ptSnd)).1 (pullback.snd f f)
    (by rw [(G.mul prBase ptFst (G.inv prBase ptSnd)).2]; exact pullback.condition)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "shearInv"
@[scoped simp] theorem shear_fst : G.shear ≫ pullback.fst f f = G.mulHom := pullback.lift_fst _ _ _
@[scoped simp] theorem shear_snd : G.shear ≫ pullback.snd f f = pullback.snd f f := pullback.lift_snd _ _ _
@[scoped simp] theorem shearInv_fst : G.shearInv ≫ pullback.fst f f = (G.mul prBase ptFst (G.inv prBase ptSnd)).1 :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem shearInv_snd : G.shearInv ≫ pullback.snd f f = pullback.snd f f := pullback.lift_snd _ _ _

theorem comp_mul_val {S : Scheme.{u}} (s : S ⟶ pullback f f) (x y : SchemeHomOver (prBase (f := f)) f) :
    s ≫ (G.mul prBase x y).1 = (G.mul (s ≫ prBase) (schemeHomOverComp s rfl x) (schemeHomOverComp s rfl y)).1 := by
  have := congrArg Subtype.val (G.mul_natural prBase (s ≫ prBase) s rfl x y)
  simpa only [schemeHomOverComp_coe] using this

theorem comp_inv_val {S : Scheme.{u}} (s : S ⟶ pullback f f) (x : SchemeHomOver (prBase (f := f)) f) :
    s ≫ (G.inv prBase x).1 = (G.inv (s ≫ prBase) (schemeHomOverComp s rfl x)).1 := by
  have := congrArg Subtype.val (G.inv_natural prBase (s ≫ prBase) s rfl x)
  simpa only [schemeHomOverComp_coe] using this

end Shear

section Translate

variable {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver s f)

noncomputable abbrev qBase : pullback s f ⟶ Spec (CommRingCat.of R) := pullback.fst s f ≫ s

noncomputable abbrev qA : SchemeHomOver (qBase s (f := f)) f :=
  schemeHomOverComp (pullback.fst s f) rfl a

noncomputable abbrev qY : SchemeHomOver (qBase s (f := f)) f :=
  ⟨pullback.snd s f, pullback.condition.symm⟩

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.translate : pullback s f ⟶ pullback s f :=
  pullback.lift (pullback.fst s f) (G.mul (qBase s) (qA s a) (qY s)).1
    (by rw [(G.mul (qBase s) (qA s a) (qY s)).2])

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "translate"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.translateInv : pullback s f ⟶ pullback s f :=
  pullback.lift (pullback.fst s f) (G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s)).1
    (by rw [(G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s)).2])

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "translateInv"
@[scoped simp] theorem translate_fst : G.translate s a ≫ pullback.fst s f = pullback.fst s f := pullback.lift_fst _ _ _
@[scoped simp] theorem translate_snd : G.translate s a ≫ pullback.snd s f = (G.mul (qBase s) (qA s a) (qY s)).1 :=
  pullback.lift_snd _ _ _
@[scoped simp] theorem translateInv_fst : G.translateInv s a ≫ pullback.fst s f = pullback.fst s f := pullback.lift_fst _ _ _
@[scoped simp] theorem translateInv_snd : G.translateInv s a ≫ pullback.snd s f =
    (G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s)).1 := pullback.lift_snd _ _ _

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.comp_mul_val' {S' : Scheme.{u}} (r : S' ⟶ pullback s f) (t' : S' ⟶ Spec (CommRingCat.of R))
    (hr : r ≫ qBase s = t') (x y : SchemeHomOver (qBase s (f := f)) f) :
    r ≫ (G.mul (qBase s) x y).1 =
      (G.mul t' (schemeHomOverComp r hr x) (schemeHomOverComp r hr y)).1 := by
  simpa only [schemeHomOverComp_coe] using congrArg Subtype.val (G.mul_natural (qBase s) t' r hr x y)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "comp_mul_val'"
theorem comp_inv_val' {S' : Scheme.{u}} (r : S' ⟶ pullback s f) (t' : S' ⟶ Spec (CommRingCat.of R))
    (hr : r ≫ qBase s = t') (x : SchemeHomOver (qBase s (f := f)) f) :
    r ≫ (G.inv (qBase s) x).1 = (G.inv t' (schemeHomOverComp r hr x)).1 := by
  simpa only [schemeHomOverComp_coe] using congrArg Subtype.val (G.inv_natural (qBase s) t' r hr x)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translate_base : G.translate s a ≫ qBase s = qBase s := by
  rw [← Category.assoc, translate_fst]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "translate_base"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translateInv_base : G.translateInv s a ≫ qBase s = qBase s := by
  rw [← Category.assoc, translateInv_fst]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "translateInv_base"
theorem translate_qA : schemeHomOverComp (G.translate s a) (G.translate_base s a) (qA s a) = qA s a := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe]
  rw [← Category.assoc, translate_fst]

theorem translate_qY : schemeHomOverComp (G.translate s a) (G.translate_base s a) (qY s) =
    G.mul (qBase s) (qA s a) (qY s) := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe, translate_snd]

theorem translateInv_qA : schemeHomOverComp (G.translateInv s a) (G.translateInv_base s a) (qA s a) = qA s a := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe]
  rw [← Category.assoc, translateInv_fst]

theorem translateInv_qY : schemeHomOverComp (G.translateInv s a) (G.translateInv_base s a) (qY s) =
    G.mul (qBase s) (G.inv (qBase s) (qA s a)) (qY s) := by
  apply Subtype.ext
  simp only [schemeHomOverComp_coe, translateInv_snd]

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translate_translateInv : G.translate s a ≫ G.translateInv s a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, translateInv_snd, G.comp_mul_val' s _ _ (G.translate_base s a), Category.id_comp]
    have hinv : schemeHomOverComp (G.translate s a) (G.translate_base s a) (G.inv (qBase s) (qA s a)) =
        G.inv (qBase s) (qA s a) := by
      rw [G.inv_natural _ _ _ (G.translate_base s a), translate_qA]
    rw [hinv, translate_qY]
    letI := G.pointGroup (qBase s (f := f))
    show ((qA s a)⁻¹ * (qA s a * qY s) : SchemeHomOver (qBase s (f := f)) f).1 = _
    rw [inv_mul_cancel_left]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "translate_translateInv"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.translateInv_translate : G.translateInv s a ≫ G.translate s a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [Category.assoc, translate_snd, G.comp_mul_val' s _ _ (G.translateInv_base s a), Category.id_comp,
      translateInv_qA, translateInv_qY]
    letI := G.pointGroup (qBase s (f := f))
    show ((qA s a) * ((qA s a)⁻¹ * qY s) : SchemeHomOver (qBase s (f := f)) f).1 = _
    rw [mul_inv_cancel_left]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "translateInv_translate"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.translateIso : pullback s f ≅ pullback s f :=
  ⟨G.translate s a, G.translateInv s a, G.translate_translateInv s a, G.translateInv_translate s a⟩

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "translateIso"
end Translate

section C4

variable {k : Type u} [Field k] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k g)

private noncomputable abbrev _root_.GoodReductionJacobian.RelativeGroupLaw.unitSec : Spec (CommRingCat.of k) ⟶ B := (L.one (𝟙 _)).1
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "unitSec"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.unitSec_comp : L.unitSec ≫ g = 𝟙 _ := (L.one (𝟙 _)).2

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "unitSec_comp"

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.unitSec_schemeNsmul (n : ℕ) : L.unitSec ≫ L.schemeNsmul n = L.unitSec := by
  have := congrArg Subtype.val (L.nsmul_unit (𝟙 _) n)
  rw [L.nsmul_coe] at this
  exact this

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "unitSec_schemeNsmul"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.pairUnit : B ⟶ pullback g g :=
  pullback.lift (𝟙 B) (g ≫ L.unitSec) (by rw [Category.assoc, L.unitSec_comp]; simp)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pairUnit"
@[scoped simp] theorem pairUnit_fst : L.pairUnit ≫ pullback.fst g g = 𝟙 B := pullback.lift_fst _ _ _
@[scoped simp] theorem pairUnit_snd : L.pairUnit ≫ pullback.snd g g = g ≫ L.unitSec := pullback.lift_snd _ _ _

theorem pairUnit_mulHom : L.pairUnit ≫ L.mulHom = 𝟙 B := by
  have hpu : L.pairUnit ≫ qBase g (f := g) = g := by
    show L.pairUnit ≫ pullback.fst g g ≫ g = g
    rw [← Category.assoc, pairUnit_fst, Category.id_comp]
  rw [mulHom, L.comp_mul_val' g L.pairUnit g hpu]
  have h1 : schemeHomOverComp L.pairUnit hpu (ptFst (f := g)) = (⟨𝟙 B, Category.id_comp g⟩ : SchemeHomOver g g) := by
    apply Subtype.ext; simp [schemeHomOverComp]
  have h2 : schemeHomOverComp L.pairUnit hpu (ptSnd (f := g)) = L.one g := by
    rw [← L.one_natural (𝟙 _) g g (Category.comp_id g)]
    apply Subtype.ext; simp [schemeHomOverComp]
  rw [h1, h2, L.mul_one]

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.symmetry_mulHom (hc : L.IsCommutative) : (pullbackSymmetry g g).hom ≫ L.mulHom = L.mulHom := by
  have hσ : (pullbackSymmetry g g).hom ≫ qBase g (f := g) = qBase g (f := g) := by
    show (pullbackSymmetry g g).hom ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]; exact pullback.condition.symm
  rw [mulHom, L.comp_mul_val' g _ _ hσ]
  have h1 : schemeHomOverComp (pullbackSymmetry g g).hom hσ (ptFst (f := g)) = ptSnd := by
    apply Subtype.ext; simp [schemeHomOverComp]
  have h2 : schemeHomOverComp (pullbackSymmetry g g).hom hσ (ptSnd (f := g)) = ptFst := by
    apply Subtype.ext; simp [schemeHomOverComp]
  rw [h1, h2, hc]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "symmetry_mulHom"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nn_cond (n : ℕ) : g ≫ 𝟙 (Spec (CommRingCat.of k)) = L.schemeNsmul n ≫ g := by
  rw [Category.comp_id, L.schemeNsmul_over]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nn_cond"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.nn (n : ℕ) : pullback g g ⟶ pullback g g :=
  pullback.map g g g g (L.schemeNsmul n) (L.schemeNsmul n) (𝟙 _) (L.nn_cond n) (L.nn_cond n)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nn"
@[scoped simp] theorem nn_fst (n : ℕ) : L.nn n ≫ pullback.fst g g = pullback.fst g g ≫ L.schemeNsmul n :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem nn_snd (n : ℕ) : L.nn n ≫ pullback.snd g g = pullback.snd g g ≫ L.schemeNsmul n :=
  pullback.lift_snd _ _ _

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.range_nn (n : ℕ) : Set.range (L.nn n) =
    pullback.fst g g ⁻¹' Set.range (L.schemeNsmul n) ∩ pullback.snd g g ⁻¹' Set.range (L.schemeNsmul n) :=
  Scheme.Pullback.range_map g g g g _ _ (𝟙 _) (L.nn_cond n) (L.nn_cond n)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "range_nn"

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nn_translateInv (hc : L.IsCommutative) (n : ℕ) :
    L.nn n ≫ L.translateInv g idPoint = L.translateInv g idPoint ≫ L.nn n := by
  have hb : L.nn n ≫ qBase g = qBase g (f := g) := by
    show L.nn n ≫ pullback.fst g g ≫ g = pullback.fst g g ≫ g
    rw [← Category.assoc, nn_fst, Category.assoc, L.schemeNsmul_over]
  have hA : schemeHomOverComp (L.nn n) hb (qA g idPoint) = L.nsmul _ n (qA g (f := g) idPoint) := by
    apply Subtype.ext
    rw [L.nsmul_coe]; simp [schemeHomOverComp, idPoint]
  have hY : schemeHomOverComp (L.nn n) hb (qY g) = L.nsmul _ n (qY g (f := g)) := by
    apply Subtype.ext
    rw [L.nsmul_coe]; simp [schemeHomOverComp]
  apply pullback.hom_ext
  · rw [Category.assoc, translateInv_fst, Category.assoc, nn_fst, ← Category.assoc, translateInv_fst]
  · rw [Category.assoc, translateInv_snd, L.comp_mul_val' g _ _ hb, L.inv_natural _ _ _ hb, hA, hY,
      Category.assoc, nn_snd, ← Category.assoc, translateInv_snd, ← L.nsmul_coe, L.nsmul_mul hc, L.nsmul_inv hc]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nn_translateInv"

theorem translate_id_snd : L.translate g idPoint ≫ pullback.snd g g = L.mulHom := by
  rw [translate_snd, mulHom]
  have : qA g (f := g) idPoint = ptFst := Subtype.ext (by simp [schemeHomOverComp, idPoint])
  rw [this]

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_flat_of_field'
    [LocallyOfFiniteType g] [IrreducibleSpace B] (hc : L.IsCommutative) (n : ℕ)
    [Flat (L.schemeNsmul n)] : Surjective (L.schemeNsmul n) := by
  classical
  set N := L.schemeNsmul n with hNdef

  haveI : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : LocallyOfFiniteType (N ≫ g) := by rw [hNdef, L.schemeNsmul_over]; infer_instance
  haveI : LocallyOfFiniteType N := locallyOfFiniteType_of_comp N g
  haveI : UniversallyOpen N := inferInstance
  let U : Set B := Set.range N
  have hUopen : IsOpen U := N.isOpenMap.isOpen_range
  have hUne : U.Nonempty := Set.range_nonempty _

  have he : ∀ b : B, L.unitSec (g b) ∈ U := fun b =>
    ⟨L.unitSec (g b), by rw [← Scheme.Hom.comp_apply, L.unitSec_schemeNsmul]⟩

  have hkey : ∀ w : ↑(pullback g g), pullback.fst g g w ∈ U → pullback.snd g g w ∉ U → L.mulHom w ∉ U := by
    intro w h1 h2 hμ

    have hτ : L.translate g idPoint w ∈ Set.range (L.nn n) := by
      rw [L.range_nn]
      refine ⟨?_, ?_⟩
      · show pullback.fst g g (L.translate g idPoint w) ∈ U
        rw [← Scheme.Hom.comp_apply, translate_fst]; exact h1
      · show pullback.snd g g (L.translate g idPoint w) ∈ U
        rw [← Scheme.Hom.comp_apply, translate_id_snd]; exact hμ
    obtain ⟨w', hw'⟩ := hτ
    apply h2

    have hw : w = L.nn n (L.translateInv g idPoint w') := by
      have h1 : (L.translate g idPoint ≫ L.translateInv g idPoint) w = w := by
        rw [L.translate_translateInv]; rfl
      rw [Scheme.Hom.comp_apply, ← hw', ← Scheme.Hom.comp_apply, L.nn_translateInv hc,
        Scheme.Hom.comp_apply] at h1
      exact h1.symm
    refine ⟨pullback.snd g g (L.translateInv g idPoint w'), ?_⟩
    conv_rhs => rw [hw, ← Scheme.Hom.comp_apply, nn_snd, Scheme.Hom.comp_apply]

  have hkey' : ∀ w : ↑(pullback g g), pullback.fst g g w ∉ U → pullback.snd g g w ∈ U → L.mulHom w ∉ U := by
    intro w h1 h2
    have := hkey ((pullbackSymmetry g g).hom w) (by rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst])
      (by rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd])
    rwa [← Scheme.Hom.comp_apply, L.symmetry_mulHom hc] at this

  have htrans : ∀ z : B, z ∉ U → ∃ V : Set B, IsOpen V ∧ z ∈ V ∧ V ⊆ Uᶜ := by
    intro z hz
    let ι := B.fromSpecResidueField z
    let Q := pullback (ι ≫ g) g
    let m : Q ⟶ pullback g g := pullback.map (ι ≫ g) g g g ι (𝟙 B) (𝟙 _) (by simp) (by simp)
    have hm1 : m ≫ pullback.fst g g = pullback.fst (ι ≫ g) g ≫ ι := pullback.lift_fst _ _ _
    have hm2 : m ≫ pullback.snd g g = pullback.snd (ι ≫ g) g := by
      rw [pullback.lift_snd, Category.comp_id]

    have hmμ : m ≫ L.mulHom = L.translate (ι ≫ g) ⟨ι, rfl⟩ ≫ pullback.snd (ι ≫ g) g := by
      rw [translate_snd, mulHom, L.comp_mul_val' g m (qBase (ι ≫ g) (f := g))
        (by rw [← Category.assoc, hm1, Category.assoc])]
      congr 1
      all_goals (apply Subtype.ext; simp [schemeHomOverComp, hm1, hm2])

    haveI : UniversallyOpen (ι ≫ g) := inferInstance
    have hsnd : IsOpenMap (pullback.snd (ι ≫ g) g) := (pullback.snd (ι ≫ g) g).isOpenMap
    let τh := Scheme.homeoOfIso (L.translateIso (ι ≫ g) ⟨ι, rfl⟩)
    refine ⟨(m ≫ L.mulHom) '' ((pullback.snd (ι ≫ g) g) ⁻¹' U), ?_, ?_, ?_⟩
    · rw [hmμ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      refine hsnd _ ?_
      have : (L.translate (ι ≫ g) ⟨ι, rfl⟩ : Q ⟶ Q) '' (pullback.snd (ι ≫ g) g ⁻¹' U) =
          τh '' (pullback.snd (ι ≫ g) g ⁻¹' U) := rfl
      rw [this]
      exact τh.isOpenMap _ (hUopen.preimage (pullback.snd (ι ≫ g) g).continuous)
    ·
      let j : Spec (B.residueField z) ⟶ Q := pullback.lift (𝟙 _) (ι ≫ g ≫ L.unitSec)
        (by rw [Category.id_comp, Category.assoc, Category.assoc, L.unitSec_comp, Category.comp_id])
      have hjm : j ≫ m = ι ≫ L.pairUnit := by
        apply pullback.hom_ext
        · rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_fst, Category.id_comp, Category.assoc,
            pairUnit_fst, Category.comp_id]
        · rw [Category.assoc, hm2, pullback.lift_snd, Category.assoc, pairUnit_snd]
      refine ⟨j (IsLocalRing.closedPoint _), ?_, ?_⟩
      · show pullback.snd (ι ≫ g) g (j (IsLocalRing.closedPoint _)) ∈ U
        rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact he _
      · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hjm, Category.assoc, pairUnit_mulHom, Category.comp_id,
          Scheme.fromSpecResidueField_apply]
    · rintro _ ⟨q, hq, rfl⟩ hU'
      refine hkey' (m q) ?_ ?_ (by rwa [Scheme.Hom.comp_apply] at hU')
      · rw [← Scheme.Hom.comp_apply, hm1, Scheme.Hom.comp_apply]
        have : ι (pullback.fst (ι ≫ g) g q) = z := by
          have := Scheme.range_fromSpecResidueField z
          exact (Set.range_subset_iff.mp (le_of_eq this) : ∀ _, _) _ |> Set.mem_singleton_iff.mp
        rw [this]; exact hz
      · rw [← Scheme.Hom.comp_apply, hm2]; exact hq

  have hUc : IsOpen Uᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V, hV, hzV, hVU⟩ := htrans z hz
    exact ⟨V, hVU, hV, hzV⟩
  have hclopen : IsClopen U := ⟨⟨hUc⟩, hUopen⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact absurd h hUne.ne_empty
  · exact ⟨fun b => by have : b ∈ U := h ▸ Set.mem_univ b; exact this⟩

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "surjective_schemeNsmul_of_flat_of_field'"
end C4

end GoodReductionJacobian.RelativeGroupLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.GoodReductionJacobian"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.GoodReductionJacobian in

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [IrreducibleSpace A]
    (G : RelativeGroupLaw k f)
    (hc : G.IsCommutative)
    (n : ℕ) [Flat (G.schemeNsmul n)] :
    Surjective (G.schemeNsmul n) :=
  G.surjective_schemeNsmul_of_flat_of_field' hc n

end S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field (solution)
