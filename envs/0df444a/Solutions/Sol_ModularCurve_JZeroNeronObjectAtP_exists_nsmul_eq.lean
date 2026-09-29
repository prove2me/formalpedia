-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_nsmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3ac09059-eadc-549c-8c4a-0a01f401fb71

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
import Theorems.Thm_AlgebraicGeometry_exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq.GoodReductionJacobian ModularCurve ModularCurve.JZeroNeronObjectAtP"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.baseChangeStr RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointOfBase RelativeGroupLaw.baseChangePointToBase_ofBase RelativeGroupLaw.baseChange_mul RelativeGroupLaw.baseChangePointToBase_one"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative pointGroup mul_assoc one inv one_mul inv_mul_cancel mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over baseChangeStr baseChangePointToBase baseChangePointOfBase baseChangePointToBase_ofBase baseChange baseChange_mul baseChangePointToBase_mul baseChangePointToBase_one fibre"
namespace CH2
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem comp_schemeNsmul (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t f) :
    z.1 ≫ L.schemeNsmul n = (L.nsmul t n z).1 := by
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (idPoint (f := f)) = z :=
    Subtype.ext (Category.comp_id _)
  have key := congrArg Subtype.val (L.nsmul_natural f t z.1 z.2 n idPoint)
  rw [e, GoodReductionJacobian.schemeHomOverComp_coe] at key
  exact key

abbrev nsmulOver (n : ℕ) : SchemeHomOver f f := ⟨L.schemeNsmul n, L.schemeNsmul_over n⟩

theorem nsmul_mul (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x y : SchemeHomOver t f) : L.nsmul t n (L.mul t x y) = L.mul t (L.nsmul t n x) (L.nsmul t n y) := by
  induction n with
  | zero => simp only [nsmul_zero]; exact (L.one_mul t _).symm
  | succ n ih =>
      simp only [nsmul_succ, ih]
      letI := L.pointGroup t
      show (L.nsmul t n x * L.nsmul t n y) * (x * y) = (L.nsmul t n x * x) * (L.nsmul t n y * y)
      rw [_root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (L.nsmul t n y), show L.nsmul t n y * x = x * L.nsmul t n y from hc t _ _,
        _root_.mul_assoc]

theorem isHom_nsmulOver (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.mul t x y) (nsmulOver L n) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (nsmulOver L n)) (NeronModelInfra.schemeHomOverComp y (nsmulOver L n)) := by
  have key : ∀ z : SchemeHomOver t f, NeronModelInfra.schemeHomOverComp z (nsmulOver L n) = L.nsmul t n z :=
    fun z => Subtype.ext (comp_schemeNsmul L n z)
  rw [key, key, key, nsmul_mul L hc]

def reb {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (x : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨x.1, x.2.trans e⟩

theorem nsmul_reb_coe {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (n : ℕ)
    (x : SchemeHomOver s f) : (L.nsmul s' n (reb e x)).1 = (L.nsmul s n x).1 := by
  cases e; rfl

variable {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem baseChangePointToBase_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((L.baseChange ι).nsmul t' n x) = L.nsmul (t' ≫ ι) n (baseChangePointToBase ι x) := by
  induction n with
  | zero => rw [nsmul_zero, nsmul_zero, baseChangePointToBase_one]
  | succ n ih => rw [nsmul_succ, nsmul_succ, baseChangePointToBase_mul, ih]

theorem schemeNsmul_baseChange (n : ℕ) :
    (L.baseChange ι).schemeNsmul n = (NeronSpecialFibreInfra.fibreRestrictAlong ι f f (nsmulOver L n)).1 := by
  apply pullback.hom_ext
  ·
    rw [NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst]
    have h1 : (L.baseChange ι).schemeNsmul n ≫ pullback.fst f ι =
        (L.nsmul (pullback.snd f ι ≫ ι) n (baseChangePointToBase ι (idPoint (f := baseChangeStr ι f)))).1 := by
      rw [← baseChangePointToBase_nsmul]; rfl
    have h2 : pullback.fst f ι ≫ (nsmulOver L n).1 =
        (L.nsmul (pullback.fst f ι ≫ f) n ⟨pullback.fst f ι, rfl⟩).1 :=
      comp_schemeNsmul L n ⟨pullback.fst f ι, rfl⟩
    have h3 : baseChangePointToBase ι (idPoint (f := baseChangeStr ι f)) =
        reb (pullback.condition) ⟨pullback.fst f ι, rfl⟩ :=
      Subtype.ext (Category.id_comp _)
    rw [h1, h2, h3, nsmul_reb_coe]
  · rw [NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd]
    exact (L.baseChange ι).schemeNsmul_over n

theorem isPullback_schemeNsmul_baseChange (n : ℕ) :
    IsPullback ((L.baseChange ι).schemeNsmul n) (pullback.fst f ι) (pullback.fst f ι) (L.schemeNsmul n) := by
  rw [schemeNsmul_baseChange]
  have sq : IsPullback (pullback.snd f ι) (pullback.fst f ι) ι f := (IsPullback.of_hasPullback f ι).flip
  refine IsPullback.of_right (h₁₂ := pullback.snd f ι) (h₂₂ := f) (v₁₃ := ι) ?_ ?_ sq
  · rw [NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd]
    change IsPullback (pullback.snd f ι) (pullback.fst f ι) ι (L.schemeNsmul n ≫ f)
    rw [L.schemeNsmul_over]
    exact sq
  · exact NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst ι f f (nsmulOver L n)

end GoodReductionJacobian.RelativeGroupLaw.CH2

namespace MROOT

theorem eq_one_of_mul_self {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f) (h : L.mul t a a = a) :
    a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h, L.inv_mul_cancel]

theorem mul_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (u v : SchemeHomOver ι f) :
    L.mul ι' (castOver h u) (castOver h v) = castOver h (L.mul ι u v) := by
  subst h; rfl

theorem one_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') :
    L.one ι' = castOver h (L.one ι) := by
  subst h; rfl

theorem nsmul_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (n : ℕ) (u : SchemeHomOver ι f) :
    L.nsmul ι' n (castOver h u) = castOver h (L.nsmul ι n u) := by
  subst h; rfl

theorem overId_eq_castOver {B T X : Scheme.{0}} {ι : T ⟶ B} {f : X ⟶ B} (x : SchemeHomOver ι f) :
    overId x = castOver (Category.id_comp ι).symm x := Subtype.ext rfl

theorem ofFibrePt_one {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) :
    ofFibrePt ((L.baseChange ι).one (𝟙 _)) = L.one ι := by
  apply Subtype.ext
  show (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).one (𝟙 _))).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_one, one_castOver L (Category.id_comp ι).symm]
  rfl

section fib
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}

theorem ofFibrePt_toFibrePt (x : SchemeHomOver ι f) : ofFibrePt (toFibrePt x) = x := by
  apply Subtype.ext
  show (RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι (overId x))).1 = x.1
  rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  rfl

theorem toFibrePt_ofFibrePt (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : toFibrePt (ofFibrePt y) = y := by
  apply Subtype.ext
  apply pullback.hom_ext
  · show pullback.lift (ofFibrePt y).1 (𝟙 _) _ ≫ pullback.fst _ _ = y.1 ≫ pullback.fst _ _
    rw [pullback.lift_fst]
    rfl
  · show pullback.lift (ofFibrePt y).1 (𝟙 _) _ ≫ pullback.snd _ _ = y.1 ≫ pullback.snd _ _
    rw [pullback.lift_snd]
    exact y.2.symm

theorem toFibrePt_injective : Function.Injective (toFibrePt (ι := ι) (f := f)) := fun x y h => by
  rw [← ofFibrePt_toFibrePt x, ← ofFibrePt_toFibrePt y, h]

theorem toFibrePt_one (L : RelativeGroupLaw R f) : toFibrePt (L.one ι) = (L.baseChange ι).one (𝟙 _) := by
  rw [← ofFibrePt_one L, toFibrePt_ofFibrePt]

theorem toFibrePt_mul (L : RelativeGroupLaw R f) (u v : SchemeHomOver ι f) :
    toFibrePt (L.mul ι u v) = (L.baseChange ι).mul (𝟙 _) (toFibrePt u) (toFibrePt v) := by
  rw [RelativeGroupLaw.baseChange_mul]
  show RelativeGroupLaw.baseChangePointOfBase ι (overId (L.mul ι u v)) = _
  rw [toFibrePt, toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase,
    overId_eq_castOver, overId_eq_castOver, overId_eq_castOver, mul_castOver]

theorem toFibrePt_nsmul (L : RelativeGroupLaw R f) (n : ℕ) (u : SchemeHomOver ι f) :
    toFibrePt (L.nsmul ι n u) = (L.baseChange ι).nsmul (𝟙 _) n (toFibrePt u) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, toFibrePt_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, toFibrePt_mul, ih]

end fib

open GoodReductionJacobian.RelativeGroupLaw.CH2 in
theorem main {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {Λ : JZeroNeronObjectAtP.LevelData N₀ p A} (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    {m : ℕ} (hm : 0 < m) (s : SchemeHomOver Λ.σA O.g) :
    ∃ z : SchemeHomOver Λ.σA O.g, O.L.nsmul Λ.σA m z = s := by

  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A

  let ι := Λ.σA
  let LA := O.L.baseChange ι
  haveI : IsSeparated O.g := O.separated
  haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr ι O.g) := inferInstance
  haveI : LocallyOfFiniteType (RelativeGroupLaw.baseChangeStr ι O.g) := inferInstance

  obtain ⟨hLQF, hQC, hFl⟩ :=
    ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange N₀ p hpN₀ A hA Λ hΛ O m hm
  haveI := hLQF
  haveI := hQC
  haveI := hFl
  have hover : LA.schemeNsmul m ≫ RelativeGroupLaw.baseChangeStr ι O.g = RelativeGroupLaw.baseChangeStr ι O.g :=
    LA.schemeNsmul_over m
  haveI : IsSeparated (LA.schemeNsmul m) := by
    haveI : IsSeparated (LA.schemeNsmul m ≫ RelativeGroupLaw.baseChangeStr ι O.g) := by rw [hover]; infer_instance
    exact IsSeparated.of_comp (LA.schemeNsmul m) (RelativeGroupLaw.baseChangeStr ι O.g)
  haveI : LocallyOfFiniteType (LA.schemeNsmul m) := by
    haveI : LocallyOfFiniteType (LA.schemeNsmul m ≫ RelativeGroupLaw.baseChangeStr ι O.g) := by rw [hover]; infer_instance
    exact locallyOfFiniteType_of_comp (LA.schemeNsmul m) (RelativeGroupLaw.baseChangeStr ι O.g)
  haveI hSj : Surjective (LA.schemeNsmul m) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_schemeNsmul_baseChange O.L ι m).flip
      (O.nsmul_surjective m hm)

  let x : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι O.g) := toFibrePt s
  let E := pullback (LA.schemeNsmul m) x.1
  let eStr : E ⟶ Spec (CommRingCat.of ↥A) := pullback.snd (LA.schemeNsmul m) x.1
  haveI : LocallyQuasiFinite eStr := MorphismProperty.pullback_snd (P := @LocallyQuasiFinite) _ _ inferInstance
  haveI : QuasiCompact eStr := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  haveI : Flat eStr := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  haveI : IsSeparated eStr := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : LocallyOfFiniteType eStr := MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  haveI : Surjective eStr := MorphismProperty.pullback_snd (P := @Surjective) _ _ inferInstance
  obtain ⟨e, he⟩ := eStr.surjective (IsLocalRing.closedPoint ↥A)
  obtain ⟨σ, hσ⟩ := AlgebraicGeometry.exists_section_of_flat_of_locallyQuasiFinite_of_henselianLocalRing_of_isAlgClosed
    (↥A) (AlgebraicClosure ℚ) eStr e he

  let zA : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι O.g) :=
    ⟨σ ≫ pullback.fst (LA.schemeNsmul m) x.1, by
      have h1 : pullback.fst (LA.schemeNsmul m) x.1 ≫ RelativeGroupLaw.baseChangeStr ι O.g =
          pullback.snd (LA.schemeNsmul m) x.1 ≫ (x.1 ≫ RelativeGroupLaw.baseChangeStr ι O.g) := by
        calc pullback.fst (LA.schemeNsmul m) x.1 ≫ RelativeGroupLaw.baseChangeStr ι O.g
            = pullback.fst (LA.schemeNsmul m) x.1 ≫ (LA.schemeNsmul m ≫ RelativeGroupLaw.baseChangeStr ι O.g) := by
              rw [LA.schemeNsmul_over]
          _ = (pullback.fst (LA.schemeNsmul m) x.1 ≫ LA.schemeNsmul m) ≫ RelativeGroupLaw.baseChangeStr ι O.g := by
              rw [Category.assoc]
          _ = (pullback.snd (LA.schemeNsmul m) x.1 ≫ x.1) ≫ RelativeGroupLaw.baseChangeStr ι O.g := by
              rw [pullback.condition]
          _ = _ := Category.assoc _ _ _
      rw [Category.assoc, h1, x.2, Category.comp_id, hσ]⟩
  have hzA : LA.nsmul (𝟙 _) m zA = x := by
    apply Subtype.ext
    rw [← comp_schemeNsmul LA m zA]
    show (σ ≫ pullback.fst (LA.schemeNsmul m) x.1) ≫ LA.schemeNsmul m = x.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

  refine ⟨ofFibrePt zA, toFibrePt_injective ?_⟩
  rw [toFibrePt_nsmul, toFibrePt_ofFibrePt, hzA]

end MROOT

end

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (m : ℕ) (hm : 0 < m) (s : SchemeHomOver Λ.σA O.g) :
    ∃ z : SchemeHomOver Λ.σA O.g, O.L.nsmul Λ.σA m z = s := by
  exact MROOT.main hΛ O hm s

end S_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq (solution)
