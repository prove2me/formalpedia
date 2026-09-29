-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a589d3d5-3b00-5813-bd95-e987fbb738ff

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_genericFibreStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve.JHNeronObjectAtP"

universe u

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP infSubgroup JH"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "Fbar LevelData ptsSp pts surjective g separated G smooth L"
namespace RedLambda
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

section Tate

variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [AddCommGroup N]

noncomputable def tmap (f : M →+ N) : TateModule p M →ₗ[ℤ_[p]] TateModule p N where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero], by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change f (((x + y : TateModule p M) : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    change f (((a • x : TateModule p M) : ℕ → M) n) = (((a • ⟨fun n => f ((x : ℕ → M) n), _⟩ : TateModule p N)) : ℕ → N) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp]
theorem tmap_apply_coe (f : M →+ N) (x : TateModule p M) (n : ℕ) :
    ((tmap f x : TateModule p N) : ℕ → N) n = f ((x : ℕ → M) n) := rfl

theorem tmap_injective (f : M →+ N)
    (hinj : ∀ (m : ℕ) (x : M), ((p ^ m : ℕ) : ℤ) • x = 0 → f x = 0 → x = 0) :
    Function.Injective (tmap (p := p) f) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext (funext fun n => ?_)
  have h := congrArg (fun y : TateModule p N => (y : ℕ → N) n) hx
  simp only [tmap_apply_coe, TateModule.coe_zero, Pi.zero_apply] at h
  exact hinj n _ (TateModule.torsion x n) h

theorem tmap_surjective (f : M →+ N)
    (hinj : ∀ (m : ℕ) (x : M), ((p ^ m : ℕ) : ℤ) • x = 0 → f x = 0 → x = 0)
    (hsurj : ∀ (n : ℕ) (y : N), ((p ^ n : ℕ) : ℤ) • y = 0 → ∃ (m : ℕ) (x : M), ((p ^ m : ℕ) : ℤ) • x = 0 ∧ f x = y) :
    Function.Surjective (tmap (p := p) f) := fun Y => by
  have hpre : ∀ n, ∃ x : M, (∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • x = 0) ∧ f x = (Y : ℕ → N) n := fun n => by
    obtain ⟨m, x, hxm, hfx⟩ := hsurj n _ (TateModule.torsion Y n)
    exact ⟨x, ⟨m, hxm⟩, hfx⟩
  choose x hxtor hfx using hpre
  have hkill : ∀ y : M, (∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • y = 0) → f y = 0 → y = 0 :=
    fun y ⟨m, hm⟩ hfy => hinj m y hm hfy
  have htors : ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 := fun n => by
    obtain ⟨m, hm⟩ := hxtor n
    refine hkill _ ⟨m, by rw [smul_comm, hm, smul_zero]⟩ ?_
    rw [map_zsmul, hfx, TateModule.torsion]
  have hcompat : ∀ n, ((p : ℕ) : ℤ) • x (n + 1) = x n := fun n => by
    rw [← sub_eq_zero]
    obtain ⟨m, hm⟩ := hxtor (n + 1)
    obtain ⟨m', hm'⟩ := hxtor n
    refine hkill _ ⟨m + m', ?_⟩ ?_
    · have h1 : ((p ^ (m + m') : ℕ) : ℤ) • (((p : ℕ) : ℤ) • x (n + 1)) = 0 := by
        rw [smul_comm, pow_add, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero, smul_zero]
      have h2 : ((p ^ (m + m') : ℕ) : ℤ) • x n = 0 := by
        rw [pow_add, Nat.cast_mul, mul_smul, hm', smul_zero]
      rw [smul_sub, h1, h2, sub_zero]
    · rw [map_sub, map_zsmul, hfx, hfx, TateModule.compat, sub_self]
  exact ⟨⟨x, fun n => ⟨htors n, hcompat n⟩⟩, Subtype.ext (funext fun n => by rw [tmap_apply_coe, hfx])⟩

end Tate

theorem ofFibrePt_baseChange_mul_toFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (x y : SchemeHomOver ι f) :
    ofFibrePt ((L.baseChange ι).mul (𝟙 _) (toFibrePt x) (toFibrePt y)) = L.mul ι x y := by
  apply Subtype.ext
  change (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).mul (𝟙 _) (toFibrePt x) (toFibrePt y))).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul]
  have hx : RelativeGroupLaw.baseChangePointToBase ι (toFibrePt x) = schemeHomOverComp (𝟙 _) rfl x := by
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact Subtype.ext (Category.id_comp _).symm
  have hy : RelativeGroupLaw.baseChangePointToBase ι (toFibrePt y) = schemeHomOverComp (𝟙 _) rfl y := by
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact Subtype.ext (Category.id_comp _).symm
  rw [hx, hy, ← L.mul_natural ι (𝟙 _ ≫ ι) (𝟙 _) rfl x y, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

theorem RelativeGroupLaw.eq_one_of_mul_self {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : L.mul t x x = x) : x = L.one t := by
  symm
  calc L.one t = L.mul t (L.inv t x) x := (L.inv_mul_cancel t x).symm
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [h]
    _ = L.mul t (L.mul t (L.inv t x) x) x := (L.mul_assoc t _ _ _).symm
    _ = L.mul t (L.one t) x := by rw [L.inv_mul_cancel]
    _ = x := L.one_mul t _

variable {p M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem valuativeCriterion (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f) :
    ValuativeCriterion Λ.f := by
  have hprop : IsProper Λ.f := hΛ.proper
  have h := congrFun (congrFun (congrFun AlgebraicGeometry.IsProper.eq_valuativeCriterion _) _) Λ.f
  rw [h] at hprop
  exact hprop.1.1.1

theorem exists_section (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (x : SchemeHomOver (genPt p) Λ.f) : ∃ s : SchemeHomOver Λ.σA Λ.f, x.1 = barPt A ≫ s.1 := by
  let S : ValuativeCommSq Λ.f :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := x.1, i₂ := Λ.σA,
      commSq := ⟨by rw [x.2, ← Λ.hσA]; rfl⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := ((valuativeCriterion Λ hΛ).existence S).exists_lift
  exact ⟨⟨l, hl₂⟩, hl₁.symm⟩

theorem section_ext (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (s s' : SchemeHomOver Λ.σA Λ.f) (h : barPt A ≫ s.1 = barPt A ≫ s'.1) : s = s' := by
  let S : ValuativeCommSq Λ.f :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := barPt A ≫ s.1, i₂ := Λ.σA,
      commSq := ⟨by rw [Category.assoc, s.2]; rfl⟩ }
  haveI : Subsingleton S.commSq.LiftStruct := (valuativeCriterion Λ hΛ).uniqueness S
  let l₁ : S.commSq.LiftStruct := ⟨s.1, rfl, s.2⟩
  let l₂ : S.commSq.LiftStruct := ⟨s'.1, h.symm, s'.2⟩
  have e : l₁ = l₂ := Subsingleton.elim _ _
  exact Subtype.ext (congrArg CommSq.LiftStruct.l e)

noncomputable def sec (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (x : JH (M / p) (infSubgroup p M H hpM)) : SchemeHomOver Λ.σA Λ.f :=
  (exists_section Λ hΛ (Λ.pts x)).choose

theorem sec_spec (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (x : JH (M / p) (infSubgroup p M H hpM)) : (Λ.pts x).1 = barPt A ≫ (sec Λ hΛ x).1 :=
  (exists_section Λ hΛ (Λ.pts x)).choose_spec

theorem pts_eq_comp_sec (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (x : JH (M / p) (infSubgroup p M H hpM)) :
    Λ.pts x = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (sec Λ hΛ x) :=
  Subtype.ext (sec_spec Λ hΛ x)

noncomputable def redSec (Λ : LevelData p M H hpM A) (s : SchemeHomOver Λ.σA Λ.f) : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f :=
  GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s

@[scoped simp] theorem redSec_coe (Λ : LevelData p M H hpM A) (s : SchemeHomOver Λ.σA Λ.f) : (redSec Λ s).1 = resPt A ≫ s.1 := rfl

noncomputable def red (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (x : JH (M / p) (infSubgroup p M H hpM)) : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  Λ.ptsSp.symm (redSec Λ (sec Λ hΛ x))

theorem red_eq_of_section (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (x : JH (M / p) (infSubgroup p M H hpM)) (s : SchemeHomOver Λ.σA Λ.f) (hs : (Λ.pts x).1 = barPt A ≫ s.1) :
    red Λ hΛ x = Λ.ptsSp.symm (redSec Λ s) := by
  have e : sec Λ hΛ x = s := section_ext Λ hΛ _ _ ((sec_spec Λ hΛ x).symm.trans hs)
  rw [red, e]

section Additive

variable (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
  (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
  (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
    Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))

include hΛptsSp_add in

theorem ptsSp_add' (x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :
    Λ.ptsSp (x + y) = Λ.L.mul (resPt A ≫ Λ.σA) (Λ.ptsSp x) (Λ.ptsSp y) := by
  rw [hΛptsSp_add, ofFibrePt_baseChange_mul_toFibrePt]

include hΛptsSp_add in
theorem ptsSp_symm_mul (u v : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f) :
    Λ.ptsSp.symm (Λ.L.mul (resPt A ≫ Λ.σA) u v) = Λ.ptsSp.symm u + Λ.ptsSp.symm v := by
  apply Λ.ptsSp.injective
  rw [Equiv.apply_symm_apply, ptsSp_add' Λ hΛptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

include hΛptsSp_add in
theorem ptsSp_zero : Λ.ptsSp 0 = Λ.L.one (resPt A ≫ Λ.σA) :=
  RelativeGroupLaw.eq_one_of_mul_self Λ.L _ _ (by rw [← ptsSp_add' Λ hΛptsSp_add, add_zero])

include hΛptsSp_add in
theorem ptsSp_nsmul (k : ℕ) (y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :
    Λ.ptsSp (k • y) = Λ.L.nsmul (resPt A ≫ Λ.σA) k (Λ.ptsSp y) := by
  induction k with
  | zero => rw [zero_nsmul, ptsSp_zero Λ hΛptsSp_add, RelativeGroupLaw.nsmul_zero]
  | succ k ih => rw [succ_nsmul, ptsSp_add' Λ hΛptsSp_add, ih, RelativeGroupLaw.nsmul_succ]

include hΛpts_add in
theorem pts_zero : Λ.pts 0 = Λ.L.one (genPt p) :=
  RelativeGroupLaw.eq_one_of_mul_self Λ.L _ _ (by rw [← hΛpts_add, add_zero])

include hΛpts_add in
theorem pts_nsmul (k : ℕ) (x : JH (M / p) (infSubgroup p M H hpM)) :
    Λ.pts (k • x) = Λ.L.nsmul (genPt p) k (Λ.pts x) := by
  induction k with
  | zero => rw [zero_nsmul, pts_zero Λ hΛpts_add, RelativeGroupLaw.nsmul_zero]
  | succ k ih => rw [succ_nsmul, hΛpts_add, ih, RelativeGroupLaw.nsmul_succ]

theorem redSec_mul (s₀ s₁ : SchemeHomOver Λ.σA Λ.f) :
    redSec Λ (Λ.L.mul Λ.σA s₀ s₁) = Λ.L.mul (resPt A ≫ Λ.σA) (redSec Λ s₀) (redSec Λ s₁) :=
  Λ.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl s₀ s₁

theorem redSec_nsmul (k : ℕ) (s : SchemeHomOver Λ.σA Λ.f) :
    redSec Λ (Λ.L.nsmul Λ.σA k s) = Λ.L.nsmul (resPt A ≫ Λ.σA) k (redSec Λ s) :=
  Λ.L.nsmul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl k s

theorem redSec_one : redSec Λ (Λ.L.one Λ.σA) = Λ.L.one (resPt A ≫ Λ.σA) :=
  Λ.L.one_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl

theorem genSec_mul (s₀ s₁ : SchemeHomOver Λ.σA Λ.f) :
    GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (Λ.L.mul Λ.σA s₀ s₁) =
      Λ.L.mul (genPt p) (GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s₀)
        (GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s₁) :=
  Λ.L.mul_natural Λ.σA (genPt p) (barPt A) Λ.hσA s₀ s₁

theorem genSec_nsmul (k : ℕ) (s : SchemeHomOver Λ.σA Λ.f) :
    GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (Λ.L.nsmul Λ.σA k s) =
      Λ.L.nsmul (genPt p) k (GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s) :=
  Λ.L.nsmul_natural Λ.σA (genPt p) (barPt A) Λ.hσA k s

theorem genSec_one :
    GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (Λ.L.one Λ.σA) = Λ.L.one (genPt p) :=
  Λ.L.one_natural Λ.σA (genPt p) (barPt A) Λ.hσA

include hΛpts_add in

theorem sec_add (x y : JH (M / p) (infSubgroup p M H hpM)) :
    sec Λ hΛ (x + y) = Λ.L.mul Λ.σA (sec Λ hΛ x) (sec Λ hΛ y) := by
  refine section_ext Λ hΛ _ _ ?_
  have h : Λ.pts (x + y) = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (Λ.L.mul Λ.σA (sec Λ hΛ x) (sec Λ hΛ y)) := by
    rw [genSec_mul, hΛpts_add, ← pts_eq_comp_sec, ← pts_eq_comp_sec]
  rw [← sec_spec]
  exact congrArg Subtype.val h

include hΛpts_add in

theorem sec_nsmul (k : ℕ) (x : JH (M / p) (infSubgroup p M H hpM)) :
    sec Λ hΛ (k • x) = Λ.L.nsmul Λ.σA k (sec Λ hΛ x) := by
  refine section_ext Λ hΛ _ _ ?_
  have h : Λ.pts (k • x) = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (Λ.L.nsmul Λ.σA k (sec Λ hΛ x)) := by
    rw [genSec_nsmul, pts_nsmul Λ hΛpts_add, ← pts_eq_comp_sec]
  rw [← sec_spec]
  exact congrArg Subtype.val h

include hΛpts_add hΛptsSp_add in

theorem red_add (x y : JH (M / p) (infSubgroup p M H hpM)) :
    red Λ hΛ (x + y) = red Λ hΛ x + red Λ hΛ y := by
  rw [red, sec_add Λ hΛ hΛpts_add, redSec_mul, ptsSp_symm_mul Λ hΛptsSp_add]
  rfl

noncomputable def redHom
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) :
    JH (M / p) (infSubgroup p M H hpM) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  AddMonoidHom.mk' (red Λ hΛ) (red_add Λ hΛ hΛpts_add hΛptsSp_add)

@[scoped simp] theorem redHom_apply (x : JH (M / p) (infSubgroup p M H hpM)) :
    redHom Λ hΛ hΛpts_add hΛptsSp_add x = red Λ hΛ x := rfl

include hΛpts_add in

theorem isTorsionPoint_sec {k : ℕ} {x : JH (M / p) (infSubgroup p M H hpM)} (hx : k • x = 0) :
    Λ.L.IsTorsionPoint Λ.σA k (sec Λ hΛ x) := by
  rw [RelativeGroupLaw.isTorsionPoint_def, ← sec_nsmul Λ hΛ hΛpts_add, hx]
  refine section_ext Λ hΛ _ _ ?_
  rw [← sec_spec, pts_zero Λ hΛpts_add, ← genSec_one]
  rfl

include hΛpts_add hΛptsSp_add in

theorem eq_zero_of_red_eq_zero (k : ℕ)
    (hInjk : ∀ (s : SchemeHomOver Λ.σA Λ.f), Λ.L.IsTorsionPoint Λ.σA k s →
      resPt A ≫ s.1 = resPt A ≫ (Λ.L.one Λ.σA).1 → s = Λ.L.one Λ.σA)
    (x : JH (M / p) (infSubgroup p M H hpM)) (hx : k • x = 0) (hr : red Λ hΛ x = 0) : x = 0 := by
  have htor := isTorsionPoint_sec Λ hΛ hΛpts_add hx

  have hred : resPt A ≫ (sec Λ hΛ x).1 = resPt A ≫ (Λ.L.one Λ.σA).1 := by
    have h1 : redSec Λ (sec Λ hΛ x) = Λ.ptsSp 0 := by
      rw [red] at hr
      rw [← hr, Equiv.apply_symm_apply]
    rw [ptsSp_zero Λ hΛptsSp_add, ← redSec_one] at h1
    exact congrArg Subtype.val h1
  have hs : sec Λ hΛ x = Λ.L.one Λ.σA := hInjk _ htor hred

  apply Λ.pts.injective
  rw [pts_eq_comp_sec Λ hΛ x, hs, genSec_one, pts_zero Λ hΛpts_add]

include hΛpts_add hΛptsSp_add in

theorem exists_red_eq (k : ℕ)
    (hSurjk : ∀ (y₀ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f), Λ.L.IsTorsionPoint (resPt A ≫ Λ.σA) k y₀ →
      ∃ s : SchemeHomOver Λ.σA Λ.f, Λ.L.IsTorsionPoint Λ.σA k s ∧ resPt A ≫ s.1 = y₀.1)
    (y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (hy : k • y = 0) :
    ∃ x : JH (M / p) (infSubgroup p M H hpM), k • x = 0 ∧ red Λ hΛ x = y := by
  have hy₀ : Λ.L.IsTorsionPoint (resPt A ≫ Λ.σA) k (Λ.ptsSp y) := by
    rw [RelativeGroupLaw.isTorsionPoint_def, ← ptsSp_nsmul Λ hΛptsSp_add, hy, ptsSp_zero Λ hΛptsSp_add]
  obtain ⟨s, hs, hsy⟩ := hSurjk _ hy₀
  refine ⟨Λ.pts.symm (GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s), ?_, ?_⟩
  · apply Λ.pts.injective
    rw [pts_nsmul Λ hΛpts_add, Equiv.apply_symm_apply, ← genSec_nsmul, hs, genSec_one, pts_zero Λ hΛpts_add]
  · have hsec : (Λ.pts (Λ.pts.symm (GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s))).1 = barPt A ≫ s.1 := by
      rw [Equiv.apply_symm_apply, GoodReductionJacobian.schemeHomOverComp_coe]
    rw [red_eq_of_section Λ hΛ _ s hsec]
    apply Λ.ptsSp.symm_apply_eq.2
    exact Subtype.ext hsy

end Additive

theorem of_levelwise
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)

    (hInj : ∀ (n : ℕ) (s : SchemeHomOver Λ.σA Λ.f), Λ.L.IsTorsionPoint Λ.σA (ℓ ^ n) s →
      resPt A ≫ s.1 = resPt A ≫ (Λ.L.one Λ.σA).1 → s = Λ.L.one Λ.σA)

    (hSurj : ∀ (n : ℕ) (y₀ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f), Λ.L.IsTorsionPoint (resPt A ≫ Λ.σA) (ℓ ^ n) y₀ →
      ∃ s : SchemeHomOver Λ.σA Λ.f, Λ.L.IsTorsionPoint Λ.σA (ℓ ^ n) s ∧ resPt A ≫ s.1 = y₀.1) :
    ∃ sp : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) ≃ₗ[ℤ_[ℓ]]
        TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      ∀ (w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM))) (n : ℕ) (s : SchemeHomOver Λ.σA Λ.f),
        (Λ.pts (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w)).1 = barPt A ≫ s.1 →
        TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (sp w) =
          Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) := by
  let r := redHom Λ hΛ hΛpts_add hΛptsSp_add
  have hinj : ∀ (m : ℕ) (x : JH (M / p) (infSubgroup p M H hpM)), ((ℓ ^ m : ℕ) : ℤ) • x = 0 → r x = 0 → x = 0 :=
    fun m x hx hr => eq_zero_of_red_eq_zero Λ hΛ hΛpts_add hΛptsSp_add (ℓ ^ m) (hInj m) x
      (by rwa [natCast_zsmul] at hx) hr
  have hsurj : ∀ (n : ℕ) (y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), ((ℓ ^ n : ℕ) : ℤ) • y = 0 →
      ∃ (m : ℕ) (x : JH (M / p) (infSubgroup p M H hpM)), ((ℓ ^ m : ℕ) : ℤ) • x = 0 ∧ r x = y := fun n y hy => by
    obtain ⟨x, hx, hrx⟩ := exists_red_eq Λ hΛ hΛpts_add hΛptsSp_add (ℓ ^ n) (hSurj n) y (by rwa [natCast_zsmul] at hy)
    exact ⟨n, x, by rw [natCast_zsmul, hx], hrx⟩
  let sp₀ := tmap (p := ℓ) r
  refine ⟨LinearEquiv.ofBijective sp₀ ⟨tmap_injective r hinj, tmap_surjective r hinj hsurj⟩, fun w n s hs => ?_⟩
  rw [LinearEquiv.ofBijective_apply, TateModule.proj_apply, tmap_apply_coe, redHom_apply,
    red_eq_of_section Λ hΛ _ s (by rw [← hs]; rfl)]
  rfl

section CommGeneral

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

noncomputable def univFst : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩

noncomputable def univSnd : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, pullback.condition.symm⟩

theorem isCommutative_of_univ
    (h : G.mul _ (univFst (f := f)) univSnd = G.mul _ univSnd univFst) : G.IsCommutative := by
  intro T t x y
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : T ⟶ pullback f f, φ ≫ pullback.fst f f = x.1 ∧ φ ≫ pullback.snd f f = y.1 :=
    ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hφ : φ ≫ (pullback.fst f f ≫ f) = t := by rw [← Category.assoc, hφ₁]; exact x.2
  have hx : GoodReductionJacobian.schemeHomOverComp φ hφ univFst = x := Subtype.ext hφ₁
  have hy : GoodReductionJacobian.schemeHomOverComp φ hφ univSnd = y := Subtype.ext hφ₂
  rw [← hx, ← hy, ← G.mul_natural, ← G.mul_natural, h]

theorem mul_comm_of_baseChange {K : Type u} [CommRing K]
    (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (hK : (G.baseChange ι).IsCommutative)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver (t' ≫ ι) f) :
    G.mul _ x y = G.mul _ y x := by
  rw [← RelativeGroupLaw.baseChangePointToBase_ofBase ι x, ← RelativeGroupLaw.baseChangePointToBase_ofBase ι y,
    ← RelativeGroupLaw.baseChangePointToBase_mul, ← RelativeGroupLaw.baseChangePointToBase_mul, hK.mul_comm]

theorem isCommutative_of_isCommutative_baseChange [IsSeparated f] [Flat f] [IsReduced (pullback f f)]
    {K : Type u} [CommRing K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [IsSchemeTheoreticallyDominant ι] (hK : (G.baseChange ι).IsCommutative) : G.IsCommutative := by
  refine isCommutative_of_univ G (Subtype.ext ?_)
  have hflat : Flat (pullback.fst f f ≫ f) := inferInstance
  have hdom : IsSchemeTheoreticallyDominant (pullback.fst (pullback.fst f f ≫ f) ι) := inferInstance
  have hsep : (G.mul _ (univFst (f := f)) univSnd).1 ≫ f = (G.mul _ univSnd univFst).1 ≫ f := by
    rw [(G.mul _ (univFst (f := f)) univSnd).2, (G.mul _ univSnd univFst).2]
  refine ext_of_isDominant_of_isSeparated f hsep (pullback.fst (pullback.fst f f ≫ f) ι) ?_
  have e₁ : pullback.fst (pullback.fst f f ≫ f) ι ≫ (G.mul _ (univFst (f := f)) univSnd).1 =
      (G.mul _ (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst f f ≫ f) ι) pullback.condition univFst)
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst f f ≫ f) ι) pullback.condition univSnd)).1 :=
    congrArg Subtype.val (G.mul_natural (pullback.fst f f ≫ f) (pullback.snd (pullback.fst f f ≫ f) ι ≫ ι)
      (pullback.fst (pullback.fst f f ≫ f) ι) pullback.condition univFst univSnd)
  have e₂ : pullback.fst (pullback.fst f f ≫ f) ι ≫ (G.mul _ (univSnd (f := f)) univFst).1 =
      (G.mul _ (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst f f ≫ f) ι) pullback.condition univSnd)
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst f f ≫ f) ι) pullback.condition univFst)).1 :=
    congrArg Subtype.val (G.mul_natural (pullback.fst f f ≫ f) (pullback.snd (pullback.fst f f ≫ f) ι ≫ ι)
      (pullback.fst (pullback.fst f f ≫ f) ι) pullback.condition univSnd univFst)
  rw [e₁, e₂, mul_comm_of_baseChange G ι hK]

theorem isDominant_specMap_of_injective {S : Type u} [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap φ)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
  exact bot_le

end CommGeneral

section Transport

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  {T : Scheme.{0}}

theorem castOver_coe {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x : SchemeHomOver t f) :
    (castOver h x).1 = x.1 := rfl

theorem one_castOver {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    castOver h (G.one t) = G.one t' := by
  subst h; rfl

theorem nsmul_castOver {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (k : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t' k (castOver h x) = castOver h (G.nsmul t k x) := by
  subst h; rfl

theorem isTorsionPoint_castOver_iff {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (k : ℕ)
    (x : SchemeHomOver t f) : G.IsTorsionPoint t' k (castOver h x) ↔ G.IsTorsionPoint t k x := by
  subst h; exact Iff.rfl

theorem castOver_castOver_symm {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x : SchemeHomOver t' f) :
    castOver h (castOver h.symm x) = x := rfl

theorem pow_eq_nsmul (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (k : ℕ) :
    (letI := G.pointGroup t; x ^ k) = G.nsmul t k x := by
  letI := G.pointGroup t
  induction k with
  | zero => rw [pow_zero]; rfl
  | succ k ih => rw [pow_succ, ih]; rfl

end Transport

section Level

variable {p M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem _root_.ModularCurve.JHNeronObjectAtP.RedLambda.geometricallyIntegral (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f) :
    GeometricallyIntegral Λ.f :=
  (GeometricallyIntegral.iff_geometricallyIntegral_fiber Λ.f).2 fun s =>
    (abelianSchemePropertyBundle_fibreStr hΛ s).geometricallyIntegral

p2m_export "ModularCurve.JHNeronObjectAtP.RedLambda" "geometricallyIntegral"

theorem isIntegral [Fact p.Prime] (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f) : IsIntegral Λ.X := by
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : Smooth Λ.f := hΛ.smooth
  haveI := geometricallyIntegral Λ hΛ
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian Λ.f

theorem isCommutative [Fact p.Prime] (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f) :
    Λ.L.IsCommutative := by
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsFractionRing (baseRing p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : Smooth Λ.f := hΛ.smooth
  haveI : IsProper Λ.f := hΛ.proper
  haveI := geometricallyIntegral Λ hΛ
  haveI : IsLocallyNoetherian Λ.X := LocallyOfFiniteType.isLocallyNoetherian Λ.f
  haveI := isIntegral Λ hΛ
  have hgen := abelianSchemePropertyBundle_genericFibreStr ℚ hΛ
  haveI : IsProper (RelativeGroupLaw.genericFibreStr ℚ Λ.f) := hgen.proper
  haveI : GeometricallyIntegral (RelativeGroupLaw.genericFibreStr ℚ Λ.f) := hgen.geometricallyIntegral
  have hK : (Λ.L.genericFibre ℚ).IsCommutative :=
    RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral _
  haveI : IsDominant (specGenericFibreInclusion (baseRing p) ℚ) :=
    isDominant_specMap_of_injective _ (IsFractionRing.injective (baseRing p) ℚ)
  haveI : IsSchemeTheoreticallyDominant (specGenericFibreInclusion (baseRing p) ℚ) := .of_isDominant _
  have hK' : (Λ.L.baseChange (specGenericFibreInclusion (baseRing p) ℚ)).IsCommutative := hK
  intro T t x y
  exact isCommutative_of_isCommutative_baseChange Λ.L (specGenericFibreInclusion (baseRing p) ℚ) hK' t x y

theorem isUnit_natCast_pow_baseRing [Fact p.Prime] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓp : ℓ ≠ p) (n : ℕ) :
    IsUnit ((ℓ ^ n : ℕ) : baseRing p) := by
  rw [Nat.cast_pow]
  refine IsUnit.pow n ?_
  have hcop : ((ℓ : ℚ)⁻¹).den.Coprime p := by
    rw [Rat.inv_natCast_den, if_neg hℓ.out.ne_zero]
    exact (Nat.coprime_primes hℓ.out Fact.out).2 hℓp
  refine isUnit_iff_exists_inv.2 ⟨⟨(ℓ : ℚ)⁻¹, hcop⟩, Subtype.ext ?_⟩
  change (ℓ : ℚ) * (ℓ : ℚ)⁻¹ = 1
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hℓ.out.ne_zero)

theorem inj_and_surj [Fact p.Prime] (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    [IsAlgClosed (ResidueField ↥A)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (n : ℕ) :
    (∀ (s : SchemeHomOver Λ.σA Λ.f), Λ.L.IsTorsionPoint Λ.σA (ℓ ^ n) s →
      resPt A ≫ s.1 = resPt A ≫ (Λ.L.one Λ.σA).1 → s = Λ.L.one Λ.σA) ∧
    (∀ (y₀ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f), Λ.L.IsTorsionPoint (resPt A ≫ Λ.σA) (ℓ ^ n) y₀ →
      ∃ s : SchemeHomOver Λ.σA Λ.f, Λ.L.IsTorsionPoint Λ.σA (ℓ ^ n) s ∧ resPt A ≫ s.1 = y₀.1) := by
  haveI : Smooth Λ.f := hΛ.smooth
  haveI : IsProper Λ.f := hΛ.proper
  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A

  set ρ : baseRing p →+* ↥A := (Spec.preimage Λ.σA).hom with hρ
  have hσ : Spec.map (CommRingCat.ofHom ρ) = Λ.σA := by
    rw [hρ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hπρ : Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)) = resPt A ≫ Λ.σA := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hσ]
  have hπ : Function.Surjective (residue ↥A) := Ideal.Quotient.mk_surjective
  have hπu : ∀ x : ↥A, IsUnit x ↔ residue ↥A x ≠ 0 := fun x => (residue_ne_zero_iff_isUnit x).symm
  obtain ⟨hinj, hsurj⟩ :=
    RelativeGroupLaw.eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
      Λ.L (isCommutative Λ hΛ) (ℓ ^ n) (isUnit_natCast_pow_baseRing hℓp n) ↥A ρ (ResidueField ↥A) (residue ↥A) hπ hπu
  refine ⟨fun s hs hred => ?_, fun y₀ hy₀ => ?_⟩
  ·
    have h1 : (letI := Λ.L.pointGroup (Spec.map (CommRingCat.ofHom ρ)); castOver hσ.symm s ^ (ℓ ^ n) = 1) := by
      rw [pow_eq_nsmul]
      exact (isTorsionPoint_castOver_iff Λ.L hσ.symm (ℓ ^ n) s).2 hs
    have h2 : Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ (castOver hσ.symm s).1 =
        (letI := Λ.L.pointGroup (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)));
          (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))) Λ.f)).1 := by
      change resPt A ≫ s.1 = (Λ.L.one _).1
      rw [hred, ← one_castOver Λ.L hπρ.symm, castOver_coe]
      exact congrArg Subtype.val (Λ.L.one_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl)
    have h3 := hinj (castOver hσ.symm s) h1 h2
    calc s = castOver hσ (castOver hσ.symm s) := rfl
      _ = Λ.L.one Λ.σA := by rw [h3]; exact one_castOver Λ.L hσ
  ·
    have h1 : (letI := Λ.L.pointGroup (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)));
        castOver hπρ.symm y₀ ^ (ℓ ^ n) = 1) := by
      rw [pow_eq_nsmul]
      exact (isTorsionPoint_castOver_iff Λ.L hπρ.symm (ℓ ^ n) y₀).2 hy₀
    obtain ⟨z, hz, hzred⟩ := hsurj (castOver hπρ.symm y₀) h1
    refine ⟨castOver hσ z, ?_, ?_⟩
    · refine (isTorsionPoint_castOver_iff Λ.L hσ (ℓ ^ n) z).2 ?_
      rw [pow_eq_nsmul] at hz
      exact hz
    · rw [castOver_coe]
      exact hzred.symm

end Level

end ModularCurve.JHNeronObjectAtP.RedLambda
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve.JHNeronObjectAtP.RedLambda"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve.JHNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.ModularCurve"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)

    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ sp : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) ≃ₗ[ℤ_[ℓ]]
        TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),

      ∀ (w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM))) (n : ℕ) (s : SchemeHomOver Λ.σA Λ.f),
        (Λ.pts (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w)).1 = barPt A ≫ s.1 →
        TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (sp w) =
          Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) :=
  ModularCurve.JHNeronObjectAtP.RedLambda.of_levelwise p M H hpM A hA Λ hΛ hΛpts_add hΛptsSp_add ℓ hℓp
    (fun n => (ModularCurve.JHNeronObjectAtP.RedLambda.inj_and_surj Λ hΛ hℓp n).1)
    (fun n => (ModularCurve.JHNeronObjectAtP.RedLambda.inj_and_surj Λ hΛ hℓp n).2)

end S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne (solution)
