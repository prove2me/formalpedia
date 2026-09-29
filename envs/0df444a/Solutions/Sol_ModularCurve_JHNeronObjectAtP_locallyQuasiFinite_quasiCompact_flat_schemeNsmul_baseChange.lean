-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e376093e-36e9-5496-b348-6d36601a46b1

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_locallyQuasiFinite_kernel
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian P2MW.S_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange.GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative pointGroup mul_assoc one one_mul mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over schemeKerStr baseChangeStr baseChangePointToBase baseChange baseChangePointToBase_mul baseChangePointToBase_one fibre locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit locallyQuasiFinite_of_locallyQuasiFinite_kernel"
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

end

open GoodReductionJacobian.RelativeGroupLaw.CH2 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeNsmul m) ∧
      QuasiCompact ((O.L.baseChange Λ.σA).schemeNsmul m) ∧ Flat ((O.L.baseChange Λ.σA).schemeNsmul m) := by
  haveI := O.locallyOfFiniteType
  haveI := O.quasiCompact
  haveI := O.separated
  haveI hflat : Flat (O.L.schemeNsmul m) := O.nsmul_flat m hm

  have he : (O.L.one (𝟙 (base p))).1 ≫ O.g = 𝟙 _ := (O.L.one (𝟙 _)).2
  haveI : IsClosedImmersion (O.L.one (𝟙 (base p))).1 := by
    have : IsClosedImmersion ((O.L.one (𝟙 (base p))).1 ≫ O.g) := by rw [he]; infer_instance
    exact .of_comp _ O.g
  have hkf : pullback.fst (O.L.schemeNsmul m) (O.L.one (𝟙 (base p))).1 ≫ O.g = O.L.schemeKerStr m := by
    calc _ = pullback.fst (O.L.schemeNsmul m) (O.L.one (𝟙 (base p))).1 ≫ O.L.schemeNsmul m ≫ O.g := by
            rw [O.L.schemeNsmul_over]
      _ = (pullback.snd (O.L.schemeNsmul m) (O.L.one (𝟙 (base p))).1 ≫ (O.L.one (𝟙 (base p))).1) ≫ O.g := by
            rw [← Category.assoc, pullback.condition]
      _ = O.L.schemeKerStr m := by rw [Category.assoc, he, Category.comp_id]
  haveI : LocallyOfFiniteType (O.L.schemeKerStr m) := by rw [← hkf]; infer_instance
  haveI : QuasiCompact (O.L.schemeKerStr m) := by rw [← hkf]; infer_instance
  haveI : Flat (O.L.schemeKerStr m) := inferInstance
  haveI hqc : QuasiCompact (O.L.schemeNsmul m) := by
    have : QuasiCompact (O.L.schemeNsmul m ≫ O.g) := by rw [O.L.schemeNsmul_over]; infer_instance
    exact QuasiCompact.of_comp _ O.g

  haveI : IsPrincipalIdealRing (baseRing p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsFractionRing (baseRing p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p

  haveI : LocallyQuasiFinite (pullback.snd (O.L.schemeKerStr m)
      (Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ)))) :=
    O.L.locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
      (Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))) (fun t x y => O.comm t x y) m
      (by exact_mod_cast (isUnit_iff_ne_zero.mpr (by exact_mod_cast hm.ne')))
  haveI : LocallyQuasiFinite (O.L.schemeKerStr m) :=
    LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber (R := baseRing p) (K := ℚ) (O.L.schemeKerStr m)
  have hlqf : LocallyQuasiFinite (O.L.schemeNsmul m) :=
    O.L.locallyQuasiFinite_of_locallyQuasiFinite_kernel O.L (nsmulOver O.L m)
      (fun t x y => isHom_nsmulOver O.L (fun t x y => O.comm t x y) m t x y)

  have sq := isPullback_schemeNsmul_baseChange O.L Λ.σA m
  exact ⟨MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq.flip hlqf,
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq.flip hqc,
    MorphismProperty.of_isPullback (P := @Flat) sq.flip hflat⟩

end S_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange (solution)
