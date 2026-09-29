-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_symm_section_eq_zero_of_toPic0Pair_snd_eq_zero_of_mem_corner_of_mem_finPts_bridgePins
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/484eaea5-9d94-5d23-8d24-39924a03faf2

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_section_eq_zero_of_toPic0Pair_snd_eq_zero_of_mem_corner_of_mem_finPts_bridgePins
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

namespace R1V11OrdCorner

open ModularCurve WithConv

section Fibre

variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
  {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}

theorem overId_eq_comp (x : SchemeHomOver ι f) :
    overId x = GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl x :=
  Subtype.ext (Category.id_comp _).symm

theorem toFibrePt_mul (L : RelativeGroupLaw R f) (x y : SchemeHomOver ι f) :
    toFibrePt (L.mul ι x y) = (L.baseChange ι).mul (𝟙 _) (toFibrePt x) (toFibrePt y) := by
  unfold toFibrePt
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase,
    RelativeGroupLaw.baseChangePointToBase_ofBase, overId_eq_comp, overId_eq_comp, overId_eq_comp,
    L.mul_natural]

theorem toFibrePt_one (L : RelativeGroupLaw R f) :
    toFibrePt (L.one ι) = (L.baseChange ι).one (𝟙 _) := by
  unfold toFibrePt
  rw [RelativeGroupLaw.baseChange_one, overId_eq_comp, L.one_natural]

theorem toFibrePt_nsmul (L : RelativeGroupLaw R f) (x : SchemeHomOver ι f) (n : ℕ) :
    toFibrePt (L.nsmul ι n x) = (L.baseChange ι).nsmul (𝟙 _) n (toFibrePt x) := by
  induction n with
  | zero => exact toFibrePt_one L
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, toFibrePt_mul, ih]

theorem ofFibrePt_toFibrePt (x : SchemeHomOver ι f) : ofFibrePt (toFibrePt x) = x := by
  apply Subtype.ext
  change (RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι (overId x))).1 = x.1
  rw [RelativeGroupLaw.baseChangePointToBase_ofBase]
  rfl

theorem toFibrePt_ofFibrePt (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) :
    toFibrePt (ofFibrePt y) = y := by
  unfold toFibrePt
  have h : overId (ofFibrePt y) = RelativeGroupLaw.baseChangePointToBase ι y := Subtype.ext rfl
  rw [h, RelativeGroupLaw.baseChangePointOfBase_toBase]

theorem toFibrePt_injective : Function.Injective (toFibrePt (ι := ι) (f := f)) := fun x y h => by
  rw [← ofFibrePt_toFibrePt x, h, ofFibrePt_toFibrePt]

end Fibre

section Torus

variable (S : Type) [CommRing S] (t : ℕ)

theorem exists_torusPt_eq (y : SchemeHomOver (𝟙 _) (torusStr S t)) : ∃ χ : torusCoord S t →ₐ[S] S, torusPt S t χ = y := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective y.1
  have h2 := y.2
  rw [← hφ, ← Spec.map_comp, ← Spec.map_id] at h2
  have h3 : CommRingCat.ofHom (algebraMap S (torusCoord S t)) ≫ φ = 𝟙 _ := Spec.map_injective h2
  have h4 : φ.hom.comp (algebraMap S (torusCoord S t)) = RingHom.id S := by
    have := congrArg CommRingCat.Hom.hom h3
    simpa using this
  refine ⟨{ φ.hom with commutes' := fun r => ?_ }, ?_⟩
  · exact congrFun (congrArg DFunLike.coe h4) r
  · apply Subtype.ext
    change Spec.map _ = y.1
    rw [← hφ]
    rfl

variable {S t}

theorem convPow_apply_single (χ : WithConv (torusCoord S t →ₐ[S] S)) (m : Fin t → ℤ) (n : ℕ) :
    (χ ^ n).ofConv (AddMonoidAlgebra.single m 1) = (χ.ofConv (AddMonoidAlgebra.single m 1)) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    simp [AddMonoidAlgebra.counit_single]
  | succ n ih =>
    rw [pow_succ, pow_succ, AlgHom.convMul_apply]
    simp [AddMonoidAlgebra.comul_single, ih]

theorem conv_eq_one_of_pow_prime_pow_eq_one [IsReduced S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (χ : WithConv (torusCoord S t →ₐ[S] S)) (v : ℕ) (h : χ ^ p ^ v = 1) : χ = 1 := by
  haveI : ExpChar S p := ExpChar.prime (Fact.out : p.Prime)
  apply WithConv.ext
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro m
  have h1 : (χ.ofConv (AddMonoidAlgebra.single m 1)) ^ (p ^ v * 1) = 1 := by
    rw [mul_one, ← convPow_apply_single, h]
    simp [AddMonoidAlgebra.counit_single]
  rw [ExpChar.pow_prime_pow_mul_eq_one_iff, pow_one] at h1
  rw [h1]
  simp [AddMonoidAlgebra.counit_single]

end Torus

section Neron

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring (AlgebraicClosure ℚ)} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}

scoped instance isDominant_barPt : IsDominant (barPt Pl) := by
  refine ⟨?_⟩
  change DenseRange (Spec.map (CommRingCat.ofHom Pl.subtype)).base
  rw [Spec.map_base]
  change DenseRange (PrimeSpectrum.comap (CommRingCat.ofHom Pl.subtype).hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, CommRingCat.hom_ofHom,
    (RingHom.injective_iff_ker_eq_bot _).mp (fun x y h => Subtype.ext h)]
  exact bot_le

theorem eq_of_barPt_comp_eq (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) (s s' : SchemeHomOver Λ.σA O.g)
    (h : barPt Pl ≫ s.1 = barPt Pl ≫ s'.1) : s = s' := by
  apply Subtype.ext
  haveI : IsSeparated O.g := O.separated
  exact ext_of_isDominant_of_isSeparated O.g (s.2.trans s'.2.symm) (barPt Pl) h

theorem pts_zero (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) : O.pts 0 = O.L.one (genPt p) := by
  letI := O.L.pointGroup (genPt p)
  have h : O.pts 0 * O.pts 0 = O.pts 0 * 1 := by
    rw [mul_one]
    have := O.pts_add 0 0
    rw [add_zero] at this
    exact this.symm
  exact mul_left_cancel h

theorem pts_nsmul (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) (x : JH M H) (n : ℕ) :
    O.pts (n • x) = O.L.nsmul (genPt p) n (O.pts x) := by
  induction n with
  | zero => rw [zero_nsmul]; exact pts_zero O
  | succ n ih => rw [succ_nsmul, O.pts_add, ih, RelativeGroupLaw.nsmul_succ]

theorem ptsSp_add' (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (a b : GluedPic0 (ResidueField ↥Pl) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset) :
    O.ptsSp (a + b) = O.L.mul _ (O.ptsSp a) (O.ptsSp b) := by
  rw [O.ptsSp_add, ← toFibrePt_mul, ofFibrePt_toFibrePt]

theorem ptsSp_zero (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) : O.ptsSp 0 = O.L.one (resPt Pl ≫ Λ.σA) := by
  letI := O.L.pointGroup (resPt Pl ≫ Λ.σA)
  have h : O.ptsSp 0 * O.ptsSp 0 = O.ptsSp 0 * 1 := by
    rw [mul_one]
    have h1 := ptsSp_add' O 0 0
    have h2 := congrArg O.ptsSp
      (add_zero (0 : GluedPic0 (ResidueField ↥Pl) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset))
    exact h1.symm.trans h2
  exact mul_left_cancel h

theorem ptsSp_nsmul (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (a : GluedPic0 (ResidueField ↥Pl) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset) (n : ℕ) :
    O.ptsSp (n • a) = O.L.nsmul (resPt Pl ≫ Λ.σA) n (O.ptsSp a) := by
  induction n with
  | zero => rw [zero_nsmul]; exact ptsSp_zero O
  | succ n ih => rw [succ_nsmul, ptsSp_add', ih, RelativeGroupLaw.nsmul_succ]

theorem ptsSp_symm_one (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) : O.ptsSp.symm (O.L.one (resPt Pl ≫ Λ.σA)) = 0 := by
  rw [← ptsSp_zero O, Equiv.symm_apply_apply]

theorem nsmul_section_eq_one (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) (n : ℕ) (w : JH M H) (hw : n • w = 0)
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts w).1 = barPt Pl ≫ s.1) :
    O.L.nsmul Λ.σA n s = O.L.one Λ.σA := by
  have hgen : GoodReductionJacobian.schemeHomOverComp (barPt Pl) Λ.hσA s = O.pts w := Subtype.ext hs.symm
  apply eq_of_barPt_comp_eq O
  have h1 := congrArg Subtype.val (O.L.nsmul_natural Λ.σA (genPt p) (barPt Pl) Λ.hσA n s)
  have h2 := congrArg Subtype.val (O.L.one_natural Λ.σA (genPt p) (barPt Pl) Λ.hσA)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1 h2
  rw [h1, h2, hgen, ← pts_nsmul, hw, pts_zero]

theorem nsmul_special_eq_one (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) (n : ℕ) (w : JH M H) (hw : n • w = 0)
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts w).1 = barPt Pl ≫ s.1) :
    O.L.nsmul (resPt Pl ≫ Λ.σA) n (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s) =
      O.L.one (resPt Pl ≫ Λ.σA) := by
  rw [← RelativeGroupLaw.nsmul_natural, nsmul_section_eq_one O n w hw s hs, O.L.one_natural]

theorem nsmul_ptsSp_symm_eq_zero (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) (n : ℕ) (w : JH M H) (hw : n • w = 0)
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts w).1 = barPt Pl ≫ s.1) :
    n • O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s) = 0 := by
  apply O.ptsSp.injective
  rw [ptsSp_nsmul, Equiv.apply_symm_apply, nsmul_special_eq_one O n w hw s hs, ptsSp_zero]

noncomputable def torusMap (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (χ : WithConv (torusCoord (ResidueField ↥Pl) O.toricRank →ₐ[ResidueField ↥Pl] ResidueField ↥Pl)) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt Pl ≫ Λ.σA) O.g) :=
  NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) O.torusFibre

theorem torusMap_mul (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (χ χ' : WithConv (torusCoord (ResidueField ↥Pl) O.toricRank →ₐ[ResidueField ↥Pl] ResidueField ↥Pl)) :
    torusMap O (χ * χ') = (O.L.baseChange (resPt Pl ≫ Λ.σA)).mul _ (torusMap O χ) (torusMap O χ') :=
  O.torusFibre_mul χ χ'

theorem torusMap_one (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) :
    torusMap O 1 = (O.L.baseChange (resPt Pl ≫ Λ.σA)).one _ := by
  letI := (O.L.baseChange (resPt Pl ≫ Λ.σA)).pointGroup
    (𝟙 (Spec (CommRingCat.of (ResidueField ↥Pl))))
  have h : torusMap O 1 * torusMap O 1 = torusMap O 1 * 1 := by
    rw [mul_one]
    have := torusMap_mul O 1 1
    rw [mul_one] at this
    exact this.symm
  exact mul_left_cancel h

theorem torusMap_pow (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (χ : WithConv (torusCoord (ResidueField ↥Pl) O.toricRank →ₐ[ResidueField ↥Pl] ResidueField ↥Pl)) (n : ℕ) :
    torusMap O (χ ^ n) = (O.L.baseChange (resPt Pl ≫ Λ.σA)).nsmul (𝟙 _) n (torusMap O χ) := by
  induction n with
  | zero => rw [pow_zero]; exact torusMap_one O
  | succ n ih => rw [pow_succ, torusMap_mul, ih, RelativeGroupLaw.nsmul_succ]

theorem torusMap_injective (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) : Function.Injective (torusMap O) := by
  intro χ χ' h
  have h1 := congrArg Subtype.val h
  simp only [torusMap, NeronModelInfra.schemeHomOverComp_coe] at h1
  haveI : IsClosedImmersion O.torusFibre.1 := O.torusFibre_isClosedImmersion
  have h2 : (torusPt _ _ χ.ofConv).1 = (torusPt _ _ χ'.ofConv).1 := (cancel_mono O.torusFibre.1).mp h1
  have h3 : CommRingCat.ofHom χ.ofConv.toRingHom = CommRingCat.ofHom χ'.ofConv.toRingHom := Spec.map_injective h2
  have h4 : χ.ofConv.toRingHom = χ'.ofConv.toRingHom := by
    have := congrArg CommRingCat.Hom.hom h3
    simpa using this
  apply WithConv.ext
  exact AlgHom.coe_ringHom_injective h4

theorem torusMap_eq_one_of_isTorsionPoint (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) (v : ℕ)
    (χ : torusCoord (ResidueField ↥Pl) O.toricRank →ₐ[ResidueField ↥Pl] ResidueField ↥Pl)
    (hχ : (O.L.baseChange (resPt Pl ≫ Λ.σA)).IsTorsionPoint (𝟙 _) (p ^ v)
      (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥Pl) O.toricRank χ) O.torusFibre)) :
    NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥Pl) O.toricRank χ) O.torusFibre =
      (O.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _) := by
  have h1 : torusMap O (toConv χ ^ p ^ v) = torusMap O 1 := by
    rw [torusMap_pow, torusMap_one]
    exact hχ
  have h2 : toConv χ = 1 := conv_eq_one_of_pow_prime_pow_eq_one p (toConv χ) v (torusMap_injective O h1)
  rw [← torusMap_one O, ← h2]
  rfl

theorem resPt_comp_eq_of_torus (O : JHNeronObjectAtP p M H hpM Pl hPl Λ) (v : ℕ) (w : JH M H) (hw : (p ^ v : ℕ) • w = 0)
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts w).1 = barPt Pl ≫ s.1)
    (y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥Pl) O.toricRank))
    (hy : NeronModelInfra.schemeHomOverComp y O.torusFibre =
      toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s)) :
    resPt Pl ≫ s.1 = (resPt Pl ≫ Λ.σA) ≫ (O.L.one (𝟙 (base p))).1 := by
  have hsp := nsmul_special_eq_one O (p ^ v) w hw s hs
  obtain ⟨χ, rfl⟩ := exists_torusPt_eq (ResidueField ↥Pl) O.toricRank y
  have htors : (O.L.baseChange (resPt Pl ≫ Λ.σA)).IsTorsionPoint (𝟙 _) (p ^ v)
      (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥Pl) O.toricRank χ) O.torusFibre) := by
    rw [RelativeGroupLaw.isTorsionPoint_def, hy, ← toFibrePt_nsmul, hsp, toFibrePt_one]
  have hone : toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s) =
      toFibrePt (O.L.one (resPt Pl ≫ Λ.σA)) := by
    rw [← hy, toFibrePt_one, torusMap_eq_one_of_isTorsionPoint O v χ htors]
  have hone' := congrArg Subtype.val (toFibrePt_injective hone)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at hone'
  rw [hone', ← O.L.one_natural (𝟙 (base p)) (resPt Pl ≫ Λ.σA) (resPt Pl ≫ Λ.σA) (Category.comp_id _)]
  rfl

theorem exists_torus_of_toPic0Pair_eq_zero (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hΛone : Λ.ptsSp.symm (Λ.L.one (resPt Pl ≫ Λ.σA)) = 0)
    (σ : SchemeHomOver (resPt Pl ≫ Λ.σA) O.g)
    (hσ : GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm σ) = 0) :
    ∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥Pl) O.toricRank),
      NeronModelInfra.schemeHomOverComp y O.torusFibre = toFibrePt σ := by
  have hi : ∀ i : Fin 2, JZeroNeronObjectAtP.fibreMap (O.abqFibre i) σ = Λ.L.one (resPt Pl ≫ Λ.σA) := by
    intro i
    have h := O.abqFibre_ptsSp (O.ptsSp.symm σ) i
    rw [Equiv.apply_symm_apply, hσ] at h
    have h0 : Λ.ptsSp.symm (JZeroNeronObjectAtP.fibreMap (O.abqFibre i) σ) = 0 := by
      rw [h]
      split_ifs <;> rfl
    exact Λ.ptsSp.symm.injective (h0.trans hΛone.symm)
  have hcomp : ∀ i : Fin 2, NeronModelInfra.schemeHomOverComp (toFibrePt σ) (O.abqFibre i) =
      (Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _) := by
    intro i
    have h := congrArg toFibrePt (hi i)
    rw [toFibrePt_one] at h
    rw [← h]
    unfold JZeroNeronObjectAtP.fibreMap
    rw [toFibrePt_ofFibrePt]
  exact (O.abqFibre_eq_one_iff (𝟙 _) (toFibrePt σ)).1 hcomp

end Neron

section Algebra

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {T : Type} [AddCommGroup T] [Module 𝒪 T] [Module B T] [IsScalarTower 𝒪 B T]

theorem smul_mem_of_gen_stable {ι : Type} (op : ι → B) (hgen : Algebra.adjoin 𝒪 (Set.range op) = ⊤)
    (N : Submodule 𝒪 T) (hN : ∀ i, ∀ t ∈ N, op i • t ∈ N) : ∀ (τ : B), ∀ t ∈ N, τ • t ∈ N := by
  intro τ
  have hτ : τ ∈ Algebra.adjoin 𝒪 (Set.range op) := hgen ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun τ _ => ∀ t ∈ N, τ • t ∈ N) ?_ ?_ ?_ ?_ hτ
  · rintro _ ⟨i, rfl⟩ t ht
    exact hN i t ht
  · intro r t ht
    rw [algebraMap_smul]
    exact N.smul_mem r ht
  · intro a b _ _ ha hb t ht
    rw [add_smul]
    exact N.add_mem (ha t ht) (hb t ht)
  · intro a b _ _ ha hb t ht
    rw [mul_smul]
    exact ha _ (hb t ht)

end Algebra

end R1V11OrdCorner
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_section_eq_zero_of_toPic0Pair_snd_eq_zero_of_mem_corner_of_mem_finPts_bridgePins.R1V11OrdCorner"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open R1V11OrdCorner in
open ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    {hB : ℕ}
    (ℬ : PDivisibleGroup R p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[R] 𝒢.level v)
    {h' : ℕ}
    (hhB : h = O.toricRank + hB)
    (hhB2 : hB = 2 * h')
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v)) = b)
    (hψred : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v))) a -
          algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hperiod : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v))) a -
          algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (ρh : ModularCurve.XHDRLevel.R p →+* R)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap R (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[R] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[R] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[R] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[R] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint R →
          x ∈ Set.range jv.base)

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    [NeZero (M / p)]

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ModularCurve.XHDRLevel.ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)

    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))
    :
    ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (x : ModularCurve.JH M H) ∈
          ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → (x : ModularCurve.JH M H) ∈ O.finPts p →
      ∀ s : NeronModelInfra.SchemeHomOver Λ.σA O.g,
        (O.pts ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H)).1 = ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ s.1 →
        (AlgebraicCurve.GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨ModularCurve.JZeroNeronObjectAtP.resPt Pl, rfl⟩ s))).2 = 0 →
        (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨ModularCurve.JZeroNeronObjectAtP.resPt Pl, rfl⟩ s)) = 0 := by
  intro x hxcor hxfin s hs h2
  have hpx : (p : ℕ) • (x : JH M H) = 0 := by
    have hx2 := Pic0.mem_torsion.1 x.2
    rwa [natCast_zsmul] at hx2

  have hfin := ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
    p M H hpM Pl hPl Λ O p

  have hfinU : ∀ (g : CohCarrier.Gen M S) (y : JH M H), y ∈ O.finPts p → genOpH M H S g y ∈ O.finPts p := by
    intro g y hy
    have hy1 : y ∈ O.finPts (p ^ 1) := by rwa [pow_one]
    obtain ⟨xg, hxg⟩ := (hΔlev 1 y).1 hy1
    obtain ⟨φ, -, hφ⟩ := hΔhecke S g
    have h1 : genOpH M H S g y ∈ O.finPts (p ^ 1) := (hΔlev 1 _).2 ⟨_, by rw [hφ, hxg]⟩
    rwa [pow_one] at h1

  let N : Submodule ℤ_[p] (TateModule p (JH M H)) :=
    { carrier := {t | TateModule.proj p (JH M H) 1 t ∈ O.finPts p}
      add_mem' := fun {a b} ha hb => by
        show TateModule.proj p (JH M H) 1 (a + b) ∈ O.finPts p
        rw [map_add]
        exact (O.finPts p).add_mem ha hb
      zero_mem' := by
        show TateModule.proj p (JH M H) 1 0 ∈ O.finPts p
        rw [map_zero]
        exact (O.finPts p).zero_mem
      smul_mem' := fun r t ht => by
        show TateModule.proj p (JH M H) 1 (r • t) ∈ O.finPts p
        rw [TateModule.proj_apply, TateModule.smul_apply]
        exact (O.finPts p).zsmul_mem ht _ }
  have hproj_op : ∀ (g : CohCarrier.Gen M S) (t : TateModule p (JH M H)),
      TateModule.proj p (JH M H) 1 (op g • t) = genOpH M H S g (TateModule.proj p (JH M H) 1 t) := by
    intro g t
    rw [hop, TateModule.proj_apply, TateModule.proj_apply, ModularCurve.tateGenOpH_apply_coe]
  have hNgen : ∀ g : CohCarrier.Gen M S, ∀ t ∈ N, op g • t ∈ N := fun g t ht => by
    show TateModule.proj p (JH M H) 1 (op g • t) ∈ O.finPts p
    rw [hproj_op]
    exact hfinU g _ ht
  have hN𝕋 : ∀ τ : 𝕋, ∀ t ∈ N, τ • t ∈ N := smul_mem_of_gen_stable (𝒪 := ℤ_[p]) op hgen N hNgen

  obtain ⟨c, hc, hcx⟩ := AddSubgroup.mem_map.1 hxcor
  have hc' : c ∈ LinearMap.range ((S'.e i₀) • (LinearMap.id : TateModule p (JH M H) →ₗ[𝕋] TateModule p (JH M H))) := hc
  obtain ⟨t', ht'⟩ := LinearMap.mem_range.1 hc'
  have hec : S'.e i₀ • c = c := by
    rw [← ht', LinearMap.smul_apply, LinearMap.id_apply, ← mul_smul, (S'.idem i₀).eq]

  obtain ⟨r, hr⟩ := IharaLemma.exists_mul_mul_eq_of_notMem (S'.idem i₀) (S'.𝔪 i₀)
    (S'.mem_of_isMaximal_of_ne i₀) hord
  have hcN : c ∈ N := by
    show TateModule.proj p (JH M H) 1 c ∈ O.finPts p
    rw [hcx]
    exact hxfin

  obtain ⟨x', hx'def⟩ : ∃ x' : JH M H, x' = TateModule.proj p (JH M H) 1 (r • c) := ⟨_, rfl⟩
  have hx'fin : x' ∈ O.finPts p := by
    rw [hx'def]
    exact hN𝕋 r c hcN
  have hUx' : genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) x' = (x : JH M H) := by
    rw [hx'def, ← hproj_op, smul_smul, ← hec, smul_smul,
      show op (CohCarrier.Gen.U p Fact.out hpM) * r * S'.e i₀ = r * op (CohCarrier.Gen.U p Fact.out hpM) * S'.e i₀ by ring,
      hr, hec, hcx]

  obtain ⟨-, s', hs'⟩ := (hfin.1 x').1 hx'fin
  have hpx' : (p : ℕ) • x' = 0 := by
    have h := Pic0.mem_torsion.1 ((hfin.1 x').1 hx'fin).1
    rwa [natCast_zsmul] at h
  have hs'' : (O.pts (x : JH M H)).1 =
      barPt Pl ≫ (NeronModelInfra.schemeHomOverComp s' (O.hecke S (CohCarrier.Gen.U p Fact.out hpM))).1 := by
    rw [← hUx', O.hecke_pts, hs', NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  have hss : s = NeronModelInfra.schemeHomOverComp s' (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)) :=
    eq_of_barPt_comp_eq O _ _ (hs.symm.trans hs'')

  have hUP := ModularCurve.JHNeronObjectAtP.toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp p M H hpM hj 𝔛 Pl hPl Λ O ρ hρ hσA
    hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull hpull hpullsp Wbar wgen hWbar hwgen S hUPgen
    (O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s'))
  rw [Equiv.apply_symm_apply] at hUP
  have hcomp : NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s')
      (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)) = GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s := by
    rw [hss]
    exact Subtype.ext (Category.assoc _ _ _)
  rw [hcomp] at hUP

  have hξp : (p : ℕ) • O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s') = 0 :=
    nsmul_ptsSp_symm_eq_zero O p x' hpx' s' hs'
  rcases hb : GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s'))
    with ⟨b0, b1⟩
  rw [hb, Pic0Pair.blockOp_apply] at hUP
  have hbp : (p : ℕ) • (b0, b1) = 0 := by
    rw [← hb, ← map_nsmul, hξp, map_zero]
  have hb0 : (p : ℕ) • b0 = 0 := by
    simpa using congrArg Prod.fst hbp

  have h2' : (GluedPic0.toPic0Pair O.ssFinset
      (O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s))).2 = 0 := h2
  rw [hUP] at h2'
  have hFb1 : F b1 = 0 := by
    have h : δ (F b1) = 0 := by simpa using h2'
    rw [hδ] at h
    exact (smul_eq_zero_iff_eq _).1 h
  have hb1z : b1 = 0 := by
    have h := DFunLike.congr_fun hFinv.2 b1
    rw [AddMonoidHom.comp_apply, hFb1, map_zero, AddMonoidHom.id_apply] at h
    exact h.symm
  have hb0z : Fstar b0 = 0 := by
    rw [hFstar, ← map_zsmul, natCast_zsmul, hb0, map_zero]
  have hσ0 : GluedPic0.toPic0Pair O.ssFinset
      (O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt Pl) rfl s)) = 0 := by
    rw [hUP, hb0z, hb1z]
    simp

  have hΛone : Λ.ptsSp.symm (Λ.L.one (resPt Pl ≫ Λ.σA)) = 0 := by
    have h1 : NeronModelInfra.schemeHomOverComp (Λ.L.one (resPt Pl ≫ Λ.σA)) (degPull 0) = O.L.one (resPt Pl ≫ Λ.σA) := by
      letI := O.L.pointGroup (resPt Pl ≫ Λ.σA)
      have h : NeronModelInfra.schemeHomOverComp (Λ.L.one (resPt Pl ≫ Λ.σA)) (degPull 0) *
          NeronModelInfra.schemeHomOverComp (Λ.L.one (resPt Pl ≫ Λ.σA)) (degPull 0) =
          NeronModelInfra.schemeHomOverComp (Λ.L.one (resPt Pl ≫ Λ.σA)) (degPull 0) * 1 := by
        rw [mul_one]
        have := hpull_mul 0 (resPt Pl ≫ Λ.σA) (Λ.L.one _) (Λ.L.one _)
        rw [Λ.L.one_mul] at this
        exact this.symm
      exact mul_left_cancel h
    have h3 := hpullsp 0 (Λ.L.one (resPt Pl ≫ Λ.σA))
    rw [if_pos rfl, h1, ptsSp_symm_one, map_zero] at h3
    exact ((Prod.ext_iff.1 h3).1).symm
  obtain ⟨y, hy⟩ := exists_torus_of_toPic0Pair_eq_zero O hΛone _ hσ0
  have hone := resPt_comp_eq_of_torus O 1 (x : JH M H) (by rwa [pow_one]) s hs y hy
  show O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (⟨resPt Pl, rfl⟩ : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.σA) s) = 0
  have hσ1 : NeronModelInfra.schemeHomOverComp (⟨resPt Pl, rfl⟩ : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.σA) s =
      O.L.one (resPt Pl ≫ Λ.σA) := by
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe]
    change resPt Pl ≫ s.1 = _
    rw [hone, ← O.L.one_natural (𝟙 (base p)) (resPt Pl ≫ Λ.σA) (resPt Pl ≫ Λ.σA) (Category.comp_id _)]
    rfl
  rw [hσ1, ptsSp_symm_one]

end S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_section_eq_zero_of_toPic0Pair_snd_eq_zero_of_mem_corner_of_mem_finPts_bridgePins
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_section_eq_zero_of_toPic0Pair_snd_eq_zero_of_mem_corner_of_mem_finPts_bridgePins (solution)
