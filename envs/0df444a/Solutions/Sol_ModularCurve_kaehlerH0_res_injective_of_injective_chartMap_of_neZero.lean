-- Prove2me | solution 1 for ModularCurve.kaehlerH0_res_injective_of_injective_chartMap_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/94c10941-6a90-50f3-8d32-518b168cc548

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_formallySmooth_cover_A0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry ModularCurve Opposite"
open scoped TensorProduct

universe u

namespace KaehlerDifferential p2m_export "KaehlerDifferential" "mapBaseChange_tmul mapBaseChange isBaseChange_of_formallyEtale exact_mapBaseChange_map map mapOfRingHom mapOfRingHom_congr mapOfRingHom_comp_apply mapOfRingHom_apply_eq_map" end KaehlerDifferential
p2m_open_scoped "KaehlerDifferential" in

theorem KaehlerDifferential.map_injective_of_charZero_of_field
    (R : Type*) [CommRing R] (K : Type*) [Field K] [CharZero K] (L : Type*) [Field L]
    [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L] :
    Function.Injective (KaehlerDifferential.map R R K L) := by

  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective

  haveI : Algebra.FormallySmooth K L := by
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range ((↑) : s → L))) L :=
      hs.isAlgebraic_field
    exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  haveI : Subsingleton (Algebra.H1Cotangent K L) := Algebra.FormallySmooth.subsingleton_h1Cotangent

  have h1 : Function.Injective (KaehlerDifferential.mapBaseChange R K L) := by
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R K L
    intro x y hxy
    rw [← sub_eq_zero, ← map_sub] at hxy
    obtain ⟨z, hz⟩ := (hex _).mp hxy
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm

  have h2 : Function.Injective (fun y : Ω[K⁄R] => (1 : L) ⊗ₜ[K] y) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
      (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
    intro y y' h
    have := congrArg (fun z => TensorProduct.lid K Ω[K⁄R] (LinearMap.rTensor Ω[K⁄R] g z)) h
    have hg1 : g 1 = 1 := by simpa using LinearMap.congr_fun hg 1
    simpa [LinearMap.rTensor_tmul, hg1] using this

  intro y y' h
  apply h2
  apply h1
  simpa [KaehlerDifferential.mapBaseChange_tmul] using h

p2m_open_scoped "KaehlerDifferential" in

theorem KaehlerDifferential.map_injective_of_formallyUnramified
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] :
    Function.Injective (KaehlerDifferential.map R S B B) := by
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S B

  haveI : Subsingleton Ω[S⁄R] := inferInstance
  have hz : ∀ z : B ⊗[S] Ω[S⁄R], z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul b w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  intro x y hxy
  rw [← sub_eq_zero, ← map_sub] at hxy
  obtain ⟨z, hz'⟩ := (hex _).mp hxy
  rw [hz z, map_zero] at hz'
  exact sub_eq_zero.mp hz'.symm

set_option autoImplicit false

namespace RESINJ

theorem kaehlerDifferential_map_injective_of_isFractionRing_of_flat
    (R A K : Type*) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]
    [Module.Flat A Ω[A⁄R]] :
    Function.Injective (KaehlerDifferential.map R R A K) := by
  haveI : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have hbc : IsBaseChange K (KaehlerDifferential.map R R A K) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale R A K

  have hfac : ∀ m : Ω[A⁄R], KaehlerDifferential.map R R A K m = hbc.equiv ((1 : K) ⊗ₜ[A] m) := by
    intro m; rw [IsBaseChange.equiv_tmul, one_smul]

  have hinj1 : Function.Injective (fun m : Ω[A⁄R] => (1 : K) ⊗ₜ[A] m) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω[A⁄R]) (Algebra.linearMap A K)
      (IsFractionRing.injective A K)
    intro m m' hmm'
    have : (Algebra.linearMap A K).rTensor Ω[A⁄R] ((1 : A) ⊗ₜ[A] m) =
        (Algebra.linearMap A K).rTensor Ω[A⁄R] ((1 : A) ⊗ₜ[A] m') := by
      simpa [LinearMap.rTensor_tmul] using hmm'
    have h2 := h this
    simpa using (TensorProduct.lid A Ω[A⁄R]).congr_arg h2
  intro m m' hmm'
  rw [hfac, hfac] at hmm'
  exact hinj1 (hbc.equiv.injective hmm')

end RESINJ

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension IsProper Spec IsIntegral Scheme Smooth functionField_isFractionRing_of_isAffineOpen Flat FormallyUnramified Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.formallySmooth_cover_A0"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "germToFunctionField Hom Γ empty functionField Opens TwoAffineOpenCover TwoAffineOpenCover.formallySmooth_cover_A0"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "cover isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1 kaehlerSections formallySmooth_cover_A0"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.swap (𝒱 : X.TwoAffineOpenCover) : X.TwoAffineOpenCover where
  U0 := 𝒱.U1
  U1 := 𝒱.U0
  isAffineOpen_U0 := 𝒱.isAffineOpen_U1
  isAffineOpen_U1 := 𝒱.isAffineOpen_U0
  sup_eq_top := by rw [sup_comm]; exact 𝒱.sup_eq_top
  isAffineOpen_inf := by rw [inf_comm]; exact 𝒱.isAffineOpen_inf

p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "swap"
@[scoped simp] theorem swap_U0 (𝒱 : X.TwoAffineOpenCover) : 𝒱.swap.U0 = 𝒱.U1 := rfl
@[scoped simp] theorem swap_U1 (𝒱 : X.TwoAffineOpenCover) : 𝒱.swap.U1 = 𝒱.U0 := rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
p2m_reactivate "P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry.Scheme.TwoAffineOpenCover"
p2m_reactivate "P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry"

namespace RESINJ

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

theorem formallySmooth_cover_A1 [Smooth c] : Algebra.FormallySmooth R (𝒱.cover c).A1 :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.formallySmooth_cover_A0 𝒱.swap c

theorem flat_kaehlerDifferential_cover_A0 [SmoothOfRelativeDimension 1 c] :
    Module.Flat (𝒱.cover c).A0 Ω[(𝒱.cover c).A0⁄R] := by
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI := AlgebraicGeometry.Scheme.TwoAffineOpenCover.formallySmooth_cover_A0 𝒱 c
  infer_instance

theorem flat_kaehlerDifferential_cover_A1 [SmoothOfRelativeDimension 1 c] :
    Module.Flat (𝒱.cover c).A1 Ω[(𝒱.cover c).A1⁄R] := by
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI := formallySmooth_cover_A1 𝒱 c
  infer_instance

theorem isDomain_cover_A0 [IsIntegral X] [Nonempty 𝒱.U0] : IsDomain (𝒱.cover c).A0 := by
  show IsDomain Γ(X, 𝒱.U0); infer_instance

theorem isDomain_cover_A1 [IsIntegral X] [Nonempty 𝒱.U1] : IsDomain (𝒱.cover c).A1 := by
  show IsDomain Γ(X, 𝒱.U1); infer_instance

theorem nonempty_U0_of_ringHom {L : Type*} [Semiring L] [Nontrivial L] (ι : (𝒱.cover c).A0 →+* L) :
    Nonempty 𝒱.U0 := by
  by_contra h
  have hU : 𝒱.U0 = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  haveI : Subsingleton (𝒱.cover c).A0 := by
    show Subsingleton Γ(X, 𝒱.U0)
    exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
  exact zero_ne_one (α := L) (by rw [← map_zero ι, ← map_one ι, Subsingleton.elim (0 : (𝒱.cover c).A0) 1])

end RESINJ
p2m_reactivate "P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry.Scheme.TwoAffineOpenCover"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry Opposite"

namespace RESINJ

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

private def swap' : X.TwoAffineOpenCover where
  U0 := 𝒱.U1
  U1 := 𝒱.U0
  isAffineOpen_U0 := 𝒱.isAffineOpen_U1
  isAffineOpen_U1 := 𝒱.isAffineOpen_U0
  sup_eq_top := by rw [sup_comm]; exact 𝒱.sup_eq_top
  isAffineOpen_inf := by rw [inf_comm]; exact 𝒱.isAffineOpen_inf

set_option maxHeartbeats 3200000 in

theorem kaehlerSections_H0_eq_zero_of_fst_eq_zero
    [IsIntegral X] [SmoothOfRelativeDimension 1 c] [Nonempty 𝒱.U0]
    (ω : (𝒱.kaehlerSections c).H0) (hω : ω.val.1 = 0) : ω = 0 := by

  suffices h2 : ω.val.2 = 0 from Subtype.ext (Prod.ext hω h2)

  have hc : (𝒱.kaehlerSections c).r1 ω.val.2 = 0 := by
    rw [← ((𝒱.kaehlerSections c).mem_H0_iff ω.val).mp ω.2, hω, map_zero]
  by_cases h1 : Nonempty 𝒱.U1
  swap
  ·
    have hU : 𝒱.U1 = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h1 ⟨⟨x, hx⟩⟩
    haveI : Subsingleton Γ(X, 𝒱.U1) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
    haveI : Subsingleton (𝒱.cover c).A1 := by show Subsingleton Γ(X, 𝒱.U1); infer_instance
    haveI : Subsingleton Ω[(𝒱.cover c).A1⁄R] := Module.subsingleton (𝒱.cover c).A1 _
    exact Subsingleton.elim _ _
  haveI := h1

  haveI h01 : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens) := by
    have hne : ((𝒱.U0 : Set X) ∩ (𝒱.U1 : Set X)).Nonempty :=
      nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen
        ⟨_, (Classical.arbitrary 𝒱.U0).2⟩ ⟨_, (Classical.arbitrary 𝒱.U1).2⟩
    exact hne.to_subtype

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : Algebra.FormallySmooth R (𝒱.cover c).A1 :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.formallySmooth_cover_A0 (swap' 𝒱) c
  haveI : IsDomain (𝒱.cover c).A1 := by show IsDomain Γ(X, 𝒱.U1); infer_instance
  letI : Algebra (𝒱.cover c).A1 X.functionField := (X.germToFunctionField 𝒱.U1).hom.toAlgebra
  letI : Algebra R X.functionField :=
    ((X.germToFunctionField 𝒱.U1).hom.comp (algebraMap R (𝒱.cover c).A1)).toAlgebra
  haveI : IsScalarTower R (𝒱.cover c).A1 X.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing (𝒱.cover c).A1 X.functionField := by
    show IsFractionRing Γ(X, 𝒱.U1) X.functionField
    exact functionField_isFractionRing_of_isAffineOpen X 𝒱.U1 𝒱.isAffineOpen_U1

  set g1 : (𝒱.cover c).A1 →+* X.functionField := (X.germToFunctionField 𝒱.U1).hom with hg1
  set g01 : (𝒱.cover c).A01 →+* X.functionField := (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom with hg01

  have hinj : Function.Injective (KaehlerDifferential.map R R (𝒱.cover c).A1 X.functionField) := by
    haveI : Algebra.FormallyEtale (𝒱.cover c).A1 X.functionField :=
      Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (𝒱.cover c).A1)
    have hbc : IsBaseChange X.functionField (KaehlerDifferential.map R R (𝒱.cover c).A1 X.functionField) :=
      KaehlerDifferential.isBaseChange_of_formallyEtale R (𝒱.cover c).A1 X.functionField
    have hfac : ∀ m, KaehlerDifferential.map R R (𝒱.cover c).A1 X.functionField m =
        hbc.equiv ((1 : X.functionField) ⊗ₜ[(𝒱.cover c).A1] m) := by
      intro m; rw [IsBaseChange.equiv_tmul, one_smul]
    have hinj1 : Function.Injective (fun m : Ω[(𝒱.cover c).A1⁄R] => (1 : X.functionField) ⊗ₜ[(𝒱.cover c).A1] m) := by
      have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω[(𝒱.cover c).A1⁄R])
        (Algebra.linearMap (𝒱.cover c).A1 X.functionField) (IsFractionRing.injective (𝒱.cover c).A1 X.functionField)
      intro m m' hmm'
      have : (Algebra.linearMap (𝒱.cover c).A1 X.functionField).rTensor _ ((1 : (𝒱.cover c).A1) ⊗ₜ[(𝒱.cover c).A1] m) =
          (Algebra.linearMap (𝒱.cover c).A1 X.functionField).rTensor _ ((1 : (𝒱.cover c).A1) ⊗ₜ[(𝒱.cover c).A1] m') := by
        simpa [LinearMap.rTensor_tmul] using hmm'
      simpa using (TensorProduct.lid (𝒱.cover c).A1 Ω[(𝒱.cover c).A1⁄R]).congr_arg (h this)
    intro m m' hmm'
    rw [hfac, hfac] at hmm'
    exact hinj1 (hbc.equiv.injective hmm')

  have hgerm : ∀ s : (𝒱.cover c).A1, g01 ((𝒱.cover c).ρ1 s) = g1 s := by
    intro s
    have hres := TopCat.Presheaf.germ_res X.presheaf (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1))
      (genericPoint X) (((genericPoint_spec X).mem_open_set_iff (𝒱.U0 ⊓ 𝒱.U1).isOpen).mpr (by simpa using h01))
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hres) s
  have h01R : g01.comp (algebraMap R (𝒱.cover c).A01) = (algebraMap R X.functionField).comp (RingHom.id R) := by
    ext r
    have e1 : algebraMap R (𝒱.cover c).A01 r = (𝒱.cover c).ρ1 (algebraMap R (𝒱.cover c).A1 r) :=
      ((𝒱.cover c).ρ1.commutes r).symm
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [e1, hgerm]
    rfl

  apply hinj
  rw [map_zero]
  have key : KaehlerDifferential.map R R (𝒱.cover c).A1 X.functionField ω.val.2 =
      KaehlerDifferential.mapOfRingHom (RingHom.id R) g01 h01R ((𝒱.kaehlerSections c).r1 ω.val.2) := by

    change _ = KaehlerDifferential.mapOfRingHom (RingHom.id R) g01 h01R
      (KaehlerDifferential.mapOfRingHom (RingHom.id R) (𝒱.cover c).ρ1.toRingHom
        (𝒱.cover c).ρ1_comp_algebraMap_eq_comp_id ω.val.2)
    have hcomp : g01.comp (𝒱.cover c).ρ1.toRingHom = g1 := RingHom.ext fun s => hgerm s
    have h1R : g1.comp (algebraMap R (𝒱.cover c).A1) = (algebraMap R X.functionField).comp (RingHom.id R) := rfl
    rw [KaehlerDifferential.mapOfRingHom_comp_apply _ _ _ _ _ _
      (h₃ := by rw [hcomp]; rfl)]
    exact (KaehlerDifferential.mapOfRingHom_apply_eq_map (RingHom.id R) g1 h1R hg1.symm ω.val.2).symm.trans
      (KaehlerDifferential.mapOfRingHom_congr hcomp.symm h1R _ ω.val.2)
  rw [key, hc, map_zero]

end RESINJ
p2m_reactivate "P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.AlgebraicGeometry.Scheme.TwoAffineOpenCover"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (hιinj : Function.Injective ι)
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1) :
    Function.Injective res := by

  haveI : Nonempty 𝒱.U0 := RESINJ.nonempty_U0_of_ringHom 𝒱 c ι
  haveI hdom : IsDomain (𝒱.cover c).A0 := RESINJ.isDomain_cover_A0 𝒱 c
  haveI hflat : Module.Flat (𝒱.cover c).A0 Ω[(𝒱.cover c).A0⁄↥(GaloisRep.ratLocalizedAt p)] := RESINJ.flat_kaehlerDifferential_cover_A0 𝒱 c
  have hL4 : ∀ ω : ↥((𝒱.kaehlerSections c).H0), ω.val.1 = 0 → ω = 0 :=
    fun ω h => RESINJ.kaehlerSections_H0_eq_zero_of_fst_eq_zero 𝒱 c ω h

  refine (injective_iff_map_eq_zero res).mpr fun ω hω => hL4 ω ?_
  rw [hres] at hω

  obtain ⟨j, hj⟩ : ∃ j : (FractionRing (𝒱.cover c).A0) →+* ↥(modularFunctionFieldBar N), j.comp (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)) = ι :=
    ⟨IsFractionRing.lift hιinj, RingHom.ext fun x => by
      rw [RingHom.comp_apply]
      exact IsFractionRing.lift_algebraMap (K := FractionRing (𝒱.cover c).A0) hιinj x⟩

  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0) := ((algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0)).toAlgebra
  haveI : @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra (FractionRing (𝒱.cover c).A0) ↥(modularFunctionFieldBar N) := j.toAlgebra
  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldBar N) := ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).toAlgebra
  haveI : @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0) Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl

  have hRK : ∀ r, algebraMap ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0) r = algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0) (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0 r) := fun _ => rfl
  have hRL : ∀ r, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldBar N) r = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r) := fun _ => rfl
  have hKL : algebraMap (FractionRing (𝒱.cover c).A0) ↥(modularFunctionFieldBar N) = j := rfl
  have hjA : ∀ a, j (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0) a) = ι a := fun a => RingHom.congr_fun hj a
  have hιr : ∀ r, ι (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0 r) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r) :=
    fun r => RingHom.congr_fun hιR r
  have hjR : ∀ r, j (algebraMap ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0) r) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldBar N) r := fun r => by
    rw [hRK, hjA, hιr, hRL]
  haveI : @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0) ↥(modularFunctionFieldBar N) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r => (hjR r).symm

  haveI : CharZero (FractionRing (𝒱.cover c).A0) := j.charZero
  haveI : Algebra.FormallyUnramified ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) := by
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    haveI : Algebra.FormallyUnramified ℚ (AlgebraicClosure ℚ) := Algebra.FormallyUnramified.of_isSeparable ℚ (AlgebraicClosure ℚ)
    haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
    haveI : Algebra.FormallyUnramified ℤ (AlgebraicClosure ℚ) := Algebra.FormallyUnramified.comp ℤ ℚ (AlgebraicClosure ℚ)
    haveI : @IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
    exact Algebra.FormallyUnramified.of_restrictScalars ℤ ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)

  have h01 : (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) = (algebraMap ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, RingHom.id_apply, hRK]
  have h12 : j.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0)) = (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldBar N)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, RingHom.id_apply, hjR]
  have h23 : (RingHom.id ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldBar N)) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, RingHom.id_apply, hRL]
  have h02 : (j.comp (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0))).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldBar N)).comp ((RingHom.id ↥(GaloisRep.ratLocalizedAt p)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, RingHom.id_apply, ← hRK, hjR]
  have h03 : ((RingHom.id ↥(modularFunctionFieldBar N)).comp (j.comp (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)))).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp ((RingHom.id ↥(GaloisRep.ratLocalizedAt p)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)))) :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, RingHom.id_apply, ← hRK, hjR, hRL]

  have fact : KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1 =
      KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) (RingHom.id ↥(modularFunctionFieldBar N)) h23
        (KaehlerDifferential.mapOfRingHom (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) j h12
          (KaehlerDifferential.mapOfRingHom (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)) h01 ω.val.1)) := by
    rw [KaehlerDifferential.mapOfRingHom_comp_apply (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)) h01
        (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) j h12 h02,
      KaehlerDifferential.mapOfRingHom_comp_apply _ _ h02 (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) (RingHom.id ↥(modularFunctionFieldBar N)) h23 h03]
    exact KaehlerDifferential.mapOfRingHom_congr (by rw [RingHom.id_comp, hj]) _ _ _

  have i1 : Function.Injective (KaehlerDifferential.mapOfRingHom (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)) h01) := by
    intro x y hxy
    rw [KaehlerDifferential.mapOfRingHom_apply_eq_map (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)) h01 rfl x,
      KaehlerDifferential.mapOfRingHom_apply_eq_map (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (algebraMap (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0)) h01 rfl y] at hxy
    exact RESINJ.kaehlerDifferential_map_injective_of_isFractionRing_of_flat ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0 (FractionRing (𝒱.cover c).A0) hxy
  have i2 : Function.Injective (KaehlerDifferential.mapOfRingHom (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) j h12) := by
    intro x y hxy
    rw [KaehlerDifferential.mapOfRingHom_apply_eq_map (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) j h12 hKL x,
      KaehlerDifferential.mapOfRingHom_apply_eq_map (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) j h12 hKL y] at hxy
    exact KaehlerDifferential.map_injective_of_charZero_of_field ↥(GaloisRep.ratLocalizedAt p) (FractionRing (𝒱.cover c).A0) ↥(modularFunctionFieldBar N) hxy
  have i3 : Function.Injective
      (KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) (RingHom.id ↥(modularFunctionFieldBar N)) h23) := by
    intro x y hxy
    rw [KaehlerDifferential.mapOfRingHom_apply_eq_map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) (RingHom.id ↥(modularFunctionFieldBar N)) h23
        rfl x,
      KaehlerDifferential.mapOfRingHom_apply_eq_map (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) (RingHom.id ↥(modularFunctionFieldBar N)) h23
        rfl y] at hxy
    exact KaehlerDifferential.map_injective_of_formallyUnramified ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) hxy

  rw [fact] at hω
  have e3 := i3 (hω.trans (map_zero _).symm)
  have e2 := i2 (e3.trans (map_zero _).symm)
  exact i1 (e2.trans (map_zero _).symm)

end S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero
end P2MW
export P2MW.S_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero (solution)
