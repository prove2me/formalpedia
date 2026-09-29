-- Prove2me | solution 1 for Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/12615a63-5a4e-5074-96a4-bab1105536ef

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace MK00Port

abbrev Tor1ResVanishing (R : Type) [CommRing R] [IsLocalRing R]
    (M : Type) [AddCommGroup M] [Module R M] : Prop :=
  IsZero (((Tor (ModuleCat.{0} R) 1).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))

section TorLES
variable {R : Type} [CommRing R]

theorem torLES_tensorRight_shortExact {S : ShortComplex (ModuleCat.{0} R)}
    (hS : S.ShortExact) (M : ModuleCat.{0} R) [Module.Flat R M] :
    (S.map (tensorRight M)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight M))
    (hS.map_of_exact (tensorLeft M))

@[reducible, simps]
noncomputable def torLES_resolutionTensorSES (S : ShortComplex (ModuleCat.{0} R))
    {Y : ModuleCat.{0} R} (P : ProjectiveResolution Y) :
    ShortComplex (HomologicalComplex (ModuleCat.{0} R) (ComplexShape.down ℕ)) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
    (by
      ext i : 1
      change S.f ▷ (P.complex.X i) ≫ S.g ▷ (P.complex.X i) = 0
      rw [← comp_whiskerRight, S.zero, MonoidalPreadditive.zero_whiskerRight])

theorem torLES_resolutionTensorSES_shortExact (S : ShortComplex (ModuleCat.{0} R))
    (hS : S.ShortExact) {Y : ModuleCat.{0} R} (P : ProjectiveResolution Y) :
    (torLES_resolutionTensorSES S P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact torLES_tensorRight_shortExact hS (P.complex.X i)

variable {Y : ModuleCat.{0} R} (P : ProjectiveResolution Y)

noncomputable def torLES_torIso (X : ModuleCat.{0} R) (n : ℕ) :
    ((Tor (ModuleCat.{0} R) n).obj X).obj Y ≅
      ((((curriedTensor (ModuleCat.{0} R)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology n :=
  P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{0} R)).obj X) n

theorem torLES_torMap_app_eq {X X' : ModuleCat.{0} R} (f : X ⟶ X') (n : ℕ) :
    ((Tor (ModuleCat.{0} R) n).map f).app Y =
      (torLES_torIso P X n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) n ≫
        (torLES_torIso P X' n).inv :=
  P.leftDerived_app_eq ((curriedTensor (ModuleCat.{0} R)).map f) n

noncomputable def torLES_torDelta (S : ShortComplex (ModuleCat.{0} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{0} R) (n + 1)).obj S.X₃).obj Y ⟶
      ((Tor (ModuleCat.{0} R) n).obj S.X₁).obj Y :=
  (torLES_torIso P S.X₃ (n + 1)).hom ≫
    (torLES_resolutionTensorSES_shortExact S hS P).δ (n + 1) n (by simp) ≫
    (torLES_torIso P S.X₁ n).inv

include P in

theorem torLES_torMap_comp_eq_zero (S : ShortComplex (ModuleCat.{0} R)) (n : ℕ) :
    ((Tor (ModuleCat.{0} R) n).map S.f).app Y ≫
      ((Tor (ModuleCat.{0} R) n).map S.g).app Y = 0 := by
  have hz : HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).f n ≫
      HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).g n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, (torLES_resolutionTensorSES S P).zero,
      HomologicalComplex.homologyMap_zero]
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  rw [torLES_torMap_app_eq P S.f n, torLES_torMap_app_eq P S.g n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

theorem torLES_torMap_comp_torDelta_eq_zero (S : ShortComplex (ModuleCat.{0} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{0} R) (n + 1)).map S.g).app Y ≫ torLES_torDelta P S hS n = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).comp_δ (n + 1) n (by simp)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq P S.g (n + 1)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

theorem torLES_torDelta_comp_eq_zero (S : ShortComplex (ModuleCat.{0} R))
    (hS : S.ShortExact) (n : ℕ) :
    torLES_torDelta P S hS n ≫ ((Tor (ModuleCat.{0} R) n).map S.f).app Y = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).δ_comp (n + 1) n (by simp)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq P S.f n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

theorem torLES_tor_exact₂ (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{0} R) n).map S.f).app Y)
      (((Tor (ModuleCat.{0} R) n).map S.g).app Y)
      (torLES_torMap_comp_eq_zero P S n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₁ n).symm (torLES_torIso P S.X₂ n).symm
      (torLES_torIso P S.X₃ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₂ n)
  · dsimp only
    rw [torLES_torMap_app_eq P S.f n]
    simp
  · dsimp only
    rw [torLES_torMap_app_eq P S.g n]
    simp

theorem torLES_tor_exact₃ (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{0} R) (n + 1)).map S.g).app Y)
      (torLES_torDelta P S hS n)
      (torLES_torMap_comp_torDelta_eq_zero P S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₂ (n + 1)).symm
      (torLES_torIso P S.X₃ (n + 1)).symm (torLES_torIso P S.X₁ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₃ (n + 1) n (by simp))
  · dsimp only
    rw [torLES_torMap_app_eq P S.g (n + 1)]
    simp
  · dsimp only [torLES_torDelta]
    simp

theorem torLES_tor_exact₁ (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (torLES_torDelta P S hS n)
      (((Tor (ModuleCat.{0} R) n).map S.f).app Y)
      (torLES_torDelta_comp_eq_zero P S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₃ (n + 1)).symm
      (torLES_torIso P S.X₁ n).symm (torLES_torIso P S.X₂ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₁ (n + 1) n (by simp))
  · dsimp only [torLES_torDelta]
    simp
  · dsimp only
    rw [torLES_torMap_app_eq P S.f n]
    simp

include P in

theorem torLES_tor_isZero_X₂ (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact)
    (n : ℕ) (h₁ : IsZero (((Tor (ModuleCat.{0} R) (n + 1)).obj S.X₁).obj Y))
    (h₃ : IsZero (((Tor (ModuleCat.{0} R) (n + 1)).obj S.X₃).obj Y)) :
    IsZero (((Tor (ModuleCat.{0} R) (n + 1)).obj S.X₂).obj Y) :=
  (torLES_tor_exact₂ P S hS (n + 1)).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end TorLES

section TorFV
variable {R : Type} [CommRing R]

theorem torFV_resolutionTensor_exactAt (M : ModuleCat.{0} R) [Module.Flat R M]
    {Y : ModuleCat.{0} R} (P : ProjectiveResolution Y) (n : ℕ) :
    ((((curriedTensor (ModuleCat.{0} R)).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).ExactAt (n + 1) :=
  Module.Flat.lTensor_shortComplex_exact M (P.complex.sc (n + 1))
    (P.complex_exactAt_succ n)

theorem torFV_tor_succ_isZero_of_flat_res (M : ModuleCat.{0} R) [Module.Flat R M]
    {Y : ModuleCat.{0} R} (P : ProjectiveResolution Y) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{0} R) (n + 1)).obj M).obj Y) := by
  refine IsZero.of_iso ?_ (torLES_torIso P M (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact torFV_resolutionTensor_exactAt M P n

theorem torFV_tor_succ_isZero_of_flat (M : ModuleCat.{0} R) [Module.Flat R M]
    (Y : ModuleCat.{0} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{0} R) (n + 1)).obj M).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  exact torFV_tor_succ_isZero_of_flat_res M P n

theorem torFV_tor_one_isZero_of_flat (M : ModuleCat.{0} R) [Module.Flat R M]
    (Y : ModuleCat.{0} R) :
    IsZero (((Tor (ModuleCat.{0} R) 1).obj M).obj Y) :=
  torFV_tor_succ_isZero_of_flat M Y 0

theorem torFV_tor_succ_isZero_of_isZero (X : ModuleCat.{0} R) (hX : IsZero X)
    (Y : ModuleCat.{0} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{0} R) (n + 1)).obj X).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  refine IsZero.of_iso ?_ (torLES_torIso P X (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.ExactAt.of_isZero
    ((tensorRight (P.complex.X (n + 1))).map_isZero hX)

theorem torFV_tor_one_isZero_of_isZero (X : ModuleCat.{0} R) (hX : IsZero X)
    (Y : ModuleCat.{0} R) :
    IsZero (((Tor (ModuleCat.{0} R) 1).obj X).obj Y) :=
  torFV_tor_succ_isZero_of_isZero X hX Y 0

end TorFV

section TorZeroBridge
variable {R : Type} [CommRing R]

theorem ar_opcyclesMap_fromLeftDerivedZero'_naturality
    {Y : ModuleCat.{0} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{0} R}
    (f : X ⟶ X') :
    HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{0} R)).obj X') =
      P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{0} R)).obj X) ≫
        ((curriedTensor (ModuleCat.{0} R)).map f).app Y := by
  rw [← cancel_epi (HomologicalComplex.pOpcycles
    ((((curriedTensor (ModuleCat.{0} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex) 0)]
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero', ← Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  exact (((curriedTensor (ModuleCat.{0} R)).map f).naturality (P.π.f 0)).symm

theorem ar_tor0_map_fromLeftDerivedZero_naturality
    {Y : ModuleCat.{0} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{0} R}
    (f : X ⟶ X') :
    ((Tor (ModuleCat.{0} R) 0).map f).app Y ≫
        ((curriedTensor (ModuleCat.{0} R)).obj X').fromLeftDerivedZero.app Y =
      ((curriedTensor (ModuleCat.{0} R)).obj X).fromLeftDerivedZero.app Y ≫
        ((curriedTensor (ModuleCat.{0} R)).map f).app Y := by
  have hM : ((Tor (ModuleCat.{0} R) 0).map f).app Y =
      (torLES_torIso P X 0).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 ≫
        (torLES_torIso P X' 0).inv :=
    torLES_torMap_app_eq P f 0
  have hF : ((curriedTensor (ModuleCat.{0} R)).obj X).fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{0} R)).obj X) 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{0} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{0} R)).obj X) :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{0} R)).obj X)
  have hG : ((curriedTensor (ModuleCat.{0} R)).obj X').fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{0} R)).obj X') 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{0} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{0} R)).obj X') :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{0} R)).obj X')
  have hι : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{0} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 =
      HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{0} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{0} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 := by
    apply HomologicalComplex.homologyι_naturality
  have hO := ar_opcyclesMap_fromLeftDerivedZero'_naturality P f
  have hbr : ∀ {Z : ModuleCat.{0} R}
      (h : ((((curriedTensor (ModuleCat.{0} R)).obj X').mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 0 ⟶ Z),
      (torLES_torIso P X' 0).inv ≫
        (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{0} R)).obj X') 0).hom ≫ h = h :=
    fun {Z} h => (torLES_torIso P X' 0).inv_hom_id_assoc h
  have hbr2 : (torLES_torIso P X 0).hom =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{0} R)).obj X) 0).hom := rfl
  rw [hM, hF, hG]
  simp only [Category.assoc]

  refine Eq.trans (whisker_eq _ (whisker_eq _ (hbr _))) ?_
  refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hι _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hO)) ?_
  exact eq_whisker hbr2 _

theorem ar_rTensor_injective_of_tor1_isZero
    {A B M : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] (e : A →ₗ[R] B) (he : Function.Injective e)
    (h1 : IsZero (((Tor (ModuleCat.{0} R) 1).obj
      (ModuleCat.of R (B ⧸ LinearMap.range e))).obj (ModuleCat.of R M))) :
    Function.Injective (LinearMap.rTensor M e) := by
  classical
  set S₀ : ShortComplex (ModuleCat.{0} R) := ShortComplex.mk (ModuleCat.ofHom e)
    (ModuleCat.ofHom (LinearMap.range e).mkQ)
    (by
      have hz : (LinearMap.range e).mkQ ∘ₗ e = 0 := LinearMap.ext fun a => by
        simpa [Submodule.Quotient.mk_eq_zero] using LinearMap.mem_range_self e a
      rw [← ModuleCat.ofHom_comp, hz]
      rfl) with hS₀def
  have hS : S₀.ShortExact := by
    refine ModuleCat.shortComplex_shortExact S₀ ?_ ?_ ?_
    · exact LinearMap.exact_map_mkQ_range e
    · exact he
    · exact Submodule.mkQ_surjective _
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution (ModuleCat.of R M)) :=
    HasProjectiveResolution.out
  have hδ : torLES_torDelta P S₀ hS 0 = 0 := h1.eq_of_src _ _
  haveI hmono : Mono (((Tor (ModuleCat.{0} R) 0).map S₀.f).app (ModuleCat.of R M)) :=
    (torLES_tor_exact₁ P S₀ hS 0).mono_g hδ
  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{0} R)).obj S₀.X₁) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{0} R)).obj S₀.X₂) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hsq := ar_tor0_map_fromLeftDerivedZero_naturality P S₀.f
  have hfac : ((curriedTensor (ModuleCat.{0} R)).map S₀.f).app (ModuleCat.of R M) =
      inv (((curriedTensor (ModuleCat.{0} R)).obj S₀.X₁).fromLeftDerivedZero.app
        (ModuleCat.of R M)) ≫
      (((Tor (ModuleCat.{0} R) 0).map S₀.f).app (ModuleCat.of R M) ≫
      ((curriedTensor (ModuleCat.{0} R)).obj S₀.X₂).fromLeftDerivedZero.app
        (ModuleCat.of R M)) :=
    (IsIso.eq_inv_comp (((curriedTensor (ModuleCat.{0} R)).obj
      S₀.X₁).fromLeftDerivedZero.app (ModuleCat.of R M))).mpr hsq.symm
  haveI hmono₂ : Mono (((curriedTensor (ModuleCat.{0} R)).obj S₀.X₂).fromLeftDerivedZero.app
      (ModuleCat.of R M)) := IsIso.mono_of_iso _
  haveI hmono₁ : Mono (inv (((curriedTensor (ModuleCat.{0} R)).obj
      S₀.X₁).fromLeftDerivedZero.app (ModuleCat.of R M))) := IsIso.mono_of_iso _
  have hm2 : Mono (((curriedTensor (ModuleCat.{0} R)).map S₀.f).app (ModuleCat.of R M)) := by
    rw [hfac]
    exact mono_comp' hmono₁ (mono_comp' hmono hmono₂)
  exact (ModuleCat.mono_iff_injective
    (((curriedTensor (ModuleCat.{0} R)).map S₀.f).app (ModuleCat.of R M))).mp hm2

end TorZeroBridge

section FiniteLengthSupply
variable {R : Type} [CommRing R]

theorem ar_isSemisimpleModule_of_isTorsionBySet_isMaximal
    (I : Ideal R) [I.IsMaximal] (M : Type) [AddCommGroup M] [Module R M]
    (htor : Module.IsTorsionBySet R M (I : Set R)) :
    IsSemisimpleModule R M := by
  letI := htor.module
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  exact htor.isSemisimpleModule_iff.mp inferInstance

theorem ar_isFiniteLength_of_finite_of_torsionBySet_pow
    [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (htor : Module.IsTorsionBySet R M ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) :
    IsFiniteLength R M := by
  revert M
  induction n with
  | zero =>
    intro M _ _ _ htor
    haveI : Subsingleton M := by
      refine ⟨fun a b => ?_⟩
      have h1 : (1 : R) ∈ ((IsLocalRing.maximalIdeal R ^ 0 : Ideal R) : Set R) := by
        rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      have ha : (1 : R) • a = 0 := htor (a := ⟨(1 : R), h1⟩)
      have hb : (1 : R) • b = 0 := htor (a := ⟨(1 : R), h1⟩)
      rw [one_smul] at ha hb
      rw [ha, hb]
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    intro M _ _ _ htor

    have htorN : Module.IsTorsionBySet R
        (↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M))
        ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
      rintro ⟨v, hv⟩ ⟨a, ha⟩
      have hav : a • v = 0 := by
        refine Submodule.smul_induction_on hv (fun r hr m _ => ?_)
          (fun u w hu hw => by rw [smul_add, hu, hw, add_zero])
        rw [smul_smul]
        have hmem : a * r ∈ ((IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) : Set R) := by
          rw [mul_comm, pow_succ]
          exact Ideal.mul_mem_mul hr ha
        exact htor (a := ⟨a * r, hmem⟩)
      exact Subtype.ext hav
    haveI hssN : IsSemisimpleModule R
        ↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) :=
      ar_isSemisimpleModule_of_isTorsionBySet_isMaximal
        (IsLocalRing.maximalIdeal R) _ htorN
    haveI : Module.Finite R
        ↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) :=
      Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    haveI hartN : IsArtinian R
        ↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) := inferInstance

    have hquot : IsFiniteLength R
        (M ⧸ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M)) := by
      refine ih _ ?_
      intro x a
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
        ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) x
      have hsm : Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
            Submodule R M) ((a : R) • m) =
          (a : R) • Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
            Submodule R M) m :=
        map_smul (Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
          Submodule R M)) (a : R) m
      rw [← hsm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul a.2 Submodule.mem_top
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hquot ⊢
    exact ⟨(isNoetherian_iff_submodule_quotient _).mpr ⟨inferInstance, hquot.1⟩,
      (isArtinian_iff_submodule_quotient _).mpr ⟨hartN, hquot.2⟩⟩

theorem ar_isFiniteLength_quotient_pow_smul [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) :
    IsFiniteLength R
      (R ⧸ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R R)) := by
  refine ar_isFiniteLength_of_finite_of_torsionBySet_pow n _ ?_
  intro x a
  obtain ⟨r, rfl⟩ :=
    Submodule.mkQ_surjective ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R R) x
  have hsm : Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
        Submodule R R) ((a : R) • r) =
      (a : R) • Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
        Submodule R R) r :=
    map_smul (Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
      Submodule R R)) (a : R) r
  rw [← hsm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul a.2 Submodule.mem_top

end FiniteLengthSupply

section DepthBookkeeping
variable {R : Type} [CommRing R]

theorem ar_tmul_mem_smul_top {B M : Type} [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] (a : Ideal R) (P : Submodule R B) {v : B}
    (hv : v ∈ a • P) (m : M) (hvP : v ∈ P) :
    ((⟨v, hvP⟩ : ↥P) ⊗ₜ[R] m) ∈ a • (⊤ : Submodule R (↥P ⊗[R] M)) := by
  have H : v ∈ P ∧ ∀ (h' : v ∈ P),
      ((⟨v, h'⟩ : ↥P) ⊗ₜ[R] m) ∈ a • (⊤ : Submodule R (↥P ⊗[R] M)) := by
    refine Submodule.smul_induction_on hv (fun r hr u hu => ?_) (fun x y hx hy => ?_)
    · refine ⟨P.smul_mem r hu, fun h' => ?_⟩
      have hmk : (⟨r • u, h'⟩ : ↥P) = r • (⟨u, hu⟩ : ↥P) := rfl
      rw [hmk, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · refine ⟨P.add_mem hx.1 hy.1, fun h' => ?_⟩
      have hmk : (⟨x + y, h'⟩ : ↥P) = (⟨x, hx.1⟩ : ↥P) + (⟨y, hy.1⟩ : ↥P) := rfl
      rw [hmk, TensorProduct.add_tmul]
      exact Submodule.add_mem _ (hx.2 hx.1) (hy.2 hy.1)
  exact H.2 hvP

theorem ar_rTensor_inclusion_apply_mem_smul {B M : Type} [AddCommGroup B]
    [Module R B] [AddCommGroup M] [Module R M] (a : Ideal R) {N P : Submodule R B}
    (hNP : N ≤ P) (hNa : N ≤ a • P) (y : ↥N ⊗[R] M) :
    LinearMap.rTensor M (Submodule.inclusion hNP) y ∈
      a • (⊤ : Submodule R (↥P ⊗[R] M)) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul w m =>
    rw [LinearMap.rTensor_tmul]
    exact ar_tmul_mem_smul_top a P (hNa w.2) m (hNP w.2)
  | add y₁ y₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂

theorem ar_mem_smul_pow_extend {S : Type} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] {W : Type}
    [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W] (k : ℕ) {z : W}
    (hz : z ∈ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) • ⊤ : Submodule R W)) :
    z ∈ ((IsLocalRing.maximalIdeal S ^ k : Ideal S) • ⊤ : Submodule S W) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_)
    (fun u v hu hv => Submodule.add_mem _ hu hv)
  rw [← algebraMap_smul S r w]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  have h1 : algebraMap R S r ∈ (IsLocalRing.maximalIdeal R ^ k).map (algebraMap R S) :=
    Ideal.mem_map_of_mem _ hr
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (algebraMap R S)) k h1

theorem ar_finite_tensorProduct_left (S : Type) [CommRing S] [Algebra R S]
    (M N : Type) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module.Finite S M] [Module.Finite R N] :
    Module.Finite S (M ⊗[R] N) := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (R := R) (M := N)
  have hsurj : Function.Surjective
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : M →ₗ[S] M) π) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul m y =>
      obtain ⟨v, rfl⟩ := hπ y
      exact ⟨m ⊗ₜ v, by simp⟩
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨w₁, rfl⟩ := h₁
      obtain ⟨w₂, rfl⟩ := h₂
      exact ⟨w₁ + w₂, map_add _ _ _⟩
  haveI : Module.Finite S (M ⊗[R] (Fin n → R)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight R S M (Fin n)).symm
  exact Module.Finite.of_surjective _ hsurj

end DepthBookkeeping

section ArtinReesTail
variable {R : Type} [CommRing R]

theorem ar_mem_range_rTensor_inf_of_ker {M : Type} [AddCommGroup M]
    [Module R M] (I : Ideal R) (J : Submodule R R)
    (htor1 : ∀ W : Submodule R (R ⧸ J),
      IsZero (((Tor (ModuleCat.{0} R) 1).obj (ModuleCat.of R ((R ⧸ J) ⧸ W))).obj
        (ModuleCat.of R M)))
    {x : ↥I ⊗[R] M} (hx : LinearMap.rTensor M (Submodule.subtype I) x = 0) :
    x ∈ Set.range (LinearMap.rTensor M
      (Submodule.inclusion (inf_le_right : J ⊓ (I : Submodule R R) ≤ I))) := by
  classical
  set g : ↥I →ₗ[R] R ⧸ J := J.mkQ ∘ₗ Submodule.subtype I with hg
  have hker : LinearMap.ker g.rangeRestrict =
      LinearMap.range (Submodule.inclusion
        (inf_le_right : J ⊓ (I : Submodule R R) ≤ I)) := by
    rw [LinearMap.ker_rangeRestrict, hg, LinearMap.ker_comp, Submodule.ker_mkQ,
      Submodule.range_inclusion, Submodule.comap_inf, Submodule.comap_subtype_self,
      inf_top_eq]
  have hexact : Function.Exact
      (Submodule.inclusion (inf_le_right : J ⊓ (I : Submodule R R) ≤ I))
      g.rangeRestrict := LinearMap.exact_iff.mpr hker
  have htex := rTensor_exact M hexact
    (LinearMap.surjective_rangeRestrict (f := g))
  have hinj : Function.Injective
      (LinearMap.rTensor M (Submodule.subtype (LinearMap.range g))) :=
    ar_rTensor_injective_of_tor1_isZero (Submodule.subtype (LinearMap.range g))
      (Submodule.injective_subtype _)
      (htor1 (LinearMap.range (Submodule.subtype (LinearMap.range g))))
  have hfac : (LinearMap.range g).subtype ∘ₗ g.rangeRestrict = g := rfl
  have h0 : LinearMap.rTensor M g.rangeRestrict x = 0 := by
    apply hinj
    rw [← LinearMap.rTensor_comp_apply, hfac, hg, LinearMap.rTensor_comp_apply, hx,
      map_zero, map_zero]
  exact (htex x).mp h0

theorem ar_flat_of_finiteLength_tor1_isZero (R' S M : Type) [CommRing R']
    [CommRing S] [Algebra R' S] [IsLocalRing R'] [IsLocalRing S] [AddCommGroup M]
    [Module R' M] [Module S M] [IsScalarTower R' S M] (hR : IsNoetherianRing R')
    (hS : IsNoetherianRing S) (hloc : IsLocalHom (algebraMap R' S))
    (hfin : Module.Finite S M)
    (htor : ∀ (N : Type) [AddCommGroup N] [Module R' N], IsFiniteLength R' N →
      IsZero (((Tor (ModuleCat.{0} R') 1).obj (ModuleCat.of R' N)).obj
        (ModuleCat.of R' M))) :
    Module.Flat R' M := by
  haveI := hR
  haveI := hS
  haveI := hloc
  haveI := hfin
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  haveI : Module.Finite R' (↥I) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian I)
  haveI : Module.Finite S (M ⊗[R'] ↥I) :=
    ar_finite_tensorProduct_left S M ↥I
  obtain ⟨c, hc⟩ :=
    Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal R') (I : Submodule R' R')

  have hxk : ∀ k : ℕ,
      x ∈ ((IsLocalRing.maximalIdeal R' ^ k : Ideal R') • ⊤ :
        Submodule R' (↥I ⊗[R'] M)) := by
    intro k
    have htor1 : ∀ W : Submodule R'
        (R' ⧸ ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤ : Submodule R' R')),
        IsZero (((Tor (ModuleCat.{0} R') 1).obj
          (ModuleCat.of R'
            ((R' ⧸ ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤ :
              Submodule R' R')) ⧸ W))).obj (ModuleCat.of R' M)) := by
      intro W
      refine htor _ ?_
      exact (ar_isFiniteLength_quotient_pow_smul (c + k)).of_surjective
        (Submodule.mkQ_surjective W)
    obtain ⟨y, hy⟩ := ar_mem_range_rTensor_inf_of_ker I
      ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤) htor1 hx
    have hAR : ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤ : Submodule R' R')
        ⊓ (I : Submodule R' R') ≤
        (IsLocalRing.maximalIdeal R' ^ k : Ideal R') • (I : Submodule R' R') := by
      have h1 := hc (c + k) (Nat.le_add_right c k)
      have h2 : c + k - c = k := by omega
      rw [h1, h2]
      exact Submodule.smul_mono le_rfl inf_le_right
    rw [← hy]
    exact ar_rTensor_inclusion_apply_mem_smul _ inf_le_right hAR y

  set y := TensorProduct.comm R' (↥I) M x with hydef
  have hyk : ∀ k : ℕ,
      y ∈ ((IsLocalRing.maximalIdeal S ^ k : Ideal S) • ⊤ :
        Submodule S (M ⊗[R'] ↥I)) := by
    intro k
    refine ar_mem_smul_pow_extend (R := R') k ?_
    have hmap := Submodule.mem_map_of_mem
      (f := (TensorProduct.comm R' (↥I) M).toLinearMap) (hxk k)
    rw [Submodule.map_smul''] at hmap
    exact Submodule.smul_mono le_rfl le_top hmap
  have hy0 : y = 0 := by
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
      (M := M ⊗[R'] ↥I) (IsLocalRing.maximalIdeal S)
      (Ideal.IsMaximal.ne_top inferInstance)
    have hmem : y ∈ (⨅ k : ℕ, (IsLocalRing.maximalIdeal S ^ k : Ideal S) • ⊤ :
        Submodule S (M ⊗[R'] ↥I)) := Submodule.mem_iInf _ |>.mpr hyk
    rw [hbot] at hmem
    simpa using hmem
  have := (LinearEquiv.map_eq_zero_iff (TensorProduct.comm R' (↥I) M)).mp
    (by rw [← hydef]; exact hy0)
  exact this

theorem ar_flat_of_finiteLength_tor1_isZero_00MK (R' S M : Type) [CommRing R']
    [CommRing S] [Algebra R' S] [IsLocalRing R'] [IsLocalRing S] [AddCommGroup M]
    [Module R' M] [Module S M] [IsScalarTower R' S M] (hR : IsNoetherianRing R')
    (hS : IsNoetherianRing S) (hloc : IsLocalHom (algebraMap R' S))
    (hfin : Module.Finite S M)
    (htor : ∀ (N : Type) [AddCommGroup N] [Module R' N], IsFiniteLength R' N →
      IsZero (((Tor (ModuleCat R') 1).obj (ModuleCat.of R' N)).obj
        (ModuleCat.of R' M))) :
    Module.Flat R' M :=
  ar_flat_of_finiteLength_tor1_isZero R' S M hR hS hloc hfin htor

end ArtinReesTail

section Devissage
variable {R : Type} [CommRing R]

theorem dv_tor_isZero_of_iso {X X' Y : ModuleCat.{0} R} (e : X ≅ X') (n : ℕ)
    (h : IsZero (((Tor (ModuleCat.{0} R) n).obj X').obj Y)) :
    IsZero (((Tor (ModuleCat.{0} R) n).obj X).obj Y) :=
  h.of_iso (((Tor (ModuleCat.{0} R) n).mapIso e).app Y)

theorem dv_simple_equiv_residueField (R : Type) [CommRing R] [IsLocalRing R]
    (S : Type) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Nonempty (S ≃ₗ[R] IsLocalRing.ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := S)).mp ‹_›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

theorem dv_tor1_simple_isZero (R : Type) [CommRing R] [IsLocalRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    (hκ : IsZero (((Tor (ModuleCat.{0} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M)))
    (S : Type) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    IsZero (((Tor (ModuleCat.{0} R) 1).obj (ModuleCat.of R S)).obj (ModuleCat.of R M)) := by
  obtain ⟨e⟩ := dv_simple_equiv_residueField R S
  exact dv_tor_isZero_of_iso e.toModuleIso 1 hκ

theorem dv_tor1_isZero_of_isFiniteLength {R : Type} [CommRing R] [IsLocalRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    (hκ : IsZero (((Tor (ModuleCat.{0} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M)))
    (N : Type) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    IsZero (((Tor (ModuleCat.{0} R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) := by
  induction hN with
  | @of_subsingleton N _ _ _ =>
    exact torFV_tor_one_isZero_of_isZero (ModuleCat.of R N)
      (ModuleCat.isZero_of_subsingleton _) (ModuleCat.of R M)
  | @of_simple_quotient N _ _ N' _ _ ih =>
    obtain ⟨P⟩ : Nonempty (ProjectiveResolution (ModuleCat.of R M)) :=
      HasProjectiveResolution.out
    refine torLES_tor_isZero_X₂ P (LinearMap.shortComplexKer (N'.mkQ))
      (LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective N')) 0 ?_ ?_
    · exact dv_tor_isZero_of_iso
        (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ N')).toModuleIso 1 ih
    · exact dv_tor1_simple_isZero R hκ (N ⧸ N')

theorem dv_tor1_isZero_of_isFiniteLength_00MK (R M : Type) [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M]
    (hκ : Tor1ResVanishing R M)
    (N : Type) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) :=
  dv_tor1_isZero_of_isFiniteLength hκ N hN

end Devissage

end MK00Port
end

open CategoryTheory CategoryTheory.Limits MK00Port in

theorem solution
    {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{0} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M := by
  exact ar_flat_of_finiteLength_tor1_isZero_00MK R S M ‹_› ‹_› ‹_› ‹_›
    (fun N _ _ hN => dv_tor1_isZero_of_isFiniteLength_00MK R M hκ N hN)

end S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
end P2MW
export P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero (solution)
