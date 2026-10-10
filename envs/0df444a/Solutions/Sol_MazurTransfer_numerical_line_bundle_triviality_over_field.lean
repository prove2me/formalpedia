-- Prove2me | solution 1 for MazurTransfer.numerical_line_bundle_triviality_over_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T23:06:02.900992+00:00
-- url     : https://prove2.me/submissions/8ec2bf8c-e095-48f1-9b82-277f5e66c488

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete helper proofs reused from official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: numerical degree-zero line bundles and nonzero global
sections over an arbitrary field. Named downstream consumer: injectivity
of the unchanged actual order-13 arithmetic Picard class map.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
universe u
namespace MazurTransfer.PublicNumericalTrivialityHelpers
noncomputable def isoUnitOfIdempotentOfInverse {C : Type*} [Category C] [MonoidalCategory C] {N M : C}
    (e : N ≅ N ⊗ N) (p : N ⊗ M ≅ 𝟙_ C) : N ≅ 𝟙_ C :=
  (ρ_ N).symm ≪≫ whiskerLeftIso N p.symm ≪≫ (α_ N N M).symm ≪≫ whiskerRightIso e.symm M ≪≫ p


theorem nonempty_invModule_top_iso (Y : Scheme.{u}) :
    Nonempty ((⊤ : Y.IdealSheafData).invModule ≅ 𝟙_ Y.Modules) := by
  have hT : (⊤ : Y.IdealSheafData).IsInvertible := Scheme.IdealSheafData.isInvertible_top

  obtain ⟨m⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hT hT
  have e : (⊤ : Y.IdealSheafData).invModule ≅ (⊤ : Y.IdealSheafData).invModule ⊗ (⊤ : Y.IdealSheafData).invModule :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule (Scheme.IdealSheafData.mul_top ⊤).symm) ≪≫ m

  have hN : Scheme.Modules.IsInvertible (⊤ : Y.IdealSheafData).invModule :=
    Scheme.IdealSheafData.IsInvertible.isInvertible_invModule hT
  have hev := Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit hN
  exact ⟨isoUnitOfIdempotentOfInverse e (@asIso _ _ _ _ ((ihom.ev (⊤ : Y.IdealSheafData).invModule).app (𝟙_ Y.Modules)) hev)⟩


theorem nonempty_lineBundle_iso_of_degree_zero {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f 0 g) : Nonempty (D.lineBundle ≅ 𝟙_ (pullback f g).Modules) := by
  obtain ⟨e⟩ := nonempty_invModule_top_iso (pullback f g)
  exact ⟨eqToIso (congrArg Scheme.IdealSheafData.invModule D.I_eq_top_of_degree_zero) ≪≫ e⟩


noncomputable def isoPullbackInvPullbackObj {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm


theorem eq_zero_of_pullback_map_eq_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p]
    {A B : Y.Modules} (φ : A ⟶ B) (h : (Scheme.Modules.pullback p).map φ = 0) : φ = 0 := by

  have hn : (Scheme.Modules.pullback (inv p)).map ((Scheme.Modules.pullback p).map φ) ≫
      (isoPullbackInvPullbackObj p B).inv = (isoPullbackInvPullbackObj p A).inv ≫ φ :=
    (Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).hom.naturality φ
  rw [h, Functor.map_zero, zero_comp] at hn
  exact (cancel_epi (isoPullbackInvPullbackObj p A).inv).mp (hn.symm.trans (comp_zero).symm)


theorem pullbackSection_ne_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] {M : Y.Modules}
    (s : 𝟙_ Y.Modules ⟶ M) (hs : s ≠ 0) : Scheme.Modules.pullbackSection p s ≠ 0 := by
  intro h
  apply hs
  apply eq_zero_of_pullback_map_eq_zero p

  exact ((Scheme.Modules.pullbackUnitIso p).hom_inv_id_assoc ((Scheme.Modules.pullback p).map s)).symm.trans
    ((congrArg ((Scheme.Modules.pullbackUnitIso p).hom ≫ ·) h).trans comp_zero)

theorem twoAffineOpenCover_ext {Y : Scheme.{u}} {𝒲 𝒲' : Y.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒲'.U0) (h1 : 𝒲.U1 = 𝒲'.U1) : 𝒲 = 𝒲' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒲
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒲'
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

end MazurTransfer.PublicNumericalTrivialityHelpers
open MazurTransfer.PublicNumericalTrivialityHelpers

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hχ : (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf x M).H1 =
      (Module.finrank k (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf x (𝟙_ X.Modules)).H1)
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by
  let p := pullback.fst x (𝟙 (Spec (CommRingCat.of k)))
  have hp : p ≫ x = pullback.snd x (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.condition.trans (Category.comp_id _)
  obtain ⟨𝒱', h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) x (asIso p) hp 𝒱 M
      ((Scheme.Modules.pullback p).obj M) (Iso.refl _)
  obtain ⟨𝒲, hU0, hU1, ⟨u0⟩, ⟨u1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) x (asIso p) hp 𝒱
      (𝟙_ X.Modules) (𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules)
      (Scheme.Modules.pullbackUnitIso p).symm
  have hc : 𝒲 = 𝒱' := twoAffineOpenCover_ext (hU0.trans h0.symm) (hU1.trans h1.symm)
  subst 𝒲
  have hχ' :
      (Module.finrank k (𝒱'.sectionsOf (pullback.snd x (𝟙 _))
        ((Scheme.Modules.pullback p).obj M)).H0 : ℤ) -
        Module.finrank k (𝒱'.sectionsOf (pullback.snd x (𝟙 _))
          ((Scheme.Modules.pullback p).obj M)).H1 =
      (Module.finrank k (𝒱'.sectionsOf (pullback.snd x (𝟙 _))
        (𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules)).H0 : ℤ) -
        Module.finrank k (𝒱'.sectionsOf (pullback.snd x (𝟙 _))
          (𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1 + 0 := by
    rw [e0.finrank_eq, e1.finrank_eq, u0.finrank_eq, u1.finrank_eq, add_zero]
    exact hχ
  obtain ⟨D, -, e, -⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
    (f := x) (𝟙 _) (hM.pullback p) (Scheme.Modules.pullbackSection p s)
    (pullbackSection_ne_zero p s hs) 𝒱' 0 (by simpa only [Nat.cast_zero] using hχ')
  obtain ⟨eu⟩ := nonempty_lineBundle_iso_of_degree_zero D
  exact ⟨isoPullbackInvPullbackObj p M ≪≫ (Scheme.Modules.pullback (inv p)).mapIso (e ≪≫ eu) ≪≫
    Scheme.Modules.pullbackUnitIso (inv p)⟩

#print axioms solution
