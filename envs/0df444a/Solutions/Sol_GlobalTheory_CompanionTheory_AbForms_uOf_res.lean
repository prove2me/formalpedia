-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.uOf_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:48:56.576701+00:00
-- url     : https://prove2.me/submissions/8d1802ab-b6b0-4930-b896-e08f5230dba5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_Zp_map
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_tzo_map
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_uOf_spec
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_of_algHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']
variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
variable [IsOpenImmersion x]
omit [IsOpenImmersion x]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [AddCommGroup M] [Module B M]
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution (α : B →ₐ[R] B') (x' : Sp B' ⟶ A.left) (hx' : x' ≫ A.hom = spMap (algebraMap R B'))
    (hxx : x' = spMap (α : B →+* B') ≫ x) :
    uOf hy x' hx' = ((SemiHom.of_algHom α).m1 : Ω[B⁄R] →ₗ[R] Ω[B'⁄R]) ∘ₗ uOf hy x hx := by
  let f : Ω[B⁄R] →ₗ[R] Ω[B'⁄R] := (SemiHom.of_algHom α).m1
  have hf : ∀ b m, (f : Ω[B⁄R] →+ Ω[B'⁄R]) (b • m) = (α : B →+* B') b • (f : Ω[B⁄R] →+ Ω[B'⁄R]) m :=
    fun b m ↦ (SemiHom.of_algHom α).oneFormMap_smul_semilinear b m
  have hα : (α : B →+* B').comp (algebraMap R B) = algebraMap R B' := α.comp_algebraMap
  have h0 : (tmap (α : B →+* B') (f : Ω[B⁄R] →+ Ω[B'⁄R]) hf).comp (sz (R := R) B Ω[B⁄R]) = sz B' Ω[B'⁄R] :=
    RingHom.ext fun r ↦ by
      ext
      · exact (fst_tmap _ _ hf _).trans (congrArg (fun t ↦ t r) hα)
      · exact (snd_tmap _ _ hf _).trans (map_zero _)
  have e : (tmap (α : B →+* B') (f : Ω[B⁄R] →+ Ω[B'⁄R]) hf).comp (diagSec R B : B →+* _) =
      (diagSec R B' : B' →+* _).comp (α : B →+* B') := RingHom.ext fun b ↦ by
    ext
    · exact (fst_tmap _ _ hf _).trans ((congrArg α (fst_derSec _ b)).trans (fst_derSec _ _).symm)
    · exact (snd_tmap _ _ hf _).trans ((congrArg f (snd_derSec _ b)).trans
        (((SemiHom.of_algHom α).m1_D b).trans (snd_derSec _ _).symm))
  have h := Zp_map x hx x' hx' (α : B →+* B') hxx hα (f : Ω[B⁄R] →+ Ω[B'⁄R]) hf (diagSec R B : B →+* _) diag_w
    (diagSec R B' : B' →+* _) diag_w e h0
  have h2 := tzo_map hy (α : B →+* B') hα f hf h0 (uOf hy x hx)
  rw [uOf_spec hy x hx, h2] at h
  exact (cot_unique (B := B') (M := Ω[B'⁄R]) hy _ (Zp_diag_fst x' hx')).unique (uOf_spec hy x' hx') h.symm
end GlobalTheory.CompanionTheory.AbForms
