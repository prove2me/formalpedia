-- Prove2me | solution 1 for GlobalTheory.exists_finiteEtale_latticeTorsionHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:23.788873+00:00
-- url     : https://prove2.me/submissions/eea61708-eb82-43c3-87b2-c5ef5ad3f9be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Theorems.Thm_GlobalTheory_LatticeTorsion_prop_powObj
import Theorems.Thm_GlobalTheory_LatticeTorsion_existsUnique_torsion
import Theorems.Thm_P2M_GlobalTheory_LatticeTorsion_torsion__pow_eq_one_04fd1c95385b
import Theorems.Thm_GlobalTheory_LatticeTorsion_eq_prod_zpow
import Theorems.Thm_GlobalTheory_GrpTangent_finiteEtale_mulN_torsion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open LatticeTorsion
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → IsUnit (n : Γ(S, ⊤)) → ∃ (Z : Over S) (et : La → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧ ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) → ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a := by
  intro S G _ _ n La _ _ _ hG hn
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  let b := Module.finBasis ℤ La
  let r := Module.finrank ℤ La
  let Z := Out.powObj (torsion G n) r
  let x : Fin r → (Z ⟶ G) := fun i => Out.powPr (torsion G n) i ≫ torsion.ι G n
  have hx : ∀ i, x i ^ n = 1 := fun i => by
    rw [← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]
  let et : La → (Z ⟶ G) := fun a => ∏ i, x i ^ (b.repr a i)
  have hadd : ∀ a c, et (a + c) = et a * et c := fun a c => by
    simp only [et, map_add, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et (b i) = x i := fun i => by
    simp only [et, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  refine ⟨Z, et, prop_powObj @IsFinite _ hfin r, prop_powObj @Etale _ het r, hadd, fun a => ?_,
    fun T et' hadd' hpow' => ?_⟩
  · simp only [et, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  · choose y hy hyu using fun i : Fin r => existsUnique_torsion G n (et' (b i)) (hpow' _)
    let h : T ⟶ Z := (Out.powIsLimit (torsion G n) r).lift (Fan.mk T y)
    have hh : ∀ i, h ≫ Out.powPr (torsion G n) i = y i := fun i =>
      (Out.powIsLimit (torsion G n) r).fac (Fan.mk T y) ⟨i⟩
    refine ⟨h, fun a => ?_, fun h' hh' => ?_⟩
    · rw [eq_prod_zpow b (fun a => h ≫ et a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
        eq_prod_zpow b et' hadd' a]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hb, ← hy i, ← hh i, Category.assoc]
    · refine (Out.powIsLimit (torsion G n) r).hom_ext fun ⟨i⟩ => ?_
      refine (hyu i _ ?_).trans (hh i).symm
      have := hh' (b i)
      rw [hb] at this
      exact (Category.assoc _ _ _).trans this
end GlobalTheory
