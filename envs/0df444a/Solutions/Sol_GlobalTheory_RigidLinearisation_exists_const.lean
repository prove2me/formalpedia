-- Prove2me | solution 1 for GlobalTheory.RigidLinearisation.exists_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:56:33.936686+00:00
-- url     : https://prove2.me/submissions/6efa68b7-cfa3-4aef-a257-5b5b7611f04f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearisation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.RigidLinearisation
namespace GlobalTheory.RigidLinearisation
theorem _root_.solution {k : Type} [Field k] [IsAlgClosed k] {F : Scheme.{0}} [IsIntegral F] (q : F ⟶ Sp k)
    (c : Γ(F, ⊤)) {n : ℕ} (hn : n ≠ 0) (hc : c ^ n = 1) : ∃ a : Γ(Sp k, ⊤), (q.app ⊤).hom a = c := by
  let f : k →+* Γ(F, ⊤) := (q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Splits := IsAlgClosed.splits _
  have hm : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Monic := Polynomial.monic_X_pow_sub_C _ hn
  have e := congrArg (Polynomial.eval₂ f c) (hs.eq_prod_roots_of_monic hm)
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at e
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one, hc, sub_self,
    Polynomial.eval₂_one] at e
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 e.symm)
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at ha
  exact ⟨_, (sub_eq_zero.1 ha).symm⟩
end GlobalTheory.RigidLinearisation
