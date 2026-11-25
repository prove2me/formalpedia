-- Prove2me | solution 1 for GlobalTheory.SharpFamRel.rel_of_isSharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:07:30.277596+00:00
-- url     : https://prove2.me/submissions/b4ef6048-fb39-44dc-bc5e-da978991ee1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
import Theorems.Thm_GlobalTheory_SharpFamRel_zpow_finsetSum
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpFamRel
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
variable {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {S : Scheme.{0}} {s : S ⟶ Sp o}
namespace GlobalTheory.SharpFamRel
theorem _root_.solution {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) :
    (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧
    (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧
    ∀ j i, t.pt i ≫ t.act j =
      (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by
  obtain ⟨pr, hpr, huniq, -, hact, hpt⟩ := H
  have ext : ∀ {T : Over S} (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y :=
    fun x y hxy => (huniq _ fun u => y ≫ pr u).unique hxy fun _ => rfl
  have pre : ∀ {T : Over S} (y : T ⟶ t.A) (n : Fin 8 → ℤ), y ≫ ∏ v, pr v ^ n v = ∏ v, (y ≫ pr v) ^ n v := by
    intro T y n
    let e : (t.A ⟶ c.A) →* (T ⟶ c.A) := MonoidHom.mk' (y ≫ ·) (MonObj.comp_mul y)
    exact (map_prod e _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow e _ _)
  have hact' : ∀ j u, t.act j ≫ pr u = ∏ v, pr v ^ a j u v := fun j u => by rw [hact, List.prod_ofFn]
  refine ⟨fun j j' j'' hm => ext _ _ fun u => ?_, fun j j' j'' hm => ext _ _ fun u => ?_,
    fun j hj => ext _ _ fun u => ?_, fun j i => ext _ _ fun u => ?_⟩
  · rw [hact', Category.assoc, hact', pre]
    simp only [hact', ← Finset.prod_zpow, ← zpow_mul]
    rw [hm, Finset.prod_comm]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Matrix.mul_apply, zpow_finsetSum]
    exact Finset.prod_congr rfl fun w _ => by rw [mul_comm]
  · have := hpr u
    rw [MonObj.mul_comp, hact', hact', hact', hm, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by rw [Matrix.add_apply, zpow_add]
  · rw [hact', hj, Category.id_comp, Finset.prod_eq_single u (fun v _ hv => by rw [Matrix.one_apply_ne hv.symm, zpow_zero])
      (fun hn => absurd (Finset.mem_univ u) hn), Matrix.one_apply_eq, zpow_one]
  · have := hpr u
    have hq : ∀ i v, t.pt i ≫ pr v = c.lev (bas (Pi.single i 1) v) := fun i v => Over.OverMorphism.ext (hpt i v)
    let M : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ c.A) :=
      MonoidHom.mk' (fun w => c.lev w.toAdd) fun x y => c.lev_add _ _
    have levsum : ∀ (ι' : Type) [Fintype ι'] (n : ι' → ℤ) (w : ι' → (Fin h ⊕ Fin h → ℤ)),
        c.lev (∑ x, n x • w x) = ∏ x, c.lev (w x) ^ n x := by
      intro ι' _ n w
      calc c.lev (∑ x, n x • w x) = M (Multiplicative.ofAdd (∑ x, n x • w x)) := rfl
        _ = ∏ x, c.lev (w x) ^ n x := by
          rw [ofAdd_sum, map_prod]
          exact Finset.prod_congr rfl fun x _ => by rw [ofAdd_zsmul, map_zpow]; rfl
    have key : ∀ n : Fin (2 * g) → ℤ, ∑ i', n i' • bas (Pi.single i' 1) = bas n := by
      intro n
      conv_rhs => rw [← Finset.univ_sum_single n]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← map_zsmul]
      congr 1
      ext m
      rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have kv := congrFun (key (bas.symm fun u => ∑ v, a j u v • bas (Pi.single i 1) v)) u
    rw [LinearEquiv.apply_symm_apply, Finset.sum_apply] at kv
    simp only [Pi.smul_apply] at kv
    let post : (Out.baseOver S ⟶ t.A) →* (Out.baseOver S ⟶ c.A) :=
      MonoidHom.mk' (· ≫ pr u) fun x y => MonObj.mul_comp x y (pr u)
    rw [Category.assoc, hact', pre]
    rw [show (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod ≫ pr u =
      post (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod from rfl,
      map_list_prod, List.map_ofFn, List.prod_ofFn]
    simp only [Function.comp_apply, map_zpow]
    simp only [post, MonoidHom.mk'_apply, hq]
    rw [← levsum, ← levsum, kv]
end GlobalTheory.SharpFamRel
