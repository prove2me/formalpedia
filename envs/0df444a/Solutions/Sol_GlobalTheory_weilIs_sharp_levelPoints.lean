-- Prove2me | solution 1 for GlobalTheory.weilIs_sharp_levelPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:14.525265+00:00
-- url     : https://prove2.me/submissions/89df2b46-7f2d-4d68-8463-bee87b918f68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CommutatorPairingE8SharpLevelPoints
import Theorems.Thm_GlobalTheory_SharpWeil_rel_biprod
import Theorems.Thm_GlobalTheory_SharpWeil_eq_sum_basis
import Theorems.Thm_GlobalTheory_SharpWeil_form_eq
import Theorems.Thm_GlobalTheory_SharpWeil_pull_unitS
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_pull
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory
open SharpWeil
namespace GlobalTheory
theorem _root_.solution : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  intro hL h g W J bas k o _ b S _ s t A _ _ pr lev hb hpr huniv hlev hpt K _ p β z hps hz X Y y y' hy hy'
  have := t.ab.comm
  let e : Over.mk p ⟶ Out.baseOver S := Over.homMk p (by simp)
  let q : Fin (2 * g) → (Over.mk p ⟶ t.A) := fun i => e ≫ t.pt i
  obtain ⟨hex, hmul, -, -⟩ := hL.weil S t.pol k (Over.mk p)
  have hq : ∀ i, q i ^ k = 1 := fun i => by
    simp only [q]
    rw [← MonObj.comp_pow, t.torsion i, MonObj.comp_one]
  have hpair : ∀ i j, Out.WeilIs t.A t.L k (q i) (q j) (unitOn z ^ Out.stdSymp g i j) := fun i j => by
    have H := CommPairing.weilIs_pull hL.globalFns t.ab t.isLB e (t.pairing i j)
    have e1 : Units.map e.left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitOn z := pull_unitS s p β b.ζ z hps hz
    rwa [map_zpow, e1] at H
  have htu : (toUnit (Over.mk p)).left = e.left :=
    congrArg Over.Hom.left (toUnit_unique (toUnit (Over.mk p)) (Over.homMk p (by simp) : Over.mk p ⟶ 𝟙_ (Over S)))
  have hqlev : ∀ i u, q i ≫ pr u = toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u) := fun i u => by
    apply Over.OverMorphism.ext
    simp only [q]
    rw [Category.assoc, Over.comp_left, hpt i u, Over.comp_left, htu]
  let levHom : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ A) :=
    MonoidHom.mk' (fun a => lev a.toAdd) (fun a c => hlev _ _)
  let ψ : (𝟙_ (Over S) ⟶ A) →* (Over.mk p ⟶ A) :=
    MonoidHom.mk' (fun f => toUnit (Over.mk p) ≫ f) (fun f f' => MonObj.comp_mul _ f f')
  have hprod : ∀ (V : Fin 8 → Fin h ⊕ Fin h → ℤ) (w : Over.mk p ⟶ t.A),
      (∀ u, w ≫ pr u = toUnit (Over.mk p) ≫ lev (V u)) → w = ∏ i, q i ^ bas.symm V i := by
    intro V w hw
    obtain ⟨x0, -, hu⟩ := huniv (Over.mk p) (fun u => w ≫ pr u)
    refine (hu w fun u => rfl).trans (hu _ fun u => ?_).symm
    have := hpr u
    let φ : (Over.mk p ⟶ t.A) →* (Over.mk p ⟶ A) :=
      MonoidHom.mk' (fun x => x ≫ pr u) (fun a c => MonObj.mul_comp a c (pr u))
    have hV : V u = ∑ i, bas.symm V i • bas (Pi.single i 1) u := by
      conv_lhs => rw [eq_sum_basis bas V]
      simp [Finset.sum_apply]
    have h1 : (∏ i, q i ^ bas.symm V i) ≫ pr u = ∏ i, (q i ≫ pr u) ^ bas.symm V i := by
      change φ (∏ i, q i ^ bas.symm V i) = ∏ i, (φ (q i)) ^ bas.symm V i
      simp only [map_prod, map_zpow]
    have h2 : toUnit (Over.mk p) ≫ lev (V u) =
        ∏ i, (toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u)) ^ bas.symm V i := by
      change ψ (levHom (Multiplicative.ofAdd (V u))) =
        ∏ i, (ψ (levHom (Multiplicative.ofAdd (bas (Pi.single i 1) u)))) ^ bas.symm V i
      rw [hV, ofAdd_sum]
      simp only [ofAdd_zsmul, map_prod, map_zpow]
    rw [h1, hw u, h2]
    exact Finset.prod_congr rfl fun i _ => by rw [hqlev i u]
  rw [form_eq hb X Y, hprod X y hy, hprod Y y' hy']
  exact rel_biprod (R := fun a c d => Out.WeilIs t.A t.L k a c d) (fun a c ha hc => hex a c ha hc)
    (fun a a' c d d' h1 h2 => hmul a a' c d d' h1 h2) (fun a c d H => CommPairing.weilIs_symm t.isLB H)
    q (unitOn z) (Out.stdSymp g) hq hpair (bas.symm X) (bas.symm Y)
end GlobalTheory
