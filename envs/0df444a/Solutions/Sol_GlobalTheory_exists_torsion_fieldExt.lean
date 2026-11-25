-- Prove2me | solution 1 for GlobalTheory.exists_torsion_fieldExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:43.254325+00:00
-- url     : https://prove2.me/submissions/25ccfb78-b760-4ff0-bf5d-bb2cfca02998

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsTorsionFieldExt
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  intro hL S _ P k k' _ _ _ _ _ j t
  let h : Over.mk (spMap j ≫ t) ⟶ Over.mk t := Over.homMk (spMap j) rfl
  let r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A) :=
    { toFun := fun x => h ≫ x, map_one' := comp_one _, map_mul' := fun x y => comp_mul _ _ _ }
  have hr : Function.Injective r := by
    letI := j.toAlgebra
    haveI : Flat (spMap j) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat k k')
    haveI : Surjective (spMap j) := ⟨fun p => ⟨(⊥ : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    haveI : Epi h.left := Flat.epi_of_flat_of_surjective (spMap j)
    haveI : Epi h := Over.epi_of_epi_left _
    exact fun x y e => (cancel_epi h).1 e
  have hu : ∀ c : kˣ, Units.map h.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
    fun c => Units.ext (congrArg (fun q => q.hom (c : k))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  have up : ∀ (n : ℕ) x y (c : kˣ), Out.WeilIs P.A P.L n x y (unitOn c) →
      Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c)) := fun n x y c H =>
    hu c ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h H
  refine ⟨r, fun _ => rfl, hr, fun n y hn hy => ?_, fun n x y c _ hx hy => ⟨up n x y c, fun H => ?_⟩⟩
  · have hk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : k') ≠ 0 := by rw [← map_natCast j]; exact (map_ne_zero j).2 hk
    have c₁ := (hL.mulN S P n hn).2.2.2.2 k t hk
    have c₂ := (hL.mulN S P n hn).2.2.2.2 k' (spMap j ≫ t) hk'
    let f : {x : Over.mk t ⟶ P.A // x ^ n = 1} → {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (hr (congrArg Subtype.val e))
    haveI : Finite {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
    obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le (by rw [c₁, c₂])).2 ⟨y, hy⟩
    exact ⟨x.1, congrArg Subtype.val hx⟩
  · obtain ⟨d, hd, -⟩ := (hL.weil S P n (Over.mk t)).1 x y hx hy
    let u : kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom d
    have e : unitOn u = d := Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) d.val)
    rw [← e] at hd
    have e₁ := ((hL.weil S P n (Over.mk (spMap j ≫ t))).1 (r x) (r y) (by rw [← map_pow, hx, map_one])
      (by rw [← map_pow, hy, map_one])).unique (up n x y u hd) H
    have e₂ : u = c := Units.ext (j.injective
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k')).inv).1 (congrArg Units.val e₁)))
    exact e₂ ▸ hd
end GlobalTheory
