-- Prove2me | solution 1 for GlobalTheory.NoBasePoint.exists_sec_value_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:04:39.043424+00:00
-- url     : https://prove2.me/submissions/ceed6248-ad9b-4c01-8436-6310bf9227b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSecValueIsUnit
import Theorems.Thm_GlobalTheory_NoBasePoint_translPt_eq
import Theorems.Thm_GlobalTheory_NoBasePoint_ptSecT_translT
import Theorems.Thm_GlobalTheory_NoBasePoint_exists_two_points
import Theorems.Thm_GlobalTheory_NoBasePoint_unitAt_of_local
import Theorems.Thm_GlobalTheory_NoBasePoint_unitAt_transl
import Theorems.Thm_GlobalTheory_NoBasePoint_exists_value_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_spec_pt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.NoBasePoint
namespace GlobalTheory.NoBasePoint
theorem _root_.solution :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v := by
  intro hGI hsq hH0 _ S _ P K _ _ t n hn x
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ inferInstance inferInstance
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := hH0 S P K t 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hsq S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e1 : translPt P.A (1 : Over.mk t ⟶ P.A) = snd _ _ := by
    rw [translPt_eq, MonObj.comp_one, _root_.one_mul]
  obtain ⟨s, τ, hτ, hv⟩ := exists_value_one P.isLB ((m + 2 : ℕ) : ℤ) x p
    (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by
      simp [Fin.sum_univ_succ, e1]
      module) (main m 1))
  exact ⟨s, τ, 1, hτ, hv, isUnit_one⟩
end GlobalTheory.NoBasePoint
