-- Prove2me | solution 1 for GlobalTheory.charPair_of_weil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:48:59.223625+00:00
-- url     : https://prove2.me/submissions/fdc090e5-ece8-4c7b-895b-4db6b9cf2c42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Theorems.Thm_GlobalTheory_existsUnique_pairing_eq_character
import Theorems.Thm_GlobalTheory_finite_torsion_of_isFinite_mul
import Theorems.Thm_GlobalTheory_hasEnoughRootsOfUnity_globalSections

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → CharPairSt := by
  intro hW hskew hnd hM K _ _ P N hN χ hχ
  haveI : NeZero (N : K) := ⟨hN⟩
  haveI : NeZero N := .of_neZero_natCast K
  haveI := (hM _ P N (NeZero.one_le)).1
  haveI := finite_torsion_of_isFinite_mul K P N
  haveI := hasEnoughRootsOfUnity_globalSections K N hN
  obtain ⟨hex, hmul, -, -⟩ := hW _ P N (baseOver (Spec (CommRingCat.of K)))
  exact existsUnique_pairing_eq_character N (fun x y c => WeilIs P.A P.L N x y c) hex hmul
    (hskew _ P N _).2.1 (hnd K P N hN) χ hχ
end GlobalTheory
