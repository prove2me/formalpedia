-- Prove2me | solution 1 for GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:25.523434+00:00
-- url     : https://prove2.me/submissions/e5be0a71-0db6-42ba-9d8a-fe046598dc70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_first_cohomology_vanishes_descent
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_exists_iso_tw
import Theorems.Thm_GlobalTheory_AbLaw_isLB_pw
import Theorems.Thm_GlobalTheory_AbLaw_isLB_tw
import Theorems.Thm_GlobalTheory_finite_torsion_of_isFinite_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish
namespace GlobalTheory.AbLaw.PowVanish
theorem _root_.solution : (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ M : LB X, M.IsLB → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → FirstCohomologyVanishes (tw M H t)) → (∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e → M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M') → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 1 ≤ n → FirstCohomologyVanishes (pw P.L n) := by
  intro hproj hsv hiso hmulp hfin hgal K _ _ P n hn
  classical
  haveI := P.isAb.comm
  obtain ⟨N, hN, m, s, hH, hva⟩ := hproj _ P K (𝟙 _) P.A.left (𝟙 _) P.A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
  choose t₀ ht₀ using fun r : ℕ => hsv K P.A.left P.A.hom _ m s hH hva (pw P.L r) (isLB_pw P.isLB r)
  let T : ℕ := (Finset.range N).sup fun r => (t₀ r).toNat
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (N * T + ringChar K + 1)
  haveI : Fact q.Prime := ⟨hqp⟩
  have hqK : (q : K) ≠ 0 := fun h0 => by
    rcases (Nat.dvd_prime hqp).1 ((ringChar.spec K q).1 h0) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  obtain ⟨α, hα⟩ := hmulp _ P q
  haveI := (hfin _ P q hqp.one_lt.le).1
  have hdiv : q ^ 2 * n = q ^ 2 * n % N + N * (q ^ 2 * n / N) := (Nat.mod_add_div _ _).symm
  have hT : T ≤ q ^ 2 * n / N := by
    rw [Nat.le_div_iff_mul_le hN]
    nlinarith [hqp.one_lt, Nat.mul_le_mul_left (q ^ 2) hn]
  have ht : t₀ (q ^ 2 * n % N) ≤ ((q ^ 2 * n / N : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2 (le_trans (Finset.le_sup (f := fun r => (t₀ r).toNat)
      (Finset.mem_range.2 (Nat.mod_lt _ hN))) hT))
  have H : FirstCohomologyVanishes ((pw P.L n).pull (mulA P.A q).left) :=
    hiso _ _ (𝟙 _) _ _ inferInstance (isLB_tw (isLB_pw P.isLB _) hH _)
      (DVR.linComb_isLB _ (isLB_pw P.isLB n) _ _)
      (exists_iso_tw P.L P.isLB _ _ n _ N _ α hα (by exact_mod_cast hdiv)) (ht₀ _ _ ht)
  let G : Subgroup (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A) := (powMonoidHom q).ker
  haveI : Finite G := finite_torsion_of_isFinite_mul K P q
  haveI : Fintype G := Fintype.ofFinite G
  have hG : IsPGroup q G := fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact g.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hG
  refine first_cohomology_vanishes_descent (mulA P.A q).left _ G (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => ?_) (fun y z => ?_) ?_ (fun U f hf => hgal K P q hqK U f fun y hy e => hf ⟨y, hy⟩ e) H
  · have hy : y.1 ^ q = 1 := y.2
    rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
      MonObj.comp_one, _root_.one_mul]
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
      Subgroup.coe_mul, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit P.A ≫ z.1)]
  · rw [← Nat.card_eq_fintype_card, hj, Nat.cast_pow]
    refine IsUnit.pow _ ?_
    have := (IsUnit.mk0 _ hqK).map (cst P.A.hom ⊤)
    rwa [map_natCast] at this
end GlobalTheory.AbLaw.PowVanish
