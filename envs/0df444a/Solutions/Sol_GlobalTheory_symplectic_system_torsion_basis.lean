-- Prove2me | solution 1 for GlobalTheory.symplectic_system_torsion_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:56.211079+00:00
-- url     : https://prove2.me/submissions/9e793557-d250-47e9-8265-d3eaa867d0a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
import Theorems.Thm_GlobalTheory_SympBasis_injective_of_pairing
import Theorems.Thm_GlobalTheory_SympBasis_comp_linComb

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
open SympBasis
namespace GlobalTheory
theorem _root_.solution :
    Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  intro hL K₀ _ P k ze pt hk hze hpt hw K _ _ x y hy
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (by simp)
  have : NeZero k := ⟨hk0⟩
  have hsep : IsSeparated P.A.hom := by
    obtain ⟨_, _, _, _⟩ := P.isAb
    infer_instance

  let h : Over.mk x ⟶ Out.baseOver (Sp K₀) := Over.homMk x (by simp)

  have hpre : ∀ s s' : Out.baseOver (Sp K₀) ⟶ P.A, h ≫ s = h ≫ s' → s = s' := by
    intro s s' hss
    have : IsReduced (Out.baseOver (Sp K₀)).left := inferInstanceAs (IsReduced (Sp K₀))
    have : IsDominant (X := Sp K) (Y := (Out.baseOver (Sp K₀)).left) x :=
      inferInstanceAs (IsDominant (X := Sp K) (Y := Sp K₀) x)
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated P.A.hom ?_ x ?_
    · rw [Over.w s, Over.w s']
    · simpa [h] using congrArg CommaMorphism.left hss

  have hzu : IsPrimitiveRoot (unitOn ze) k := by
    unfold unitOn
    refine hze.map_of_injective (Units.map_injective ?_)
    exact Function.LeftInverse.injective
      (g := (Scheme.ΓSpecIso (CommRingCat.of K₀)).hom.hom) fun a => by simp

  obtain ⟨hu, hm, -, -⟩ := hL.weil (Sp K₀) P k (Out.baseOver (Sp K₀))
  have hinj0 := SympBasis.injective_of_pairing (fun a b c => Out.WeilIs P.A P.L (k : ℤ) a b c) k hu
    (fun a a' b c c' => hm a a' b c c') pt hpt (unitOn ze) hzu hw

  have hlin : ∀ c : Fin (2 * P.g) → ZMod k,
      Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) = h ≫ ∏ i, pt i ^ (c i).val := by
    intro c
    rw [← SympBasis.comp_linComb]
    unfold Out.linComb
    rw [List.prod_ofFn]
  have htors : ∀ c : Fin (2 * P.g) → ZMod k,
      (Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val)) ^ k = 1 := by
    intro c
    rw [hlin, ← MonObj.comp_pow, ← Finset.prod_pow,
      Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hpt i, one_pow]]
    exact MonObj.comp_one _
  let Φ : (Fin (2 * P.g) → ZMod k) → {y : Over.mk x ⟶ P.A // y ^ k = 1} := fun c => ⟨_, htors c⟩
  have hΦ : Function.Injective Φ := by
    intro c c' hcc
    have h1 : Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) =
        Out.linComb (fun i => h ≫ pt i) (fun i => (c' i).val) := congrArg Subtype.val hcc
    rw [hlin, hlin] at h1
    exact hinj0 (hpre _ _ h1)

  have hkK : ((k : ℕ) : K) ≠ 0 := by
    have hc : ((k : ℕ) : K) = (Spec.preimage x).hom (k : K₀) := by simp
    rw [hc]
    exact (map_ne_zero_iff _ (Spec.preimage x).hom.injective).2 hk
  have hcard := (hL.mulN (Sp K₀) P k (Nat.one_le_iff_ne_zero.2 hk0)).2.2.2.2 K x hkK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective Φ := hΦ.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin])
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc,
    fun c' hc' => hbij.1 (Subtype.ext (hc'.trans (congrArg Subtype.val hc).symm))⟩
end GlobalTheory
