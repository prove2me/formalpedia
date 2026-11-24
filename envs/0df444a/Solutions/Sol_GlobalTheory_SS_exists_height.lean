-- Prove2me | solution 1 for GlobalTheory.SS.exists_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:17:04.750785+00:00
-- url     : https://prove2.me/submissions/7b1899f8-363f-4a84-a026-f0b8ce181226

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
import Theorems.Thm_GlobalTheory_SS_Height_isUnit_gs
import Theorems.Thm_GlobalTheory_SS_Height_integral_value
import Theorems.Thm_GlobalTheory_SS_Height_ext_unique
import Theorems.Thm_GlobalTheory_SS_Height_ext_exists
import Theorems.Thm_GlobalTheory_SS_Height_centre_finite
import Theorems.Thm_GlobalTheory_SS_Height_od_fin
import Theorems.Thm_GlobalTheory_SS_Height_od_sum
import Theorems.Thm_GlobalTheory_SS_Height_od_mul
import Theorems.Thm_GlobalTheory_SS_Height_od_zpow
import Theorems.Thm_GlobalTheory_SS_Height_od_prod
import Theorems.Thm_GlobalTheory_SS_Height_od_section
import Theorems.Thm_GlobalTheory_SS_Height_od_unit
import Theorems.Thm_GlobalTheory_SS_Height_gs_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS
open IsLocalRing Height
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (Pl : Places k K) (B : Over (Sp k)), IsProper B.hom → ∀ (L : LB B.left), L.IsLB → ∃ h : (Over.mk (spMap (algebraMap k K)) ⟶ B) → ℤ, (∀ (Z : Over (Sp k)), IsProper Z.hom → ∀ (n : ℕ) (φ : Fin n → (Z ⟶ B)) (ε : Fin n → ℤ), (∃ t : LB.Gen (LB.LinComb L (fun i => (φ i).left) ε), t.IsGen) → ∀ z : Over.mk (spMap (algebraMap k K)) ⟶ Z, ∑ i, ε i * h (z ≫ φ i) = 0) ∧ ∀ (N : ℕ) (s : LB.Sec (GlobalTheory.AbLaw.pw L N)) (x : Over.mk (spMap (algebraMap k K)) ⟶ B), 1 ≤ N → Set.range x.left ⊆ Out.nonzeroLocus s → 0 ≤ h x ∧ (h x = 0 → ∀ i, ∃ b : Sp (Pl.O i) ⟶ B.left, spMap (Pl.O i).subtype ≫ b = x.left ∧ Set.range b ⊆ Out.nonzeroLocus s) := by
  intro k K _ _ _ Pl B hB L hL
  choose b hb using fun (x : Over.mk (spMap (algebraMap k K)) ⟶ B) (i : Pl.I) =>
    ext_exists (Pl.O i) (Pl.const i) B x
  choose ch hch using exists_chart hL
  let j₀ : (Over.mk (spMap (algebraMap k K)) ⟶ B) → L.ι := fun x => ch (x.left (closedPoint K))
  let j : (Over.mk (spMap (algebraMap k K)) ⟶ B) → Pl.I → L.ι := fun x i => ch (b x i (closedPoint (Pl.O i)))
  let g : (Over.mk (spMap (algebraMap k K)) ⟶ B) → Pl.I → ℤ := fun x i =>
    od Pl i (gm (Y := Sp K) x.left (closedPoint K) (L.U (j x i) ⊓ L.U (j₀ x)) (L.g (j x i) (j₀ x)))
  have hj : ∀ x i, x.left (closedPoint K) ∈ L.U (j x i) := fun x i =>
    hb x i ▸ (integral_value _ (b x i) _ (hch _)).1
  have hg : ∀ x, (Function.support (g x)).Finite := fun x =>
    (centre_finite Pl B x (b x) (hb x) (L.U (j₀ x)) (hch _)).subset fun i hi => by
      by_contra hn
      exact hi (od_unit Pl i (b x i) x.left (hb x i) (L.U (j x i) ⊓ L.U (j₀ x)) ⟨hch _, not_not.1 hn⟩ _)
  refine ⟨fun x => ∑ᶠ i, g x i, ?_, ?_⟩
  · rintro Z hZ n φ ε ⟨t, ht⟩ z
    have m₀ : z.left (closedPoint K) ∈ LB.wchart L (fun m => (φ m).left) (fun m => j₀ (z ≫ φ m)) :=
      Set.mem_iInter.2 fun m => hch _
    have key : ∀ i, ∑ m, ε m * g (z ≫ φ m) i = -od Pl i (gm (Y := Sp K) z.left (closedPoint K)
        (LB.wchart L (fun m => (φ m).left) (fun m => j₀ (z ≫ φ m))) (t.s (fun m => j₀ (z ≫ φ m)))) := by
      intro i
      obtain ⟨c, hc⟩ := ext_exists (Pl.O i) (Pl.const i) Z z
      have e : ∀ m, b (z ≫ φ m) i = c ≫ (φ m).left := fun m =>
        ext_unique _ B (by rw [hb, ← Category.assoc, hc]; rfl)
      have m₁ : c (closedPoint (Pl.O i)) ∈ LB.wchart L (fun m => (φ m).left) (fun m => j (z ≫ φ m) i) :=
        Set.mem_iInter.2 fun m => by
          have := hch (b (z ≫ φ m) i (closedPoint (Pl.O i)))
          rw [e m] at this
          simp only [j]
          rw [e m]
          exact this
      have m₂ : z.left (closedPoint K) ∈ LB.wchart L (fun m => (φ m).left) (fun m => j (z ≫ φ m) i) :=
        Set.mem_iInter.2 fun m => hj (z ≫ φ m) i
      have h1 := ((od_unit Pl i c z.left hc _ m₁ _).symm.trans
        (congrArg (od Pl i) (gen_trans ht (Z := Sp K) z.left (closedPoint K) m₂ m₀))).trans (od_mul Pl i _ _)
      refine eq_neg_of_add_eq_zero_left (Eq.trans ?_ h1.symm)
      congr 1
      exact ((od_prod Pl i _).trans (Finset.sum_congr rfl fun m _ => od_zpow Pl i _ _)).symm
    simp only [mul_finsum]
    rw [← finsum_sum_comm _ (fun i m => ε m * g (z ≫ φ m) i)
      (fun m _ => (hg _).subset (Function.support_mul_subset_right _ _))]
    simp only [key]
    rw [finsum_neg_distrib, od_sum, neg_zero]
  · intro N s x hN hx
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hx ⟨closedPoint K, rfl⟩)
    have ha' : x.left (closedPoint K) ∈ L.U a := B.left.basicOpen_le _ ha
    obtain ⟨u, hu⟩ := (isUnit_gs (Y := Sp K) x.left _ _ ha' _).2 ha
    have h₀ := gs_pw s (Y := Sp K) x.left (closedPoint K) (hch _) ha'
    rw [← hu, ← Units.val_mul] at h₀
    generalize _ * u = u₀ at h₀
    have key : ∀ i, 0 ≤ (N : ℤ) * g x i + od Pl i u₀ ∧ ((N : ℤ) * g x i + od Pl i u₀ = 0 ↔
        b x i (closedPoint (Pl.O i)) ∈ B.left.basicOpen (s.f (j x i))) := fun i => by
      have h₁ := gs_pw s (Y := Sp K) x.left (closedPoint K) (hj x i) (hch _)
      rw [h₀, ← Units.val_mul] at h₁
      have := od_section Pl i (b x i) x.left (hb x i) _ (hch _) _ _ h₁
      rwa [od_mul, od_zpow] at this
    have f₁ : (Function.support fun i => (N : ℤ) * g x i).Finite :=
      (hg _).subset (Function.support_mul_subset_right _ _)
    have hs : ∑ᶠ i, ((N : ℤ) * g x i + od Pl i u₀) = N * ∑ᶠ i, g x i := by
      rw [finsum_add_distrib f₁ (od_fin Pl u₀), od_sum, add_zero, mul_finsum]
    have hp : 0 ≤ (N : ℤ) * ∑ᶠ i, g x i := hs ▸ finsum_nonneg fun i => (key i).1
    refine ⟨(mul_nonneg_iff_of_pos_left (by exact_mod_cast hN)).1 hp, fun h0 i => ⟨b x i, hb x i, ?_⟩⟩
    have h0' : ∑ᶠ i, g x i = 0 := h0
    rw [h0', mul_zero] at hs
    have hi : (N : ℤ) * g x i + od Pl i u₀ = 0 := by
      by_contra hne
      exact (finsum_pos (fun i => (key i).1) ⟨i, lt_of_le_of_ne (key i).1 (Ne.symm hne)⟩
        ((f₁.union (od_fin Pl u₀)).subset (Function.support_add _ _))).ne' hs
    have hm : b x i (closedPoint (Pl.O i)) ∈ Out.nonzeroLocus s :=
      TopologicalSpace.Opens.mem_iSup.2 ⟨_, (key i).2.1 hi⟩
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (Pl.O i)) (b x i) hm).ge (x := y) trivial
end GlobalTheory.SS
