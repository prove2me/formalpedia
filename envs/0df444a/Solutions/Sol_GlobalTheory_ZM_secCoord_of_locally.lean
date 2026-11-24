-- Prove2me | solution 1 for GlobalTheory.ZM.secCoord_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:16.961635+00:00
-- url     : https://prove2.me/submissions/c1bb4f04-b227-4922-b817-3b5d50f661a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing
import Theorems.Thm_GlobalTheory_ZM_sec_eq_of_openImm
import Theorems.Thm_GlobalTheory_ZM_sec_isUnit_of_pull
import Theorems.Thm_GlobalTheory_ZM_appLE_spConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM
private theorem mem_pull_U_iff' {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j : PUnit → M.ι) (p : T) :
    p ∈ (M.pull y).U j ↔ y p ∈ M.U (j PUnit.unit) := by
  unfold LB.pull LB.LinComb LB.wchart
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
  exact ⟨fun h => h _, fun h _ => h⟩
private theorem appLE_appLE_lemma_2 {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (V' : Z.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hV' : V' ≤ f ⁻¹ᵁ V) (h3 : V' ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (f.appLE V V' hV').hom ((g.appLE U V hV).hom s) = ((f ≫ g).appLE U V' h3).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
private theorem appLE_resG_eq_resG_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V1 V2 : Y.Opens} {W1 W2 : Z.Opens}
    (hV : V1 ≤ V2) (hW : W1 ≤ W2) (h1 : W1 ≤ f ⁻¹ᵁ V1) (h2 : W2 ≤ f ⁻¹ᵁ V2) (s : Γ(Y, V2)) :
    (f.appLE V1 W1 h1).hom (resG Y hV s) = resG Z hW ((f.appLE V2 W2 h2).hom s) := by
  simp only [resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
private theorem pull_g_coe_eq_appLE_g {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull y).U j ⊓ (M.pull y).U j' ≤ y ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull y).g j j' : (Γ(T, (M.pull y).U j ⊓ (M.pull y).U j'))ˣ) : Γ(T, (M.pull y).U j ⊓ (M.pull y).U j')) =
      (y.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp [pullU, res, Scheme.Hom.appLE]
  rfl
end GlobalTheory.ZM
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R]
    (x : Sp R ⟶ X) (v : I → R) (_hM : M.IsLB) (hv : Ideal.span (Set.range v) = ⊤)
    (H : ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧
      p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) :
    SecCoord M th x v := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have W1 : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit) :=
    fun j p hp => (mem_pull_U_iff' M x j p).1 hp
  have W2 : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (j : PUnit → M.ι),
      (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun φ j z hz => (mem_pull_U_iff' M x j _).2 ((mem_pull_U_iff' M _ j z).1 hz)
  let t : ∀ j : PUnit → M.ι, Γ(Sp R, (M.pull x).U j) := fun j =>
    c.sum (fun i a => spConst R _ a * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit)))
  have pt : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (τ' : (M.pull (spMap φ ≫ x)).Gen),
      (∀ i j h, ((spMap φ ≫ x).appLE (M.U (j PUnit.unit)) ((M.pull (spMap φ ≫ x)).U j) h).hom
          ((th i).f (j PUnit.unit)) = spConst R' _ (φ (v i)) * (τ'.s j).val) →
      ∀ j, ((spMap φ).appLE _ _ (W2 φ j)).hom (t j) = (τ'.s j).val := by
    intro R' _ φ τ' hco j
    have e1 : ∀ i, ((spMap φ).appLE _ _ (W2 φ j)).hom
        (spConst R _ (c i) * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit))) =
        spConst R' _ (φ (c i) * φ (v i)) * (τ'.s j).val := by
      intro i
      rw [map_mul, appLE_spConst, appLE_appLE_lemma_2 (spMap φ) x _ _ _ (W1 j) (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp), map_mul, _root_.mul_assoc]
      exact congrArg (spConst R' _ (φ (c i)) * ·) (hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp))
    have e2 : ∑ i ∈ c.support, φ (c i) * φ (v i) = 1 := by
      have := congrArg φ hc
      rw [map_one, Finsupp.sum, map_sum] at this
      simpa [map_mul] using this
    show ((spMap φ).appLE _ _ (W2 φ j)).hom (∑ i ∈ c.support, _) = _
    rw [map_sum, Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul, ← map_sum, e2, map_one, _root_.one_mul]
  have hu : ∀ j, IsUnit (t j) := by
    intro j
    apply sec_isUnit_of_pull
    intro p hp
    obtain ⟨R', _, φ, _, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, z, (M.pull (spMap φ ≫ x)).U j, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [pt φ τ' hco j]; exact (τ'.s j).isUnit
  unfold SecCoord
  refine ⟨⟨fun j => (hu j).unit⟩, ?_, ?_⟩
  · intro i j
    apply Units.ext
    show resG _ inf_le_left (t i) = ((M.pull x).g i j).val * resG _ inf_le_right (t j)
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', hg, hco⟩ := H p
    have Wi : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
        spMap φ ⁻¹ᵁ ((M.pull x).U i ⊓ (M.pull x).U j) := fun z hz => ⟨W2 φ i hz.1, W2 φ j hz.2⟩
    refine ⟨Sp R', spMap φ, hoi, z, _, Wi, ?_, rfl, ?_⟩
    · exact ⟨(mem_pull_U_iff' M _ i z).2 ((mem_pull_U_iff' M x i _).1 hp.1),
        (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp.2)⟩
    · rw [map_mul, appLE_resG_eq_resG_appLE (spMap φ) inf_le_left inf_le_left Wi (W2 φ i),
        appLE_resG_eq_resG_appLE (spMap φ) inf_le_right inf_le_right Wi (W2 φ j), pt φ τ' hco i, pt φ τ' hco j]
      have h3 : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
          (spMap φ ≫ x) ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
        fun q hq => ⟨(mem_pull_U_iff' M _ i q).1 hq.1, (mem_pull_U_iff' M _ j q).1 hq.2⟩
      rw [pull_g_coe_eq_appLE_g M x i j (fun q hq => ⟨W1 i hq.1, W1 j hq.2⟩)]
      erw [appLE_appLE_lemma_2 (spMap φ) x _ _ _ _ Wi h3, ← pull_g_coe_eq_appLE_g M (spMap φ ≫ x) i j h3]
      exact congrArg Units.val (hg i j)
  · intro i j h
    show _ = spConst R _ (v i) * t j
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, hoi, z, _, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [map_mul, appLE_spConst, pt φ τ' hco j, appLE_appLE_lemma_2 (spMap φ) x _ _ _ h (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)]
      exact hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)
end GlobalTheory.ZM
