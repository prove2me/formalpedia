-- Prove2me | solution 1 for GlobalTheory.exists_isGen_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:52.130799+00:00
-- url     : https://prove2.me/submissions/5ffa1930-c0f3-4d49-afa6-8dd34b5ae68c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIsGenOfInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y'))
    (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, φ' k = m ≫ φ k)
    (u : LB.Gen (LB.LinComb L φ' ε)) (hu : u.IsGen)
    (hinv : ∀ i y J, Good L y J → val u (t i) y J = val u (𝟙 Y') y J) :
    ∃ v : LB.Gen (LB.LinComb L φ ε), v.IsGen := by
  obtain rfl : φ' = fun k => m ≫ φ k := funext hφ
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have le : ∀ j : K → L.ι, m ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => m ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hex : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j)ˣ, pullU m _ b = res (le j) (u.s j) := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    have hJ' : Good L y J := hJ
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ LB.wchart L φ j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    refine (gm_res (t i) y (le j) (e hy) _).trans (Eq.trans ?_ (gm_res (𝟙 Y') y (le j) hy _).symm)
    refine (gen_trans hu (t i) y (le j (e hy)) (hJ'.mem _ _)).trans
      (Eq.trans ?_ (gen_trans hu (𝟙 Y') y (le j hy) (hJ'.mem _ _)).symm)
    refine congrArg₂ (· * ·) ?_ (hinv i y J hJ')
    have e3 : ∀ k, t i ≫ m ≫ φ k = 𝟙 Y' ≫ m ≫ φ k := fun k => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X => gm ψ y (L.U (j k) ⊓ L.U (J ψ)) (L.g (j k) (J ψ)) ^ ε k) (e3 k)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j : K → L.ι, y ∈ m ⁻¹ᵁ LB.wchart L φ j →
      gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (u.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans ((congrArg _ (hb j)).trans (gm_res (𝟙 Y') y (le j) hj _))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans
    ((gen_trans hu (𝟙 Y') y (le i hy.1) (le j hy.2)).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_linComb L φ ε (𝟙 Y' ≫ m) y i j hy.1 hy.2).trans ?_) ((gm_res _ y _ hy _).trans (val j hy.2)))
  simp only [trF, Category.assoc]
end GlobalTheory
