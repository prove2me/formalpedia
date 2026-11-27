-- Prove2me | solution 1 for GlobalTheory.ChF.nilChart_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:57.689173+00:00
-- url     : https://prove2.me/submissions/c9faa924-6937-456b-91ec-fa913ed6b9e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentChartBaseChangeFormalGroup
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem exists_mulEquiv {B B' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G']
    {f : B' ⟶ B} {π : G'.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G' G f π) {Y : Scheme.{0}}
    (t' : Y ⟶ B') (t : Y ⟶ B) (ht : t = t' ≫ f) :
    ∃ e : (Over.mk t' ⟶ G') ≃* (Over.mk t ⟶ G), ∀ z, (e z).left = z.left ≫ π := by
  subst ht
  let m : (Over.mk t' ⟶ G') → (Over.mk (t' ≫ f) ⟶ G) := fun z =>
    Over.homMk (z.left ≫ π) (by
      have := Over.w z
      simp only [Over.mk_hom] at this
      simp only [Over.mk_hom, Category.assoc, h.1.w]
      rw [← Category.assoc, this])
  have hm : ∀ z, (m z).left = z.left ≫ π := fun _ => rfl
  have hb : Function.Bijective m := by
    refine ⟨fun z w hzw => ?_, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      refine h.1.hom_ext ?_ ?_
      · rw [← hm, ← hm, hzw]
      · rw [Over.w z, Over.w w]
    · refine ⟨Over.homMk (h.1.lift y.left t' (Over.w y)) (h.1.lift_snd _ _ _), ?_⟩
      apply Over.OverMorphism.ext
      exact h.1.lift_fst _ _ _
  refine ⟨MulEquiv.mk (Equiv.ofBijective m hb) (fun z w => ?_), hm⟩
  apply Over.OverMorphism.ext
  exact (h.2 (Over.mk t') z w (m z) (m w) rfl rfl).symm
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (β : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom β)) π → ∀ (d : ℕ) (F : Fin d → PS R 2 d) (X : Fam G d), NilChart G F X → ∃ X' : Fam G' d, NilChart G' (fun i => MvPowerSeries.map β (F i)) X' ∧ ∀ (f : G ⟶ G) (f' : G' ⟶ G') (α : Fin d → PS R 1 d), f'.left ≫ π = π ≫ f.left → Reads X X f α → Reads X' X' f' (fun i => MvPowerSeries.map β (α i)) := by
  intro R R' _ _ β G _ _ G' _ _ π h d F X hX
  have key : ∀ (S : Type) [CommRing S] [Algebra R' S],
      ∃ e : (sp (R₀ := R') S ⟶ G') ≃* (@sp R _ S _ (resAlg β S) ⟶ G), ∀ z, (e z).left = z.left ≫ π :=
    fun S _ _ => exists_mulEquiv h _ _ (by rw [← Spec.map_comp]; rfl)
  choose e he using key
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R' S] (S' : Type) [CommRing S'] [Algebra R' S']
      (φ : S →ₐ[R'] S') (z : sp (R₀ := R') S ⟶ G'), e S' (spMap φ ≫ z) =
        @spMap R _ S S' _ (resAlg β S) _ (resAlg β S') (resHom β φ) ≫ e S z := by
    intro S _ _ S' _ _ φ z
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc]
    rfl
  have hnv : ∀ (S : Type) [CommRing S] [Algebra R' S] (n : ℕ) (a : Fin n → Fin d → S),
      (∀ i j, IsNilpotent (a i j)) → ∀ f : PS R n d,
      nv (@algebraMap R S _ _ (resAlg β S)) f a = nv (algebraMap R' S) (MvPowerSeries.map β f) a :=
    fun S _ _ n a ha f => (nv_calculus R' S (algebraMap R' S) n d a ha).2.2.2.1 R β f
  refine ⟨fun S _ _ a => (e S).symm (@X S _ (resAlg β S) a), ⟨fun S _ _ => ?_, fun S _ _ S' _ _ φ a ha => ?_,
    fun S _ _ a b ha hb hab => ?_, fun S _ _ S' _ _ ρ σ hρ hn z hz => ?_, fun S _ _ a b ha hb => ?_⟩,
    fun f f' α hf hα => ⟨fun j => ?_, fun S _ _ a ha => ?_⟩⟩
  · rw [@hX.zero S _ (resAlg β S), map_one]
  · apply (e S').injective
    rw [hnat, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact @hX.nat S _ (resAlg β S) S' _ (resAlg β S') (resHom β φ) a ha
  · exact @hX.inj S _ (resAlg β S) a b ha hb ((e S).symm.injective hab)
  · obtain ⟨a, ha, hz'⟩ := @hX.surj S _ (resAlg β S) S' _ (resAlg β S') (resHom β ρ) (resHom β σ)
      (by
        letI := resAlg β S
        letI := resAlg β S'
        exact AlgHom.ext fun x => DFunLike.congr_fun hρ x) hn (e S z)
      (by rw [← hnat, hz, map_one])
    exact ⟨a, ha, by rw [← hz', MulEquiv.symm_apply_apply]⟩
  · rw [← map_mul, @hX.law S _ (resAlg β S) a b ha hb]
    refine congrArg (fun c => (e S).symm (@X S _ (resAlg β S) c)) (funext fun k => hnv S 2 _ (fun i j => ?_) _)
    fin_cases i
    · exact ha j
    · exact hb j
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hα.1 j, map_zero]
  · apply (e S).injective
    have h1 : ∀ z : sp (R₀ := R') S ⟶ G', e S (z ≫ f') = e S z ≫ f := fun z => by
      apply Over.OverMorphism.ext
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hf]
    rw [h1, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, @hα.2 S _ (resAlg β S) a ha]
    refine congrArg (@X S _ (resAlg β S)) (funext fun k => hnv S 1 _ (fun i j => ?_) _)
    fin_cases i
    exact ha j
end GlobalTheory.ChF
