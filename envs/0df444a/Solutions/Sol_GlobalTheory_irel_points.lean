-- Prove2me | solution 1 for GlobalTheory.irel_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:30.090937+00:00
-- url     : https://prove2.me/submissions/9dc697dd-aacf-4cdd-87b7-08fdb1b3b322

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsStruct
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
section
open scoped CategoryTheory.Obj
private theorem mul_left_fst {S' S : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {Y : Over S} {Z : Over S'}
    (e : Y.left ⟶ Z.left) (a b : Z ⟶ (Over.pullback f).obj G) (za zb : Y ⟶ G)
    (ha : e ≫ a.left ≫ pullback.fst G.hom f = za.left) (hb : e ≫ b.left ≫ pullback.fst G.hom f = zb.left) :
    e ≫ (a * b).left ≫ pullback.fst G.hom f = (za * zb).left := by
  let F := Over.pullback f
  let m : Z ⟶ F.obj (G ⊗ G) := lift a b ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom f) ≫ g.left =
      (m ≫ F.map g).left ≫ pullback.fst G.hom f := by
    intro g
    rw [Category.assoc, ← SplitTorusPoints.map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  have h1 : m ≫ F.map (fst G G) = a := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  have h2 : m ≫ F.map (snd G G) = b := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  have h3 : m ≫ F.map μ[G] = a * b := Category.assoc _ _ _
  have hq : e ≫ m.left ≫ pullback.fst (G ⊗ G).hom f = (lift za zb).left := by
    apply pullback.hom_ext
    · have := key (fst G G)
      rw [h1] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (ha.trans
        (congrArg (fun t => t.left) (lift_fst za zb)).symm))
    · have := key (snd G G)
      rw [h2] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (hb.trans
        (congrArg (fun t => t.left) (lift_snd za zb)).symm))
  have := key μ[G]
  rw [h3] at this
  rw [← this, ← Category.assoc, hq]
  rfl
end
private theorem mono_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) : Mono (Out.thick R I e) := by
  have : IsClosedImmersion (Out.thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance
private theorem exists_struct {R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (S : Type) [CommRing S] [Algebra R S]
    (h : Kills I k S) : ∃ s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))),
      s ≫ Out.thick R I k = (sp (R₀ := R) S).hom := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R S) h)), ?_⟩
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))) = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
private theorem exists_equiv {B : Scheme.{0}} (X : Type) [AddCommGroup X] (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ B) :
    ∃ e : (Over.mk s ⟶ splitTorus B X) ≃* (Multiplicative X →* Sˣ), ∀ t χ, e t = χ ↔
      ∀ x : X, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) = (χ (Multiplicative.ofAdd x) : S) := by
  let u : Γ(Spec (CommRingCat.of S), ⊤)ˣ ≃* Sˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨(splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight), fun t χ => ?_⟩
  have hv : ∀ x : X, ((((splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight)) t
      (Multiplicative.ofAdd x) : Sˣ) : S) = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) := fun x =>
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (splitTorusPointsEquiv_val B X (Over.mk s) t x)
  constructor
  · rintro rfl x
    exact (hv x).symm
  · intro h
    ext x
    exact (hv x).trans (h x)
private theorem irel_iff {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegPre R} {k : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G)
    (S : Type) [CommRing S] [Algebra R S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))))
    (hs : s ≫ Out.thick R I k = (sp (R₀ := R) S).hom) :
    ∃ e : (Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X) ≃* (Multiplicative D.X →* Sˣ),
      ∀ χ z, IRel c S χ z ↔ (e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k) = z.left := by
  obtain ⟨e, he⟩ := exists_equiv D.X S s
  refine ⟨e, fun χ z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨w, hw, hz⟩
    have := mono_thick I k
    have hws : w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).hom = s := by
      rw [← cancel_mono (Out.thick R I k), hs, ← Over.w z, ← hz, ← Over.w c.i]
      simp only [Category.assoc]
      exact congrArg (fun g => w ≫ c.i.left ≫ g) (Over.w (Out.fstG I k G)).symm
    let t : Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w hws
    have ht : e t = χ := (he t χ).2 hw
    rw [← ht, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).trans hz
  · exact ⟨(e.symm χ).left, (he _ χ).1 (e.apply_symm_apply χ), (Category.assoc _ _ _).symm.trans h⟩
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open scoped CategoryTheory.Obj
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ χ, ∃! z, IRel c S χ z) ∧ (∀ χ χ' z z', IRel c S χ z → IRel c S χ' z' → IRel c S (χ * χ') (z * z')) ∧ ∀ χ χ' z, IRel c S χ z → IRel c S χ' z → χ = χ') ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') χ z, IRel c S χ z → IRel c S' ((Units.map (φ : S →* S')).comp χ) (spMap φ ≫ z) := by
  intro R _ _ I D k G _ _ c
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_struct I k S hS
    obtain ⟨e, he⟩ := irel_iff c S s hs
    refine ⟨fun χ => ?_, fun χ χ' z z' h h' => ?_, fun χ χ' z h h' => ?_⟩
    · refine ⟨Over.homMk ((e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k)) ?_,
        (he _ _).2 rfl, fun z hz => Over.OverMorphism.ext ((he _ _).1 hz).symm⟩
      rw [← hs]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Out.thick R I k) (Over.w (e.symm χ ≫ c.i)))))
    · rw [he] at h h' ⊢
      have := c.i_hom
      rw [map_mul, MonObj.mul_comp]
      exact (Category.id_comp _).symm.trans (mul_left_fst (Out.thick R I k) G (Y := sp S) (Z := Over.mk s) (𝟙 _)
        _ _ z z' ((Category.id_comp _).trans h) ((Category.id_comp _).trans h'))
    · rw [he] at h h'
      have := mono_thick I k
      have h1 : e.symm χ ≫ c.i = e.symm χ' ≫ c.i :=
        Over.OverMorphism.ext ((cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (h.trans h'.symm))
      exact e.symm.injective (c.isKernel.hom_ext h1 (toUnit_unique _ _))
  · rintro S _ _ S' _ _ φ χ z ⟨w, hw, hz⟩
    refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ w, fun x => ?_, ?_⟩
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← RingHom.comp_apply,
        ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, RingHom.comp_apply, hw]
      rfl
    · rw [Category.assoc, hz]
      rfl
end GlobalTheory
