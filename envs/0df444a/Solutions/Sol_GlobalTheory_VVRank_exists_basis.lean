-- Prove2me | solution 1 for GlobalTheory.VVRank.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:59:34.378966+00:00
-- url     : https://prove2.me/submissions/d80d63c8-2054-4718-8096-c0d39996c504

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_GlobalTheory_VVRank_isPullSec_pullS
import Theorems.Thm_GlobalTheory_VVRank_pullM_ofSec
import Theorems.Thm_GlobalTheory_VVRank_pullM_comp
import Theorems.Thm_GlobalTheory_VVRank_pullM_id

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
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution (P : PolAV S) (n : ℕ) {V : S.Opens} {κ : Type} [Fintype κ]
    (b : κ → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
        (b' : κ → LB.Sec (LPow P.A P.L n (baseAt t))),
        (∀ i, IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) (b' i)) →
        LinearIndependent Γ((baseAt t).left, ⊤)
            (fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) ∧
          Submodule.span Γ((baseAt t).left, ⊤)
            (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) = ⊤)
    (T : Over S) [IsAffine T.left] (h : T ⟶ overRes (T := baseOver S) V) :
    ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T),
      ∀ i, c i = pullM P.A P.L n h (SecM.ofSec P.A (b i)) := by
  let t : Spec (CommRingCat.of Γ(T.left, ⊤)) ⟶ (overRes (T := baseOver S) V).left :=
    T.left.isoSpec.inv ≫ h.left
  let u : baseAt t ⟶ T := Over.homMk T.left.isoSpec.inv (by
    change T.left.isoSpec.inv ≫ T.hom = (T.left.isoSpec.inv ≫ h.left) ≫ _
    rw [Category.assoc, Over.w h])
  have hu : u ≫ h = homAt t := Over.OverMorphism.ext rfl
  have : IsIso u.left := inferInstanceAs (IsIso T.left.isoSpec.inv)
  have : IsIso ((Over.forget S).map u) := this
  have : IsIso u := isIso_of_reflects_iso u (Over.forget S)
  have hσ : Function.Bijective u.left.appTop.hom :=
    ConcreteCategory.bijective_of_isIso (u.left.app ⊤)
  have hφ : Function.Injective (pullM P.A P.L n u) := Function.LeftInverse.injective
    (g := pullM P.A P.L n (inv u)) fun f => by
      rw [pullM_comp P.A P.isLB, IsIso.inv_hom_id, pullM_id P.A P.isLB]
  obtain ⟨h₁, h₂⟩ := hb _ t (fun i => pullS P.A n (homAt t) (b i))
    (fun i => isPullSec_pullS P.A n (homAt t) (b i))
  have e : ∀ i, pullM P.A P.L n u (pullM P.A P.L n h (SecM.ofSec P.A (b i))) =
      SecM.ofSec P.A (pullS P.A n (homAt t) (b i)) := fun i => by
    rw [pullM_comp P.A P.isLB, hu, pullM_ofSec]
  refine ⟨Module.Basis.mk (v := fun i => pullM P.A P.L n h (SecM.ofSec P.A (b i))) ?_ ?_,
    fun i => Module.Basis.mk_apply _ _ _⟩
  · rw [Fintype.linearIndependent_iff] at h₁ ⊢
    intro g hg i
    have := congrArg (pullM P.A P.L n u) hg
    simp only [map_sum, LinearMap.map_smulₛₗ, map_zero, e] at this
    exact hσ.1 ((h₁ _ this i).trans (map_zero _).symm)
  · intro x _
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (h₂.ge (Submodule.mem_top (x := pullM P.A P.L n u x)))
    choose g' hg' using fun i => hσ.2 (g i)
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨g', hφ ?_⟩
    simp only [map_sum, LinearMap.map_smulₛₗ, e, hg', hg]
end GlobalTheory.VVRank
