-- Prove2me | solution 1 for GlobalTheory.AbLaw.sections_finite_of_perf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:34.296337+00:00
-- url     : https://prove2.me/submissions/c9819ad6-8250-4217-9b55-2f143988ca01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFinite
import Theorems.Thm_GlobalTheory_AbLaw_Perf_exists_relation

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
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution
    (hperf : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M))
    (hva : ∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S)
      (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)),
      IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)),
        (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s)
    (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left)
    (hM : M.IsLB) :
    ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
      ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0 := by
  obtain ⟨N, -, m, σ, hLB, hσ⟩ := hva _ P K (𝟙 _) P.A.left (𝟙 _) P.A.hom (IsPullback.id_horiz _)
  have hsm : Smooth P.A.hom := by
    haveI := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g _
  obtain ⟨Q⟩ := hperf K P.A.left P.A.hom hsm ⟨_, hLB, m, σ, hσ⟩ M hM
  refine ⟨Q.a + 1, fun s => ?_⟩
  obtain ⟨c, hc, h⟩ := Q.exists_relation s
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c k), fun h0 => hc ?_, h⟩
  funext k
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
  exact hinj ((congrFun h0 k).trans (map_zero _).symm)
end GlobalTheory.AbLaw
