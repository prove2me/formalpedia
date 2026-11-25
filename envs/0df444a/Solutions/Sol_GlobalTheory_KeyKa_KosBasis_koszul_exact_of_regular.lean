-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosBasis.koszul_exact_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:50.308937+00:00
-- url     : https://prove2.me/submissions/39179b68-dfe6-493c-9595-3b4e691d4a8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfRegular
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_phi_zero
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_phi_sum
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_phi_inj
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_phi_surj
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_phi_mulVec
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_mem_iff
import Theorems.Thm_GlobalTheory_T_koszul_exact_inl_nonempty_of_graded_regular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosBasis
variable {K : Type} [CommRing K]
namespace GlobalTheory.KeyKa.KosBasis
theorem _root_.solution : ∀ (K : Type) [CommRing K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ (i : Fin x.P.g) (j : ℕ), j + 1 + i ≤ x.P.g → ∀ (y : RR x (l - (j + 1) * n)) (ta : Fin x.P.g → RR x (l - (j + 1) * n)), (∀ c, (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) * (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (ta i').f c)) → ∃ tb : Fin x.P.g → RR x (l - (j + 2) * n), ∀ c, (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (tb i').f c)) → ∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  intro K _ x n l s b m _ hb hm hreg
  refine GlobalTheory.T.koszul_exact_inl_nonempty_of_graded_regular K x.P.g (fun j => (l - j * n) ^ x.P.g) m ?_ ?_
  · intro i i' j hj
    refine Matrix.ext_of_mulVec_single fun k => ?_
    refine phi_inj x (hb j (by omega)) fun c => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, phi_mulVec x hm i (by omega),
      phi_mulVec x hm i' (by omega), phi_mulVec x hm i' (by omega), phi_mulVec x hm i (by omega)]
    ring
  · intro i j y hj hy
    have hjg : j < x.P.g := by omega
    obtain ⟨t, ht⟩ := (mem_iff i (fun i' => m i' j (j + 1)) _).1 hy
    refine (mem_iff i (fun i' => m i' (j + 1) (j + 2)) _).2 ?_
    obtain ⟨tb, htb⟩ := hreg i j hj (sec x (b (j + 1)) y) (fun i' => sec x (b (j + 1)) (t i')) (fun c => by
      change lf x (s i) c * phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * phi x (b (j + 1)) (t i') c
      rw [← phi_mulVec x hm i hjg, ht, phi_sum]
      exact Finset.sum_congr rfl fun i' _ => phi_mulVec x hm i' hjg _ _)
    have htb' : ∀ c, phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * lf x (tb i') c := htb
    by_cases h2 : j + 2 ≤ x.P.g
    · choose u hu using fun i' => phi_surj x (hb (j + 2) h2) (tb i')
      refine ⟨u, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', phi_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hu]
      exact (phi_mulVec x hm i' (j := j + 1) (by omega) _ _).symm
    · have he : Finset.univ.filter (· < i) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun i' _ h => ?_
        have : (i' : ℕ) < i := h
        omega
      refine ⟨0, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', he, Finset.sum_empty, Finset.sum_empty, phi_zero]
end GlobalTheory.KeyKa.KosBasis
