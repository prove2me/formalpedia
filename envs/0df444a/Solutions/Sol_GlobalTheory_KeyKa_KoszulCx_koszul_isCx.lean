-- Prove2me | solution 1 for GlobalTheory.KeyKa.KoszulCx.koszul_isCx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:49.263357+00:00
-- url     : https://prove2.me/submissions/90340cf5-2935-425f-80d7-4c20cb8fd099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_isCx_kosD
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_valH_cst
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_cast_step
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_ring_eval
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_coords_mul
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_eq


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
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KoszulCx
variable {R : Type} [CommRing R]
namespace GlobalTheory.KeyKa.KoszulCx
theorem _root_.solution : ∀ (R : Type) [CommRing R] (x : KeyIn R) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → (∃ m, IsMul x l s b m) ∧ ∀ m, IsMul x l s b m → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := R) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))) := by
  intro R _ x n l d s b z ch hl hb
  refine ⟨?_, fun m hm hz hs => ?_⟩
  · have h1 : ∀ i j, ∀ k : Fin ((l - (j + 1) * n) ^ x.P.g), ∃ c : Fin ((l - j * n) ^ x.P.g) → R, j < x.P.g →
        Coords x (b j) c (fun c => (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) *
          (show Γ(x.P.A.left, x.P.L.U c) from (b (j + 1) k).f c)) := by
      intro i j k
      by_cases hj : j < x.P.g
      · obtain ⟨c, hc, -⟩ := hb j hj.le (mulSec x.P.L (cast_step hl hj) (s i) (b (j + 1) k))
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose c hc using h1
    refine ⟨fun i j j' => if h : j' = j + 1 then Matrix.of fun k' k => c i j (h ▸ k) k' else 0, fun i j hj k => ?_⟩
    simp only [dif_pos, Matrix.of_apply]
    exact hc i j k hj
  · refine isCx_kosD (N := fun j => (l - j * n) ^ x.P.g) m _ (fun i i' j hj => ?_) (fun i => ?_)
    · ext k' k
      have hj0 : j < x.P.g := by omega
      have hj1 : j + 1 < x.P.g := by omega
      have e₁ := coords_mul x (b j) (b (j + 1)) (m i j (j + 1)) _ _ _ (hm i j hj0) (hm i' (j + 1) hj1 k)
      have e₂ := coords_mul x (b j) (b (j + 1)) (m i' j (j + 1)) _ _ _ (hm i' j hj0) (hm i (j + 1) hj1 k)
      have hu := hb j hj0.le (mulSec x.P.L (cast_step hl hj0) (s i)
        (mulSec x.P.L (cast_step hl hj1) (s i') (b (j + 2) k)))
      have e₃ := hu.unique e₁ (fun c => (mul_left_comm _ _ _).trans (e₂ c))
      exact congrFun e₃ k'
    · ext a k
      exact ring_eval (cst x.P.A.hom (x.P.L.U (ch a))) (valT (T := R) (z a).left (x.P.L.U (ch a))) _
        (EtBaseChange.valT_eq (T := R) (z a).left _ (hz a)) (valH_cst x (z a) _ (hz a)) _ _ _ _ (hs a i)
        (hm i 0 i.pos k (ch a))
end GlobalTheory.KeyKa.KoszulCx
