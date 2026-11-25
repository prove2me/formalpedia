-- Prove2me | solution 1 for GlobalTheory.SS.FrobLB.frob_pullPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:15.499588+00:00
-- url     : https://prove2.me/submissions/ad7ab9de-b130-4e9a-87c6-9facfc04f15e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPowOfFix
import Theorems.Thm_GlobalTheory_SS_FrobLB_Fix_pow
import Theorems.Thm_GlobalTheory_SS_FrobLB_pullPow_of_fix
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
namespace GlobalTheory.SS.FrobLB
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (F : End G) (q : ℕ), FrobG G F q → ∀ L : LB G.left, L.IsLB → ∃ m, 1 ≤ m ∧ ∀ l, PullPow (show G ⟶ G from F ^ (m * l)).left L ((q : ℤ) ^ (m * l)) := by
  intro k _ G _ hG F q hF L hL
  classical
  obtain ⟨-, -, hsep, hqc, -⟩ := hG
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hx : ∀ x : G.left, ∃ (V : G.left.Opens) (i : L.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨_, ⟨V, hV, rfl⟩, h₁, h₂⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hi (L.U i).isOpen
    exact ⟨V, i, hV, h₁, h₂⟩
  choose V c hA hxV hV using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set G.left)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  choose m hm hfix using fun p : s × s => hF.2 (V p.1 ⊓ V p.2) ((hA p.1).inf (hA p.2))
    (res (inf_le_inf (hV p.1) (hV p.2)) (L.g (c p.1) (c p.2))).val
  refine ⟨∏ p, m p, Finset.one_le_prod' fun p _ => hm p, fun l => ?_⟩
  have := pullPow_of_fix hL (show G ⟶ G from F ^ ((∏ p, m p) * l)).left (q ^ ((∏ p, m p) * l))
    (fun a : s => V a) (fun a => c a) (fun y => by
      obtain ⟨a, ha, hy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
      exact ⟨⟨a, ha⟩, hy⟩) (fun a => hV a) (fun a b => by
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (a, b))
      rw [hr, Nat.mul_assoc]
      exact Fix.pow (hfix (a, b)) _)
  exact_mod_cast this
end GlobalTheory.SS.FrobLB
