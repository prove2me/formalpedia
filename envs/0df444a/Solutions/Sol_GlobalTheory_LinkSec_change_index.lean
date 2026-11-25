-- Prove2me | solution 1 for GlobalTheory.LinkSec.change_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:27.594061+00:00
-- url     : https://prove2.me/submissions/a86fa676-fb34-4a20-877c-d142ca2c56d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GsSpMapGermAt
import Theorems.Thm_GlobalTheory_LinkSec_comp_psum_two
import Theorems.Thm_GlobalTheory_LinkSec_psum_mem
import Theorems.Thm_GlobalTheory_JetSer_prod_lam
import Theorems.Thm_GlobalTheory_JetSer_prod_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkSec
namespace GlobalTheory.LinkSec
theorem _root_.solution {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (w : G ⟶ G)
    (x : T ⟶ G) (s : T ⟶ T') (x₀ x₁ : T' ⟶ G) (h₀ : s ≫ x₀ = x) (h₁ : s ≫ x₁ = x ≫ w)
    (e : LB.Gen (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (cε 2)))
    (he : e.IsGen) (ρ : LB.Gen (LB.LinComb L (JetSer.primφ w) JetSer.primε)) (hρ : ρ.IsGen) (q : ℕ) (σ : H0 L q)
    (j : L.ι) (y : T.left) (hj : x.left y ∈ LB.wchart L (JetSer.primφ w) (fun _ => j)) (J) (hJ : Good L y J) :
    s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (fun _ => j) ∧
    ∃ c : (T.left.presheaf.stalk y)ˣ,
      sval σ x.left y J = (c ^ q).val * gs x.left y _ (σ.f fun _ => j) ∧
      val ρ x.left y J * val e s.left y J =
        c * (gm x.left y _ (ρ.s fun _ => j) * gm s.left y _ (e.s fun _ => j)) := by
  have E : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![x, x ≫ w] I).left := fun I => by
    rw [comp_psum_two, h₀, h₁]
  have hs : s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left)
      (fun _ => j) := Set.mem_iInter.2 fun I => by
    obtain ⟨k, hk⟩ := psum_mem w x I.down
    have a : (x.left ≫ JetSer.primφ w k) y ∈ L.U j := Set.mem_iInter.1 hj k
    rw [← hk, ← E] at a
    exact a
  have hx : x.left y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  let h : (T.left ⟶ G.left) → (T.left.presheaf.stalk y)ˣ := fun ψ => gm ψ y (L.U (J ψ) ⊓ L.U j) (L.g (J ψ) j)
  refine ⟨hs, h x.left, ?_, ?_⟩
  · refine (sec_trans σ x.left y (hJ.mem _ _) hx).trans (congrArg (· * _) (congrArg Units.val ?_))
    show ∏ _k : Fin 1, h (x.left ≫ 𝟙 _) ^ (q : ℤ) = _
    rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]
  · have a : val ρ x.left y J = (∏ k, h (x.left ≫ JetSer.primφ w k) ^ JetSer.primε k) *
        gm x.left y _ (ρ.s fun _ => j) := gen_trans hρ x.left y (hJ.mem _ _) hj
    have b : val e s.left y J = (∏ I : ULift.{0} (Finset (Fin 2)),
        h (s.left ≫ (psum G ![x₀, x₁] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))) *
        gm s.left y _ (e.s fun _ => j) := gen_trans he s.left y (hJ.mem _ _) hs
    simp only [E] at b
    rw [a, b, JetSer.prod_prim, JetSer.prod_lam, _root_.mul_mul_mul_comm]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end GlobalTheory.LinkSec
