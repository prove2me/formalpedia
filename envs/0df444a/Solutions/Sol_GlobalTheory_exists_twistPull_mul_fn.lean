-- Prove2me | solution 1 for GlobalTheory.exists_twistPull_mul_fn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:13.652982+00:00
-- url     : https://prove2.me/submissions/93a3e0d3-6620-4e1c-b59b-2c6eec6c37d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTwistPullMulFn
import Theorems.Thm_GlobalTheory_exists_mulPull_gen_over
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mulT
import Theorems.Thm_GlobalTheory_ThetaFn_pull_analytic_at
import Theorems.Thm_GlobalTheory_ThetaPtExist_exists_isTwistPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (th : LB.Sec (Out.LPow P.A P.L 1 T)), u.IsAH Hm χ → Odd N → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) → ∃ (s1 : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)) (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ N).left] ![(N : ℤ) ^ 2, -1])) (c : ℂ), c ≠ 0 ∧ α.IsGen ∧ Out.IsTwistPull P.A P.L (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α th s1 ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s1.f j) = c * θ ((N : ℂ) • z) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  intro hLaw _ _ _ P u Hm χ N θ T _ p th hAH _ hth
  have hL := P.isLB
  obtain ⟨α, hα⟩ := exists_mulPull_gen_over hLaw.mulPull P T N
  obtain ⟨s1, hs1⟩ := ThetaPtExist.exists_isTwistPull hL (Out.mulT P.A T N) (snd T P.A ^ N) (lift_snd _ _)
    ((N : ℤ) ^ 2) 1 α hα th
  obtain ⟨c, hc0, -, hc, -⟩ := (ThetaFn.pull_analytic_at hL hAH (ψ := Out.mulT P.A T N) (p := p)
    (m := snd T P.A ^ N) (lift_snd _ _) (Φ := (N : ℂ) • LinearMap.id) (fun z => by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ThetaFn.exAt_mulT]) (a := (N : ℤ) ^ 2) (b := 1) hα).2
  have h1 : ThetaFn.IsFnAt u p 1 th θ := fun j z hj =>
    hth j z ((ThetaFn.exAt_mem_chart_iff u p 1 j z).1 hj)
  have h2 := ThetaFn.isFnAt_fnAt u p hL ((N : ℤ) ^ 2) s1
  refine ⟨s1, α, c, hc0, hα, hs1, fun j z hj => ?_⟩
  refine (h2 j z ((ThetaFn.exAt_mem_chart_iff u p _ j z).2 hj)).trans ?_
  rw [hc th s1 θ _ hs1 h1 h2 z]
  rfl
end GlobalTheory
