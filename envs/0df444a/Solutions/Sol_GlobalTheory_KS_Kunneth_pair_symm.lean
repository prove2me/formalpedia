-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.pair_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:59.877788+00:00
-- url     : https://prove2.me/submissions/04b9b0a1-a5d4-46f6-add7-af0a159dd818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
import Theorems.Thm_GlobalTheory_KS_Kunneth_rsT_of_le
import Theorems.Thm_GlobalTheory_KS_Kunneth_res_pbT
import Theorems.Thm_GlobalTheory_KS_Kunneth_rsT_self
import Theorems.Thm_GlobalTheory_KS_Kunneth_prod_functional
import Theorems.Thm_GlobalTheory_KS_Kunneth_functional_eq_sum
import Theorems.Thm_GlobalTheory_KS_Kunneth_functional_cob

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth
namespace GlobalTheory.KS.Kunneth
theorem _root_.solution {K : Type} [Field K] {Y Z : Scheme.{0}} {q : Y ⟶ Sp K} {p₁ p₂ : Z ⟶ Y} {I : Type} [Finite I]
    {U : I → Y.Opens} {g : ℕ} (θ φ : Fin g → C1 U) (hq : IsSeparated q) (H : IsPullback p₁ p₂ q q)
    (hU : ∀ i, IsAffineOpen (U i)) (u : ∀ i i' j, Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j))
    (u' : ∀ i j j', Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')))
    (hu : ∀ i i' j j', ∑ a, (pbT p₁ (θ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (φ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - pbT p₁ (φ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (θ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) = (rsT (u i i' j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u i i' j) (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) + (rsT (u' i' j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u' i j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))))
    (α β : C1 U →+ K)
    (hα : ∀ (c : K) (x : C1 U), α (fun i j => constFn q (U i ⊓ U j) c * x i j) = c * α x)
    (hβ : ∀ (c : K) (x : C1 U), β (fun i j => constFn q (U i ⊓ U j) c * x i j) = c * β x)
    (hα0 : ∀ c, IsCob U c → α c = 0) (hβ0 : ∀ c, IsCob U c → β c = 0) :
    ∑ a, α (θ a) * β (φ a) = ∑ a, α (φ a) * β (θ a) := by
  classical
  haveI := Fintype.ofFinite I
  haveI := hq
  have haff : ∀ i i', IsAffineOpen (U i ⊓ U i') := fun i i' =>
    (isAffineHom_diagonal_iff (f := q)).mp inferInstance ⊤ (isAffineOpen_top _) (U i) (by simp) (U i') (by simp)
      (hU i) (hU i')
  let sg : ∀ i i', Γ(Y, U i ⊓ U i') →+ C1 U := fun i i' =>
    (AddMonoidHom.single (fun k => ∀ l, Γ(Y, U k ⊓ U l)) i).comp
      (AddMonoidHom.single (fun l => Γ(Y, U i ⊓ U l)) i')
  have hcs : ∀ (c : K) i i' (x : Γ(Y, U i ⊓ U i')),
      (fun k l => constFn q (U k ⊓ U l) c * (Pi.single i (Pi.single i' x) : C1 U) k l) =
        (Pi.single i (Pi.single i' (constFn q (U i ⊓ U i') c * x)) : C1 U) := by
    intro c i i' x
    funext k l
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = i'
      · subst hl
        simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_same, Pi.single_eq_of_ne hl, MulZeroClass.mul_zero]
    · simp only [Pi.single_eq_of_ne hk, Pi.zero_apply, MulZeroClass.mul_zero]
  have hαc : ∀ i i' (c : K) (x : Γ(Y, U i ⊓ U i')),
      (α.comp (sg i i')) (constFn q (U i ⊓ U i') c * x) = c * (α.comp (sg i i')) x := by
    intro i i' c x
    show α (Pi.single i (Pi.single i' (constFn q _ c * x))) = c * α (Pi.single i (Pi.single i' x))
    rw [← hcs c i i' x]
    exact hα c _
  have hβc : ∀ i i' (c : K) (x : Γ(Y, U i ⊓ U i')),
      (β.comp (sg i i')) (constFn q (U i ⊓ U i') c * x) = c * (β.comp (sg i i')) x := by
    intro i i' c x
    show β (Pi.single i (Pi.single i' (constFn q _ c * x))) = c * β (Pi.single i (Pi.single i' x))
    rw [← hcs c i i' x]
    exact hβ c _
  have hF0 : ∀ i i' j j', ∃ F : Γ(Z, (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) →+ K, ∀ a b,
      F (pbT p₁ a (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ b (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) =
        α (Pi.single i (Pi.single i' a)) * β (Pi.single j (Pi.single j' b)) := fun i i' j j' =>
    (prod_functional H (haff i i') (haff j j')).1 (α.comp (sg i i')) (β.comp (sg j j')) (hαc i i') (hβc j j')
  choose F hF using hF0
  have T1 : ∀ i i', ∑ j, ∑ j', (F i i' j j' (rsT (u i i' j') _) - F i i' j j' (rsT (u i i' j) _)) = 0 := by
    intro i i'
    have hG : ∀ j (w : Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)),
        ∑ j', (F i i' j' j (rsT w _) - F i i' j j' (rsT w _)) = 0 := by
      intro j
      have hle1 : ∀ j', (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j' ⊓ U j)) ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j := fun j' => by
        intro x hx
        exact ⟨hx.1, hx.2.2⟩
      have hle2 : ∀ j', (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j := fun j' => by
        intro x hx
        exact ⟨hx.1, hx.2.1⟩
      let G : Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) →+ K :=
        ∑ j', ((F i i' j' j).comp (resG Z (hle1 j')).toAddMonoidHom -
          (F i i' j j').comp (resG Z (hle2 j')).toAddMonoidHom)
      have hGw : ∀ w, G w = ∑ j', (F i i' j' j (rsT w _) - F i i' j j' (rsT w _)) := by
        intro w
        simp only [G, AddMonoidHom.finsetSum_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [rsT_of_le w (hle1 j'), rsT_of_le w (hle2 j')]
        rfl
      intro w
      rw [← hGw]
      refine (prod_functional H (haff i i') (hU j)).2 G (fun a b => ?_) w
      rw [hGw]
      have e : ∀ j', F i i' j' j (rsT (pbT p₁ a (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) *
            pbT p₂ b (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) _) -
          F i i' j j' (rsT (pbT p₁ a (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) *
            pbT p₂ b (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) _) =
          α (Pi.single i (Pi.single i' a)) * (β (Pi.single j' (Pi.single j (rsT b (U j' ⊓ U j)))) -
            β (Pi.single j (Pi.single j' (rsT b (U j ⊓ U j'))))) := by
        intro j'
        rw [rsT_of_le _ (hle1 j'), rsT_of_le _ (hle2 j'), map_mul (resG Z (hle1 j')), map_mul (resG Z (hle2 j')),
          res_pbT p₁ a inf_le_left (hle1 j') le_rfl inf_le_left,
          res_pbT p₂ b inf_le_right (hle1 j') inf_le_right inf_le_right,
          res_pbT p₁ a inf_le_left (hle2 j') le_rfl inf_le_left,
          res_pbT p₂ b inf_le_right (hle2 j') inf_le_left inf_le_right,
          rsT_self, hF, hF, mul_sub]
      rw [Finset.sum_congr rfl fun j' _ => e j', ← Finset.mul_sum, Finset.sum_sub_distrib,
        functional_cob β hβ0 j b, sub_self, MulZeroClass.mul_zero]
    calc _ = ∑ j, ∑ j', F i i' j' j (rsT (u i i' j) _) - ∑ j, ∑ j', F i i' j j' (rsT (u i i' j) _) := by
          simp only [Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_comm
      _ = ∑ j, ∑ j', (F i i' j' j (rsT (u i i' j) _) - F i i' j j' (rsT (u i i' j) _)) := by
          simp only [Finset.sum_sub_distrib]
      _ = 0 := Finset.sum_eq_zero fun j _ => hG j (u i i' j)
  have T2 : ∀ j j', ∑ i, ∑ i', (F i i' j j' (rsT (u' i' j j') _) - F i i' j j' (rsT (u' i j j') _)) = 0 := by
    intro j j'
    have hG : ∀ i (w : Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))),
        ∑ i', (F i' i j j' (rsT w _) - F i i' j j' (rsT w _)) = 0 := by
      intro i
      have hle1 : ∀ i', (p₁ ⁻¹ᵁ (U i' ⊓ U i) ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := fun i' => by
        intro x hx
        exact ⟨hx.1.2, hx.2⟩
      have hle2 : ∀ i', (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := fun i' => by
        intro x hx
        exact ⟨hx.1.1, hx.2⟩
      let G : Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) →+ K :=
        ∑ i', ((F i' i j j').comp (resG Z (hle1 i')).toAddMonoidHom -
          (F i i' j j').comp (resG Z (hle2 i')).toAddMonoidHom)
      have hGw : ∀ w, G w = ∑ i', (F i' i j j' (rsT w _) - F i i' j j' (rsT w _)) := by
        intro w
        simp only [G, AddMonoidHom.finsetSum_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [rsT_of_le w (hle1 i'), rsT_of_le w (hle2 i')]
        rfl
      intro w
      rw [← hGw]
      refine (prod_functional H (hU i) (haff j j')).2 G (fun a b => ?_) w
      rw [hGw]
      have e : ∀ i', F i' i j j' (rsT (pbT p₁ a (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) *
            pbT p₂ b (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) _) -
          F i i' j j' (rsT (pbT p₁ a (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) *
            pbT p₂ b (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) _) =
          (α (Pi.single i' (Pi.single i (rsT a (U i' ⊓ U i)))) -
            α (Pi.single i (Pi.single i' (rsT a (U i ⊓ U i'))))) * β (Pi.single j (Pi.single j' b)) := by
        intro i'
        rw [rsT_of_le _ (hle1 i'), rsT_of_le _ (hle2 i'), map_mul (resG Z (hle1 i')), map_mul (resG Z (hle2 i')),
          res_pbT p₁ a inf_le_left (hle1 i') inf_le_right inf_le_left,
          res_pbT p₂ b inf_le_right (hle1 i') le_rfl inf_le_right,
          res_pbT p₁ a inf_le_left (hle2 i') inf_le_left inf_le_left,
          res_pbT p₂ b inf_le_right (hle2 i') le_rfl inf_le_right,
          rsT_self, hF, hF, sub_mul]
      rw [Finset.sum_congr rfl fun i' _ => e i', ← Finset.sum_mul, Finset.sum_sub_distrib,
        functional_cob α hα0 i a, sub_self, MulZeroClass.zero_mul]
    calc _ = ∑ i, ∑ i', F i' i j j' (rsT (u' i j j') _) - ∑ i, ∑ i', F i i' j j' (rsT (u' i j j') _) := by
          simp only [Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_comm
      _ = ∑ i, ∑ i', (F i' i j j' (rsT (u' i j j') _) - F i i' j j' (rsT (u' i j j') _)) := by
          simp only [Finset.sum_sub_distrib]
      _ = 0 := Finset.sum_eq_zero fun i _ => hG i (u' i j j')
  have key : ∀ i i' j j', ∑ a, (α (Pi.single i (Pi.single i' (θ a i i'))) * β (Pi.single j (Pi.single j' (φ a j j'))) -
      α (Pi.single i (Pi.single i' (φ a i i'))) * β (Pi.single j (Pi.single j' (θ a j j')))) =
      F i i' j j' (rsT (u i i' j') _ - rsT (u i i' j) _ + (rsT (u' i' j j') _ - rsT (u' i j j') _)) := by
    intro i i' j j'
    rw [← hu, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sub, hF, hF]
  have expand : ∀ x y : C1 U, α x * β y = ∑ i, ∑ i', ∑ j, ∑ j',
      α (Pi.single i (Pi.single i' (x i i'))) * β (Pi.single j (Pi.single j' (y j j'))) := by
    intro x y
    rw [functional_eq_sum α x, functional_eq_sum β y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have step : ∀ f : Fin g → I → I → I → I → K, ∑ a, ∑ i, ∑ i', ∑ j, ∑ j', f a i i' j j' =
      ∑ i, ∑ i', ∑ j, ∑ j', ∑ a, f a i i' j j' := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  have swap : ∀ f : I → I → I → I → K, ∑ i, ∑ i', ∑ j, ∑ j', f i i' j j' = ∑ j, ∑ j', ∑ i, ∑ i', f i i' j j' := by
    intro f
    calc ∑ i, ∑ i', ∑ j, ∑ j', f i i' j j' = ∑ i, ∑ j, ∑ j', ∑ i', f i i' j j' := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ j, ∑ j', ∑ i, ∑ i', f i i' j j' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
  have hsplit : ∀ i i' j j', F i i' j j' (rsT (u i i' j') _ - rsT (u i i' j) _ + (rsT (u' i' j j') _ - rsT (u' i j j') _)) =
      (F i i' j j' (rsT (u i i' j') _) - F i i' j j' (rsT (u i i' j) _)) +
        (F i i' j j' (rsT (u' i' j j') _) - F i i' j j' (rsT (u' i j j') _)) := by
    intro i i' j j'
    rw [map_add, map_sub, map_sub]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have e1 : ∀ a, α (θ a) * β (φ a) - α (φ a) * β (θ a) = ∑ i, ∑ i', ∑ j, ∑ j',
      (α (Pi.single i (Pi.single i' (θ a i i'))) * β (Pi.single j (Pi.single j' (φ a j j'))) -
        α (Pi.single i (Pi.single i' (φ a i i'))) * β (Pi.single j (Pi.single j' (θ a j j')))) := by
    intro a
    rw [expand (θ a) (φ a), expand (φ a) (θ a)]
    simp only [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun a _ => e1 a, step]
  simp only [key, hsplit, Finset.sum_add_distrib, T1, _root_.zero_add]
  rw [swap]
  simp only [T2, Finset.sum_const_zero]
end GlobalTheory.KS.Kunneth
