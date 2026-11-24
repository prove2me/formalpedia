-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Vf2.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:24.404919+00:00
-- url     : https://prove2.me/submissions/fc339990-6b30-4fbc-8ad2-7d0ba6cdf1e1

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo
import Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_rank_lt
import Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_skew_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]
variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}
namespace GlobalTheory.ThK.Dbl.Vf2
theorem _root_.solution (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) (h0 : (M.map r).det = 0) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := by
  have mv : ∀ (N : Matrix β β A) x, N.map r *ᵥ r ∘ x = r ∘ (N *ᵥ x) := fun N x => funext fun i => (r.map_mulVec N x i).symm
  have mc : ∀ (N : Matrix β β A) x, N.map c *ᵥ c ∘ x = c ∘ (N *ᵥ x) := fun N x => funext fun i => (c.map_mulVec N x i).symm
  obtain ⟨y₀, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨y, rfl⟩ := hr.comp_left y₀
  obtain ⟨i, hi⟩ : ∃ i, r ((m *ᵥ y) i) ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun N : Matrix β β A => N.map r *ᵥ r ∘ y) inj
    simp only [Matrix.map_add _ (map_add r), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero,
      Matrix.map_one _ (map_zero r) (map_one r), one_mulVec] at this
    rw [mv m, show r ∘ (m *ᵥ y) = 0 from funext h, mulVec_zero, add_zero] at this
    exact hy0 this.symm
  let w : β → A := c ∘ (G' *ᵥ Pi.single i 1)
  have hw : G *ᵥ c ∘ w = Pi.single i 1 := by
    rw [show c ∘ w = G' *ᵥ Pi.single i 1 from funext fun _ => hc _, mulVec_mulVec, hG', one_mulVec]
  have fin : ∀ (u : β → A) (z : β → K), (∀ a b, r (u a * (Pi.single i 1 : β → A) b - w a * (G *ᵥ c ∘ u) b) =
      z a * (Pi.single i 1 : β → K) b) → z ∉ LinearMap.range (M.map r).mulVecLin → ∃ S : Matrix β β A,
      Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := fun u z h1 h2 => by
    refine ⟨_, skew_two hc hG u w, ?_⟩
    rw [Matrix.map_add _ (map_add r), Matrix.map_mul, hw, show (vecMulVec u (Pi.single i 1) - vecMulVec w (G *ᵥ c ∘ u)).map r =
      vecMulVec z (Pi.single i 1) from Matrix.ext h1, vecMulVec_mul]
    refine rank_lt hy h2 ?_
    rwa [← dotProduct_mulVec, mv, single_dotProduct, one_mul]
  have sg : ∀ b, r ((Pi.single i 1 : β → A) b) = (Pi.single i 1 : β → K) b := fun b => by
    simp [Pi.single_apply, apply_ite r]
  rcases hcase with ⟨h1, κ, hκ⟩ | ⟨η, h1, h2⟩
  · refine fin (κ • w) (r (κ - c κ) • r ∘ w) (fun a b => ?_) fun h => ?_
    · rw [show c ∘ (κ • w) = c κ • c ∘ w from funext fun _ => map_mul c _ _, mulVec_smul, hw]
      simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply]
      ring
    · obtain ⟨x₀, hx⟩ := (Submodule.smul_mem_iff _ hκ).1 h
      obtain ⟨x, rfl⟩ := hr.comp_left x₀
      rw [mulVecLin_apply, mv] at hx
      have l := congrArg (fun N => y ⬝ᵥ N *ᵥ c ∘ x) lag
      simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec, mc, zero_mulVec, dotProduct_zero] at l
      rw [dotProduct_mulVec y, dotProduct_mulVec y mᵀ, vecMul_transpose, vecMul_transpose] at l
      have e : (m *ᵥ y) i = (m *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (w - M *ᵥ x) - (M *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (m *ᵥ x) := by
        rw [show c ∘ (w - M *ᵥ x) = c ∘ w - c ∘ (M *ᵥ x) from funext fun _ => map_sub c _ _, mulVec_sub, dotProduct_sub, hw,
          dotProduct_single, mul_one]
        linear_combination l
      refine hi ?_
      rw [mv] at hy
      rw [e, map_sub, r.map_dotProduct, r.map_dotProduct, hy, zero_dotProduct, ← mv G, show r ∘ c ∘ (w - M *ᵥ x) = 0 from
        funext fun a => h1 _ (by rw [Pi.sub_apply, map_sub]; exact sub_eq_zero.2 (congrFun hx a).symm), mulVec_zero,
        dotProduct_zero, sub_zero]
  · obtain ⟨z₀, hz⟩ : ∃ z, z ∉ LinearMap.range (M.map r).mulVecLin := by
      by_contra h
      push Not at h
      exact ((isUnit_iff_isUnit_det _).1 (mulVec_surjective_iff_isUnit.1 h)).ne_zero h0
    obtain ⟨z, rfl⟩ := hr.comp_left z₀
    refine fin (η • z) _ (fun a b => ?_) hz
    rw [show c ∘ (η • z) = c η • c ∘ z from funext fun _ => map_mul c _ _, mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply, h1, h2]
    ring
end GlobalTheory.ThK.Dbl.Vf2
