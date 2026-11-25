-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.exists_nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:27.790884+00:00
-- url     : https://prove2.me/submissions/d4aa88d3-3f0b-4397-9ed9-6997e2d09c94

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_reframe
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_inv_lower
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_comb_sub_mem
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_perp
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_common
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_ist
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_sum_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
namespace GlobalTheory.DegCnt.RatNormal
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) (T : ℕ) (𝔡 : Ideal (𝓞 K)) (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ) (A B : Matrix (Fin j) (Fin j) K), NFFull F F' j hj c → F.T = T → F'.T = T → (∀ σ : K →+* ℂ, F.PosDefAt σ) → 𝔡 ≠ ⊥ → (∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) → (∀ a b, a < b → A a b = 0 ∧ B b a = 0) → (∀ a, A a a = 1 ∧ B a a = 1) → ((Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r))) = A * (Matrix.of fun a b => w.mat a b * ((sgn b : ℤ) : K)) * B) → ∃ N : NF H r, N.j = j ∧ N.c = c ∧ N.T = T ∧ N.𝔡 = 𝔡 ∧ (∀ a, N.F.e a - F.e a ∈ F.Xa a.val) ∧ ∀ a, N.F'.e a - F'.e a ∈ F'.Xa a.val := by
  intro K V _ _ _ _ _ _ _ _ H _ r F F' j hj c T 𝔡 w sgn A B hNF hT hT' hpos h𝔡 h𝔡s h0 h1 hZ
  obtain ⟨hS, hcn, hD, -⟩ := hNF
  obtain ⟨M, hM, hM0, hM1⟩ := exists_inv_lower A (fun a b h => (h0 a b h).1) fun a => (h1 a).1
  obtain ⟨M', hM', hM0', hM1'⟩ := exists_inv_lower B.transpose (fun a b h => (h0 a b h).2) fun a => (h1 a).2
  choose y hy hy' using exists_common F F' hj hS hD
  obtain ⟨f, hf⟩ : ∃ f : Fin (r + 1) → V, ∀ a, f a = if h : a.val < j then
      ∑ b, M ⟨a.val, h⟩ b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) else y a (not_lt.mp h) := ⟨_, fun _ => rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f' : Fin (r + 1) → V, ∀ a, f' a = if h : a.val < j then
      ∑ b, (M'.map star) ⟨a.val, h⟩ b • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)
      else c • y a (not_lt.mp h) := ⟨_, fun _ => rfl⟩
  have hF : ∀ a, f a - F.e a ∈ F.Xa a.val := fun a => by
    rw [hf]
    split_ifs with h
    · exact comb_sub_mem F hj M hM0 hM1 ⟨a.val, h⟩
    · exact hy a _
  have hF' : ∀ a, f' a - F'.e a ∈ F'.Xa a.val := fun a => by
    rw [hf']
    split_ifs with h
    · exact comb_sub_mem F' hj (M'.map star) (fun a b h => by simp [hM0' a b h]) (fun a => by simp [hM1' a]) ⟨a.val, h⟩
    · exact hy' a _
  obtain ⟨G, hG, hGT, hGX⟩ := exists_reframe F f hF
  obtain ⟨G', hG', hGT', hGX'⟩ := exists_reframe F' f' hF'
  have same : ∀ a : Fin (r + 1), j ≤ a.val → G'.e a = c • G.e a := fun a ha => by
    rw [hG, hG', hf, hf', dif_neg (not_lt.mpr ha), dif_neg (not_lt.mpr ha)]
  obtain ⟨ist, i1, i2, i3, i4⟩ := exists_ist G G' hj hS.1 same fun v => by
    obtain ⟨x, hx, hp⟩ := exists_perp F F' hj hD v
    exact ⟨x, Xa_le_X G j (by rwa [hGX]), fun u hu => hp u (by rwa [← hGX'])⟩
  have hcn' : c * star c = 1 := by
    rw [hT', ← hT] at hcn
    exact mul_right_cancel₀ F.hT (by rw [hcn, one_mul])
  have hBM : B * M'.transpose = 1 := by
    have := congrArg Matrix.transpose hM'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hW : M * (Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r))) *
      M'.transpose = Matrix.of fun a b => w.mat a b * ((sgn b : ℤ) : K) := by
    rw [hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, Matrix.one_mul, Matrix.mul_assoc, hBM, Matrix.mul_one]
  have pair : ∀ a b : Fin j, H.B (G.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
      (G'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) = w.mat a b * ((sgn b : ℤ) : K) := fun a b => by
    have h := congrFun (congrFun hW a) b
    rw [Matrix.of_apply] at h
    rw [← h, hG, hG', hf, hf', dif_pos (show (Fin.castLE (hj.trans (Nat.le_succ r)) a).val < j from a.isLt),
      dif_pos (show (Fin.castLE (hj.trans (Nat.le_succ r)) b).val < j from b.isLt), map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smulₛₗ, B_sum_left, Matrix.mul_apply]
    rw [starRingEnd_apply, Matrix.map_apply, star_star, smul_eq_mul, mul_comm]
    rfl
  have posdef : ∀ σ : K →+* ℂ, G.PosDefAt σ := fun σ v hv hvX => by
    have hXX : G.X = F.X := hGX r
    refine hpos σ v (fun a => ?_) (by rwa [← hXX])
    have h2 : H.B (f a - F.e a) v = 0 :=
      perp_X G (fun b => hv b.castSucc) _ (by rw [hXX]; exact Xa_le_X F _ (hF a))
    have h3 := hv a
    rw [hG] at h3
    rwa [map_sub, LinearMap.sub_apply, h3, zero_sub, neg_eq_zero] at h2
  refine ⟨⟨G, G', j, hj, c, hcn', T, hGT.trans hT, hGT'.trans hT', same, w, sgn, pair, ist, fun a b _ => i1 a b,
    fun a b ha _ => i2 b _ (e_mem_Xa G' a ha), fun b _ => i3 b, i4, posdef, 𝔡, h𝔡, h𝔡s⟩, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro a; show G.e a - _ ∈ _; rw [hG]; exact hF a
  · intro a; show G'.e a - _ ∈ _; rw [hG']; exact hF' a
end GlobalTheory.DegCnt.RatNormal
