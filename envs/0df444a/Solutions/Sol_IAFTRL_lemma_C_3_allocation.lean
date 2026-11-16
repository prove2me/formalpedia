-- Prove2me | solution 1 for IAFTRL.lemma_C_3_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T09:12:51.891285+00:00
-- url     : https://prove2.me/submissions/4bf0bd09-ceea-4a96-b9a1-c94e61a508b8

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost
import Definitions.Def_IAFTRL_allocMass
import Definitions.Def_IAFTRL_GA
import Theorems.Thm_IAFTRL_lemma_C_3_cstar_bound
import Theorems.Thm_IAFTRL_lemma_C_4
import Theorems.Thm_IAFTRL_lemma_J_3_finite

open Matrix

namespace C3A

lemma gram_bil {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) (β v : Fin r → ℝ) :
    ((∑ c, n c • vecMulVec (X c) (X c)) *ᵥ β) ⬝ᵥ v = ∑ c, n c * (X c ⬝ᵥ β) * (X c ⬝ᵥ v) := by
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, sum_dotProduct,
    smul_dotProduct, smul_eq_mul, op_smul_eq_smul]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma gram_qf {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) (v : Fin r → ℝ) :
    v ⬝ᵥ ((∑ c, n c • vecMulVec (X c) (X c)) *ᵥ v) = ∑ c, n c * (X c ⬝ᵥ v) ^ 2 := by
  rw [dotProduct_comm, gram_bil]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma gram_herm {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) :
    (∑ c, n c • vecMulVec (X c) (X c)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]

/-- Cauchy–Schwarz for a positive definite matrix. -/
lemma cs_pd {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) (hH : H.PosDef) (a w : Fin r → ℝ) :
    (a ⬝ᵥ w) ^ 2 ≤ (a ⬝ᵥ H⁻¹ *ᵥ a) * (w ⬝ᵥ H *ᵥ w) := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hT : Hᵀ = H := by
    have := hH.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set v := H⁻¹ *ᵥ a with hv
  have hHv : H *ᵥ v = a := by rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  -- symmetry of the bilinear form
  have hsym : ∀ x y : Fin r → ℝ, x ⬝ᵥ H *ᵥ y = y ⬝ᵥ H *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have haw : a ⬝ᵥ w = v ⬝ᵥ H *ᵥ w := by rw [← hHv, hsym, dotProduct_comm]
  have hav : a ⬝ᵥ v = v ⬝ᵥ H *ᵥ v := by rw [hHv, dotProduct_comm]
  rw [haw, hav]
  by_cases hw : w = 0
  · subst hw; simp
  have hww : 0 < w ⬝ᵥ H *ᵥ w := by
    have := hH.dotProduct_mulVec_pos hw
    rwa [star_trivial] at this
  set t := (v ⬝ᵥ H *ᵥ w) / (w ⬝ᵥ H *ᵥ w)
  have hpsd : 0 ≤ (v - t • w) ⬝ᵥ H *ᵥ (v - t • w) := by
    by_cases h0 : v - t • w = 0
    · rw [h0]; simp
    · have := hH.dotProduct_mulVec_pos h0
      rw [star_trivial] at this
      exact this.le
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at hpsd
  rw [hsym w v] at hpsd
  have ht : t * (w ⬝ᵥ H *ᵥ w) = v ⬝ᵥ H *ᵥ w := by
    simp only [t]; field_simp
  nlinarith [ht]

/-- A quadratic-form bound gives the inverse-form bound. -/
lemma inv_le_of_qf {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) (hH : H.PosDef) (a : Fin r → ℝ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hqf : ∀ w, (a ⬝ᵥ w) ^ 2 ≤ κ * (w ⬝ᵥ H *ᵥ w)) :
    a ⬝ᵥ H⁻¹ *ᵥ a ≤ κ := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  set v := H⁻¹ *ᵥ a with hv
  have hHv : H *ᵥ v = a := by rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  have h := hqf v
  rw [hHv, dotProduct_comm v a] at h
  by_cases hp : a ⬝ᵥ v ≤ 0
  · linarith
  · have hp' : 0 < a ⬝ᵥ v := lt_of_not_ge hp
    nlinarith

/-- Vectors orthogonal to a spanning family vanish. -/
lemma eq_zero_of_orth {K d : ℕ} (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) (w : Fin d → ℝ)
    (h : ∀ c, arms c ⬝ᵥ w = 0) : w = 0 := by
  have : ∀ v ∈ Submodule.span ℝ (Set.range arms), v ⬝ᵥ w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact h c
    | zero => simp
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
    | smul t x _ hx => rw [smul_dotProduct, hx, smul_zero]
  have hw := this w (by rw [hspan]; trivial)
  exact dotProduct_self_eq_zero.mp hw

end C3A

namespace C3A

open IAFTRL

theorem core {d K r : ℕ} (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (θ : Fin d → ℝ) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀)
    (hΔ : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ)
    (hcstar : BanditAlgorithm.linearBanditAllocationValue arms (-θ) ≤ 2 * (d : ℝ) / Δ₀)
    (n₀ : Fin K → ℝ) (hn₀0 : ∀ j, 0 ≤ n₀ j)
    (hn₀PD : (BanditAlgorithm.linearAllocationMatrix arms n₀).PosDef)
    (hn₀f : ∀ j, j ≠ jstar → arms j ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms n₀)⁻¹ *ᵥ
      arms j ≤ ((arms j - arms jstar) ⬝ᵥ θ) ^ 2 / 2)
    (G : ℝ) (hG : 0 < G)
    (U : Matrix (Fin d) (Fin r) ℝ) (hUU : Uᵀ * U = 1) (hUb : Uᵀ *ᵥ arms jstar = 0)
    (uv : Fin d → ℝ) (ρ : ℝ)
    (hcomp : ∀ c w : Fin d → ℝ, c ⬝ᵥ w = (c ⬝ᵥ uv) * (uv ⬝ᵥ w) + (Uᵀ *ᵥ c) ⬝ᵥ (Uᵀ *ᵥ w))
    (hb : ∀ w, arms jstar ⬝ᵥ w = ρ * (uv ⬝ᵥ w))
    (hres : ∀ m : Fin K → ℝ, (∀ c, 0 ≤ m c) →
      (∑ c, m c • vecMulVec (Uᵀ *ᵥ arms c) (Uᵀ *ᵥ arms c)).PosDef →
      ∀ a, a ≠ jstar →
        |arms a ⬝ᵥ uv - (Uᵀ *ᵥ arms a) ⬝ᵥ
          ((∑ c, m c • vecMulVec (Uᵀ *ᵥ arms c) (Uᵀ *ᵥ arms c))⁻¹ *ᵥ
            ∑ c, (m c * (arms c ⬝ᵥ uv)) • (Uᵀ *ᵥ arms c))| ≤ G * ρ) :
    ∃ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n ∧
      allocCost arms θ jstar n ≤ 2 * BanditAlgorithm.linearBanditAllocationValue arms (-θ) ∧
      allocMass n ≤ 4 * ((d : ℝ) + G ^ 2) / Δ₀ ^ 2 := by
  classical
  -- gaps
  set Δ : Fin K → ℝ := fun j => (arms j - arms jstar) ⬝ᵥ θ with hΔdef
  have hΔstar : Δ jstar = 0 := by simp [Δ]
  have hΔpos : ∀ j, j ≠ jstar → 0 < Δ j := fun j hj => lt_of_lt_of_le hΔ₀ (hΔ j hj)
  have hΔnn : ∀ j, 0 ≤ Δ j := by
    intro j
    by_cases h : j = jstar
    · rw [h, hΔstar]
    · exact (hΔpos j h).le
  have hsup : (⨆ j', arms j' ⬝ᵥ -θ) = arms jstar ⬝ᵥ -θ := by
    have : Nonempty (Fin K) := ⟨jstar⟩
    apply le_antisymm
    · apply ciSup_le
      intro j'
      by_cases h : j' = jstar
      · rw [h]
      · have := hu j' h
        simp only [dotProduct_neg]
        linarith
    · exact le_ciSup (f := fun j' => arms j' ⬝ᵥ -θ) (Set.finite_range _).bddAbove jstar
  have hgap : ∀ j, BanditAlgorithm.linearArmGap arms (-θ) j = Δ j := by
    intro j
    simp only [BanditAlgorithm.linearArmGap]
    rw [hsup]
    simp only [Δ, dotProduct_neg, sub_dotProduct]
    ring
  -- projected actions
  set x : Fin K → Fin r → ℝ := fun c => Uᵀ *ᵥ arms c with hxdef
  have hxb : x jstar = 0 := hUb
  have hxU : ∀ c (y : Fin r → ℝ), arms c ⬝ᵥ (U *ᵥ y) = x c ⬝ᵥ y := by
    intro c y
    simp only [x]
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  set cost : (Fin K → ℝ) → ℝ := fun m => ∑ c, m c * Δ c with hcostdef
  have hcont : Continuous cost :=
    continuous_finsetSum _ fun c _ => (continuous_apply c).mul continuous_const
  -- the program defining `c*`
  set Sfull : Set (Fin K → ℝ) := {α | (∀ j, 0 ≤ α j) ∧
      (BanditAlgorithm.linearAllocationMatrix arms α).PosDef ∧
      ∀ j, 0 < BanditAlgorithm.linearArmGap arms (-θ) j →
        arms j ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms α)⁻¹ *ᵥ arms j ≤
          BanditAlgorithm.linearArmGap arms (-θ) j ^ 2 / 2} with hSfull
  have hn₀mem : n₀ ∈ Sfull := by
    refine ⟨hn₀0, hn₀PD, fun j hj => ?_⟩
    rw [hgap] at hj ⊢
    have hjs : j ≠ jstar := by
      rintro rfl
      rw [hΔstar] at hj
      exact lt_irrefl _ hj
    exact hn₀f j hjs
  -- the projected program
  set F : ℝ → Set (Fin K → ℝ) := fun B => {m | (∀ c, 0 ≤ m c) ∧ m jstar = 0 ∧ cost m ≤ B ∧
      ∀ a, a ≠ jstar → ∀ y : Fin r → ℝ,
        (x a ⬝ᵥ y) ^ 2 ≤ Δ a ^ 2 / 2 * ∑ c, m c * (x c ⬝ᵥ y) ^ 2} with hFdef
  set restr : (Fin K → ℝ) → (Fin K → ℝ) := fun α c => if c = jstar then 0 else α c with hrestr
  have hrestr_cost : ∀ α, cost (restr α) = cost α := by
    intro α
    simp only [cost, restr]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with h
    · rw [h, hΔstar]; simp
    · rfl
  have hrestr_mem : ∀ α ∈ Sfull, ∀ B, cost α ≤ B → restr α ∈ F B := by
    intro α hα B hB
    obtain ⟨hα0, hαPD, hαfeas⟩ := hα
    refine ⟨fun c => ?_, by simp [restr], (hrestr_cost α).le.trans hB, ?_⟩
    · simp only [restr]; split_ifs; exacts [le_rfl, hα0 c]
    intro a ha y
    have hfa := hαfeas a (by rw [hgap]; exact hΔpos a ha)
    rw [hgap] at hfa
    have hcs := cs_pd _ hαPD (arms a) (U *ᵥ y)
    rw [hxU] at hcs
    have hq := gram_qf arms α (U *ᵥ y)
    have hsum : ∑ c, α c * (arms c ⬝ᵥ U *ᵥ y) ^ 2 =
        ∑ c, restr α c * (x c ⬝ᵥ y) ^ 2 := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hxU]
      simp only [restr]
      split_ifs with h
      · rw [h, hxb]; simp
      · rfl
    have hnn : 0 ≤ (U *ᵥ y) ⬝ᵥ BanditAlgorithm.linearAllocationMatrix arms α *ᵥ (U *ᵥ y) := by
      unfold BanditAlgorithm.linearAllocationMatrix
      rw [hq]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (hα0 c) (sq_nonneg _)
    calc (x a ⬝ᵥ y) ^ 2
        ≤ (arms a ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms α)⁻¹ *ᵥ arms a) *
            ((U *ᵥ y) ⬝ᵥ BanditAlgorithm.linearAllocationMatrix arms α *ᵥ (U *ᵥ y)) := hcs
      _ ≤ Δ a ^ 2 / 2 *
            ((U *ᵥ y) ⬝ᵥ BanditAlgorithm.linearAllocationMatrix arms α *ᵥ (U *ᵥ y)) :=
          mul_le_mul_of_nonneg_right hfa hnn
      _ = Δ a ^ 2 / 2 * ∑ c, restr α c * (x c ⬝ᵥ y) ^ 2 := by
          unfold BanditAlgorithm.linearAllocationMatrix
          rw [hq, hsum]
  -- compactness and a minimizer
  set B₀ := cost n₀ with hB₀def
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg fun c _ => mul_nonneg (hn₀0 c) (hΔnn c)
  have hFne : (F B₀).Nonempty := ⟨_, hrestr_mem n₀ hn₀mem B₀ le_rfl⟩
  have hFsub : F B₀ ⊆ Set.pi Set.univ (fun _ => Set.Icc 0 (B₀ / Δ₀)) := by
    rintro m ⟨hm0, hmb, hmc, -⟩ c -
    refine ⟨hm0 c, ?_⟩
    by_cases hc : c = jstar
    · rw [hc, hmb]; positivity
    · rw [le_div_iff₀ hΔ₀]
      calc m c * Δ₀ ≤ m c * Δ c := mul_le_mul_of_nonneg_left (hΔ c hc) (hm0 c)
        _ ≤ cost m := Finset.single_le_sum (f := fun c => m c * Δ c)
            (fun c _ => mul_nonneg (hm0 c) (hΔnn c)) (Finset.mem_univ c)
        _ ≤ B₀ := hmc
  have hFclosed : IsClosed (F B₀) := by
    have hF : F B₀ = (⋂ c, {m : Fin K → ℝ | 0 ≤ m c}) ∩ {m | m jstar = 0} ∩ {m | cost m ≤ B₀} ∩
        ⋂ a, ⋂ (_ : a ≠ jstar), ⋂ y : Fin r → ℝ,
          {m | (x a ⬝ᵥ y) ^ 2 ≤ Δ a ^ 2 / 2 * ∑ c, m c * (x c ⬝ᵥ y) ^ 2} := by
      ext m
      simp only [F, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      tauto
    rw [hF]
    refine (((isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c)).inter
      (isClosed_eq (continuous_apply jstar) continuous_const)).inter
      (isClosed_le hcont continuous_const)).inter
      (isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_iInter fun y =>
        isClosed_le continuous_const ?_)
    exact continuous_const.mul
      (continuous_finsetSum _ fun c _ => (continuous_apply c).mul continuous_const)
  have hFcpt : IsCompact (F B₀) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hFclosed hFsub
  obtain ⟨m, hmF, hmin⟩ := hFcpt.exists_isMinOn hFne hcont.continuousOn
  obtain ⟨hm0, hmb, hmc, hmQ⟩ := hmF
  -- the minimal projected cost is at most `c*`
  have hcostle : cost m ≤ BanditAlgorithm.linearBanditAllocationValue arms (-θ) := by
    have hval : BanditAlgorithm.linearBanditAllocationValue arms (-θ) =
        sInf ((fun α => ∑ j, α j * BanditAlgorithm.linearArmGap arms (-θ) j) '' Sfull) := rfl
    rw [hval]
    refine le_csInf ⟨_, n₀, hn₀mem, rfl⟩ ?_
    rintro _ ⟨α, hα, rfl⟩
    show cost m ≤ ∑ j, α j * BanditAlgorithm.linearArmGap arms (-θ) j
    have hαc : (∑ j, α j * BanditAlgorithm.linearArmGap arms (-θ) j) = cost α := by
      simp only [hgap, cost]
    rw [hαc]
    by_cases hle : cost α ≤ B₀
    · have := isMinOn_iff.mp hmin _ (hrestr_mem α hα B₀ hle)
      rw [hrestr_cost] at this
      exact this
    · linarith
  -- the projected design is positive definite
  set D : Matrix (Fin r) (Fin r) ℝ := ∑ c, m c • vecMulVec (x c) (x c) with hDdef
  have hDpd : D.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (gram_herm x m) fun y hy => ?_
    rw [star_trivial, gram_qf]
    by_contra hle
    have hz : ∑ c, m c * (x c ⬝ᵥ y) ^ 2 = 0 :=
      le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun c _ => mul_nonneg (hm0 c) (sq_nonneg _))
    have hxy : ∀ c, x c ⬝ᵥ y = 0 := by
      intro c
      by_cases hc : c = jstar
      · rw [hc, hxb, zero_dotProduct]
      · have h2 := hmQ c hc y
        rw [hz, mul_zero] at h2
        exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _))
    have hUy : U *ᵥ y = 0 := eq_zero_of_orth arms hspan _ fun c => by rw [hxU]; exact hxy c
    apply hy
    calc y = (Uᵀ * U) *ᵥ y := by rw [hUU, Matrix.one_mulVec]
      _ = Uᵀ *ᵥ (U *ᵥ y) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hUy, Matrix.mulVec_zero]
  have hdetD : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDpd.isUnit
  -- weighted least squares and the normal equations
  set S : Fin r → ℝ := ∑ c, (m c * (arms c ⬝ᵥ uv)) • x c with hSdef
  set β : Fin r → ℝ := D⁻¹ *ᵥ S with hβdef
  have hDβ : D *ᵥ β = S := by
    rw [hβdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetD, Matrix.one_mulVec]
  have hnormal : ∀ v, ∑ c, m c * (arms c ⬝ᵥ uv - x c ⬝ᵥ β) * (x c ⬝ᵥ v) = 0 := by
    intro v
    have h1 := gram_bil x m β v
    rw [← hDdef, hDβ] at h1
    have h2 : S ⬝ᵥ v = ∑ c, m c * (arms c ⬝ᵥ uv) * (x c ⬝ᵥ v) := by
      simp only [S, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    have h3 : ∑ c, m c * (arms c ⬝ᵥ uv - x c ⬝ᵥ β) * (x c ⬝ᵥ v) =
        ∑ c, m c * (arms c ⬝ᵥ uv) * (x c ⬝ᵥ v) - ∑ c, m c * (x c ⬝ᵥ β) * (x c ⬝ᵥ v) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [h3, ← h2, ← h1, sub_self]
  have hres_m := hres m hm0 hDpd
  -- the lift: double `m` and put mass `N` on `a*`
  set N : ℝ := 4 * G ^ 2 / Δ₀ ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  set n : Fin K → ℝ := fun c => if c = jstar then N else 2 * m c with hndef
  have hnsum : ∀ f : Fin K → ℝ, ∑ c, n c * f c = N * f jstar + 2 * ∑ c, m c * f c := by
    intro f
    have : ∀ c, n c * f c = (if c = jstar then N * f c else 0) + 2 * (m c * f c) := by
      intro c
      by_cases hc : c = jstar
      · simp [n, hc, hmb]
      · simp [n, hc]; ring
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ← Finset.mul_sum]
    simp
  have hQF : ∀ a, a ≠ jstar → ∀ w : Fin d → ℝ, (arms a ⬝ᵥ w) ^ 2 ≤
      Δ a ^ 2 / 2 * (N * (arms jstar ⬝ᵥ w) ^ 2 + 2 * ∑ c, m c * (arms c ⬝ᵥ w) ^ 2) := by
    intro a ha w
    set s := uv ⬝ᵥ w with hs
    set y := Uᵀ *ᵥ w with hy
    set y' := y + s • β with hy'
    set rr : Fin K → ℝ := fun c => arms c ⬝ᵥ uv - x c ⬝ᵥ β with hrr
    have hcw : ∀ c, arms c ⬝ᵥ w = x c ⬝ᵥ y' + rr c * s := by
      intro c
      rw [hcomp (arms c) w]
      simp only [y', rr, x, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    have hexp : ∑ c, m c * (arms c ⬝ᵥ w) ^ 2 =
        ∑ c, m c * (x c ⬝ᵥ y') ^ 2 + s ^ 2 * ∑ c, m c * rr c ^ 2 := by
      have hn0 := hnormal y'
      have : ∀ c, m c * (arms c ⬝ᵥ w) ^ 2 = m c * (x c ⬝ᵥ y') ^ 2 +
          2 * s * (m c * rr c * (x c ⬝ᵥ y')) + s ^ 2 * (m c * rr c ^ 2) := by
        intro c; rw [hcw c]; ring
      rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [rr] at hn0 ⊢
      rw [hn0]
      ring
    have hP : ∑ c, m c * (x c ⬝ᵥ y') ^ 2 ≤ ∑ c, m c * (arms c ⬝ᵥ w) ^ 2 := by
      rw [hexp]
      have : 0 ≤ s ^ 2 * ∑ c, m c * rr c ^ 2 :=
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun c _ => mul_nonneg (hm0 c) (sq_nonneg _))
      linarith
    have hX := hmQ a ha y'
    have hra : rr a ^ 2 ≤ G ^ 2 * ρ ^ 2 := by
      have h := hres_m a ha
      have h0 : 0 ≤ G * ρ := (abs_nonneg _).trans h
      calc rr a ^ 2 = |rr a| ^ 2 := (sq_abs _).symm
        _ ≤ (G * ρ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = G ^ 2 * ρ ^ 2 := by ring
    have hbw : (arms jstar ⬝ᵥ w) ^ 2 = ρ ^ 2 * s ^ 2 := by rw [hb w]; ring
    have hN : 2 * G ^ 2 ≤ Δ a ^ 2 / 2 * N := by
      have h1 : Δ₀ ^ 2 ≤ Δ a ^ 2 := pow_le_pow_left₀ hΔ₀.le (hΔ a ha) 2
      have h2 : 1 ≤ Δ a ^ 2 / Δ₀ ^ 2 := (one_le_div (by positivity)).mpr h1
      have h3 : Δ a ^ 2 / 2 * N = 2 * G ^ 2 * (Δ a ^ 2 / Δ₀ ^ 2) := by
        simp only [N]; field_simp; ring
      rw [h3]
      nlinarith [sq_nonneg G]
    have ha2 : (arms a ⬝ᵥ w) ^ 2 ≤ 2 * (x a ⬝ᵥ y') ^ 2 + 2 * (rr a ^ 2 * s ^ 2) := by
      rw [hcw a]
      nlinarith [sq_nonneg (x a ⬝ᵥ y' - rr a * s)]
    have hΔa2 : 0 ≤ Δ a ^ 2 := sq_nonneg _
    have e1 : 2 * (x a ⬝ᵥ y') ^ 2 ≤ Δ a ^ 2 * ∑ c, m c * (arms c ⬝ᵥ w) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hP hΔa2
      linarith
    have e2 : 2 * (rr a ^ 2 * s ^ 2) ≤ Δ a ^ 2 / 2 * N * (ρ ^ 2 * s ^ 2) := by
      have hs2 := sq_nonneg s
      have h4 := mul_le_mul_of_nonneg_right hra hs2
      have h5 := mul_le_mul_of_nonneg_right hN (mul_nonneg (sq_nonneg ρ) hs2)
      nlinarith
    rw [hbw]
    have e3 : Δ a ^ 2 / 2 * (N * (ρ ^ 2 * s ^ 2) + 2 * ∑ c, m c * (arms c ⬝ᵥ w) ^ 2) =
        Δ a ^ 2 / 2 * N * (ρ ^ 2 * s ^ 2) + Δ a ^ 2 * ∑ c, m c * (arms c ⬝ᵥ w) ^ 2 := by ring
    rw [e3]
    linarith
  -- the lifted design
  have hHqf : ∀ w : Fin d → ℝ, w ⬝ᵥ BanditAlgorithm.linearAllocationMatrix arms n *ᵥ w =
      N * (arms jstar ⬝ᵥ w) ^ 2 + 2 * ∑ c, m c * (arms c ⬝ᵥ w) ^ 2 := by
    intro w
    unfold BanditAlgorithm.linearAllocationMatrix
    rw [gram_qf, hnsum (fun c => (arms c ⬝ᵥ w) ^ 2)]
  have hHpd : (BanditAlgorithm.linearAllocationMatrix arms n).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (gram_herm arms n) fun w hw => ?_
    rw [star_trivial, hHqf]
    by_contra hle
    have hA0 : 0 ≤ N * (arms jstar ⬝ᵥ w) ^ 2 := mul_nonneg hNpos.le (sq_nonneg _)
    have hB0 : 0 ≤ ∑ c, m c * (arms c ⬝ᵥ w) ^ 2 :=
      Finset.sum_nonneg fun c _ => mul_nonneg (hm0 c) (sq_nonneg _)
    have hzero : N * (arms jstar ⬝ᵥ w) ^ 2 + 2 * ∑ c, m c * (arms c ⬝ᵥ w) ^ 2 = 0 := by
      linarith [not_lt.mp hle]
    apply hw
    refine eq_zero_of_orth arms hspan w fun c => ?_
    by_cases hc : c = jstar
    · rw [hc]
      have : N * (arms jstar ⬝ᵥ w) ^ 2 = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hNpos.ne'
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    · have h := hQF c hc w
      rw [hzero, mul_zero] at h
      exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h (sq_nonneg _))
  refine ⟨n, ⟨fun c => ?_, hHpd, fun j hj => ?_⟩, ?_, ?_⟩
  · simp only [n]; split_ifs; exacts [hNpos.le, by linarith [hm0 c]]
  · refine inv_le_of_qf _ hHpd (arms j) (Δ j ^ 2 / 2) (by positivity) fun w => ?_
    rw [hHqf]
    exact hQF j hj w
  · -- cost
    show ∑ j, n j * Δ j ≤ _
    rw [hnsum Δ, hΔstar, mul_zero, zero_add]
    linarith [hcostle]
  · -- mass
    show ∑ j, n j ≤ _
    have h1 := hnsum (fun _ => 1)
    simp only [mul_one] at h1
    rw [h1]
    have hsm : Δ₀ * ∑ c, m c ≤ cost m := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      by_cases hc : c = jstar
      · rw [hc, hmb]; simp
      · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hΔ c hc) (hm0 c)
    have hsm2 : Δ₀ ^ 2 * ∑ c, m c ≤ 2 * d := by
      have := hsm.trans (hcostle.trans hcstar)
      have h' : Δ₀ * (Δ₀ * ∑ c, m c) ≤ Δ₀ * (2 * d / Δ₀) := mul_le_mul_of_nonneg_left this hΔ₀.le
      rw [mul_div_cancel₀ _ hΔ₀.ne'] at h'
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    have : N * Δ₀ ^ 2 = 4 * G ^ 2 := by simp only [N]; field_simp
    nlinarith

end C3A

namespace C3A

lemma exists_perp {d : ℕ} (hd : 1 ≤ d) (b : Fin d → ℝ) (hb : b ≠ 0) :
    ∃ U : Matrix (Fin d) (Fin (d - 1)) ℝ, Uᵀ * U = 1 ∧ Uᵀ *ᵥ b = 0 := by
  classical
  set B : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 b with hBdef
  have hB : B ≠ 0 := by
    intro h
    apply hb
    have := congrArg WithLp.ofLp h
    simpa [B] using this
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = (d - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  have hW : Module.finrank ℝ (ℝ ∙ B)ᗮ = d - 1 := Submodule.finrank_orthogonal_span_singleton hB
  let e := (stdOrthonormalBasis ℝ (ℝ ∙ B)ᗮ).reindex (finCongr hW)
  refine ⟨Matrix.of fun i k => WithLp.ofLp (((e k : (ℝ ∙ B)ᗮ)) : EuclideanSpace ℝ (Fin d)) i,
    ?_, ?_⟩
  · ext k l
    have h := (orthonormal_iff_ite.mp e.orthonormal) k l
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    simp only [Matrix.transpose_apply, Matrix.of_apply, dotProduct, star_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ext k
    have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (e k).2
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply] at h ⊢
    rw [← h]
    simp [B]

lemma complete_decomp {d : ℕ} (hd : 1 ≤ d) (U : Matrix (Fin d) (Fin (d - 1)) ℝ) (u : Fin d → ℝ)
    (hUU : Uᵀ * U = 1) (hUu : Uᵀ *ᵥ u = 0) (huu : u ⬝ᵥ u = 1) :
    ∀ c w : Fin d → ℝ, c ⬝ᵥ w = (c ⬝ᵥ u) * (u ⬝ᵥ w) + (Uᵀ *ᵥ c) ⬝ᵥ (Uᵀ *ᵥ w) := by
  classical
  let Q : Matrix (Fin d) (Option (Fin (d - 1))) ℝ :=
    Matrix.of fun i o => o.elim (u i) (fun k => U i k)
  have hUu' : ∀ k, ∑ i, U i k * u i = 0 := by
    intro k
    have := congrFun hUu k
    simpa [Matrix.mulVec, dotProduct] using this
  have hUU' : ∀ k l, ∑ i, U i k * U i l = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hUU k) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have huu' : ∑ i, u i * u i = 1 := by simpa [dotProduct] using huu
  have hQ : Qᵀ * Q = 1 := by
    ext o o'
    cases o with
    | none =>
      cases o' with
      | none => simpa [Q, Matrix.mul_apply] using huu'
      | some l =>
        simp only [Q, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Option.elim,
          Matrix.one_apply, reduceCtorEq, if_false]
        rw [← hUu' l]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    | some k =>
      cases o' with
      | none =>
        simp only [Q, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Option.elim,
          Matrix.one_apply, reduceCtorEq, if_false]
        exact hUu' k
      | some l =>
        simp only [Q, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Option.elim,
          Matrix.one_apply, Option.some.injEq]
        exact hUU' k l
  have hcard : Fintype.card (Fin d) = Fintype.card (Option (Fin (d - 1))) := by
    simp only [Fintype.card_fin, Fintype.card_option]; omega
  let e : Fin d ≃ Option (Fin (d - 1)) := Fintype.equivOfCardEq hcard
  have hQ'' : Q * Qᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hQ
  intro c w
  have key : c ⬝ᵥ w = c ⬝ᵥ (Q * Qᵀ) *ᵥ w := by rw [hQ'', Matrix.one_mulVec]
  rw [key, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  rw [Fintype.sum_option]
  simp only [Q, Matrix.of_apply, Option.elim]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end C3A

namespace C3A

open IAFTRL

/-- `G_𝒜 ≥ 1`, and every admissible residual ratio is at most `G_𝒜`. -/
theorem GA_spec {d K : ℕ} (arms : Fin K → Fin d → ℝ) :
    1 ≤ GA arms ∧ ∀ (jb : Fin K) (I : Finset (Fin K)) (hI : I.card = d - 1) (a : Fin K),
      arms jb ≠ 0 → jb ∉ I → a ≠ jb →
      (Matrix.of fun i k => ((perpBasis (arms jb))ᵀ *ᵥ arms (I.orderEmbOfFin hI i)) k :
          Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ).det ≠ 0 →
      |(arms jb ⬝ᵥ arms a) / Real.sqrt (arms jb ⬝ᵥ arms jb) -
          ((perpBasis (arms jb))ᵀ *ᵥ arms a) ⬝ᵥ
            ((Matrix.of fun i k => ((perpBasis (arms jb))ᵀ *ᵥ arms (I.orderEmbOfFin hI i)) k :
                Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ)⁻¹ *ᵥ
              fun i => (arms jb ⬝ᵥ arms (I.orderEmbOfFin hI i)) /
                Real.sqrt (arms jb ⬝ᵥ arms jb))| /
        Real.sqrt (arms jb ⬝ᵥ arms jb) ≤ GA arms := by
  classical
  let f : Fin K × Finset (Fin K) × Fin K → ℝ := fun p =>
    if hI : p.2.1.card = d - 1 then
      |(arms p.1 ⬝ᵥ arms p.2.2) / Real.sqrt (arms p.1 ⬝ᵥ arms p.1) -
          ((perpBasis (arms p.1))ᵀ *ᵥ arms p.2.2) ⬝ᵥ
            ((Matrix.of fun i k =>
                ((perpBasis (arms p.1))ᵀ *ᵥ arms (p.2.1.orderEmbOfFin hI i)) k :
                Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ)⁻¹ *ᵥ
              fun i => (arms p.1 ⬝ᵥ arms (p.2.1.orderEmbOfFin hI i)) /
                Real.sqrt (arms p.1 ⬝ᵥ arms p.1))| /
        Real.sqrt (arms p.1 ⬝ᵥ arms p.1)
    else 0
  have hbdd : BddAbove ({1} ∪ {g : ℝ | ∃ (jb : Fin K) (I : Finset (Fin K)) (hI : I.card = d - 1)
      (a : Fin K), arms jb ≠ 0 ∧ jb ∉ I ∧ a ≠ jb ∧
      (Matrix.of fun i k => ((perpBasis (arms jb))ᵀ *ᵥ arms (I.orderEmbOfFin hI i)) k :
          Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ).det ≠ 0 ∧
      g = |(arms jb ⬝ᵥ arms a) / Real.sqrt (arms jb ⬝ᵥ arms jb) -
            ((perpBasis (arms jb))ᵀ *ᵥ arms a) ⬝ᵥ
              ((Matrix.of fun i k => ((perpBasis (arms jb))ᵀ *ᵥ arms (I.orderEmbOfFin hI i)) k :
                  Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ)⁻¹ *ᵥ
                fun i => (arms jb ⬝ᵥ arms (I.orderEmbOfFin hI i)) /
                  Real.sqrt (arms jb ⬝ᵥ arms jb))| /
          Real.sqrt (arms jb ⬝ᵥ arms jb)}) := by
    apply Set.Finite.bddAbove
    refine (Set.finite_singleton 1).union ((Set.finite_range f).subset ?_)
    rintro g ⟨jb, I, hI, a, -, -, -, -, rfl⟩
    exact ⟨(jb, I, a), by simp [f, hI]⟩
  refine ⟨le_csSup hbdd (Or.inl rfl), fun jb I hI a h1 h2 h3 h4 => ?_⟩
  exact le_csSup hbdd (Or.inr ⟨jb, I, hI, a, h1, h2, h3, h4, rfl⟩)

end C3A

open IAFTRL C3A

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀)
    (hΔ : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) :
    ∃ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n ∧
      allocCost arms θ jstar n ≤ 2 * BanditAlgorithm.linearBanditAllocationValue arms (-θ) ∧
      allocMass n ≤ 4 * ((d : ℝ) + GA arms ^ 2) / Δ₀ ^ 2 := by
  classical
  have hspan := hA.2.2
  have hcstar := lemma_C_3_cstar_bound hd arms hA θ jstar hu Δ₀ hΔ₀ hΔ
  obtain ⟨hG1, hGmem⟩ := GA_spec arms
  have hGpos : 0 < GA arms := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- a feasible starting allocation: a scaled G-optimal law
  obtain ⟨π, hπ0, -, hπPD, hπG⟩ := lemma_J_3_finite hd arms hspan
  set κ : ℝ := 2 * d / Δ₀ ^ 2 with hκ
  have hκpos : 0 < κ := by positivity
  set n₀ : Fin K → ℝ := fun j => κ * π j with hn₀def
  have hn₀H : BanditAlgorithm.linearAllocationMatrix arms n₀ =
      κ • BanditAlgorithm.linearAllocationMatrix arms π := by
    simp only [BanditAlgorithm.linearAllocationMatrix, n₀, Finset.smul_sum, smul_smul]
  have hπunit : IsUnit (BanditAlgorithm.linearAllocationMatrix arms π).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hπPD.isUnit
  have hn₀inv : (BanditAlgorithm.linearAllocationMatrix arms n₀)⁻¹ =
      κ⁻¹ • (BanditAlgorithm.linearAllocationMatrix arms π)⁻¹ := by
    rw [hn₀H]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hπunit, smul_smul,
      inv_mul_cancel₀ hκpos.ne', one_smul]
  have hn₀0 : ∀ j, 0 ≤ n₀ j := fun j => mul_nonneg hκpos.le (hπ0 j)
  have hn₀PD : (BanditAlgorithm.linearAllocationMatrix arms n₀).PosDef := by
    rw [hn₀H]; exact hπPD.smul hκpos
  have hn₀f : ∀ j, j ≠ jstar → arms j ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms n₀)⁻¹ *ᵥ
      arms j ≤ ((arms j - arms jstar) ⬝ᵥ θ) ^ 2 / 2 := by
    intro j hj
    rw [hn₀inv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h1 := hπG j
    have h2 : Δ₀ ^ 2 ≤ ((arms j - arms jstar) ⬝ᵥ θ) ^ 2 := pow_le_pow_left₀ hΔ₀.le (hΔ j hj) 2
    calc κ⁻¹ * (arms j ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms π)⁻¹ *ᵥ arms j)
        ≤ κ⁻¹ * d := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hκpos.le)
      _ = Δ₀ ^ 2 / 2 := by simp only [κ]; field_simp
      _ ≤ _ := by linarith
  by_cases hb0 : arms jstar = 0
  · -- `a* = 0`: no projection is needed
    refine core arms hspan θ jstar hu Δ₀ hΔ₀ hΔ hcstar n₀ hn₀0 hn₀PD hn₀f (GA arms) hGpos
      (1 : Matrix (Fin d) (Fin d) ℝ) (by simp) (by simp [hb0]) 0 0
      (by intro c w; simp) (by intro w; simp [hb0]) ?_
    intro m _ _ a _
    simp
  · -- `a* ≠ 0`: project onto `(a*)^⊥` with `perpBasis`
    set b := arms jstar with hbdef
    have hex := exists_perp hd b hb0
    have hspec : (perpBasis b)ᵀ * perpBasis b = 1 ∧ (perpBasis b)ᵀ *ᵥ b = 0 :=
      Classical.epsilon_spec hex
    set U := perpBasis b with hUdef
    have hbb : 0 < b ⬝ᵥ b := by
      have hnn : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun i _ => mul_self_nonneg (b i)
      exact lt_of_le_of_ne hnn fun h => hb0 (dotProduct_self_eq_zero.mp h.symm)
    set ρ := Real.sqrt (b ⬝ᵥ b) with hρdef
    have hρpos : 0 < ρ := Real.sqrt_pos.mpr hbb
    have hρsq : ρ * ρ = b ⬝ᵥ b := Real.mul_self_sqrt hbb.le
    set uv : Fin d → ℝ := ρ⁻¹ • b with huvdef
    have hUu : Uᵀ *ᵥ uv = 0 := by rw [huvdef, Matrix.mulVec_smul, hspec.2, smul_zero]
    have huu : uv ⬝ᵥ uv = 1 := by
      rw [huvdef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hρsq]
      field_simp
    have hcomp := complete_decomp hd U uv hspec.1 hUu huu
    have hz : ∀ c, arms c ⬝ᵥ uv = (b ⬝ᵥ arms c) / ρ := by
      intro c
      rw [huvdef, dotProduct_smul, smul_eq_mul, dotProduct_comm]
      field_simp
    refine core arms hspan θ jstar hu Δ₀ hΔ₀ hΔ hcstar n₀ hn₀0 hn₀PD hn₀f (GA arms) hGpos
      U hspec.1 hspec.2 uv ρ hcomp ?_ ?_
    · intro w
      rw [huvdef, smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hρpos.ne', one_mul]
    · intro m hm0 hV a ha
      have hC4 := lemma_C_4 (fun c => Uᵀ *ᵥ arms c) (fun c => arms c ⬝ᵥ uv) m hm0 hV
      obtain ⟨heq, hω0, hω1⟩ := hC4
      simp only at heq hω0 hω1
      rw [heq, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul]
      -- write the residual as an average of interpolation residuals
      set filt := Finset.univ.filter (fun I : {I : Finset (Fin K) // I.card = d - 1} =>
        (Matrix.of fun i k => (Uᵀ *ᵥ arms (I.1.orderEmbOfFin I.2 i)) k :
          Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ).det ≠ 0) with hfilt
      set ω := fun I : {I : Finset (Fin K) // I.card = d - 1} =>
        (Matrix.of fun i k => (Uᵀ *ᵥ arms (I.1.orderEmbOfFin I.2 i)) k :
          Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ).det ^ 2 * (∏ a ∈ I.1, m a) /
          (∑ a, m a • vecMulVec (Uᵀ *ᵥ arms a) (Uᵀ *ᵥ arms a)).det with hωdef
      set v := fun I : {I : Finset (Fin K) // I.card = d - 1} =>
        (Matrix.of fun i k => (Uᵀ *ᵥ arms (I.1.orderEmbOfFin I.2 i)) k :
          Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ)⁻¹ *ᵥ
            fun i => arms (I.1.orderEmbOfFin I.2 i) ⬝ᵥ uv with hvdef
      have hsplit : arms a ⬝ᵥ uv - ∑ I ∈ filt, ω I * ((Uᵀ *ᵥ arms a) ⬝ᵥ v I) =
          ∑ I ∈ filt, ω I * (arms a ⬝ᵥ uv - (Uᵀ *ᵥ arms a) ⬝ᵥ v I) := by
        have h1 : ∑ I ∈ filt, ω I * (arms a ⬝ᵥ uv - (Uᵀ *ᵥ arms a) ⬝ᵥ v I) =
            (∑ I ∈ filt, ω I) * (arms a ⬝ᵥ uv) - ∑ I ∈ filt, ω I * ((Uᵀ *ᵥ arms a) ⬝ᵥ v I) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun I _ => by ring
        rw [h1, hω1, one_mul]
      rw [hsplit]
      -- each interpolation residual is at most `G_𝒜 ρ`
      have hI : ∀ I ∈ filt, |arms a ⬝ᵥ uv - (Uᵀ *ᵥ arms a) ⬝ᵥ v I| ≤ GA arms * ρ := by
        intro I hImem
        have hdet := (Finset.mem_filter.mp hImem).2
        have hjI : jstar ∉ I.1 := by
          intro hj
          have hj' : jstar ∈ Set.range (I.1.orderEmbOfFin I.2) := by
            rw [Finset.range_orderEmbOfFin]; exact hj
          obtain ⟨i, hi⟩ := hj'
          apply hdet
          apply Matrix.det_eq_zero_of_row_eq_zero i
          intro k
          simp only [Matrix.of_apply, hi]
          rw [← hbdef, hspec.2]
          rfl
        have hg := hGmem jstar I.1 I.2 a hb0 hjI ha hdet
        have hvI : v I = (Matrix.of fun i k => (Uᵀ *ᵥ arms (I.1.orderEmbOfFin I.2 i)) k :
            Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ)⁻¹ *ᵥ
              fun i => (b ⬝ᵥ arms (I.1.orderEmbOfFin I.2 i)) / ρ := by
          simp only [v]
          congr 1
          funext i
          exact hz _
        rw [hz a, hvI]
        exact (div_le_iff₀ hρpos).mp hg
      calc |∑ I ∈ filt, ω I * (arms a ⬝ᵥ uv - (Uᵀ *ᵥ arms a) ⬝ᵥ v I)|
          ≤ ∑ I ∈ filt, |ω I * (arms a ⬝ᵥ uv - (Uᵀ *ᵥ arms a) ⬝ᵥ v I)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ I ∈ filt, ω I * (GA arms * ρ) := by
            refine Finset.sum_le_sum fun I hImem => ?_
            rw [abs_mul, abs_of_nonneg (hω0 I)]
            exact mul_le_mul_of_nonneg_left (hI I hImem) (hω0 I)
        _ = GA arms * ρ := by rw [← Finset.sum_mul, hω1, one_mul]
