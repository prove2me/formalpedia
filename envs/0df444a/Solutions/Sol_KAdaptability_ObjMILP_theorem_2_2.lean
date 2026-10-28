-- Prove2me | solution 2 for KAdaptability.ObjMILP.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:56:07.387983+00:00
-- url     : https://prove2.me/submissions/f491889c-b677-4f6d-b1ba-cf76659c2d94

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem
import Definitions.Def_KAdaptability_ObjMILP_POK
import Definitions.Def_KAdaptability_ObjMILP_MILP5
import Theorems.Thm_LP_exists_dual_of_isBounded
import Theorems.Thm_LP_strong_duality_matrix

-- carved verbatim out of submission 68409d51-7f93-472d-85a5-9b7ccebaa982, lines 844-882

section
open Matrix
open KAdaptability.ObjMILP
variable {N M L nQ R : ℕ}

lemma beta_le_one {K : ℕ} (β : Fin K → ℝ) (hβ : 0 ≤ β) (hs : (1 : Fin K → ℝ) ⬝ᵥ β = 1)
    (k : Fin K) : β k ≤ 1 := by
  have hs' : ∑ j, β j = 1 := by simpa [dotProduct] using hs
  rw [← hs']
  exact Finset.single_le_sum (fun j _ => hβ j) (Finset.mem_univ k)

noncomputable def bigA (P : Problem N M L nQ R) (K : ℕ) (ys : Fin K → Fin M → ℝ) :
    Matrix (Fin R ⊕ Fin K) (Fin nQ ⊕ Unit) ℝ :=
  Matrix.fromBlocks P.A 0 (Matrix.of fun k j => -(P.Q *ᵥ ys k) j) (Matrix.of fun _ _ => 1)

lemma iInf_coe_eq {K : ℕ} (r : Fin K → ℝ) (k0 : Fin K) (hk0 : ∀ k, r k0 ≤ r k) :
    (⨅ k, ((r k : ℝ) : EReal)) = ((r k0 : ℝ) : EReal) :=
  le_antisymm (iInf_le _ k0) (le_iInf fun k => EReal.coe_le_coe_iff.mpr (hk0 k))

lemma mcCormick_eq {M : ℕ} (y z : Fin M → ℝ) (b : ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hz0 : 0 ≤ z) (hzy : z ≤ y) (hzb : z ≤ b • (1 : Fin M → ℝ))
    (hzl : (b - 1) • (1 : Fin M → ℝ) + y ≤ z) : z = b • y := by
  funext i
  have h0 := hz0 i; have h1 := hzy i; have h2 := hzb i; have h3 := hzl i
  simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
    mul_one] at h0 h1 h2 h3 ⊢
  rcases hy i with h | h <;> rw [h] at h1 h3 ⊢ <;> linarith

lemma objPOK_le (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ) (ys zs : Fin K → Fin M → ℝ)
    (α : Fin R → ℝ) (β : Fin K → ℝ) (hF : P.MILPFeasible K x ys zs α β) :
    P.objPOK K x ys ≤ ((P.b ⬝ᵥ α : ℝ) : EReal) := by
  obtain ⟨_, hY, hz0, hα, hβ, hA, hs, hk⟩ := hF
  have hzs : ∀ k, zs k = β k • ys k := fun k =>
    mcCormick_eq (ys k) (zs k) (β k) (P.Y_binary _ (hY k)) (hz0 k) (hk k).2.1 (hk k).2.2.1
      (hk k).2.2.2
  have hK : Nonempty (Fin K) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [dotProduct] at hs
  unfold Problem.objPOK
  refine iSup₂_le fun ξ hξ => ?_
  obtain ⟨k0, hk0⟩ := Finite.exists_min (fun k => ξ ⬝ᵥ (P.Q *ᵥ ys k))
  rw [iInf_coe_eq _ k0 hk0, ← EReal.coe_add, EReal.coe_le_coe_iff]
  -- weighted average ≥ minimum
  have hs' : ∑ j, β j = 1 := by simpa [dotProduct] using hs
  have havg : ξ ⬝ᵥ (P.Q *ᵥ ys k0) ≤ ∑ k, β k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) := by
    calc ξ ⬝ᵥ (P.Q *ᵥ ys k0) = ∑ k, β k * (ξ ⬝ᵥ (P.Q *ᵥ ys k0)) := by
          rw [← Finset.sum_mul, hs', one_mul]
      _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk0 k) (hβ k)
  have hid : ξ ⬝ᵥ (P.C *ᵥ x) + ∑ k, β k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) = (P.A *ᵥ ξ) ⬝ᵥ α := by
    have e : (P.A *ᵥ ξ) ⬝ᵥ α = ξ ⬝ᵥ (P.Aᵀ *ᵥ α) := by rw [dotProduct_mulVec, vecMul_transpose]
    rw [e, hA, dotProduct_add, dotProduct_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hzs k, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hAb : (P.A *ᵥ ξ) ⬝ᵥ α ≤ P.b ⬝ᵥ α := dotProduct_le_dotProduct_of_nonneg_right hξ hα
  linarith

lemma exists_attain (P : Problem N M L nQ R) (K : ℕ) (hK : 0 < K) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) (hF : P.FeasibleK K x ys) :
    ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
      P.MILPFeasible K x ys zs α β ∧ ((P.b ⬝ᵥ α : ℝ) : EReal) = P.objPOK K x ys := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  set bb : Fin R ⊕ Fin K → ℝ := Sum.elim P.b 0 with hbb
  set cc : Fin nQ ⊕ Unit → ℝ := Sum.elim (P.C *ᵥ x) (fun _ => 1) with hcc
  -- primal feasibility
  have hP : ∃ v, bigA P K ys *ᵥ v ≤ bb := by
    obtain ⟨ξ0, hξ0⟩ := P.Xi_nonempty
    obtain ⟨k0, hk0⟩ := Finite.exists_min (fun k => ξ0 ⬝ᵥ (P.Q *ᵥ ys k))
    refine ⟨Sum.elim ξ0 (fun _ => ξ0 ⬝ᵥ (P.Q *ᵥ ys k0)), ?_⟩
    intro i
    rcases i with r | k
    · simpa [bigA, fromBlocks_mulVec, hbb] using hξ0 r
    · have := hk0 k
      simp only [bigA, fromBlocks_mulVec, hbb, Sum.elim_inr, Pi.add_apply, Pi.zero_apply]
      simp only [mulVec, dotProduct, of_apply, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
        Finset.univ_unique, Finset.sum_singleton, one_mul, neg_mul, Finset.sum_neg_distrib]
      simp only [dotProduct, mulVec] at this
      have e : ∑ x, (∑ x_1, P.Q x x_1 * ys k x_1) * ξ0 x = ∑ i, ξ0 i * ∑ j, P.Q i j * ys k j :=
        Finset.sum_congr rfl fun _ _ => mul_comm _ _
      linarith
  -- dual feasibility
  have hD : ∃ w, 0 ≤ w ∧ (bigA P K ys)ᵀ *ᵥ w = cc := by
    let k0 : Fin K := ⟨0, hK⟩
    obtain ⟨α0, hα0, hA0⟩ := LP.exists_dual_of_isBounded P.A P.b P.Xi_nonempty
      P.Xi_bounded (P.C *ᵥ x + P.Q *ᵥ ys k0)
    refine ⟨Sum.elim α0 (fun k => if k = k0 then 1 else 0), ?_, ?_⟩
    · intro i
      rcases i with r | k
      · exact hα0 r
      · simp only [Sum.elim_inr, Pi.zero_apply]; split_ifs <;> norm_num
    · funext j
      rcases j with j | u
      · have := congrFun hA0 j
        simp only [bigA, fromBlocks_transpose, fromBlocks_mulVec, hcc, Sum.elim_inl,
          Pi.add_apply, Function.comp_def] at this ⊢
        rw [this]
        simp [mulVec, dotProduct, transpose_apply, of_apply]
      · simp [bigA, hcc, mulVec, dotProduct]
  obtain ⟨v, w, hv, hw0, hwA, hval, -⟩ := LP.strong_duality_matrix _ bb cc hP hD
  set ξ : Fin nQ → ℝ := v ∘ Sum.inl with hξdef
  set t : ℝ := v (Sum.inr ()) with htdef
  set α : Fin R → ℝ := w ∘ Sum.inl with hαdef
  set β : Fin K → ℝ := w ∘ Sum.inr with hβdef
  -- extract primal facts
  have hξ : ξ ∈ P.Xi := by
    intro r
    have := hv (Sum.inl r)
    simpa [bigA, fromBlocks_mulVec, hbb, Function.comp_def, hξdef] using this
  have ht : ∀ k, t ≤ ξ ⬝ᵥ (P.Q *ᵥ ys k) := by
    intro k
    have := hv (Sum.inr k)
    simp only [bigA, fromBlocks_mulVec, hbb, Sum.elim_inr, Pi.add_apply, Pi.zero_apply] at this
    simp only [mulVec, dotProduct, of_apply, Function.comp_apply, Finset.univ_unique,
      Finset.sum_singleton, one_mul, neg_mul, Finset.sum_neg_distrib] at this
    have e : ∑ x, (∑ x_1, P.Q x x_1 * ys k x_1) * v (Sum.inl x) =
        ξ ⬝ᵥ (P.Q *ᵥ ys k) := by
      simp only [dotProduct, mulVec, hξdef, Function.comp_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have : t = v (Sum.inr default) := rfl
    linarith
  -- extract dual facts
  have hα : 0 ≤ α := fun r => hw0 (Sum.inl r)
  have hβ : 0 ≤ β := fun k => hw0 (Sum.inr k)
  have hsum : (1 : Fin K → ℝ) ⬝ᵥ β = 1 := by
    have := congrFun hwA (Sum.inr ())
    simpa [bigA, fromBlocks_transpose, fromBlocks_mulVec, hcc, mulVec, dotProduct,
      Function.comp_def, hβdef] using this
  have hAα : P.Aᵀ *ᵥ α = P.C *ᵥ x + ∑ k, P.Q *ᵥ (β k • ys k) := by
    funext j
    have := congrFun hwA (Sum.inl j)
    simp only [bigA, fromBlocks_transpose, fromBlocks_mulVec, hcc, Sum.elim_inl,
      Pi.add_apply] at this
    have e : ((of fun k j => -(P.Q *ᵥ ys k) j : Matrix (Fin K) (Fin nQ) ℝ)ᵀ *ᵥ
        (w ∘ Sum.inr)) j = -∑ k, β k * (P.Q *ᵥ ys k) j := by
      simp only [mulVec, dotProduct, transpose_apply, of_apply, hβdef, neg_mul,
        Finset.sum_neg_distrib]
      exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
    simp only [mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rw [e] at this
    have hα' : (P.Aᵀ *ᵥ α) j = (P.Aᵀ *ᵥ (w ∘ Sum.inl)) j := rfl
    linarith
  have hvalue : P.b ⬝ᵥ α = ξ ⬝ᵥ (P.C *ᵥ x) + t := by
    have e1 : cc ⬝ᵥ v = (P.C *ᵥ x) ⬝ᵥ ξ + t := by
      simp [hcc, dotProduct, Fintype.sum_sum_type, hξdef, htdef]
    have e2 : bb ⬝ᵥ w = P.b ⬝ᵥ α := by
      simp [hbb, dotProduct, Fintype.sum_sum_type, hαdef]
    rw [← e2, ← hval, e1, dotProduct_comm]
  have hFeas : P.MILPFeasible K x ys (fun k => β k • ys k) α β := by
    obtain ⟨hX, hk⟩ := hF
    refine ⟨hX, fun k => (hk k).1, ?_, hα, hβ, hAα, hsum, fun k => ⟨(hk k).2, ?_, ?_, ?_⟩⟩
    · intro k i
      have hb0 : 0 ≤ β k := hβ k
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      rcases P.Y_binary _ (hk k).1 i with h | h <;> simp [h, hb0]
    all_goals
      intro i
      have hb1 := beta_le_one β hβ hsum k
      have hb0 : 0 ≤ β k := hβ k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      rcases P.Y_binary _ (hk k).1 i with h | h <;> rw [h] <;> linarith
  refine ⟨fun k => β k • ys k, α, β, hFeas, le_antisymm ?_ (objPOK_le P K x ys _ α β hFeas)⟩
  unfold Problem.objPOK
  refine le_trans ?_ (le_iSup₂ (f := fun ξ (_ : ξ ∈ P.Xi) =>
    (((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + ⨅ k, ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal))) ξ hξ)
  rw [hvalue, EReal.coe_add]
  exact add_le_add le_rfl (le_iInf fun k => EReal.coe_le_coe_iff.mpr (ht k))

end

section
open Matrix

open KAdaptability.ObjMILP in
theorem solution {N M L nQ R : ℕ} (P : Problem N M L nQ R) (K : ℕ) (hK : 0 < K) :
    (∀ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ),
      P.FeasibleK K x ys ↔
        ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
          P.MILPFeasible K x ys zs α β) ∧
    (∀ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ), P.FeasibleK K x ys →
      P.objPOK K x ys = P.milpValueAt K x ys ∧
        ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
          P.MILPFeasible K x ys zs α β ∧ ((P.b ⬝ᵥ α : ℝ) : EReal) = P.objPOK K x ys) ∧
    P.optPOK K = P.optMILP K := by
  have hfeas : ∀ x ys zs α β, P.MILPFeasible K x ys zs α β → P.FeasibleK K x ys :=
    fun x ys zs α β h => ⟨h.1, fun k => ⟨h.2.1 k, (h.2.2.2.2.2.2.2 k).1⟩⟩
  refine ⟨fun x ys => ⟨fun h => ?_, fun ⟨zs, α, β, h⟩ => hfeas x ys zs α β h⟩,
    fun x ys h => ⟨?_, exists_attain P K hK x ys h⟩, ?_⟩
  · obtain ⟨zs, α, β, h', -⟩ := exists_attain P K hK x ys h
    exact ⟨zs, α, β, h'⟩
  · obtain ⟨zs, α, β, h', he⟩ := exists_attain P K hK x ys h
    refine le_antisymm ?_ ?_
    · unfold Problem.milpValueAt
      exact le_iInf fun zs => le_iInf fun α => le_iInf fun β => le_iInf fun hF =>
        objPOK_le P K x ys zs α β hF
    · rw [← he]
      unfold Problem.milpValueAt
      exact iInf_le_of_le zs <| iInf_le_of_le α <| iInf_le_of_le β <| iInf_le _ h'
  · refine le_antisymm ?_ ?_
    · unfold Problem.optMILP Problem.optPOK
      refine le_iInf fun x => le_iInf fun ys => le_iInf fun zs => le_iInf fun α =>
        le_iInf fun β => le_iInf fun hF => ?_
      exact iInf_le_of_le x <| iInf_le_of_le ys <| iInf_le_of_le (hfeas x ys zs α β hF) <|
        objPOK_le P K x ys zs α β hF
    · unfold Problem.optMILP Problem.optPOK
      refine le_iInf fun x => le_iInf fun ys => le_iInf fun hF => ?_
      obtain ⟨zs, α, β, h', he⟩ := exists_attain P K hK x ys hF
      rw [← he]
      exact iInf_le_of_le x <| iInf_le_of_le ys <| iInf_le_of_le zs <| iInf_le_of_le α <|
        iInf_le_of_le β <| iInf_le _ h'

end
