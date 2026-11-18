-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.residual_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:01:15.544203+00:00
-- url     : https://prove2.me/submissions/abe93ee5-8fe1-4383-8a24-381fa0e321ca

import Definitions.Def_NearlyOptimalPPR_Computation_model

set_option autoImplicit false
open Finset Matrix
open NearlyOptimalPPR.Computation

namespace NearlyOptimalPPR.Computation
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance positive_adjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (positiveGraph G).Adj :=
  inferInstanceAs (DecidableRel (G.induce {v | 0 < G.degree v}).Adj)

lemma lap_mul_apply (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (x : V → ℝ) (v : V) :
    (LocalPush.Lα G α *ᵥ x) v =
      LocalPush.deg G v * x v - (1 - α) * ∑ u ∈ G.neighborFinset v, x u := by
  simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, sub_mulVec,
    smul_mulVec, SimpleGraph.adjMatrix_mulVec_apply, mulVec_diagonal]

lemma lap_maximum_principle (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : LocalPush.NoIsolated G) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ (LocalPush.Lα G α *ᵥ x) v) :
    ∀ v, 0 ≤ x v := by
  intro v
  by_contra hv
  have hv : x v < 0 := lt_of_not_ge hv
  obtain ⟨w, _, hw⟩ := Finset.exists_min_image Finset.univ x ⟨v, mem_univ v⟩
  have hwv : x w ≤ x v := hw v (mem_univ v)
  have hd : 0 < LocalPush.deg G w := by
    unfold LocalPush.deg
    exact_mod_cast hG w
  have hs : LocalPush.deg G w * x w ≤ ∑ u ∈ G.neighborFinset w, x u := by
    calc
      _ = ∑ u ∈ G.neighborFinset w, x w := by simp [LocalPush.deg]
      _ ≤ _ := Finset.sum_le_sum fun u _ => hw u (mem_univ u)
  have hh := hx w
  rw [lap_mul_apply] at hh
  have := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hα')
  have hn := mul_neg_of_pos_of_neg (mul_pos hα hd) (lt_of_le_of_lt hwv hv)
  nlinarith

lemma lap_isUnit (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : LocalPush.NoIsolated G) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1) :
    IsUnit (LocalPush.Lα G α) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : LocalPush.Lα G α *ᵥ (x-y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  have hp := lap_maximum_principle G hG α hα hα' (x-y) (by simp [hz])
  have hn := lap_maximum_principle G hG α hα hα' (y-x) (by
    have h : LocalPush.Lα G α *ᵥ (y-x) = 0 := by rw [mulVec_sub, hxy, sub_self]
    simp [h])
  ext v
  have := hp v
  have := hn v
  simp only [Pi.sub_apply] at *
  linarith

lemma pr_potential (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : LocalPush.NoIsolated G) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (b : V → ℝ) :
    LocalPush.pr G α b = potentialOutput G α ((LocalPush.Lα G α)⁻¹ *ᵥ b) := by
  have hdi : LocalPush.Dinv G * LocalPush.degM G = 1 := by
    unfold LocalPush.Dinv LocalPush.degM
    rw [diagonal_mul_diagonal]
    ext i j
    have hd : LocalPush.deg G i ≠ 0 := by
      unfold LocalPush.deg
      exact_mod_cast (hG i).ne'
    by_cases h : i = j
    · subst j
      simp [LocalPush.Dinv, LocalPush.degM, hd]
    · simp [LocalPush.Dinv, LocalPush.degM, Matrix.diagonal, h]
  have hm : (1 - (1 - α) • (LocalPush.adjM G * LocalPush.Dinv G)) *
      LocalPush.degM G = LocalPush.Lα G α := by
    rw [sub_mul, one_mul, smul_mul, mul_assoc, hdi, mul_one]
    rfl
  have hi : (1 - (1 - α) • (LocalPush.adjM G * LocalPush.Dinv G))⁻¹ =
      LocalPush.degM G * (LocalPush.Lα G α)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← mul_assoc, hm]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (lap_isUnit G hG α hα hα'))
  rw [LocalPush.pr, hi]
  ext v
  change α * ((LocalPush.degM G * (LocalPush.Lα G α)⁻¹) *ᵥ b) v =
    α * LocalPush.deg G v * ((LocalPush.Lα G α)⁻¹ *ᵥ b) v
  rw [← mulVec_mulVec]
  simp only [LocalPush.degM, mulVec_diagonal]
  ring

lemma lap_inverse_solve (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : LocalPush.NoIsolated G) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (b : V → ℝ) :
    LocalPush.Lα G α *ᵥ ((LocalPush.Lα G α)⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (lap_isUnit G hG α hα hα')), one_mulVec]

lemma lap_inverse_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : LocalPush.NoIsolated G) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (ε : ℝ) (b : V → ℝ) (hb : ∀ v, 0 ≤ b v ∧ b v ≤ ε * LocalPush.deg G v) :
    ∀ v, 0 ≤ ((LocalPush.Lα G α)⁻¹ *ᵥ b) v ∧
      ((LocalPush.Lα G α)⁻¹ *ᵥ b) v ≤ ε / α := by
  have hs := lap_inverse_solve G hG α hα hα' b
  have hpos := lap_maximum_principle G hG α hα hα' ((LocalPush.Lα G α)⁻¹ *ᵥ b) (by rw [hs]; exact fun v => (hb v).1)
  have hc : LocalPush.Lα G α *ᵥ (fun _ => ε / α) = fun v => ε * LocalPush.deg G v := by
    ext v
    rw [lap_mul_apply]
    simp only [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree,
      LocalPush.deg]
    field_simp
    <;> ring
  have hle := lap_maximum_principle G hG α hα hα'
    ((fun _ => ε / α) - ((LocalPush.Lα G α)⁻¹ *ᵥ b)) (by
      rw [mulVec_sub, hc, hs]
      exact fun v => sub_nonneg.mpr (hb v).2)
  exact fun v => ⟨hpos v, sub_nonneg.mp (hle v)⟩

lemma positive_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : PositiveVertices G) : (positiveGraph G).degree v = G.degree v := by
  unfold positiveGraph
  exact SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := {v | 0 < G.degree v}) (v := v)
    (fun u hu => (show G.Adj v.val u from hu).degree_pos_right)

lemma positive_lap (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) :
    (LocalPush.Lα G α).submatrix Subtype.val Subtype.val =
      LocalPush.Lα (positiveGraph G) α := by
  ext i j
  simp only [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, submatrix_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
  congr 1
  · by_cases h : i = j
    · subst j
      simp [LocalPush.deg, positive_degree]
    · have hh : i.val ≠ j.val := fun h' => h (Subtype.ext h')
      simp [Matrix.diagonal_apply_ne _ hh, Matrix.diagonal_apply_ne _ h]

lemma lap_restrict (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (z : V → ℝ) (v : PositiveVertices G) :
    (LocalPush.Lα G α *ᵥ z) v =
      (LocalPush.Lα (positiveGraph G) α *ᵥ (fun u => z u)) v := by
  rw [lap_mul_apply, lap_mul_apply]
  have hd : LocalPush.deg (positiveGraph G) v = LocalPush.deg G v := by
    simp [LocalPush.deg, positive_degree]
  rw [hd]
  congr 1
  congr 1
  apply Finset.sum_bij (fun u hu => (⟨u, SimpleGraph.Adj.degree_pos_right
      (by simpa only [SimpleGraph.mem_neighborFinset] using hu)⟩ : PositiveVertices G))
  · intro u hu
    exact ((positiveGraph G).mem_neighborFinset v _).mpr
      (show (positiveGraph G).Adj v _ from (G.mem_neighborFinset v.val u).mp hu)
  · intro u hu w hw he
    exact congrArg Subtype.val he
  · intro u hu
    exact ⟨u.val, (G.mem_neighborFinset v.val _).mpr
      (show G.Adj v.val u.val from ((positiveGraph G).mem_neighborFinset v _).mp hu), by simp⟩
  · intro u hu
    rfl

lemma residual_restrict (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : V) (hs : 0 < G.degree s) (α : ℝ) (z : V → ℝ) :
    (fun v : PositiveVertices G => residual G α s z v) =
      LocalPush.e (⟨s, hs⟩ : PositiveVertices G) -
        LocalPush.Lα (positiveGraph G) α *ᵥ (fun v => z v) := by
  ext v
  simp only [residual, Pi.sub_apply, lap_restrict]
  congr 1
  simp [LocalPush.e, Pi.single_apply, Subtype.ext_iff]

lemma residual_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : V) (hs : 0 < G.degree s) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (z : V → ℝ) :
    ppr G α s - potentialOutput G α z =
      potentialOutput G α (green G α (residual G α s z)) := by
  have hG : LocalPush.NoIsolated (positiveGraph G) := by
    intro v
    rw [positive_degree]
    exact v.property
  have hm := lap_isUnit (positiveGraph G) hG α hα hα'
  have hid : (LocalPush.Lα (positiveGraph G) α)⁻¹ *ᵥ
      (fun v : PositiveVertices G => residual G α s z v) =
        (LocalPush.Lα (positiveGraph G) α)⁻¹ *ᵥ LocalPush.e ⟨s, hs⟩ -
          (fun v : PositiveVertices G => z v) := by
    rw [residual_restrict G s hs, mulVec_sub, mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hm), one_mulVec]
  ext v
  by_cases hv : 0 < G.degree v
  · have hpr := congrFun (pr_potential (positiveGraph G) hG α hα hα'
        (LocalPush.e ⟨s, hs⟩)) (⟨v, hv⟩ : PositiveVertices G)
    have hh := congrFun hid (⟨v, hv⟩ : PositiveVertices G)
    simp only [Pi.sub_apply] at hh
    have hpr' : ppr G α s v = α * LocalPush.deg G v *
        ((LocalPush.Lα (positiveGraph G) α)⁻¹ *ᵥ LocalPush.e ⟨s, hs⟩) ⟨v, hv⟩ := by
      simp only [potentialOutput, LocalPush.deg, positive_degree] at hpr
      simp only [ppr, dif_pos hs, extendPositive, dif_pos hv]
      convert! hpr using 1 <;> congr! <;> exact Subsingleton.elim _ _
    simp only [Pi.sub_apply, potentialOutput, green, positive_lap, extendPositive, dif_pos hv]
    rw [hpr']
    have key :
        α * LocalPush.deg G v * ((LocalPush.Lα (positiveGraph G) α)⁻¹ *ᵥ LocalPush.e ⟨s, hs⟩) ⟨v, hv⟩ -
          α * LocalPush.deg G v * z v =
        α * LocalPush.deg G v *
          ((LocalPush.Lα (positiveGraph G) α)⁻¹ *ᵥ (fun u : PositiveVertices G => residual G α s z u)) ⟨v, hv⟩ := by
      rw [hh]
      ring
    convert! key using 1 <;> congr! <;> exact Subsingleton.elim _ _

  · have hd : LocalPush.deg G v = 0 := by
      unfold LocalPush.deg
      exact_mod_cast (Nat.eq_zero_of_not_pos hv)
    simp [ppr, hs, extendPositive, hv, potentialOutput, hd]

lemma residual_acl (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : V) (hs : 0 < G.degree s) (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1)
    (ε : ℝ) (z : V → ℝ)
    (hr : ∀ v, 0 ≤ residual G α s z v ∧ residual G α s z v ≤ ε * LocalPush.deg G v) :
    ACL G α ε s (potentialOutput G α z) := by
  have hG : LocalPush.NoIsolated (positiveGraph G) := by
    intro v
    rw [positive_degree]
    exact v.property
  have hb : ∀ v : PositiveVertices G,
      0 ≤ residual G α s z v ∧ residual G α s z v ≤ ε * LocalPush.deg (positiveGraph G) v := by
    intro v
    simpa only [LocalPush.deg, positive_degree] using hr v
  have hbnd := lap_inverse_bound (positiveGraph G) hG α hα hα' ε
      (fun v : PositiveVertices G => residual G α s z v) hb
  have hid := residual_identity G s hs α hα hα' z
  intro v
  have hh := congrFun hid v
  simp only [Pi.sub_apply] at hh
  rw [abs_sub_comm, hh]
  by_cases hv : 0 < G.degree v
  · have hp := hbnd (⟨v, hv⟩ : PositiveVertices G)
    simp only [potentialOutput, green, positive_lap, extendPositive, dif_pos hv]
    have hd : 0 ≤ LocalPush.deg G v := by unfold LocalPush.deg; positivity
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hα.le hd) hp.1)]
    calc
      _ ≤ α * LocalPush.deg G v * (ε / α) :=
        mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hα.le hd)
      _ = ε * LocalPush.deg G v := by field_simp
  · have hd : LocalPush.deg G v = 0 := by
      unfold LocalPush.deg
      exact_mod_cast (Nat.eq_zero_of_not_pos hv)
    simp [potentialOutput, hd]

end NearlyOptimalPPR.Computation

open NearlyOptimalPPR.Computation

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < G.degree s)
    (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) :
    ppr G α s - potentialOutput G α z =
        potentialOutput G α (green G α (residual G α s z)) ∧
      ((∀ v, 0 ≤ residual G α s z v ∧ residual G α s z v ≤ ε * LocalPush.deg G v) →
        ACL G α ε s (potentialOutput G α z)) := by
  exact ⟨residual_identity G s hs α hα.1 hα.2.le z,
    fun hr => residual_acl G s hs α hα.1 hα.2.le ε z hr⟩

