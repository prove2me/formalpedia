-- Prove2me | solution 1 for OAI.Saxl.Path.fourRow_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:20:04.700648+00:00
-- url     : https://prove2.me/submissions/bb329a48-c04f-4d30-ac4d-a2ce9c9d15ed

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandPairing.lean:L111-L126
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.Path.fourRow_support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Theorems.Thm_OAI_Saxl_Band_basis_mul
import Theorems.Thm_OAI_Saxl_Columns_mapped_columnTableau
import Theorems.Thm_OAI_Saxl_hom_to_cyclic_of_pair

-- ---- from OAI.RepresentationTheory.Saxl.BandMatrices ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band
/- Consecutive segments with the original global position parities. -/
/- Enumeration of the finite symmetric group for the four small matrix calculations. -/
lemma sum_perm_succ {A : Type uA} [AddCommMonoid A] (n : ℕ)
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ π, f π) = ∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, σ)) := by
  calc
    (∑ π, f π) = ∑ x : Fin (n + 1) × Equiv.Perm (Fin n),
        f (Equiv.Perm.decomposeFin.symm x) :=
      Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (by intro π; simp)
    _ = _ := Fintype.sum_prod_type _

lemma decompose_apply_two {n : ℕ} (e : Equiv.Perm (Fin (n + 2))) (p : Fin (n + 3)) :
    Equiv.Perm.decomposeFin.symm (p, e) 2 = Equiv.swap 0 p (e 1).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (1 : Fin (n + 2)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 1

lemma decompose_apply_three {n : ℕ} (e : Equiv.Perm (Fin (n + 3))) (p : Fin (n + 4)) :
    Equiv.Perm.decomposeFin.symm (p, e) 3 = Equiv.swap 0 p (e 2).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (2 : Fin (n + 3)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 2

lemma segment_one_even : segment 1 0 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_one_odd : segment 1 1 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_two_even : segment 2 0 = (2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_two_odd : segment 2 1 = (-2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_three_even : segment 3 0 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_three_odd : segment 3 1 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_four_even : segment 4 0 = (24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma segment_four_odd : segment 4 1 = (-24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff,
      Equiv.Perm.decomposeFin.symm_sign,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/- Only the original global parity matters. -/
lemma segment_mod (r p : ℕ) : segment r p = segment r (p % 2) := by
  simp [segment, D, Nat.add_mod]

lemma scaledBasis_smul (c : ℂ) (hc : c ≠ 0) (i : Fin 4) :
    ScaledBasis (c • basis i.val) := ⟨c, hc, i, rfl⟩

lemma scaledBasis_one : ScaledBasis 1 := by
  exact ⟨1, one_ne_zero, 0, by simp [basis]⟩

lemma ScaledBasis.mul {X Y : Mat} (hX : ScaledBasis X) (hY : ScaledBasis Y) :
    ScaledBasis (X * Y) := by
  obtain ⟨c, hc, i, rfl⟩ := hX
  obtain ⟨d, hd, j, rfl⟩ := hY
  obtain ⟨e, he, k, hk⟩ := basis_mul i j
  refine ⟨c * d * e, mul_ne_zero (mul_ne_zero hc hd) he, k, ?_⟩
  rw [smul_mul_smul_comm, hk, smul_smul]

lemma segment_scaled (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p) := by
  rw [segment_mod]
  have hp := Nat.mod_two_eq_zero_or_one p
  obtain ⟨hr1, hr4⟩ := hr
  interval_cases r <;> rcases hp with hp | hp <;> rw [hp]
  all_goals simp only [segment_one_even, segment_one_odd,
    segment_two_even, segment_two_odd, segment_three_even, segment_three_odd,
    segment_four_even, segment_four_odd]
  all_goals first
    | exact scaledBasis_one
    | exact scaledBasis_smul _ (by norm_num) 0
    | exact scaledBasis_smul _ (by norm_num) 1
    | exact scaledBasis_smul _ (by norm_num) 3

lemma blocks_scaled (rs : List ℕ) (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) (p : ℕ) :
    ScaledBasis (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact scaledBasis_one
  | cons r rs ih =>
    exact (segment_scaled r p (hrs r (by simp))).mul
      (ih (fun a ha => hrs a (by simp [ha])) (p + r))

lemma Q_mul_Qinv : Q * Qinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]

lemma Qinv_mul_Q : Qinv * Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, Qinv, Matrix.mul_apply, Fin.sum_univ_two]

lemma Q_inverse : Q⁻¹ = Qinv := by
  exact Matrix.inv_eq_left_inv Qinv_mul_Q

lemma Q_basis_ne_zero (i : Fin 4) : (Q * basis i.val * Q⁻¹) 0 0 ≠ 0 := by
  rw [Q_inverse]
  fin_cases i <;> norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]

/- Endpoint noncancellation for arbitrary consecutive columns of lengths at most four. -/
end Saxl.Band

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.PathContraction ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path
/- EXACT coefficients of the path-ordered alternating band: the two endpoint
singletons carry letter 0, and row/column pairs have coefficients J. Here r=m-1. -/
/- Ordinary pure position tensor pairing, with no conjugation. -/
lemma chainML_apply (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = (List.ofFn fun i => Band.D (p + i.val) (X i)).prod := rfl

lemma entry_sum (X : Mat) :
    (∑ a : Letter, X (parts a).1 (parts a).2 • entry a) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]

lemma chain_expand (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = ∑ w : Fin n → Letter, pureWord X w •
      chainML n p (fun i => entry (w i)) := by
  calc
    chainML n p X = chainML n p (fun i => ∑ a : Letter,
      X i (parts a).1 (parts a).2 • entry a) := by
        congr 1; funext i; exact (entry_sum (X i)).symm
    _ = _ := ?_
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MultilinearMap.map_smul_univ]
  rfl

lemma adj_entry (a : Letter) (i j : Fin 2) :
    (entry a).adjugate i j = -(J i (parts a).2 * J (parts a).1 j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]

lemma D_shift (q : ℕ) (X : Mat) : Band.D (q + 2) X = Band.D q X := by
  simp [Band.D]

lemma chain_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    chainML (2 * (r+1) + 1) 1 (fun i => entry (w i)) =
      entry (w 0) * (entry (w 1)).adjugate *
      chainML (2 * r + 1) 1 (fun i => entry (w i.succ.succ)) := by
  rw [chainML_apply, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons, chainML_apply]
  simp only [Fin.val_zero, Fin.val_succ, add_zero]
  rw [show Band.D 1 = id from by funext X; simp [Band.D],
    show Band.D 2 = Matrix.adjugate from by funext X; simp [Band.D]]
  simp only [id_eq]
  rw [mul_assoc]
  apply congrArg (fun A : Mat => entry (w 0) * ((entry (w 1)).adjugate * A))
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  rw [show 1 + (i.val + 1 + 1) = (1 + i.val) + 2 by omega, D_shift]

lemma pair_product_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    (∏ i : Fin (r+1), J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) =
    (J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1) *
    ∏ i : Fin r, J (parts (w (leftPos i).succ.succ)).2
      (parts (w (midPos i).succ.succ)).2 *
      J (parts (w (midPos i).succ.succ)).1 (parts (w (rightPos i).succ.succ)).1 := by
  rw [Fin.prod_univ_succ]
  rfl

lemma chain_entries (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) =
    ((-1 : ℂ)^r * ∏ i : Fin r,
      J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) •
    Matrix.single (parts (w 0)).1 (parts (w (Fin.last (2*r)))).2 1 := by
  induction r with
  | zero => simp [chainML_apply, List.ofFn_succ, Band.D, entry]
  | succ r ih =>
    rw [chain_step, ih, Matrix.mul_smul, pair_product_step]
    rw [show (0 : Fin (2*r+1)).succ.succ = 2 from Fin.ext rfl]
    change _ = _ • Matrix.single _ (parts (w (Fin.last (2*r)).succ.succ)).2 1
    unfold entry at *
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [show (Matrix.single (parts (w 1)).1 (parts (w 1)).2 (1 : ℂ)).adjugate
      (parts (w 0)).2 (parts (w 2)).1 =
      -(J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1)
      from adj_entry (w 1) _ _]
    rw [show ∀ (c : ℂ) (i j : Fin 2), Matrix.single i j c = c • Matrix.single i j 1
      from fun c i j => by ext a b; simp [Matrix.single, smul_eq_mul]]
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring

lemma chain_entries_endpoint (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) 0 0 =
      (-1 : ℂ)^r * bandWord r w := by
  rw [chain_entries]
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, Matrix.single, h₁, h₂]

lemma J_real (i j : Fin 2) : star (J i j) = J i j := by
  fin_cases i <;> fin_cases j <;> simp [J]

lemma bandWord_real (r : ℕ) : star (bandWord r) = bandWord r := by
  funext w
  change star (bandWord r w) = bandWord r w
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, h₁, h₂, star_mul, star_prod, J_real, mul_comm]
end Saxl.Path

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.ColumnContraction ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/
/- The matrix product indexed by the actual consecutive position order. -/
lemma chain_cons (r : ℕ) (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat)
    (π : Equiv.Perm (Fin r)) (σ : Perms rs) :
    chain (r :: rs) p N (π, σ) =
      (List.ofFn fun j : Fin r => Band.D (p + j.val) (N (π j).val)).prod *
      chain rs (p + r) N σ := by
  unfold chain
  erw [List.ofFn_add, List.prod_append]
  congr 2
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + j.val) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.castAdd rs.sum j))))) = _
    rw [enumerate_left]
    rfl
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + (r + j.val)) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.natAdd r j))))) = _
    erw [enumerate_right r rs (show Fin rs.sum from j)]
    simp only [perm, Equiv.sumCongr_apply, Sum.map_inr, row, Nat.add_assoc]

/- Ordered product of independent alternating column segments. -/
/- Factorization over independent column permutations, without commuting factors. -/
lemma sum_chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) :
    (∑ π : Perms rs, sg π • chain rs p N π) = segments p rs N := by
  induction rs generalizing p with
  | nil => simp [Perms, chain, sg, segments]
  | cons r rs ih =>
    simp only [Perms, Fintype.sum_prod_type, sg, chain_cons, segments]
    simp_rw [← smul_mul_smul_comm, ← Finset.mul_sum, ← Finset.sum_mul, ih]

/- The column-recursive coordinates enumerate the actual Ferrers cells. -/
end Saxl.Columns

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.BandPairing ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

lemma conjugation_one : conjugation 1 = 1 := by
  change Q * 1 * Qinv = 1
  rw [mul_one, Q_mul_Qinv]

lemma conjugation_mul (X Y : Mat) : conjugation (X * Y) = conjugation X * conjugation Y := by
  change Q * (X * Y) * Qinv = (Q * X * Qinv) * (Q * Y * Qinv)
  simp only [mul_assoc, ← mul_assoc Qinv Q, Qinv_mul_Q, one_mul]

lemma conjugation_D (q : ℕ) (X : Mat) : D q (conjugation X) = conjugation (D q X) := by
  by_cases h : q % 2 = 0
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, h, conjugation, Q, Qinv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  · simp [D, h]

lemma conjugation_prod (l : List Mat) : (l.map conjugation).prod = conjugation l.prod := by
  induction l with
  | nil => simp [conjugation_one]
  | cons a l ih => simp [ih, conjugation_mul]

lemma segments_conjugation (rs : List ℕ) (p : ℕ) :
    Columns.segments p rs (fun i => conjugation (basis i)) = conjugation (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact conjugation_one.symm
  | cons r rs ih =>
    simp only [Columns.segments, blocks, ih, conjugation_mul]
    congr 1
    unfold segment
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [map_smul]
    congr 1
    simp_rw [conjugation_D]
    have he := conjugation_prod (List.ofFn fun j : Fin r => D (p + j.val) (basis (π j).val))
    rw [List.map_ofFn] at he
    exact he

lemma conjugation_blocks_ne_zero (rs : List ℕ)
    (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) : conjugation (blocks 1 rs) 0 0 ≠ 0 := by
  obtain ⟨c, hc, i, hi⟩ := blocks_scaled rs hrs 1
  rw [hi, map_smul]
  apply mul_ne_zero hc
  simpa only [conjugation, LinearMap.coe_mk, AddHom.coe_mk, Q_inverse] using Q_basis_ne_zero i

end Saxl.Band
namespace Saxl.Path

lemma chainFunctional_pure (n p : ℕ) (X : Fin n → Mat) :
    chainFunctional n p (pureWord X) = chainML n p X := (chain_expand n p X).symm

lemma chainFunctional_column (μ : YoungDiagram) (p : ℕ) (N : ℕ → Mat) :
    chainFunctional μ.transpose.rowLens.sum p
      (wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
        N i.val (parts a).1 (parts a).2) (polytabloid (Columns.columnTableau μ))) =
      Columns.segments p μ.transpose.rowLens N := by
  rw [Columns.mapped_columnTableau, map_sum]
  simp_rw [map_smul, chainFunctional_pure]
  exact Columns.sum_chain μ.transpose.rowLens p N

lemma chainFunctional_endpoint (r : ℕ) (x : WordSpace (2*r+1) 4) :
    chainFunctional (2*r+1) 1 x 0 0 = (-1 : ℂ)^r * dotProduct x (bandWord r) := by
  change (∑ w : Fin (2*r+1) → Fin 4,
    x w • chainML (2*r+1) 1 (fun i => entry (w i))) 0 0 = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, chain_entries_endpoint]
  simp [dotProduct, Finset.mul_sum, mul_left_comm]

lemma fourRow_column_lengths (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4) :
    ∀ r ∈ μ.transpose.rowLens, 1 ≤ r ∧ r ≤ 4 := by
  intro r hr
  refine ⟨μ.transpose.pos_of_mem_rowLens r hr, ?_⟩
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
  rw [← he, YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose]
  exact (μ.colLen_anti 0 j (Nat.zero_le _)).trans hμ

lemma fourRow_tableau_noncancellation (n : ℕ) (μ : YoungDiagram)
    (hn : μ.transpose.rowLens.sum = n) (hμ : μ.colLen 0 ≤ 4) :
    ∃ s : Tableau n μ, chainFunctional n 1
      (wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
        Band.conjugation (Band.basis i.val) (parts a).1 (parts a).2) (polytabloid s)) 0 0 ≠ 0 := by
  subst n
  refine ⟨Columns.columnTableau μ, ?_⟩
  rw [chainFunctional_column μ 1 (fun i => Band.conjugation (Band.basis i)),
    Band.segments_conjugation]
  exact Band.conjugation_blocks_ne_zero _ (fourRow_column_lengths μ hμ)

/- The actual complex Specht modules with at most four rows occur in the
specified two-layer alternating path cyclic module. -/
theorem fourRow_support (r : ℕ) (_hr : 2 ≤ r) (μ : YoungDiagram)
    (t : Tableau (2*r+1) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r+1) 4) (bandWord r)).toRepresentation, f ≠ 0 := by
  have hn : μ.transpose.rowLens.sum = 2*r+1 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr ((Columns.columnTableau μ).trans t.symm)
  obtain ⟨s, hs⟩ := fourRow_tableau_noncancellation (2*r+1) μ hn hμ
  let L : Fin (μ.colLen 0) → Fin 4 → ℂ := fun i a =>
    Band.conjugation (Band.basis i.val) (parts a).1 (parts a).2
  apply hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid s, polytabloid_mem_all t s⟩ (bandWord r) (bandWord_real r)
  intro h
  rw [chainFunctional_endpoint] at hs
  exact hs (by change (-1 : ℂ)^r * dotProduct (wordMap L (polytabloid s)) (bandWord r) = 0
               rw [h, mul_zero])

end Saxl.Path

namespace Saxl.PathLayer

end Saxl.PathLayer

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl OAI.Saxl.Path
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.Path.fourRow_support := @_root_.OAI.Saxl.Path.fourRow_support
